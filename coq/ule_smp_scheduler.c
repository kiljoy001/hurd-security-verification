/* ULE-based SMP Scheduler for GNU Hurd - Implementation
 * Based on formally verified Coq specifications
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include "ule_smp_scheduler.h"
#include <mach/mach_types.h>
#include <kern/kern_types.h>
#include <kern/sched_prim.h>
#include <kern/processor.h>
#include <kern/cpu_number.h>
#include <string.h>
#include <assert.h>
#include <math.h>  /* For pow(), exp(), fmax(), fmin() */
#include <sys/time.h>  /* For gettimeofday() */

/* Global scheduler state */
ule_microkernel_state_t *ule_global_scheduler = NULL;
static ule_scheduler_config_t ule_config;

/* Forward declarations */
static void ule_message_queue_init(ule_message_queue_t *queue);
static kern_return_t ule_message_queue_enqueue(ule_message_queue_t *queue, ule_message_t *msg);
static ule_message_t *ule_message_queue_dequeue(ule_message_queue_t *queue);
static ule_server_queue_t *ule_server_lookup(uint32_t server_id);
static uint64_t ule_get_current_time_ms(void);
static void ule_init_default_nash_components(ule_nash_components_t *nash);

/*
 * Interactivity calculation - implements verified calculate_interactivity
 * 
 * From Coq proof:
 * Definition calculate_interactivity (sleep run : nat) : nat :=
 *   if Nat.ltb 0 run then
 *     if Nat.leb sleep run then
 *       min 100 (50 + (run * 50) / (sleep + 1))
 *     else
 *       min 100 ((sleep * 50) / (run + 1))
 *   else 0.
 *
 * Theorem: calculate_interactivity sleep run <= 100 (verified)
 */
uint32_t 
ule_calculate_interactivity(uint32_t sleep_time, uint32_t run_time)
{
    /* Verified bounds: result is always <= 100 */
    if (run_time > 0) {
        if (sleep_time <= run_time) {
            /* Non-interactive case: sleep <= run */
            uint32_t interactivity = ULE_INTERACTIVITY_BASE + 
                                   (run_time * ULE_INTERACTIVITY_BASE) / (sleep_time + 1);
            return (interactivity > ULE_INTERACTIVITY_MAX) ? 
                   ULE_INTERACTIVITY_MAX : interactivity;
        } else {
            /* Interactive case: sleep > run */
            uint32_t interactivity = (sleep_time * ULE_INTERACTIVITY_BASE) / (run_time + 1);
            return (interactivity > ULE_INTERACTIVITY_MAX) ? 
                   ULE_INTERACTIVITY_MAX : interactivity;
        }
    }
    return 0;
}

/*
 * Interactive message classification - implements verified is_interactive
 * 
 * From Coq proof:
 * Definition is_interactive (m : message) : bool :=
 *   Nat.leb (calculate_interactivity (sleep_time m) (run_time m)) 30.
 */
bool 
ule_is_interactive(ule_message_t *msg)
{
    assert(msg != NULL);
    
    uint32_t interactivity = ule_calculate_interactivity(msg->sleep_time, msg->run_time);
    return interactivity <= ule_config.interactive_threshold;
}

/*
 * Growth function g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2
 * 
 * From Coq specification:
 * Definition growth_function (t : threat_data) : R :=
 *   let k1 := (1.5)%R in
 *   let k2 := (2.0)%R in
 *   (1 + k1 * threat_probability t * Rpower (2 - defense_effectiveness t) k2)%R.
 */
double 
ule_growth_function(double threat_probability, double defense_effectiveness, double k1, double k2)
{
    assert(threat_probability >= 0.0 && threat_probability <= 1.0);
    assert(defense_effectiveness >= 0.0 && defense_effectiveness <= 1.0);
    assert(k1 > 0.0 && k2 > 0.0);
    
    /* Implements g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2 */
    double effectiveness_term = 2.0 - defense_effectiveness;
    double power_term = pow(effectiveness_term, k2);
    return 1.0 + k1 * threat_probability * power_term;
}

/*
 * Sum of growth functions for all active threats: ∑_{i∈active} g(p_i, E_i)
 * 
 * From Coq specification:
 * Fixpoint threat_sum (threats : list threat_data) : R :=
 *   match threats with
 *   | [] => (1.0)%R
 *   | t :: rest => (growth_function t + threat_sum rest)%R
 *   end.
 */
double 
ule_threat_sum(ule_threat_data_t *threats, uint32_t num_threats)
{
    if (num_threats == 0 || threats == NULL) {
        return 1.0;  /* Default to 1.0 if no active threats */
    }
    
    double sum = 0.0;
    for (uint32_t i = 0; i < num_threats; i++) {
        sum += ule_growth_function(threats[i].threat_probability,
                                 threats[i].defense_effectiveness,
                                 ULE_DYNAMIC_BCRA_K1,
                                 ULE_DYNAMIC_BCRA_K2);
    }
    return sum;
}

/*
 * Nash equilibrium multiplier Π_nash
 * 
 * From Coq specification:
 * Definition nash_multiplier (nc : nash_components) : R :=
 *   let w1 := (0.3)%R in let w2 := (0.2)%R in let w3 := (0.2)%R in
 *   let w4 := (0.15)%R in let w5 := (0.15)%R in
 *   (w1 * equilibrium_factor nc + w2 * competition_factor nc + 
 *    w3 * reputation_factor nc + w4 * bayesian_factor nc + 
 *    w5 * signaling_factor nc)%R.
 */
double 
ule_nash_multiplier(ule_nash_components_t *nash)
{
    assert(nash != NULL);
    
    return ULE_NASH_WEIGHT_EQUILIBRIUM * nash->equilibrium_factor +
           ULE_NASH_WEIGHT_COMPETITION * nash->competition_factor +
           ULE_NASH_WEIGHT_REPUTATION * nash->reputation_factor +
           ULE_NASH_WEIGHT_BAYESIAN * nash->bayesian_factor +
           ULE_NASH_WEIGHT_SIGNALING * nash->signaling_factor;
}

/*
 * Full Dynamic BCRA formula implementation
 * 
 * Scott J. Guyton's complete Dynamic BCRA formula:
 * CA(t) = max(10, min(C_max, C_base × ∑_{i∈active} g(p_i, E_i) × Π_nash))
 * 
 * From Coq specification:
 * Definition dynamic_routing_cost (ca : route_ca) : R :=
 *   let threat_component := threat_sum (active_threats ca) in
 *   let nash_component := nash_multiplier (nash_context ca) in
 *   let raw_cost := (INR (base_cost ca) * threat_component * nash_component)%R in
 *   let bounded_cost := Rmin (INR (max_cost ca)) raw_cost in
 *   Rmax (10.0)%R bounded_cost.
 */
double 
ule_dynamic_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    
    /* Check cache validity first for performance */
    uint64_t current_time = 0;  /* TODO: Get actual system time */
    if (ule_is_cache_valid(ca, current_time)) {
        return ca->cached_result;
    }
    
    /* Calculate threat component: ∑_{i∈active} g(p_i, E_i) */
    double threat_component = ule_threat_sum(ca->active_threats, ca->num_active_threats);
    
    /* Calculate Nash equilibrium component: Π_nash */
    double nash_component = ule_nash_multiplier(&ca->nash_context);
    
    /* Calculate raw cost: C_base × ∑g(p_i, E_i) × Π_nash */
    double raw_cost = (double)ca->base_cost * threat_component * nash_component;
    
    /* Apply bounds: max(10, min(C_max, raw_cost)) */
    double bounded_cost = fmin((double)ca->max_cost, raw_cost);
    double final_cost = fmax(ULE_DYNAMIC_BCRA_MIN_COST, bounded_cost);
    
    /* Cache the result */
    ca->cached_result = final_cost;
    ca->cache_timestamp = current_time;
    ca->cache_valid = true;
    
    return final_cost;
}

/*
 * Simplified routing cost for backward compatibility
 * 
 * Original simplified implementation:
 * routing_cost = base_cost * (1 + attack_load * (2 - defense_strength))
 */
double 
ule_simple_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    assert(ca->simple_attack_load >= 0.0 && ca->simple_attack_load <= 1.0);
    assert(ca->simple_defense_strength >= 0.0 && ca->simple_defense_strength <= 1.0);
    
    double cost_multiplier = 1.0 + ca->simple_attack_load * (2.0 - ca->simple_defense_strength);
    return (double)ca->base_cost * cost_multiplier;
}

/*
 * Primary routing cost function - uses full Dynamic BCRA formula
 * 
 * This implements the routing_cost definition from Coq:
 * Definition routing_cost (ca : route_ca) : R := dynamic_routing_cost ca.
 */
double 
ule_calculate_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    
    /* Use the full Dynamic BCRA formula as primary implementation */
    return ule_dynamic_routing_cost(ca);
}

/*
 * Initialize message queue
 */
static void 
ule_message_queue_init(ule_message_queue_t *queue)
{
    assert(queue != NULL);
    
    queue->head = NULL;
    queue->tail = NULL;
    queue->count = 0;
    simple_lock_init(&queue->lock);
}

/*
 * Enqueue message to queue (thread-safe)
 */
static kern_return_t 
ule_message_queue_enqueue(ule_message_queue_t *queue, ule_message_t *msg) 
{
    assert(queue != NULL && msg != NULL);
    
    simple_lock(&queue->lock);
    
    msg->next = NULL;
    msg->prev = queue->tail;
    
    if (queue->tail) {
        queue->tail->next = msg;
    } else {
        queue->head = msg;
    }
    
    queue->tail = msg;
    queue->count++;
    
    simple_unlock(&queue->lock);
    return KERN_SUCCESS;
}

/*
 * Dequeue message from front of queue (thread-safe)
 */
static ule_message_t *
ule_message_queue_dequeue(ule_message_queue_t *queue)
{
    assert(queue != NULL);
    
    simple_lock(&queue->lock);
    
    ule_message_t *msg = queue->head;
    if (msg) {
        queue->head = msg->next;
        if (queue->head) {
            queue->head->prev = NULL;
        } else {
            queue->tail = NULL;
        }
        queue->count--;
        
        msg->next = msg->prev = NULL;
    }
    
    simple_unlock(&queue->lock);
    return msg;
}

/*
 * Get queue length - implements verified get_queue_length
 * 
 * From Coq proof:
 * Definition get_queue_length (sq : server_queue) : nat :=
 *   length (current_queue sq) + length (next_queue sq).
 */
uint32_t 
ule_get_queue_length(ule_server_queue_t *server)
{
    assert(server != NULL);
    
    simple_lock(&server->lock);
    uint32_t length = server->current_queue.count + server->next_queue.count;
    simple_unlock(&server->lock);
    
    return length;
}

/*
 * Server lookup by ID
 */
static ule_server_queue_t *
ule_server_lookup(uint32_t server_id)
{
    assert(ule_global_scheduler != NULL);
    
    simple_lock(&ule_global_scheduler->global_lock);
    
    ule_server_queue_t *server = ule_global_scheduler->servers;
    while (server) {
        if (server->server_id == server_id) {
            simple_unlock(&ule_global_scheduler->global_lock);
            return server;
        }
        server = server->next;
    }
    
    simple_unlock(&ule_global_scheduler->global_lock);
    return NULL;
}

/*
 * Find minimum cost server - implements verified ca_routing_optimal
 * 
 * From Coq proof:
 * Theorem ca_routing_optimal : forall servers stype sq,
 *   find_min_cost_server servers stype = Some sq ->
 *   In sq servers /\
 *   server_type sq = stype /\  
 *   forall sq', In sq' servers -> server_type sq' = stype ->
 *     (routing_cost (server_ca sq) <= routing_cost (server_ca sq'))%R.
 */
ule_server_queue_t *
ule_find_min_cost_server(ule_server_type_t server_type)
{
    assert(ule_global_scheduler != NULL);
    assert(server_type < ULE_SERVER_COUNT);
    
    simple_lock(&ule_global_scheduler->global_lock);
    
    ule_server_queue_t *min_server = NULL;
    double min_cost = HUGE_VAL;
    
    /* Find all eligible servers of the specified type */
    ule_server_queue_t *server = ule_global_scheduler->servers;
    while (server) {
        if (server->server_type == server_type) {
            double cost = ule_calculate_routing_cost(&server->server_ca);
            
            /* This implements the verified minimum-finding algorithm */
            if (min_server == NULL || cost <= min_cost) {
                min_server = server;
                min_cost = cost;
            }
        }
        server = server->next;
    }
    
    simple_unlock(&ule_global_scheduler->global_lock);
    
    /* Verified property: if result is non-NULL, it has minimum cost among eligible servers */
    return min_server;
}

/*
 * Message enqueue with interactive priority - implements verified interactive_priority
 * 
 * From Coq proof:
 * Theorem interactive_priority : forall m sq sq',
 *   is_interactive m = true ->
 *   sq' = mkServerQueue (server sq) (mid m :: current_queue sq) ... ->
 *   In (mid m) (current_queue sq').
 */
kern_return_t 
ule_message_enqueue(ule_message_t *msg)
{
    assert(msg != NULL);
    assert(ule_global_scheduler != NULL);
    
    /* Update message arrival time */
    msg->arrival_time = ule_global_scheduler->global_time++;
    
    /* Find the optimal server using verified CA routing */
    ule_server_queue_t *target_server = ule_find_min_cost_server(msg->target_service);
    if (!target_server) {
        return KERN_FAILURE;
    }
    
    simple_lock(&target_server->lock);
    
    /* Classify message and enqueue to appropriate queue */
    /* This implements the verified interactive priority theorem */
    if (ule_is_interactive(msg)) {
        /* Interactive messages go to current_queue (verified property) */
        kern_return_t result = ule_message_queue_enqueue(&target_server->current_queue, msg);
        if (result == KERN_SUCCESS) {
            target_server->queue_load++;
            ule_global_scheduler->stats.interactive_promotions++;
        }
        simple_unlock(&target_server->lock);
        return result;
    } else {
        /* Non-interactive messages go to next_queue */
        kern_return_t result = ule_message_queue_enqueue(&target_server->next_queue, msg);
        if (result == KERN_SUCCESS) {
            target_server->queue_load++;
        }
        simple_unlock(&target_server->lock);
        return result;
    }
}

/*
 * Message dequeue - implements ULE scheduling policy
 */
ule_message_t *
ule_message_dequeue(ule_server_type_t server_type)
{
    ule_server_queue_t *server = ule_find_min_cost_server(server_type);
    if (!server) {
        return NULL;
    }
    
    simple_lock(&server->lock);
    
    ule_message_t *msg = NULL;
    
    /* ULE scheduling order: current -> next -> idle */
    msg = ule_message_queue_dequeue(&server->current_queue);
    if (!msg) {
        msg = ule_message_queue_dequeue(&server->next_queue);
        if (!msg) {
            msg = ule_message_queue_dequeue(&server->idle_queue);
        }
    }
    
    if (msg) {
        server->queue_load--;
        ule_global_scheduler->stats.messages_processed++;
        
        /* Update message history */
        uint32_t idx = server->history_index % ule_config.max_message_history;
        server->message_history[idx].msg_id = msg->msg_id;
        server->message_history[idx].timestamp = ule_global_scheduler->global_time;
        server->history_index++;
    }
    
    simple_unlock(&server->lock);
    return msg;
}

/*
 * Core-specific message dequeue for SMP support
 */
ule_message_t *
ule_message_dequeue_core(uint32_t core_id)
{
    assert(core_id < ule_global_scheduler->core_count);
    
    /* First, try dedicated servers for this core */
    simple_lock(&ule_global_scheduler->global_lock);
    
    ule_server_queue_t *server = ule_global_scheduler->servers;
    while (server) {
        if (server->dedicated_core == core_id) {
            simple_unlock(&ule_global_scheduler->global_lock);
            
            simple_lock(&server->lock);
            ule_message_t *msg = ule_message_queue_dequeue(&server->current_queue);
            if (!msg) {
                msg = ule_message_queue_dequeue(&server->next_queue);
                if (!msg) {
                    msg = ule_message_queue_dequeue(&server->idle_queue);
                }
            }
            
            if (msg) {
                server->queue_load--;
                ule_global_scheduler->stats.messages_processed++;
            }
            simple_unlock(&server->lock);
            
            if (msg) {
                return msg;
            }
            
            simple_lock(&ule_global_scheduler->global_lock);
        }
        server = server->next;
    }
    
    simple_unlock(&ule_global_scheduler->global_lock);
    
    /* If no dedicated work, try any available server */
    /* This could be enhanced with load balancing heuristics */
    for (int stype = 0; stype < ULE_SERVER_COUNT; stype++) {
        ule_message_t *msg = ule_message_dequeue((ule_server_type_t)stype);
        if (msg) {
            return msg;
        }
    }
    
    return NULL;
}

/*
 * Queue switching - implements verified queue_switch_preserves
 * 
 * From Coq proof:
 * Theorem queue_switch_preserves : forall sq,
 *   let sq' := mkServerQueue (server sq) (next_queue sq) (current_queue sq) ... in
 *   forall m, (In m (current_queue sq) \/ In m (next_queue sq)) <->
 *           (In m (current_queue sq') \/ In m (next_queue sq')).
 */
kern_return_t 
ule_queue_switch(ule_server_queue_t *server)
{
    assert(server != NULL);
    
    simple_lock(&server->lock);
    
    /* Implement verified queue switching: swap current and next queues */
    ule_message_queue_t temp = server->current_queue;
    server->current_queue = server->next_queue;
    server->next_queue = temp;
    
    /* The verified theorem guarantees message preservation */
    
    simple_unlock(&server->lock);
    return KERN_SUCCESS;
}

/*
 * Server registration
 */
kern_return_t 
ule_server_register(uint32_t server_id, ule_server_type_t server_type, uint32_t dedicated_core)
{
    assert(ule_global_scheduler != NULL);
    assert(server_type < ULE_SERVER_COUNT);
    
    /* Check if server already exists */
    if (ule_server_lookup(server_id)) {
        return KERN_FAILURE;
    }
    
    /* Allocate and initialize server queue */
    ule_server_queue_t *server = (ule_server_queue_t *)kalloc(sizeof(ule_server_queue_t));
    if (!server) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    memset(server, 0, sizeof(ule_server_queue_t));
    
    server->server_id = server_id;
    server->server_type = server_type;
    server->dedicated_core = dedicated_core;
    server->interactive_threshold = ule_config.interactive_threshold;
    
    /* Initialize queues */
    ule_message_queue_init(&server->current_queue);
    ule_message_queue_init(&server->next_queue);
    ule_message_queue_init(&server->idle_queue);
    
    /* Initialize CA routing with defaults for full Dynamic BCRA formula */
    server->server_ca.base_cost = 100;          /* C_base: default base cost */
    server->server_ca.max_cost = 1000;          /* C_max: default maximum cost */
    server->server_ca.num_active_threats = 0;  /* No active threats initially */
    server->server_ca.k1 = ULE_DYNAMIC_BCRA_K1;/* k1 = 1.5 */
    server->server_ca.k2 = ULE_DYNAMIC_BCRA_K2;/* k2 = 2.0 */
    
    /* Initialize Nash equilibrium components with defaults */
    ule_init_default_nash_components(&server->server_ca.nash_context);
    
    /* Backward compatibility - simple formula defaults */
    server->server_ca.simple_attack_load = 0.0;
    server->server_ca.simple_defense_strength = 1.0;
    
    /* Initialize cache */
    server->server_ca.cached_result = 0.0;
    server->server_ca.cache_timestamp = 0;
    server->server_ca.cache_valid = false;
    
    simple_lock_init(&server->lock);
    
    /* Add to global server list */
    simple_lock(&ule_global_scheduler->global_lock);
    
    server->next = ule_global_scheduler->servers;
    if (ule_global_scheduler->servers) {
        ule_global_scheduler->servers->prev = server;
    }
    ule_global_scheduler->servers = server;
    ule_global_scheduler->server_count++;
    
    simple_unlock(&ule_global_scheduler->global_lock);
    
    return KERN_SUCCESS;
}

/*
 * Server unregistration
 */
kern_return_t 
ule_server_unregister(uint32_t server_id)
{
    ule_server_queue_t *server = ule_server_lookup(server_id);
    if (!server) {
        return KERN_FAILURE;
    }
    
    simple_lock(&ule_global_scheduler->global_lock);
    simple_lock(&server->lock);
    
    /* Remove from global list */
    if (server->prev) {
        server->prev->next = server->next;
    } else {
        ule_global_scheduler->servers = server->next;
    }
    
    if (server->next) {
        server->next->prev = server->prev;
    }
    
    ule_global_scheduler->server_count--;
    
    simple_unlock(&server->lock);
    simple_unlock(&ule_global_scheduler->global_lock);
    
    /* TODO: Handle any remaining messages in the queues */
    /* In a production system, these would need to be redistributed */
    
    kfree((vm_offset_t)server, sizeof(ule_server_queue_t));
    return KERN_SUCCESS;
}

/*
 * Scheduler initialization
 */
kern_return_t 
ule_scheduler_init(ule_scheduler_config_t *config)
{
    if (ule_global_scheduler) {
        return KERN_FAILURE; /* Already initialized */
    }
    
    /* Set default configuration if none provided */
    if (config) {
        ule_config = *config;
    } else {
        ule_config.time_quantum_ms = ULE_DEFAULT_TIME_QUANTUM_MS;
        ule_config.interactive_threshold = ULE_DEFAULT_INTERACTIVE_THRESH;
        ule_config.max_message_history = ULE_DEFAULT_MAX_HISTORY;
        ule_config.ca_attack_decay = ULE_DEFAULT_CA_ATTACK_DECAY;
        ule_config.ca_defense_boost = ULE_DEFAULT_CA_DEFENSE_BOOST;
        ule_config.enable_smp_affinity = true;
        ule_config.enable_ca_routing = true;
    }
    
    /* Allocate global scheduler state */
    ule_global_scheduler = (ule_microkernel_state_t *)kalloc(sizeof(ule_microkernel_state_t));
    if (!ule_global_scheduler) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    memset(ule_global_scheduler, 0, sizeof(ule_microkernel_state_t));
    
    /* Initialize scheduler state */
    ule_global_scheduler->servers = NULL;
    ule_global_scheduler->server_count = 0;
    ule_global_scheduler->pending_messages = NULL;
    ule_global_scheduler->pending_count = 0;
    ule_global_scheduler->global_time = 0;
    ule_global_scheduler->core_count = real_ncpus; /* From Mach */
    
    simple_lock_init(&ule_global_scheduler->global_lock);
    
    /* Initialize statistics */
    memset(&ule_global_scheduler->stats, 0, sizeof(ule_global_scheduler->stats));
    
    return KERN_SUCCESS;
}

/*
 * Scheduler cleanup
 */
void 
ule_scheduler_cleanup(void)
{
    if (!ule_global_scheduler) {
        return;
    }
    
    /* Unregister all servers */
    while (ule_global_scheduler->servers) {
        ule_server_unregister(ule_global_scheduler->servers->server_id);
    }
    
    kfree((vm_offset_t)ule_global_scheduler, sizeof(ule_microkernel_state_t));
    ule_global_scheduler = NULL;
}

/*
 * Get scheduler statistics
 */
void 
ule_scheduler_get_stats(struct ule_scheduler_stats *stats)
{
    assert(stats != NULL);
    assert(ule_global_scheduler != NULL);
    
    simple_lock(&ule_global_scheduler->global_lock);
    *stats = ule_global_scheduler->stats;
    simple_unlock(&ule_global_scheduler->global_lock);
}

/*
 * Reset scheduler statistics
 */
void 
ule_scheduler_reset_stats(void)
{
    assert(ule_global_scheduler != NULL);
    
    simple_lock(&ule_global_scheduler->global_lock);
    memset(&ule_global_scheduler->stats, 0, sizeof(ule_global_scheduler->stats));
    simple_unlock(&ule_global_scheduler->global_lock);
}

/*
 * Threat management functions for Dynamic BCRA
 */

/*
 * Add a new threat to the CA routing context
 */
kern_return_t 
ule_add_threat(ule_route_ca_t *ca, double probability, double effectiveness)
{
    assert(ca != NULL);
    assert(probability >= 0.0 && probability <= 1.0);
    assert(effectiveness >= 0.0 && effectiveness <= 1.0);
    
    if (ca->num_active_threats >= ULE_MAX_ACTIVE_THREATS) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    ule_threat_data_t *threat = &ca->active_threats[ca->num_active_threats];
    threat->threat_probability = probability;
    threat->defense_effectiveness = effectiveness;
    threat->timestamp = ule_get_current_time_ms();
    
    /* Calculate decay time using Scott J. Guyton's formula */
    /* T_decay(i) = T_base + α × p^β × T_base */
    /* For simplicity, using fixed parameters here */
    double alpha = 1.0;
    double beta = 2.0;
    double T_base = 365.0 * 24.0 * 60.0 * 60.0 * 1000.0;  /* 365 days in ms */
    threat->decay_time = T_base + alpha * pow(probability, beta) * T_base;
    
    ca->num_active_threats++;
    ule_invalidate_cache(ca);
    
    return KERN_SUCCESS;
}

/*
 * Remove expired threats from the CA routing context
 */
kern_return_t 
ule_remove_expired_threats(ule_route_ca_t *ca, uint64_t current_time)
{
    assert(ca != NULL);
    
    uint32_t active_count = 0;
    bool threats_removed = false;
    
    for (uint32_t i = 0; i < ca->num_active_threats; i++) {
        ule_threat_data_t *threat = &ca->active_threats[i];
        
        /* Check if threat has expired */
        if ((current_time - threat->timestamp) <= threat->decay_time) {
            /* Threat is still active - keep it */
            if (active_count != i) {
                ca->active_threats[active_count] = *threat;
            }
            active_count++;
        } else {
            threats_removed = true;
        }
    }
    
    ca->num_active_threats = active_count;
    
    if (threats_removed) {
        ule_invalidate_cache(ca);
    }
    
    return KERN_SUCCESS;
}

/*
 * Update Nash equilibrium components
 */
void 
ule_update_nash_components(ule_route_ca_t *ca, ule_nash_components_t *nash)
{
    assert(ca != NULL);
    assert(nash != NULL);
    
    ca->nash_context = *nash;
    ule_invalidate_cache(ca);
}

/*
 * Cache management functions
 */

/*
 * Invalidate the routing cost cache
 */
void 
ule_invalidate_cache(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    ca->cache_valid = false;
    ca->cache_timestamp = 0;
    ca->cached_result = 0.0;
}

/*
 * Check if cache is valid (within 1 second)
 */
bool 
ule_is_cache_valid(ule_route_ca_t *ca, uint64_t current_time)
{
    assert(ca != NULL);
    
    if (!ca->cache_valid) {
        return false;
    }
    
    return (current_time - ca->cache_timestamp) < ULE_CACHE_VALIDITY_MS;
}

/*
 * Utility functions
 */

/*
 * Get current time in milliseconds
 */
static uint64_t 
ule_get_current_time_ms(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000 + (uint64_t)tv.tv_usec / 1000;
}

/*
 * Initialize default Nash equilibrium components
 */
static void 
ule_init_default_nash_components(ule_nash_components_t *nash)
{
    assert(nash != NULL);
    
    /* Set reasonable default values */
    nash->equilibrium_factor = 1.0;
    nash->competition_factor = 1.0;
    nash->reputation_factor = 1.0;
    nash->bayesian_factor = 1.0;
    nash->signaling_factor = 1.0;
}