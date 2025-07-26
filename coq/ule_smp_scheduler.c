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

/* Global scheduler state */
ule_microkernel_state_t *ule_global_scheduler = NULL;
static ule_scheduler_config_t ule_config;

/* Forward declarations */
static void ule_message_queue_init(ule_message_queue_t *queue);
static kern_return_t ule_message_queue_enqueue(ule_message_queue_t *queue, ule_message_t *msg);
static ule_message_t *ule_message_queue_dequeue(ule_message_queue_t *queue);
static ule_server_queue_t *ule_server_lookup(uint32_t server_id);

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
 * CA-based routing cost calculation - implements verified routing_cost
 * 
 * Original formula specified by Scott J. Guyton:
 * routing_cost = base_cost * (1 + attack_load * (2 - defense_strength))
 * 
 * From verified Coq proof:
 * Definition routing_cost (ca : route_ca) : R :=
 *   (INR (base_cost ca) * (1 + attack_load ca * (2 - defense_strength ca)))%R.
 */
double 
ule_calculate_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    assert(ca->attack_load >= 0.0 && ca->attack_load <= 1.0);
    assert(ca->defense_strength >= 0.0 && ca->defense_strength <= 1.0);
    
    /* Implements the verified formula */
    double cost_multiplier = 1.0 + ca->attack_load * (2.0 - ca->defense_strength);
    return (double)ca->base_cost * cost_multiplier;
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
    
    /* Initialize CA routing with defaults */
    server->server_ca.base_cost = 100;  /* Default base cost */
    server->server_ca.attack_load = 0.0;
    server->server_ca.defense_strength = 1.0;
    
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