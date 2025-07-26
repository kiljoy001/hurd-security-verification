/* ULE Scheduler Extensions
 * Advanced features: Message batching, NUMA awareness, DOS prevention
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include "ule_smp_scheduler.h"
#include <sys/types.h>
#include <mach/vm_param.h>

/* NUMA topology support */
typedef struct ule_numa_node {
    uint32_t node_id;
    uint32_t cpu_mask;          /* CPUs in this NUMA node */
    uint32_t memory_latency_ns; /* Average memory access latency */
    uint32_t distance[MAX_NUMA_NODES]; /* Distance to other nodes */
} ule_numa_node_t;

/* Enhanced CA routing with NUMA awareness */
typedef struct ule_route_ca_numa {
    ule_route_ca_t base_ca;     /* Base CA routing */
    uint32_t numa_distance;     /* NUMA distance cost */
    uint32_t memory_bandwidth;  /* Available memory bandwidth */
    double locality_factor;     /* Data locality factor (0.0-1.0) */
} ule_route_ca_numa_t;

/* Message batch for reducing context switches */
typedef struct ule_message_batch {
    ule_message_t *messages[ULE_BATCH_SIZE];
    uint32_t count;
    uint32_t target_core;
    uint64_t batch_timestamp;
    struct ule_message_batch *next;
} ule_message_batch_t;

/* Enhanced server queue with DOS prevention */
typedef struct ule_server_queue_enhanced {
    ule_server_queue_t base;    /* Base server queue */
    
    /* DOS prevention */
    uint32_t max_queue_depth;   /* Maximum messages per queue */
    uint32_t current_depth;     /* Current total depth */
    uint32_t dos_threshold;     /* DOS detection threshold */
    uint64_t last_dos_check;    /* Last DOS check timestamp */
    uint32_t rejected_messages; /* Messages rejected due to DOS */
    
    /* Message batching */
    ule_message_batch_t *pending_batches;
    uint32_t batch_size_target;
    uint64_t last_batch_time;
    
    /* NUMA awareness */
    uint32_t preferred_numa_node;
    ule_route_ca_numa_t numa_ca;
    
} ule_server_queue_enhanced_t;

/* Global NUMA topology */
static ule_numa_node_t numa_topology[MAX_NUMA_NODES];
static uint32_t numa_node_count = 0;
static bool numa_enabled = false;

/* Batching configuration */
#define ULE_BATCH_SIZE              8
#define ULE_BATCH_TIMEOUT_US        100  /* 100 microseconds */
#define ULE_MIN_BATCH_SIZE          2
#define ULE_MAX_BATCH_SIZE          16

/* DOS prevention configuration */  
#define ULE_DEFAULT_MAX_QUEUE_DEPTH 1000
#define ULE_DOS_CHECK_INTERVAL_US   1000  /* Check every 1ms */
#define ULE_DOS_REJECTION_THRESHOLD 0.8   /* Reject if >80% full */

/*
 * Initialize NUMA topology
 */
kern_return_t 
ule_numa_init(void)
{
    /* Detect NUMA topology (simplified for demonstration) */
    /* In a real implementation, this would query ACPI/firmware */
    
    numa_node_count = (real_ncpus + 3) / 4; /* Assume 4 CPUs per NUMA node */
    if (numa_node_count > MAX_NUMA_NODES) {
        numa_node_count = MAX_NUMA_NODES;
    }
    
    for (uint32_t i = 0; i < numa_node_count; i++) {
        numa_topology[i].node_id = i;
        numa_topology[i].cpu_mask = 0xF << (i * 4); /* 4 CPUs per node */
        numa_topology[i].memory_latency_ns = 100 + (i * 50); /* Increasing latency */
        
        /* Initialize distance matrix */
        for (uint32_t j = 0; j < MAX_NUMA_NODES; j++) {
            if (i == j) {
                numa_topology[i].distance[j] = 10; /* Local access */
            } else {
                numa_topology[i].distance[j] = 20 + abs((int)i - (int)j) * 10;
            }
        }
    }
    
    numa_enabled = true;
    return KERN_SUCCESS;
}

/*
 * Get NUMA node for CPU
 */
static uint32_t 
ule_get_numa_node(uint32_t cpu_id)
{
    if (!numa_enabled) {
        return 0;
    }
    
    for (uint32_t i = 0; i < numa_node_count; i++) {
        if (numa_topology[i].cpu_mask & (1 << cpu_id)) {
            return i;
        }
    }
    
    return 0; /* Default to node 0 */
}

/*
 * Calculate NUMA-aware routing cost
 */
static double 
ule_calculate_numa_routing_cost(ule_route_ca_numa_t *numa_ca, uint32_t source_cpu, uint32_t target_cpu)
{
    assert(numa_ca != NULL);
    
    /* Base CA cost */
    double base_cost = ule_calculate_routing_cost(&numa_ca->base_ca);
    
    if (!numa_enabled) {
        return base_cost;
    }
    
    uint32_t source_node = ule_get_numa_node(source_cpu);
    uint32_t target_node = ule_get_numa_node(target_cpu);
    
    /* NUMA distance penalty */
    double numa_penalty = 1.0;
    if (source_node < numa_node_count && target_node < numa_node_count) {
        numa_penalty = 1.0 + (numa_topology[source_node].distance[target_node] / 100.0);
    }
    
    /* Memory bandwidth factor */
    double bandwidth_factor = 1.0 + (1.0 - (numa_ca->memory_bandwidth / 100.0)) * 0.5;
    
    /* Locality bonus */
    double locality_bonus = numa_ca->locality_factor;
    
    return base_cost * numa_penalty * bandwidth_factor * (1.0 - locality_bonus * 0.3);
}

/*
 * Create message batch
 */
static ule_message_batch_t *
ule_create_message_batch(uint32_t target_core)
{
    ule_message_batch_t *batch = (ule_message_batch_t *)kalloc(sizeof(ule_message_batch_t));
    if (!batch) {
        return NULL;
    }
    
    memset(batch, 0, sizeof(ule_message_batch_t));
    batch->target_core = target_core;
    batch->batch_timestamp = ule_global_scheduler->global_time;
    
    return batch;
}

/*
 * Add message to batch
 */
static bool 
ule_batch_add_message(ule_message_batch_t *batch, ule_message_t *msg)
{
    assert(batch != NULL && msg != NULL);
    
    if (batch->count >= ULE_BATCH_SIZE) {
        return false;
    }
    
    batch->messages[batch->count++] = msg;
    return true;
}

/*
 * Process message batch
 */
static kern_return_t 
ule_process_message_batch(ule_message_batch_t *batch)
{
    assert(batch != NULL);
    
    if (batch->count == 0) {
        return KERN_SUCCESS;
    }
    
    /* Process all messages in the batch together */
    /* This reduces context switching by handling related messages together */
    
    for (uint32_t i = 0; i < batch->count; i++) {
        ule_message_t *msg = batch->messages[i];
        
        /* Find target server with NUMA awareness */
        ule_server_queue_t *server = ule_find_min_cost_server(msg->target_service);
        if (server) {
            /* Enhanced server would use NUMA-aware routing */
            ule_server_queue_enhanced_t *enhanced = (ule_server_queue_enhanced_t *)server;
            
            /* Check DOS prevention */
            if (enhanced->current_depth >= enhanced->max_queue_depth) {
                enhanced->rejected_messages++;
                kfree((vm_offset_t)msg, sizeof(ule_message_t));
                continue;
            }
            
            /* Enqueue message */
            if (ule_is_interactive(msg)) {
                ule_message_queue_enqueue(&server->current_queue, msg);
            } else {
                ule_message_queue_enqueue(&server->next_queue, msg);
            }
            
            enhanced->current_depth++;
            server->queue_load++;
        }
    }
    
    /* Free the batch */
    kfree((vm_offset_t)batch, sizeof(ule_message_batch_t));
    return KERN_SUCCESS;
}

/*
 * Enhanced message enqueue with batching and DOS prevention
 */
kern_return_t 
ule_message_enqueue_enhanced(ule_message_t *msg, uint32_t source_cpu)
{
    assert(msg != NULL && ule_global_scheduler != NULL);
    
    /* Find target server */
    ule_server_queue_t *base_server = ule_find_min_cost_server(msg->target_service);
    if (!base_server) {
        return KERN_FAILURE;
    }
    
    ule_server_queue_enhanced_t *server = (ule_server_queue_enhanced_t *)base_server;
    
    simple_lock(&server->base.lock);
    
    /* DOS prevention check */
    uint64_t current_time = ule_global_scheduler->global_time;
    if (current_time - server->last_dos_check > ULE_DOS_CHECK_INTERVAL_US) {
        server->last_dos_check = current_time;
        
        /* Check if we're approaching DOS threshold */
        if (server->current_depth > server->max_queue_depth * ULE_DOS_REJECTION_THRESHOLD) {
            server->rejected_messages++;
            simple_unlock(&server->base.lock);
            return KERN_RESOURCE_SHORTAGE;
        }
    }
    
    /* Try to add to existing batch */
    bool batched = false;
    ule_message_batch_t *batch = server->pending_batches;
    while (batch && !batched) {
        if (batch->target_core == source_cpu && batch->count < ULE_BATCH_SIZE) {
            batched = ule_batch_add_message(batch, msg);
            break;
        }
        batch = batch->next;
    }
    
    /* Create new batch if needed */
    if (!batched) {
        batch = ule_create_message_batch(source_cpu);
        if (batch) {
            ule_batch_add_message(batch, msg);
            batch->next = server->pending_batches;
            server->pending_batches = batch;
            batched = true;
        }
    }
    
    /* Check if batch should be processed */
    if (batch && (batch->count >= server->batch_size_target || 
                  current_time - batch->batch_timestamp > ULE_BATCH_TIMEOUT_US)) {
        
        /* Remove batch from pending list */
        if (server->pending_batches == batch) {
            server->pending_batches = batch->next;
        } else {
            ule_message_batch_t *prev = server->pending_batches;
            while (prev && prev->next != batch) {
                prev = prev->next;
            }
            if (prev) {
                prev->next = batch->next;
            }
        }
        
        simple_unlock(&server->base.lock);
        
        /* Process the batch */
        return ule_process_message_batch(batch);
    }
    
    simple_unlock(&server->base.lock);
    
    if (batched) {
        return KERN_SUCCESS;
    } else {
        /* Fall back to immediate processing */
        return ule_message_enqueue(msg);
    }
}

/*
 * Enhanced server registration with DOS prevention and NUMA awareness
 */
kern_return_t 
ule_server_register_enhanced(uint32_t server_id, ule_server_type_t server_type, 
                            uint32_t dedicated_core, uint32_t max_queue_depth)
{
    assert(ule_global_scheduler != NULL);
    assert(server_type < ULE_SERVER_COUNT);
    
    /* Check if server already exists */
    if (ule_server_lookup(server_id)) {
        return KERN_FAILURE;
    }
    
    /* Allocate enhanced server queue */
    ule_server_queue_enhanced_t *server = (ule_server_queue_enhanced_t *)
        kalloc(sizeof(ule_server_queue_enhanced_t));
    if (!server) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    memset(server, 0, sizeof(ule_server_queue_enhanced_t));
    
    /* Initialize base server */
    server->base.server_id = server_id;
    server->base.server_type = server_type;
    server->base.dedicated_core = dedicated_core;
    server->base.interactive_threshold = ule_config.interactive_threshold;
    
    /* Initialize queues */
    ule_message_queue_init(&server->base.current_queue);
    ule_message_queue_init(&server->base.next_queue);
    ule_message_queue_init(&server->base.idle_queue);
    
    /* Initialize DOS prevention */
    server->max_queue_depth = max_queue_depth ? max_queue_depth : ULE_DEFAULT_MAX_QUEUE_DEPTH;
    server->current_depth = 0;
    server->dos_threshold = server->max_queue_depth * ULE_DOS_REJECTION_THRESHOLD;
    server->last_dos_check = 0;
    server->rejected_messages = 0;
    
    /* Initialize message batching */
    server->pending_batches = NULL;
    server->batch_size_target = ULE_BATCH_SIZE / 2; /* Start conservative */
    server->last_batch_time = 0;
    
    /* Initialize NUMA awareness */
    if (numa_enabled && dedicated_core != (uint32_t)-1) {
        server->preferred_numa_node = ule_get_numa_node(dedicated_core);
    } else {
        server->preferred_numa_node = 0;
    }
    
    /* Initialize NUMA CA routing */
    server->numa_ca.base_ca.base_cost = 100;
    server->numa_ca.base_ca.attack_load = 0.0;
    server->numa_ca.base_ca.defense_strength = 1.0;
    server->numa_ca.numa_distance = 0;
    server->numa_ca.memory_bandwidth = 100; /* 100% initially */
    server->numa_ca.locality_factor = 1.0;  /* Full locality initially */
    
    simple_lock_init(&server->base.lock);
    
    /* Add to global server list */
    simple_lock(&ule_global_scheduler->global_lock);
    
    server->base.next = ule_global_scheduler->servers;
    if (ule_global_scheduler->servers) {
        ule_global_scheduler->servers->prev = &server->base;
    }
    ule_global_scheduler->servers = &server->base;
    ule_global_scheduler->server_count++;
    
    simple_unlock(&ule_global_scheduler->global_lock);
    
    return KERN_SUCCESS;
}

/*
 * Update NUMA CA routing metrics based on system state
 */
void 
ule_update_numa_metrics(uint32_t server_id, uint32_t memory_bandwidth, double locality_factor)
{
    ule_server_queue_t *base_server = ule_server_lookup(server_id);
    if (!base_server) {
        return;
    }
    
    ule_server_queue_enhanced_t *server = (ule_server_queue_enhanced_t *)base_server;
    
    simple_lock(&server->base.lock);
    
    server->numa_ca.memory_bandwidth = memory_bandwidth;
    server->numa_ca.locality_factor = locality_factor;
    
    /* Update attack load based on queue pressure */
    double queue_pressure = (double)server->current_depth / server->max_queue_depth;
    server->numa_ca.base_ca.attack_load = queue_pressure * 0.5; /* Scale to 0-0.5 */
    
    /* Update defense strength based on recent performance */
    double rejection_rate = (double)server->rejected_messages / 
                           (server->rejected_messages + server->current_depth + 1);
    server->numa_ca.base_ca.defense_strength = 1.0 - rejection_rate;
    
    simple_unlock(&server->base.lock);
}

/*
 * Adaptive batch size adjustment
 */
static void 
ule_adjust_batch_size(ule_server_queue_enhanced_t *server)
{
    assert(server != NULL);
    
    /* Increase batch size if we have consistent load */
    if (server->current_depth > server->max_queue_depth / 2) {
        server->batch_size_target = min(server->batch_size_target + 1, ULE_MAX_BATCH_SIZE);
    } 
    /* Decrease batch size if load is light */
    else if (server->current_depth < server->max_queue_depth / 4) {
        server->batch_size_target = max(server->batch_size_target - 1, ULE_MIN_BATCH_SIZE);
    }
}

/*
 * Process pending batches (called periodically)
 */
void 
ule_process_pending_batches(void)
{
    if (!ule_global_scheduler) {
        return;
    }
    
    simple_lock(&ule_global_scheduler->global_lock);
    
    ule_server_queue_t *base_server = ule_global_scheduler->servers;
    while (base_server) {
        ule_server_queue_enhanced_t *server = (ule_server_queue_enhanced_t *)base_server;
        
        simple_lock(&server->base.lock);
        
        uint64_t current_time = ule_global_scheduler->global_time;
        
        /* Process timed-out batches */
        ule_message_batch_t *batch = server->pending_batches;
        ule_message_batch_t *prev = NULL;
        
        while (batch) {
            ule_message_batch_t *next = batch->next;
            
            if (current_time - batch->batch_timestamp > ULE_BATCH_TIMEOUT_US) {
                /* Remove from list */
                if (prev) {
                    prev->next = next;
                } else {
                    server->pending_batches = next;
                }
                
                simple_unlock(&server->base.lock);
                ule_process_message_batch(batch);
                simple_lock(&server->base.lock);
            } else {
                prev = batch;
            }
            
            batch = next;
        }
        
        /* Adjust batch size based on load */
        ule_adjust_batch_size(server);
        
        simple_unlock(&server->base.lock);
        base_server = base_server->next;
    }
    
    simple_unlock(&ule_global_scheduler->global_lock);
}

/*
 * Get enhanced server statistics
 */
kern_return_t 
ule_get_enhanced_server_stats(uint32_t server_id, struct ule_enhanced_server_stats *stats)
{
    assert(stats != NULL);
    
    ule_server_queue_t *base_server = ule_server_lookup(server_id);
    if (!base_server) {
        return KERN_FAILURE;
    }
    
    ule_server_queue_enhanced_t *server = (ule_server_queue_enhanced_t *)base_server;
    
    simple_lock(&server->base.lock);
    
    stats->queue_depth = server->current_depth;
    stats->max_queue_depth = server->max_queue_depth;
    stats->rejected_messages = server->rejected_messages;
    stats->batch_size_target = server->batch_size_target;
    stats->preferred_numa_node = server->preferred_numa_node;
    stats->memory_bandwidth = server->numa_ca.memory_bandwidth;
    stats->locality_factor = server->numa_ca.locality_factor;
    stats->routing_cost = ule_calculate_numa_routing_cost(&server->numa_ca, 0, 0);
    
    /* Count pending batches */
    stats->pending_batches = 0;
    ule_message_batch_t *batch = server->pending_batches;
    while (batch) {
        stats->pending_batches++;
        batch = batch->next;
    }
    
    simple_unlock(&server->base.lock);
    
    return KERN_SUCCESS;
}

/* Statistics structure definition for the header */
struct ule_enhanced_server_stats {
    uint32_t queue_depth;
    uint32_t max_queue_depth;
    uint32_t rejected_messages;
    uint32_t batch_size_target;
    uint32_t preferred_numa_node;
    uint32_t memory_bandwidth;
    double locality_factor;
    double routing_cost;
    uint32_t pending_batches;
};

#define MAX_NUMA_NODES 8