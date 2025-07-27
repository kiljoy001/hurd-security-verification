/* FSM IPC + ULE Scheduler Integration Implementation
 * Combines FSM-based IPC with ULE SMP scheduling for optimal performance
 */

#include "fsm_ule_integration.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>

/* ===== Helper Functions ===== */

static uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

static uint32_t hash_message_for_core(const fsm_message_t *msg, uint32_t num_cores) {
    /* Simple hash based on source port and destination */
    uint32_t hash = (msg->source_port * 31) + msg->dest_server;
    return hash % num_cores;
}

/* ===== Type Conversion Functions ===== */

ule_server_type_t fsm_to_ule_server_type(fsm_server_type_t fsm_type) {
    switch (fsm_type) {
        case FSM_SERVER_FILESYSTEM: return ULE_SERVER_FILESYSTEM;
        case FSM_SERVER_NETWORK:    return ULE_SERVER_NETWORK;
        case FSM_SERVER_PROCESS:    return ULE_SERVER_PROCESS;
        case FSM_SERVER_MEMORY:     return ULE_SERVER_MEMORY;
        case FSM_SERVER_DEVICE:     return ULE_SERVER_DEVICE;
        case FSM_SERVER_GUI:        return ULE_SERVER_GUI;
        case FSM_SERVER_AUDIO:      return ULE_SERVER_AUDIO;
        default:                    return ULE_SERVER_PROCESS;
    }
}

ule_msg_class_t fsm_to_ule_message_class(fsm_state_t fsm_state) {
    switch (fsm_state) {
        case FSM_STATE_CREATED:     return ULE_MSG_INTERACTIVE;  /* High priority for new messages */
        case FSM_STATE_ROUTED:      return ULE_MSG_BATCH;        /* Normal processing */
        case FSM_STATE_VALIDATED:   return ULE_MSG_BATCH;        /* Normal processing */
        case FSM_STATE_DELIVERED:   return ULE_MSG_REALTIME;     /* Time-critical delivery */
        case FSM_STATE_ACKNOWLEDGED: return ULE_MSG_IDLE;        /* Low priority cleanup */
        case FSM_STATE_ERROR:       return ULE_MSG_INTERRUPT;    /* High priority error handling */
        default:                    return ULE_MSG_BATCH;
    }
}

/* ===== Default Configuration ===== */

void fsm_ule_init_default_priority_map(fsm_ule_integration_t *integration) {
    if (!integration) return;
    
    /* Initialize priority mappings */
    integration->priority_map[0] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_CREATED,
        .ule_priority = ULE_MSG_INTERACTIVE,
        .timeslice_us = 500,      /* Short timeslice for interactive */
        .preemptible = true
    };
    
    integration->priority_map[1] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_ROUTED,
        .ule_priority = ULE_MSG_BATCH,
        .timeslice_us = 1000,     /* Standard timeslice */
        .preemptible = true
    };
    
    integration->priority_map[2] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_VALIDATED,
        .ule_priority = ULE_MSG_BATCH,
        .timeslice_us = 1000,
        .preemptible = true
    };
    
    integration->priority_map[3] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_DELIVERED,
        .ule_priority = ULE_MSG_REALTIME,
        .timeslice_us = 100,      /* Very short for real-time */
        .preemptible = false
    };
    
    integration->priority_map[4] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_ACKNOWLEDGED,
        .ule_priority = ULE_MSG_IDLE,
        .timeslice_us = 2000,     /* Long timeslice for cleanup */
        .preemptible = true
    };
    
    integration->priority_map[5] = (fsm_ule_priority_map_t){
        .fsm_state = FSM_STATE_ERROR,
        .ule_priority = ULE_MSG_INTERRUPT,
        .timeslice_us = 50,       /* Very short for error handling */
        .preemptible = false
    };
}

void fsm_ule_init_default_affinity_map(fsm_ule_integration_t *integration) {
    if (!integration) return;
    
    /* Filesystem servers prefer cores 0-1 (I/O focused) */
    integration->affinity_map[0] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_FILESYSTEM,
        .ule_server_type = ULE_SERVER_FILESYSTEM,
        .preferred_cores = {0, 1},
        .num_preferred_cores = 2
    };
    
    /* Network servers prefer cores 2-3 (network stack) */
    integration->affinity_map[1] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_NETWORK,
        .ule_server_type = ULE_SERVER_NETWORK,
        .preferred_cores = {2, 3},
        .num_preferred_cores = 2
    };
    
    /* Process servers can use any core */
    integration->affinity_map[2] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_PROCESS,
        .ule_server_type = ULE_SERVER_PROCESS,
        .preferred_cores = {0, 1, 2, 3},
        .num_preferred_cores = 4
    };
    
    /* Memory servers prefer cores close to memory controllers */
    integration->affinity_map[3] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_MEMORY,
        .ule_server_type = ULE_SERVER_MEMORY,
        .preferred_cores = {0, 2},  /* Assuming NUMA layout */
        .num_preferred_cores = 2
    };
    
    /* Device servers prefer dedicated cores */
    integration->affinity_map[4] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_DEVICE,
        .ule_server_type = ULE_SERVER_DEVICE,
        .preferred_cores = {1, 3},
        .num_preferred_cores = 2
    };
    
    /* GUI servers prefer high-performance cores */
    integration->affinity_map[5] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_GUI,
        .ule_server_type = ULE_SERVER_GUI,
        .preferred_cores = {2, 3},
        .num_preferred_cores = 2
    };
    
    /* Audio servers need low-latency cores */
    integration->affinity_map[6] = (fsm_ule_affinity_map_t){
        .fsm_server_type = FSM_SERVER_AUDIO,
        .ule_server_type = ULE_SERVER_AUDIO,
        .preferred_cores = {0},     /* Dedicated core for audio */
        .num_preferred_cores = 1
    };
}

void fsm_ule_apply_performance_defaults(fsm_ule_integration_t *integration) {
    if (!integration) return;
    
    integration->numa_aware = true;
    integration->power_management = false;  /* Disabled for performance */
    integration->adaptive_scheduling = true;
    integration->load_balance_interval_ms = 10;  /* 10ms load balancing */
}

/* ===== Core Integration Functions ===== */

bool fsm_ule_integration_init(fsm_ule_integration_t *integration,
                              uint32_t num_cores,
                              fsm_ule_scheduling_policy_t policy) {
    if (!integration || num_cores == 0 || num_cores > FSM_ULE_MAX_CORES) {
        return false;
    }
    
    memset(integration, 0, sizeof(fsm_ule_integration_t));
    integration->num_cores = num_cores;
    
    /* Initialize FSM processor system */
    integration->fsm_processor = malloc(sizeof(fsm_processor_system_t));
    integration->fsm_routing = malloc(sizeof(fsm_routing_system_t));
    
    if (!integration->fsm_processor || !integration->fsm_routing) {
        fsm_ule_integration_shutdown(integration);
        return false;
    }
    
    /* Initialize FSM components */
    if (!fsm_routing_init(integration->fsm_routing)) {
        fsm_ule_integration_shutdown(integration);
        return false;
    }
    
    if (!fsm_processor_init(integration->fsm_processor, integration->fsm_routing, num_cores)) {
        fsm_ule_integration_shutdown(integration);
        return false;
    }
    
    /* Initialize ULE scheduler */
    integration->ule_scheduler = malloc(sizeof(ule_sched_global_t));
    if (!integration->ule_scheduler) {
        fsm_ule_integration_shutdown(integration);
        return false;
    }
    
    /* Initialize ULE scheduler (assuming this function exists) */
    if (!ule_sched_init(integration->ule_scheduler, num_cores)) {
        fsm_ule_integration_shutdown(integration);
        return false;
    }
    
    /* Initialize per-core contexts */
    for (uint32_t i = 0; i < num_cores; i++) {
        fsm_ule_core_context_t *context = &integration->core_contexts[i];
        
        context->core_id = i;
        context->fsm_context = &integration->fsm_processor->contexts[i];
        context->current_load = 0.0;
        context->preemption_enabled = true;
        context->current_timeslice_us = FSM_ULE_TIMESLICE_US;
        
        /* Initialize priority queues */
        for (int j = 0; j < FSM_ULE_PRIORITY_LEVELS; j++) {
            context->queue_heads[j] = 0;
            context->queue_tails[j] = 0;
            context->queue_counts[j] = 0;
        }
    }
    
    /* Configure default mappings */
    fsm_ule_init_default_priority_map(integration);
    fsm_ule_init_default_affinity_map(integration);
    fsm_ule_apply_performance_defaults(integration);
    
    return true;
}

void fsm_ule_integration_shutdown(fsm_ule_integration_t *integration) {
    if (!integration) return;
    
    if (integration->fsm_processor) {
        fsm_processor_shutdown(integration->fsm_processor);
        free(integration->fsm_processor);
    }
    
    if (integration->fsm_routing) {
        /* Routing shutdown function would go here */
        free(integration->fsm_routing);
    }
    
    if (integration->ule_scheduler) {
        /* ULE scheduler shutdown would go here */
        free(integration->ule_scheduler);
    }
    
    memset(integration, 0, sizeof(fsm_ule_integration_t));
}

/* ===== Message Scheduling Functions ===== */

ule_msg_class_t fsm_ule_get_message_priority(const fsm_message_t *msg) {
    if (!msg) return ULE_MSG_BATCH;
    
    return fsm_to_ule_message_class(msg->current_state);
}

uint32_t fsm_ule_select_optimal_core(fsm_ule_integration_t *integration,
                                     const fsm_message_t *msg) {
    if (!integration || !msg) return 0;
    
    /* Simple load balancing: find core with lowest load */
    uint32_t best_core = 0;
    double min_load = integration->core_contexts[0].current_load;
    
    for (uint32_t i = 1; i < integration->num_cores; i++) {
        double load = integration->core_contexts[i].current_load;
        if (load < min_load) {
            min_load = load;
            best_core = i;
        }
    }
    
    return best_core;
}

fsm_processing_result_t fsm_ule_schedule_message(fsm_ule_integration_t *integration,
                                                 fsm_message_t *msg,
                                                 uint32_t preferred_core) {
    if (!integration || !msg) {
        return FSM_RESULT_ERROR;
    }
    
    /* Select optimal core if not specified */
    uint32_t target_core = preferred_core;
    if (preferred_core >= integration->num_cores) {
        target_core = fsm_ule_select_optimal_core(integration, msg);
    }
    
    /* Get message priority */
    ule_msg_class_t priority = fsm_ule_get_message_priority(msg);
    
    /* Add to appropriate priority queue */
    fsm_ule_core_context_t *context = &integration->core_contexts[target_core];
    uint32_t priority_level = (uint32_t)priority;
    
    if (priority_level >= FSM_ULE_PRIORITY_LEVELS) {
        priority_level = FSM_ULE_PRIORITY_LEVELS - 1;
    }
    
    if (context->queue_counts[priority_level] >= 64) {
        /* Queue full, try next priority level */
        priority_level = (priority_level + 1) % FSM_ULE_PRIORITY_LEVELS;
        if (context->queue_counts[priority_level] >= 64) {
            return FSM_RESULT_RETRY;  /* All queues full */
        }
    }
    
    /* Add message to queue */
    uint32_t tail = context->queue_tails[priority_level];
    context->priority_queues[priority_level][tail] = msg;
    context->queue_tails[priority_level] = (tail + 1) % 64;
    context->queue_counts[priority_level]++;
    
    integration->total_messages_scheduled++;
    
    return FSM_RESULT_PENDING;
}

fsm_processing_result_t fsm_ule_process_next_message(fsm_ule_integration_t *integration,
                                                     uint32_t core_id) {
    if (!integration || core_id >= integration->num_cores) {
        return FSM_RESULT_ERROR;
    }
    
    fsm_ule_core_context_t *context = &integration->core_contexts[core_id];
    
    /* Find highest priority message */
    for (int priority = 0; priority < FSM_ULE_PRIORITY_LEVELS; priority++) {
        if (context->queue_counts[priority] > 0) {
            /* Get message from queue */
            uint32_t head = context->queue_heads[priority];
            fsm_message_t *msg = context->priority_queues[priority][head];
            
            context->queue_heads[priority] = (head + 1) % 64;
            context->queue_counts[priority]--;
            
            /* Process the message */
            uint64_t start_time = get_time_ns();
            fsm_processing_result_t result = fsm_process_message(integration->fsm_processor, msg, core_id);
            uint64_t end_time = get_time_ns();
            
            /* Update statistics */
            uint64_t processing_time = end_time - start_time;
            fsm_ule_update_load_metrics(integration, core_id, processing_time);
            
            return result;
        }
    }
    
    return FSM_RESULT_SUCCESS;  /* No messages to process */
}

uint32_t fsm_ule_process_message_batch(fsm_ule_integration_t *integration,
                                      uint32_t core_id,
                                      uint32_t max_messages) {
    if (!integration || core_id >= integration->num_cores) {
        return 0;
    }
    
    uint32_t processed = 0;
    
    for (uint32_t i = 0; i < max_messages; i++) {
        fsm_processing_result_t result = fsm_ule_process_next_message(integration, core_id);
        
        if (result == FSM_RESULT_SUCCESS && processed == 0) {
            break;  /* No more messages */
        }
        
        if (result == FSM_RESULT_PENDING || result == FSM_RESULT_SUCCESS) {
            processed++;
        }
    }
    
    return processed;
}

/* ===== Load Balancing Functions ===== */

bool fsm_ule_load_balance(fsm_ule_integration_t *integration) {
    if (!integration) return false;
    
    /* Simple load balancing algorithm */
    double total_load = 0.0;
    for (uint32_t i = 0; i < integration->num_cores; i++) {
        total_load += integration->core_contexts[i].current_load;
    }
    
    double avg_load = total_load / integration->num_cores;
    
    /* Find overloaded and underloaded cores */
    for (uint32_t i = 0; i < integration->num_cores; i++) {
        fsm_ule_core_context_t *context = &integration->core_contexts[i];
        
        if (context->current_load > avg_load * 1.5) {
            /* Core is overloaded, try to migrate some messages */
            for (uint32_t j = 0; j < integration->num_cores; j++) {
                if (j != i && integration->core_contexts[j].current_load < avg_load * 0.8) {
                    /* Found underloaded core, migrate a message */
                    for (int priority = FSM_ULE_PRIORITY_LEVELS - 1; priority >= 0; priority--) {
                        if (context->queue_counts[priority] > 0) {
                            /* Move one message from overloaded to underloaded core */
                            uint32_t head = context->queue_heads[priority];
                            fsm_message_t *msg = context->priority_queues[priority][head];
                            
                            context->queue_heads[priority] = (head + 1) % 64;
                            context->queue_counts[priority]--;
                            
                            /* Add to target core's queue */
                            fsm_ule_core_context_t *target = &integration->core_contexts[j];
                            uint32_t tail = target->queue_tails[priority];
                            target->priority_queues[priority][tail] = msg;
                            target->queue_tails[priority] = (tail + 1) % 64;
                            target->queue_counts[priority]++;
                            
                            integration->load_balance_operations++;
                            break;
                        }
                    }
                    break;
                }
            }
        }
    }
    
    return true;
}

/* ===== Performance Monitoring ===== */

void fsm_ule_update_load_metrics(fsm_ule_integration_t *integration,
                                 uint32_t core_id,
                                 uint64_t processing_time_ns) {
    if (!integration || core_id >= integration->num_cores) return;
    
    fsm_ule_core_context_t *context = &integration->core_contexts[core_id];
    
    context->messages_processed++;
    context->total_latency_ns += processing_time_ns;
    
    /* Calculate current load as exponential moving average */
    double new_load = (double)processing_time_ns / 1000000.0;  /* Convert to ms */
    context->current_load = context->current_load * 0.9 + new_load * 0.1;
    
    /* Update system-wide statistics */
    integration->average_latency_us = 
        (integration->average_latency_us * 0.95) + 
        ((double)processing_time_ns / 1000.0 * 0.05);
}

void fsm_ule_get_system_stats(const fsm_ule_integration_t *integration,
                              uint64_t *total_messages,
                              double *avg_latency_us,
                              double *system_load) {
    if (!integration) return;
    
    if (total_messages) {
        *total_messages = integration->total_messages_scheduled;
    }
    
    if (avg_latency_us) {
        *avg_latency_us = integration->average_latency_us;
    }
    
    if (system_load) {
        double total_load = 0.0;
        for (uint32_t i = 0; i < integration->num_cores; i++) {
            total_load += integration->core_contexts[i].current_load;
        }
        *system_load = total_load / integration->num_cores;
    }
}

/* ===== Configuration Functions ===== */

void fsm_ule_set_numa_aware(fsm_ule_integration_t *integration, bool enabled) {
    if (integration) {
        integration->numa_aware = enabled;
    }
}

void fsm_ule_set_power_management(fsm_ule_integration_t *integration, bool enabled) {
    if (integration) {
        integration->power_management = enabled;
    }
}

bool fsm_ule_configure_adaptive_scheduling(fsm_ule_integration_t *integration,
                                           uint32_t load_threshold_percent,
                                           uint32_t balance_interval_ms) {
    if (!integration || load_threshold_percent > 100) {
        return false;
    }
    
    integration->adaptive_scheduling = true;
    integration->load_balance_interval_ms = balance_interval_ms;
    
    return true;
}

/* ===== Utility Functions ===== */

uint32_t fsm_ule_get_recommended_timeslice(const fsm_message_t *msg) {
    if (!msg) return FSM_ULE_TIMESLICE_US;
    
    switch (msg->current_state) {
        case FSM_STATE_CREATED:     return 500;   /* Interactive - short slice */
        case FSM_STATE_DELIVERED:   return 100;   /* Real-time - very short */
        case FSM_STATE_ERROR:       return 50;    /* Interrupt - immediate */
        case FSM_STATE_ACKNOWLEDGED: return 2000; /* Idle - long slice */
        default:                    return 1000;  /* Batch - standard */
    }
}

bool fsm_ule_is_preemptible(const fsm_message_t *msg) {
    if (!msg) return true;
    
    /* Real-time and interrupt messages are non-preemptible */
    return (msg->current_state != FSM_STATE_DELIVERED && 
            msg->current_state != FSM_STATE_ERROR);
}