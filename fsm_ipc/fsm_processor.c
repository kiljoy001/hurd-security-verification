/* FSM Message Processor Implementation
 * High-performance state machine processing
 */

#include "fsm_processor.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sched.h>
#include <time.h>
#include <errno.h>

/* Initialize the FSM processor system */
bool fsm_processor_init(fsm_processor_system_t *processor,
                       fsm_routing_system_t *routing,
                       uint32_t num_cores) {
    if (!processor || !routing || num_cores == 0 || num_cores > 32) {
        return false;
    }
    
    memset(processor, 0, sizeof(fsm_processor_system_t));
    
    processor->routing = routing;
    processor->num_cores = num_cores;
    processor->numa_affinity_enabled = true;
    processor->batch_processing_enabled = true;
    processor->prefetch_enabled = true;
    processor->batch_size = FSM_BATCH_SIZE;
    processor->stats_update_interval_ms = 1000;  /* 1 second */
    
    /* Initialize per-core contexts */
    for (uint32_t i = 0; i < num_cores; i++) {
        fsm_processor_context_t *context = &processor->contexts[i];
        
        context->cpu_core = i;
        context->numa_node = i / 4;  /* Assume 4 cores per NUMA node */
        
        /* Initialize message pool */
        if (!fsm_init_message_pool(&context->message_pool)) {
            return false;
        }
        
        /* Initialize queue */
        context->queue_head = 0;
        context->queue_tail = 0;
        context->queue_count = 0;
        
        if (pthread_mutex_init(&context->queue_lock, NULL) != 0) {
            return false;
        }
        
        /* Initialize statistics */
        memset(&context->stats, 0, sizeof(fsm_processor_stats_t));
        context->stats.min_latency_ns = UINT64_MAX;
    }
    
    /* Initialize global message pools */
    processor->num_pools = (num_cores + 3) / 4;  /* One pool per 4 cores */
    for (uint32_t i = 0; i < processor->num_pools; i++) {
        if (!fsm_init_message_pool(&processor->global_pools[i])) {
            return false;
        }
    }
    
    return true;
}

/* Initialize message pool */
bool fsm_init_message_pool(fsm_message_pool_t *pool) {
    if (!pool) {
        return false;
    }
    
    memset(pool, 0, sizeof(fsm_message_pool_t));
    
    if (pthread_mutex_init(&pool->lock, NULL) != 0) {
        return false;
    }
    
    return true;
}

/* Allocate message from pool */
fsm_message_t *fsm_alloc_message(fsm_processor_system_t *processor,
                                uint32_t cpu_core) {
    if (!processor || cpu_core >= processor->num_cores) {
        return NULL;
    }
    
    fsm_processor_context_t *context = &processor->contexts[cpu_core];
    fsm_message_pool_t *pool = &context->message_pool;
    
    pthread_mutex_lock(&pool->lock);
    
    /* Find next free message slot */
    for (uint32_t i = 0; i < FSM_MESSAGES_PER_POOL; i++) {
        uint32_t idx = (pool->next_free + i) % FSM_MESSAGES_PER_POOL;
        
        if (!pool->allocated[idx]) {
            pool->allocated[idx] = true;
            pool->allocated_count++;
            pool->next_free = (idx + 1) % FSM_MESSAGES_PER_POOL;
            
            fsm_message_t *msg = &pool->messages[idx];
            memset(msg, 0, sizeof(fsm_message_t));
            
            pthread_mutex_unlock(&pool->lock);
            return msg;
        }
    }
    
    pthread_mutex_unlock(&pool->lock);
    
    /* Local pool full, try global pool */
    uint32_t global_pool_idx = cpu_core / 4;
    if (global_pool_idx < processor->num_pools) {
        fsm_message_pool_t *global_pool = &processor->global_pools[global_pool_idx];
        
        pthread_mutex_lock(&global_pool->lock);
        
        for (uint32_t i = 0; i < FSM_MESSAGES_PER_POOL; i++) {
            uint32_t idx = (global_pool->next_free + i) % FSM_MESSAGES_PER_POOL;
            
            if (!global_pool->allocated[idx]) {
                global_pool->allocated[idx] = true;
                global_pool->allocated_count++;
                global_pool->next_free = (idx + 1) % FSM_MESSAGES_PER_POOL;
                
                fsm_message_t *msg = &global_pool->messages[idx];
                memset(msg, 0, sizeof(fsm_message_t));
                
                pthread_mutex_unlock(&global_pool->lock);
                return msg;
            }
        }
        
        pthread_mutex_unlock(&global_pool->lock);
    }
    
    return NULL;  /* All pools exhausted */
}

/* Free message back to pool */
void fsm_free_message(fsm_processor_system_t *processor,
                     fsm_message_t *msg,
                     uint32_t cpu_core) {
    if (!processor || !msg || cpu_core >= processor->num_cores) {
        return;
    }
    
    fsm_processor_context_t *context = &processor->contexts[cpu_core];
    fsm_message_pool_t *pool = &context->message_pool;
    
    /* Check if message belongs to local pool */
    if (msg >= pool->messages && 
        msg < pool->messages + FSM_MESSAGES_PER_POOL) {
        
        pthread_mutex_lock(&pool->lock);
        
        uint32_t idx = msg - pool->messages;
        if (pool->allocated[idx]) {
            pool->allocated[idx] = false;
            pool->allocated_count--;
        }
        
        pthread_mutex_unlock(&pool->lock);
        return;
    }
    
    /* Check global pools */
    for (uint32_t i = 0; i < processor->num_pools; i++) {
        fsm_message_pool_t *global_pool = &processor->global_pools[i];
        
        if (msg >= global_pool->messages && 
            msg < global_pool->messages + FSM_MESSAGES_PER_POOL) {
            
            pthread_mutex_lock(&global_pool->lock);
            
            uint32_t idx = msg - global_pool->messages;
            if (global_pool->allocated[idx]) {
                global_pool->allocated[idx] = false;
                global_pool->allocated_count--;
            }
            
            pthread_mutex_unlock(&global_pool->lock);
            return;
        }
    }
}

/* Process FSM state transition */
static fsm_processing_result_t fsm_advance_state(fsm_message_t *msg) {
    if (!msg) {
        return FSM_RESULT_ERROR;
    }
    
    /* Validate transition */
    if (!fsm_valid_transition(msg->current_state, msg->next_state)) {
        msg->current_state = FSM_STATE_ERROR;
        return FSM_RESULT_ERROR;
    }
    
    /* Advance to next state */
    fsm_state_t old_state = msg->current_state;
    msg->current_state = msg->next_state;
    
    /* Set next expected state */
    switch (msg->current_state) {
        case FSM_STATE_ROUTED:
            msg->next_state = FSM_STATE_VALIDATED;
            break;
        case FSM_STATE_VALIDATED:
            msg->next_state = FSM_STATE_DELIVERED;
            break;
        case FSM_STATE_DELIVERED:
            msg->next_state = FSM_STATE_ACKNOWLEDGED;
            break;
        case FSM_STATE_ACKNOWLEDGED:
            /* Terminal state */
            return FSM_RESULT_SUCCESS;
        case FSM_STATE_ERROR:
            /* Terminal state */
            return FSM_RESULT_ERROR;
        default:
            /* Handle special states */
            if (msg->current_state == FSM_STATE_BULK_DATA) {
                msg->next_state = FSM_STATE_DELIVERED;
            } else if (msg->current_state >= FSM_STATE_STREAM_START &&
                      msg->current_state <= FSM_STATE_STREAM_END) {
                /* Streaming states handled separately */
                return FSM_RESULT_PENDING;
            }
            break;
    }
    
    return FSM_RESULT_PENDING;
}

/* Stage 1: Route message using Dynamic BCRA */
fsm_processing_result_t fsm_stage_routing(fsm_processor_system_t *processor,
                                         fsm_message_t *msg,
                                         uint32_t cpu_core) {
    if (!processor || !msg || cpu_core >= processor->num_cores) {
        return FSM_RESULT_ERROR;
    }
    
    FSM_TIMING_START();
    
    /* Route message to best server */
    uint16_t best_server = fsm_route_message(processor->routing, msg, cpu_core);
    
    if (best_server == 0) {
        /* No suitable server found */
        msg->current_state = FSM_STATE_ERROR;
        processor->contexts[cpu_core].stats.routing_failures++;
        return FSM_RESULT_ERROR;
    }
    
    /* Update destination if routing changed it */
    msg->dest_server = best_server;
    
    /* Advance FSM state */
    fsm_processing_result_t result = fsm_advance_state(msg);
    
    processor->contexts[cpu_core].stats.routing_decisions++;
    FSM_TIMING_END(&processor->contexts[cpu_core].stats, total_latency_ns);
    
    return result;
}

/* Stage 2: Validate message security and integrity */
fsm_processing_result_t fsm_stage_validation(fsm_processor_system_t *processor,
                                            fsm_message_t *msg) {
    if (!processor || !msg) {
        return FSM_RESULT_ERROR;
    }
    
    FSM_TIMING_START();
    
    /* Validate message integrity */
    if (!fsm_message_validate(msg)) {
        msg->current_state = FSM_STATE_ERROR;
        processor->global_stats.validation_failures++;
        return FSM_RESULT_ERROR;
    }
    
    /* Security validation */
    if (processor->security_validator && 
        !processor->security_validator(msg)) {
        msg->current_state = FSM_STATE_ERROR;
        processor->global_stats.security_violations++;
        return FSM_RESULT_DROP;
    }
    
    /* Port permission validation */
    if (processor->mach_port_validator &&
        !processor->mach_port_validator(msg->source_port, msg->dest_server)) {
        msg->current_state = FSM_STATE_ERROR;
        processor->global_stats.security_violations++;
        return FSM_RESULT_DROP;
    }
    
    /* Advance FSM state */
    fsm_processing_result_t result = fsm_advance_state(msg);
    
    FSM_TIMING_END(&processor->global_stats, total_latency_ns);
    
    return result;
}

/* Stage 3: Deliver message to destination server */
fsm_processing_result_t fsm_stage_delivery(fsm_processor_system_t *processor,
                                          fsm_message_t *msg) {
    if (!processor || !msg) {
        return FSM_RESULT_ERROR;
    }
    
    FSM_TIMING_START();
    
    /* In real implementation, this would interface with Mach IPC
     * to deliver the message to the destination server */
    
    /* Simulate delivery by advancing state */
    fsm_processing_result_t result = fsm_advance_state(msg);
    
    if (result == FSM_RESULT_ERROR) {
        processor->global_stats.delivery_failures++;
    }
    
    FSM_TIMING_END(&processor->global_stats, total_latency_ns);
    
    return result;
}

/* Stage 4: Handle acknowledgment */
fsm_processing_result_t fsm_stage_acknowledgment(fsm_processor_system_t *processor,
                                                fsm_message_t *msg) {
    if (!processor || !msg) {
        return FSM_RESULT_ERROR;
    }
    
    /* Advance to terminal state */
    fsm_processing_result_t result = fsm_advance_state(msg);
    
    return result;
}

/* Process a single message through FSM pipeline */
fsm_processing_result_t fsm_process_message(fsm_processor_system_t *processor,
                                           fsm_message_t *msg,
                                           uint32_t cpu_core) {
    if (!processor || !msg || cpu_core >= processor->num_cores) {
        return FSM_RESULT_ERROR;
    }
    
    FSM_TIMING_START();
    
    fsm_processor_context_t *context = &processor->contexts[cpu_core];
    fsm_processing_result_t result = FSM_RESULT_PENDING;
    
    /* Prefetch hint for next message in batch */
    if (processor->prefetch_enabled) {
        FSM_PREFETCH_READ(msg + 1);
    }
    
    /* Process message through pipeline based on current state */
    switch (msg->current_state) {
        case FSM_STATE_CREATED:
            result = fsm_stage_routing(processor, msg, cpu_core);
            break;
            
        case FSM_STATE_ROUTED:
            result = fsm_stage_validation(processor, msg);
            break;
            
        case FSM_STATE_VALIDATED:
            result = fsm_stage_delivery(processor, msg);
            break;
            
        case FSM_STATE_DELIVERED:
            result = fsm_stage_acknowledgment(processor, msg);
            break;
            
        case FSM_STATE_ACKNOWLEDGED:
            result = FSM_RESULT_SUCCESS;
            break;
            
        case FSM_STATE_ERROR:
            result = FSM_RESULT_ERROR;
            break;
            
        default:
            /* Handle special states (bulk data, streaming) */
            if (msg->current_state == FSM_STATE_BULK_DATA) {
                result = fsm_stage_delivery(processor, msg);
            } else {
                result = FSM_RESULT_ERROR;
                context->stats.invalid_transitions++;
            }
            break;
    }
    
    /* Update statistics */
    context->stats.messages_processed++;
    context->stats.state_transitions++;
    
    FSM_TIMING_END(&context->stats, total_latency_ns);
    
    /* Update latency statistics */
    uint64_t message_latency = context->stats.total_latency_ns / context->stats.messages_processed;
    if (message_latency < context->stats.min_latency_ns) {
        context->stats.min_latency_ns = message_latency;
    }
    if (message_latency > context->stats.max_latency_ns) {
        context->stats.max_latency_ns = message_latency;
    }
    context->stats.avg_latency_ns = message_latency;
    
    return result;
}

/* Batch process multiple messages for efficiency */
uint32_t fsm_process_message_batch(fsm_processor_system_t *processor,
                                  fsm_message_t **messages,
                                  uint32_t count,
                                  uint32_t cpu_core) {
    if (!processor || !messages || count == 0 || cpu_core >= processor->num_cores) {
        return 0;
    }
    
    uint32_t processed = 0;
    
    /* Process messages in batch for cache efficiency */
    for (uint32_t i = 0; i < count; i++) {
        if (!messages[i]) {
            continue;
        }
        
        /* Prefetch next message */
        if (processor->prefetch_enabled && i + 1 < count) {
            FSM_PREFETCH_READ(messages[i + 1]);
        }
        
        fsm_processing_result_t result = fsm_process_message(processor, 
                                                           messages[i], 
                                                           cpu_core);
        
        if (result == FSM_RESULT_SUCCESS || result == FSM_RESULT_PENDING) {
            processed++;
        }
    }
    
    return processed;
}

/* Enqueue message for processing */
bool fsm_enqueue_message(fsm_processor_context_t *context,
                        fsm_message_t *msg) {
    if (!context || !msg) {
        return false;
    }
    
    pthread_mutex_lock(&context->queue_lock);
    
    if (context->queue_count >= FSM_MAX_PENDING_MESSAGES) {
        pthread_mutex_unlock(&context->queue_lock);
        return false;  /* Queue full */
    }
    
    context->pending_queue[context->queue_tail] = msg;
    context->queue_tail = (context->queue_tail + 1) % FSM_MAX_PENDING_MESSAGES;
    context->queue_count++;
    
    pthread_mutex_unlock(&context->queue_lock);
    
    return true;
}

/* Dequeue next message for processing */
fsm_message_t *fsm_dequeue_message(fsm_processor_context_t *context) {
    if (!context) {
        return NULL;
    }
    
    pthread_mutex_lock(&context->queue_lock);
    
    if (context->queue_count == 0) {
        pthread_mutex_unlock(&context->queue_lock);
        return NULL;  /* Queue empty */
    }
    
    fsm_message_t *msg = context->pending_queue[context->queue_head];
    context->queue_head = (context->queue_head + 1) % FSM_MAX_PENDING_MESSAGES;
    context->queue_count--;
    
    pthread_mutex_unlock(&context->queue_lock);
    
    return msg;
}

/* Submit message for asynchronous processing */
bool fsm_submit_message_async(fsm_processor_system_t *processor,
                             fsm_message_t *msg) {
    if (!processor || !msg) {
        return false;
    }
    
    /* Select optimal core for processing */
    uint32_t target_core = fsm_select_optimal_core(processor, msg);
    
    return fsm_enqueue_message(&processor->contexts[target_core], msg);
}

/* Select optimal core for message processing */
uint32_t fsm_select_optimal_core(fsm_processor_system_t *processor,
                                const fsm_message_t *msg) {
    if (!processor || !msg) {
        return 0;
    }
    
    /* Simple load balancing: find core with smallest queue */
    uint32_t best_core = 0;
    uint32_t min_queue_depth = UINT32_MAX;
    
    for (uint32_t i = 0; i < processor->num_cores; i++) {
        uint32_t queue_depth = fsm_get_queue_depth(&processor->contexts[i]);
        
        if (queue_depth < min_queue_depth) {
            min_queue_depth = queue_depth;
            best_core = i;
        }
    }
    
    return best_core;
}

/* Get queue depth for load balancing */
uint32_t fsm_get_queue_depth(const fsm_processor_context_t *context) {
    if (!context) {
        return 0;
    }
    
    return context->queue_count;
}

/* Get processor statistics */
void fsm_get_processor_stats(const fsm_processor_system_t *processor,
                            fsm_processor_stats_t *stats) {
    if (!processor || !stats) {
        return;
    }
    
    memset(stats, 0, sizeof(fsm_processor_stats_t));
    stats->min_latency_ns = UINT64_MAX;
    
    /* Aggregate statistics from all cores */
    for (uint32_t i = 0; i < processor->num_cores; i++) {
        const fsm_processor_stats_t *core_stats = &processor->contexts[i].stats;
        
        stats->messages_processed += core_stats->messages_processed;
        stats->state_transitions += core_stats->state_transitions;
        stats->routing_decisions += core_stats->routing_decisions;
        stats->validation_failures += core_stats->validation_failures;
        stats->delivery_failures += core_stats->delivery_failures;
        stats->total_latency_ns += core_stats->total_latency_ns;
        
        if (core_stats->min_latency_ns < stats->min_latency_ns) {
            stats->min_latency_ns = core_stats->min_latency_ns;
        }
        if (core_stats->max_latency_ns > stats->max_latency_ns) {
            stats->max_latency_ns = core_stats->max_latency_ns;
        }
    }
    
    /* Calculate average latency */
    if (stats->messages_processed > 0) {
        stats->avg_latency_ns = stats->total_latency_ns / stats->messages_processed;
    }
    
    /* Add global statistics */
    stats->validation_failures += processor->global_stats.validation_failures;
    stats->delivery_failures += processor->global_stats.delivery_failures;
    stats->security_violations += processor->global_stats.security_violations;
}

/* Set CPU affinity for worker thread */
bool fsm_set_cpu_affinity(pthread_t thread, uint32_t cpu_core) {
    cpu_set_t cpuset;
    
    CPU_ZERO(&cpuset);
    CPU_SET(cpu_core, &cpuset);
    
    return pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset) == 0;
}

/* Validate message meets security requirements */
bool fsm_validate_message_security(const fsm_message_t *msg) {
    if (!msg) {
        return false;
    }
    
    /* Basic security checks */
    
    /* Check payload length */
    if (msg->payload_length > 56) {
        return false;
    }
    
    /* Check state validity */
    if (msg->current_state > FSM_STATE_STREAM_END) {
        return false;
    }
    
    /* Check port numbers are in valid ranges */
    if (msg->source_port == 0 || msg->dest_server == 0) {
        return false;
    }
    
    return true;
}

/* Cleanup message pool */
void fsm_cleanup_message_pool(fsm_message_pool_t *pool) {
    if (!pool) {
        return;
    }
    
    pthread_mutex_destroy(&pool->lock);
    memset(pool, 0, sizeof(fsm_message_pool_t));
}

/* Shutdown the processor system */
void fsm_processor_shutdown(fsm_processor_system_t *processor) {
    if (!processor) {
        return;
    }
    
    processor->shutdown_requested = true;
    
    /* Stop worker threads */
    fsm_stop_worker_threads(processor);
    
    /* Cleanup per-core contexts */
    for (uint32_t i = 0; i < processor->num_cores; i++) {
        fsm_processor_context_t *context = &processor->contexts[i];
        
        fsm_cleanup_message_pool(&context->message_pool);
        pthread_mutex_destroy(&context->queue_lock);
    }
    
    /* Cleanup global pools */
    for (uint32_t i = 0; i < processor->num_pools; i++) {
        fsm_cleanup_message_pool(&processor->global_pools[i]);
    }
    
    memset(processor, 0, sizeof(fsm_processor_system_t));
}

/* Worker thread stub functions */
void *fsm_worker_thread(void *arg) {
    /* Implementation would depend on specific threading model */
    return NULL;
}

bool fsm_start_worker_threads(fsm_processor_system_t *processor) {
    /* Implementation would create worker threads for each core */
    return true;
}

void fsm_stop_worker_threads(fsm_processor_system_t *processor) {
    /* Implementation would stop all worker threads */
}