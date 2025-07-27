/* FSM Message Processor
 * High-performance state machine for message processing
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _FSM_PROCESSOR_H_
#define _FSM_PROCESSOR_H_

#include "fsm_message.h"
#include "fsm_routing.h"
#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>

/* Maximum number of concurrent message pools */
#define FSM_MAX_MESSAGE_POOLS       16
#define FSM_MESSAGES_PER_POOL      1024
#define FSM_MAX_PENDING_MESSAGES   4096

/* Processing pipeline configuration */
#define FSM_PIPELINE_STAGES         4
#define FSM_BATCH_SIZE             64

/* Performance targets */
#define FSM_TARGET_LATENCY_NS      1000     /* 1 microsecond */
#define FSM_TARGET_THROUGHPUT      1000000  /* 1M messages/sec */

/* Message processing statistics */
typedef struct {
    uint64_t messages_processed;
    uint64_t state_transitions;
    uint64_t routing_decisions;
    uint64_t validation_failures;
    uint64_t delivery_failures;
    
    /* Latency statistics (nanoseconds) */
    uint64_t min_latency_ns;
    uint64_t max_latency_ns;
    uint64_t avg_latency_ns;
    uint64_t total_latency_ns;
    
    /* Throughput statistics */
    uint64_t messages_per_second;
    uint64_t peak_throughput;
    
    /* Error statistics */
    uint64_t invalid_transitions;
    uint64_t routing_failures;
    uint64_t security_violations;
    
} fsm_processor_stats_t;

/* Message pool for high-performance allocation */
typedef struct {
    fsm_message_t   messages[FSM_MESSAGES_PER_POOL];
    bool            allocated[FSM_MESSAGES_PER_POOL];
    uint32_t        next_free;
    uint32_t        allocated_count;
    pthread_mutex_t lock;
} fsm_message_pool_t;

/* Processing context for each CPU core */
typedef struct {
    uint32_t            cpu_core;
    uint32_t            numa_node;
    
    /* Local message pool */
    fsm_message_pool_t  message_pool;
    
    /* Pending message queue */
    fsm_message_t      *pending_queue[FSM_MAX_PENDING_MESSAGES];
    uint32_t            queue_head;
    uint32_t            queue_tail;
    uint32_t            queue_count;
    pthread_mutex_t     queue_lock;
    
    /* Statistics */
    fsm_processor_stats_t stats;
    
    /* Pipeline stages timing */
    uint64_t            stage_times[FSM_PIPELINE_STAGES];
    
} fsm_processor_context_t;

/* Main FSM processor system */
typedef struct {
    /* Routing system integration */
    fsm_routing_system_t   *routing;
    
    /* Per-core processing contexts */
    fsm_processor_context_t contexts[32];  /* Support up to 32 CPU cores */
    uint32_t                num_cores;
    
    /* Global message pools */
    fsm_message_pool_t      global_pools[FSM_MAX_MESSAGE_POOLS];
    uint32_t                num_pools;
    
    /* System configuration */
    bool                    numa_affinity_enabled;
    bool                    batch_processing_enabled;
    bool                    prefetch_enabled;
    uint32_t                batch_size;
    
    /* Global statistics */
    fsm_processor_stats_t   global_stats;
    
    /* Security validation */
    bool (*security_validator)(const fsm_message_t *msg);
    bool (*mach_port_validator)(uint16_t port, uint16_t server);
    
    /* Performance monitoring */
    uint64_t                last_stats_update;
    uint64_t                stats_update_interval_ms;
    
    /* Thread management */
    pthread_t               worker_threads[32];
    bool                    shutdown_requested;
    
} fsm_processor_system_t;

/* Processing pipeline stages */
typedef enum {
    FSM_STAGE_ROUTING       = 0,    /* Route message to best server */
    FSM_STAGE_VALIDATION    = 1,    /* Security and integrity validation */
    FSM_STAGE_DELIVERY      = 2,    /* Deliver to destination */
    FSM_STAGE_ACKNOWLEDGMENT = 3    /* Handle acknowledgment */
} fsm_pipeline_stage_t;

/* Message processing result */
typedef enum {
    FSM_RESULT_SUCCESS      = 0,    /* Processing completed successfully */
    FSM_RESULT_PENDING      = 1,    /* Processing continues asynchronously */
    FSM_RESULT_ERROR        = 2,    /* Processing failed */
    FSM_RESULT_RETRY        = 3,    /* Should retry processing */
    FSM_RESULT_DROP         = 4     /* Drop message (security violation) */
} fsm_processing_result_t;

/* Core processor functions */

/* Initialize the FSM processor system */
bool fsm_processor_init(fsm_processor_system_t *processor,
                       fsm_routing_system_t *routing,
                       uint32_t num_cores);

/* Shutdown the processor system */
void fsm_processor_shutdown(fsm_processor_system_t *processor);

/* Process a single message through FSM pipeline */
fsm_processing_result_t fsm_process_message(fsm_processor_system_t *processor,
                                           fsm_message_t *msg,
                                           uint32_t cpu_core);

/* Batch process multiple messages for efficiency */
uint32_t fsm_process_message_batch(fsm_processor_system_t *processor,
                                  fsm_message_t **messages,
                                  uint32_t count,
                                  uint32_t cpu_core);

/* Submit message for asynchronous processing */
bool fsm_submit_message_async(fsm_processor_system_t *processor,
                             fsm_message_t *msg);

/* Pipeline stage functions */

/* Stage 1: Route message using Dynamic BCRA */
fsm_processing_result_t fsm_stage_routing(fsm_processor_system_t *processor,
                                         fsm_message_t *msg,
                                         uint32_t cpu_core);

/* Stage 2: Validate message security and integrity */
fsm_processing_result_t fsm_stage_validation(fsm_processor_system_t *processor,
                                            fsm_message_t *msg);

/* Stage 3: Deliver message to destination server */
fsm_processing_result_t fsm_stage_delivery(fsm_processor_system_t *processor,
                                          fsm_message_t *msg);

/* Stage 4: Handle acknowledgment */
fsm_processing_result_t fsm_stage_acknowledgment(fsm_processor_system_t *processor,
                                                fsm_message_t *msg);

/* Memory management functions */

/* Allocate message from pool */
fsm_message_t *fsm_alloc_message(fsm_processor_system_t *processor,
                                uint32_t cpu_core);

/* Free message back to pool */
void fsm_free_message(fsm_processor_system_t *processor,
                     fsm_message_t *msg,
                     uint32_t cpu_core);

/* Initialize message pool */
bool fsm_init_message_pool(fsm_message_pool_t *pool);

/* Cleanup message pool */
void fsm_cleanup_message_pool(fsm_message_pool_t *pool);

/* Performance optimization functions */

/* Enable NUMA affinity for optimal memory access */
bool fsm_enable_numa_affinity(fsm_processor_system_t *processor);

/* Enable batch processing for throughput optimization */
void fsm_enable_batch_processing(fsm_processor_system_t *processor,
                                bool enable,
                                uint32_t batch_size);

/* Enable memory prefetching hints */
void fsm_enable_prefetch(fsm_processor_system_t *processor, bool enable);

/* Set CPU affinity for worker thread */
bool fsm_set_cpu_affinity(pthread_t thread, uint32_t cpu_core);

/* Statistics and monitoring functions */

/* Get processor statistics */
void fsm_get_processor_stats(const fsm_processor_system_t *processor,
                            fsm_processor_stats_t *stats);

/* Get per-core statistics */
bool fsm_get_core_stats(const fsm_processor_system_t *processor,
                       uint32_t cpu_core,
                       fsm_processor_stats_t *stats);

/* Reset statistics counters */
void fsm_reset_processor_stats(fsm_processor_system_t *processor);

/* Update performance metrics */
void fsm_update_performance_metrics(fsm_processor_system_t *processor);

/* Security and validation functions */

/* Set security validation callback */
void fsm_set_security_validator(fsm_processor_system_t *processor,
                               bool (*validator)(const fsm_message_t *msg));

/* Set Mach port validation callback */
void fsm_set_port_validator(fsm_processor_system_t *processor,
                           bool (*validator)(uint16_t port, uint16_t server));

/* Validate message meets security requirements */
bool fsm_validate_message_security(const fsm_message_t *msg);

/* Check if source has permission to send to destination */
bool fsm_validate_send_permission(uint16_t source_port, uint16_t dest_server);

/* Worker thread functions */

/* Main worker thread function */
void *fsm_worker_thread(void *arg);

/* Start worker threads for all CPU cores */
bool fsm_start_worker_threads(fsm_processor_system_t *processor);

/* Stop all worker threads */
void fsm_stop_worker_threads(fsm_processor_system_t *processor);

/* Queue management functions */

/* Enqueue message for processing */
bool fsm_enqueue_message(fsm_processor_context_t *context,
                        fsm_message_t *msg);

/* Dequeue next message for processing */
fsm_message_t *fsm_dequeue_message(fsm_processor_context_t *context);

/* Get queue depth for load balancing */
uint32_t fsm_get_queue_depth(const fsm_processor_context_t *context);

/* Integration functions */

/* Create FSM message from Mach message */
fsm_message_t *fsm_create_from_mach(fsm_processor_system_t *processor,
                                   const void *mach_msg,
                                   size_t msg_size);

/* Convert FSM message to Mach format for delivery */
bool fsm_convert_to_mach(const fsm_message_t *fsm_msg,
                        void *mach_msg,
                        size_t max_size,
                        size_t *actual_size);

/* Register with Mach port system */
bool fsm_register_mach_integration(fsm_processor_system_t *processor);

/* Advanced features */

/* SIMD batch processing for multiple messages */
uint32_t fsm_simd_process_batch(fsm_message_t **messages, uint32_t count);

/* Adaptive load balancing across cores */
uint32_t fsm_select_optimal_core(fsm_processor_system_t *processor,
                                const fsm_message_t *msg);

/* Priority-based message scheduling */
bool fsm_set_message_priority(fsm_message_t *msg, uint32_t priority);

/* Streaming data reassembly */
fsm_message_t *fsm_reassemble_stream(fsm_processor_system_t *processor,
                                    const fsm_message_t *fragment);

/* Configuration and tuning */

/* Set processing targets */
void fsm_set_performance_targets(fsm_processor_system_t *processor,
                                uint64_t target_latency_ns,
                                uint64_t target_throughput);

/* Configure pipeline stages */
bool fsm_configure_pipeline(fsm_processor_system_t *processor,
                           uint32_t num_stages,
                           const uint32_t *stage_config);

/* Set memory allocation strategy */
void fsm_set_allocation_strategy(fsm_processor_system_t *processor,
                                int strategy);

/* Debug and diagnostics */

#ifdef FSM_DEBUG
/* Dump processor state for debugging */
void fsm_dump_processor_state(const fsm_processor_system_t *processor);

/* Dump message processing pipeline */
void fsm_dump_pipeline_state(const fsm_processor_context_t *context);

/* Trace message processing */
void fsm_trace_message(const fsm_message_t *msg, const char *stage);

/* Validate processor invariants */
bool fsm_validate_processor_invariants(const fsm_processor_system_t *processor);
#endif

/* Utility macros for performance measurement */
#define FSM_TIMING_START() \
    struct timespec _start_time; \
    clock_gettime(CLOCK_MONOTONIC, &_start_time)

#define FSM_TIMING_END(stats, field) \
    do { \
        struct timespec _end_time; \
        clock_gettime(CLOCK_MONOTONIC, &_end_time); \
        uint64_t _elapsed = (_end_time.tv_sec - _start_time.tv_sec) * 1000000000ULL + \
                           (_end_time.tv_nsec - _start_time.tv_nsec); \
        (stats)->field += _elapsed; \
    } while(0)

/* Prefetch hints for performance */
#ifdef __GNUC__
#define FSM_PREFETCH_READ(addr)  __builtin_prefetch((addr), 0, 3)
#define FSM_PREFETCH_WRITE(addr) __builtin_prefetch((addr), 1, 3)
#else
#define FSM_PREFETCH_READ(addr)  /* no-op */
#define FSM_PREFETCH_WRITE(addr) /* no-op */
#endif

#endif /* _FSM_PROCESSOR_H_ */