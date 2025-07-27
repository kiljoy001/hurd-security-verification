/* FSM IPC + ULE Scheduler Integration
 * Combines FSM-based IPC with ULE SMP scheduling for optimal performance
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _FSM_ULE_INTEGRATION_H_
#define _FSM_ULE_INTEGRATION_H_

#include "fsm_message.h"
#include "fsm_routing.h"
#include "fsm_processor.h"
#include "ule_sched_mock.h"

/* Integration configuration */
#define FSM_ULE_MAX_CORES           32
#define FSM_ULE_PRIORITY_LEVELS     5
#define FSM_ULE_TIMESLICE_US        1000    /* 1ms default timeslice */

/* Message priority mapping from FSM to ULE */
typedef struct {
    fsm_state_t         fsm_state;
    ule_msg_class_t     ule_priority;
    uint32_t            timeslice_us;
    bool                preemptible;
} fsm_ule_priority_map_t;

/* Server affinity mapping */
typedef struct {
    fsm_server_type_t   fsm_server_type;
    ule_server_type_t   ule_server_type;
    uint32_t           preferred_cores[8];  /* Preferred CPU cores */
    uint32_t           num_preferred_cores;
} fsm_ule_affinity_map_t;

/* Core scheduling context */
typedef struct {
    uint32_t            core_id;
    ule_sched_state_t   ule_state;          /* ULE scheduler state */
    fsm_processor_context_t *fsm_context;  /* FSM processor context */
    
    /* Load balancing metrics */
    uint64_t            messages_processed;
    uint64_t            total_latency_ns;
    double              current_load;       /* 0.0 to 1.0 */
    
    /* Priority queues for FSM messages */
    fsm_message_t      *priority_queues[FSM_ULE_PRIORITY_LEVELS][64];
    uint32_t            queue_heads[FSM_ULE_PRIORITY_LEVELS];
    uint32_t            queue_tails[FSM_ULE_PRIORITY_LEVELS];
    uint32_t            queue_counts[FSM_ULE_PRIORITY_LEVELS];
    
    /* Timing and scheduling */
    uint64_t            last_schedule_time;
    uint32_t            current_timeslice_us;
    bool                preemption_enabled;
    
} fsm_ule_core_context_t;

/* Main integration system */
typedef struct {
    /* FSM and ULE systems */
    fsm_processor_system_t  *fsm_processor;
    fsm_routing_system_t    *fsm_routing;
    ule_sched_global_t      *ule_scheduler;
    
    /* Per-core contexts */
    fsm_ule_core_context_t  core_contexts[FSM_ULE_MAX_CORES];
    uint32_t                num_cores;
    
    /* Configuration */
    fsm_ule_priority_map_t  priority_map[10];   /* FSM state -> ULE priority */
    fsm_ule_affinity_map_t  affinity_map[7];    /* Server type affinities */
    
    /* Performance optimization */
    bool                    numa_aware;
    bool                    power_management;
    bool                    adaptive_scheduling;
    uint32_t               load_balance_interval_ms;
    
    /* Statistics */
    uint64_t               total_messages_scheduled;
    uint64_t               context_switches;
    uint64_t               load_balance_operations;
    double                 average_latency_us;
    
} fsm_ule_integration_t;

/* Scheduling policies */
typedef enum {
    FSM_ULE_POLICY_FIFO         = 0,  /* First-in-first-out */
    FSM_ULE_POLICY_PRIORITY     = 1,  /* Priority-based scheduling */
    FSM_ULE_POLICY_FAIR         = 2,  /* Fair share scheduling */
    FSM_ULE_POLICY_REALTIME     = 3,  /* Real-time scheduling */
    FSM_ULE_POLICY_ADAPTIVE     = 4   /* Adaptive based on load */
} fsm_ule_scheduling_policy_t;

/* ===== Core Integration Functions ===== */

/* Initialize FSM+ULE integrated system */
bool fsm_ule_integration_init(fsm_ule_integration_t *integration,
                              uint32_t num_cores,
                              fsm_ule_scheduling_policy_t policy);

/* Shutdown integrated system */
void fsm_ule_integration_shutdown(fsm_ule_integration_t *integration);

/* ===== Message Scheduling Functions ===== */

/* Schedule FSM message using ULE scheduler */
fsm_processing_result_t fsm_ule_schedule_message(fsm_ule_integration_t *integration,
                                                 fsm_message_t *msg,
                                                 uint32_t preferred_core);

/* Process next message from ULE-scheduled queue */
fsm_processing_result_t fsm_ule_process_next_message(fsm_ule_integration_t *integration,
                                                     uint32_t core_id);

/* Batch process messages with ULE scheduling */
uint32_t fsm_ule_process_message_batch(fsm_ule_integration_t *integration,
                                      uint32_t core_id,
                                      uint32_t max_messages);

/* ===== Load Balancing Functions ===== */

/* Perform load balancing across cores */
bool fsm_ule_load_balance(fsm_ule_integration_t *integration);

/* Get optimal core for message based on ULE scheduling */
uint32_t fsm_ule_select_optimal_core(fsm_ule_integration_t *integration,
                                     const fsm_message_t *msg);

/* Migrate message to different core */
bool fsm_ule_migrate_message(fsm_ule_integration_t *integration,
                             fsm_message_t *msg,
                             uint32_t from_core,
                             uint32_t to_core);

/* ===== Priority and Affinity Management ===== */

/* Set message priority based on FSM state and ULE class */
ule_msg_class_t fsm_ule_get_message_priority(const fsm_message_t *msg);

/* Get server affinity for optimal core placement */
uint32_t fsm_ule_get_server_affinity(fsm_server_type_t server_type,
                                     const fsm_ule_integration_t *integration);

/* Update priority mapping configuration */
bool fsm_ule_configure_priority_map(fsm_ule_integration_t *integration,
                                    fsm_state_t fsm_state,
                                    ule_msg_class_t ule_priority,
                                    uint32_t timeslice_us);

/* Configure server-to-core affinity */
bool fsm_ule_configure_affinity(fsm_ule_integration_t *integration,
                                fsm_server_type_t fsm_server,
                                ule_server_type_t ule_server,
                                const uint32_t *preferred_cores,
                                uint32_t num_cores);

/* ===== Performance Monitoring ===== */

/* Get per-core performance statistics */
void fsm_ule_get_core_stats(const fsm_ule_integration_t *integration,
                            uint32_t core_id,
                            fsm_ule_core_context_t *stats);

/* Get system-wide performance metrics */
void fsm_ule_get_system_stats(const fsm_ule_integration_t *integration,
                              uint64_t *total_messages,
                              double *avg_latency_us,
                              double *system_load);

/* Update load balancing metrics */
void fsm_ule_update_load_metrics(fsm_ule_integration_t *integration,
                                 uint32_t core_id,
                                 uint64_t processing_time_ns);

/* ===== Advanced Features ===== */

/* Enable/disable NUMA-aware scheduling */
void fsm_ule_set_numa_aware(fsm_ule_integration_t *integration, bool enabled);

/* Enable/disable power management features */
void fsm_ule_set_power_management(fsm_ule_integration_t *integration, bool enabled);

/* Configure adaptive scheduling parameters */
bool fsm_ule_configure_adaptive_scheduling(fsm_ule_integration_t *integration,
                                           uint32_t load_threshold_percent,
                                           uint32_t balance_interval_ms);

/* Set scheduling policy for specific server type */
bool fsm_ule_set_server_policy(fsm_ule_integration_t *integration,
                               fsm_server_type_t server_type,
                               fsm_ule_scheduling_policy_t policy);

/* ===== Real-time Features ===== */

/* Reserve CPU bandwidth for real-time messages */
bool fsm_ule_reserve_bandwidth(fsm_ule_integration_t *integration,
                               uint32_t core_id,
                               uint32_t percent_bandwidth);

/* Set deadline for time-critical messages */
bool fsm_ule_set_message_deadline(fsm_message_t *msg, uint64_t deadline_ns);

/* Check if message missed its deadline */
bool fsm_ule_check_deadline_miss(const fsm_message_t *msg);

/* ===== Integration Utilities ===== */

/* Convert FSM server type to ULE server type */
ule_server_type_t fsm_to_ule_server_type(fsm_server_type_t fsm_type);

/* Convert FSM state to ULE message class */
ule_msg_class_t fsm_to_ule_message_class(fsm_state_t fsm_state);

/* Get recommended timeslice for message type */
uint32_t fsm_ule_get_recommended_timeslice(const fsm_message_t *msg);

/* Check if preemption is allowed for message */
bool fsm_ule_is_preemptible(const fsm_message_t *msg);

/* ===== Debug and Diagnostics ===== */

#ifdef FSM_ULE_DEBUG
/* Dump scheduler state for debugging */
void fsm_ule_dump_scheduler_state(const fsm_ule_integration_t *integration,
                                  uint32_t core_id);

/* Validate system consistency */
bool fsm_ule_validate_system_state(const fsm_ule_integration_t *integration);

/* Trace message scheduling decisions */
void fsm_ule_trace_scheduling(const fsm_ule_integration_t *integration,
                              const fsm_message_t *msg,
                              uint32_t selected_core,
                              const char *reason);
#endif

/* ===== Default Configuration ===== */

/* Initialize with default priority mappings */
void fsm_ule_init_default_priority_map(fsm_ule_integration_t *integration);

/* Initialize with default server affinities */
void fsm_ule_init_default_affinity_map(fsm_ule_integration_t *integration);

/* Apply performance-optimized defaults */
void fsm_ule_apply_performance_defaults(fsm_ule_integration_t *integration);

#endif /* _FSM_ULE_INTEGRATION_H_ */