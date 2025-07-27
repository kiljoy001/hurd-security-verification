/* Mock ULE Scheduler Types for FSM Integration
 * Simplified types to enable compilation without full ULE implementation
 */

#ifndef _ULE_SCHED_MOCK_H_
#define _ULE_SCHED_MOCK_H_

#include <stdint.h>
#include <stdbool.h>

/* Mock ULE scheduler global state */
typedef struct {
    uint32_t num_cores;
    uint64_t total_context_switches;
    double global_load_avg;
    bool power_management_enabled;
} ule_sched_global_t;

/* Mock ULE scheduler per-core state */
typedef struct {
    uint32_t core_id;
    uint32_t running_threads;
    double cpu_utilization;
    uint64_t last_schedule_time;
} ule_sched_state_t;

/* Mock ULE server types (matching the original) */
typedef enum {
    ULE_SERVER_FILESYSTEM = 0,
    ULE_SERVER_NETWORK    = 1,
    ULE_SERVER_PROCESS    = 2,
    ULE_SERVER_MEMORY     = 3,
    ULE_SERVER_DEVICE     = 4,
    ULE_SERVER_GUI        = 5,
    ULE_SERVER_AUDIO      = 6,
    ULE_SERVER_COUNT      = 7
} ule_server_type_t;

/* Mock ULE message classes (matching the original) */
typedef enum {
    ULE_MSG_INTERRUPT   = 0,
    ULE_MSG_REALTIME    = 1,
    ULE_MSG_INTERACTIVE = 2,
    ULE_MSG_BATCH       = 3,
    ULE_MSG_IDLE        = 4
} ule_msg_class_t;

/* Mock ULE scheduler functions */
bool ule_sched_init(ule_sched_global_t *scheduler, uint32_t num_cores);
void ule_sched_shutdown(ule_sched_global_t *scheduler);

#endif /* _ULE_SCHED_MOCK_H_ */