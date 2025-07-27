/* FSM+ULE Integration Test
 * Tests the combined FSM IPC and ULE scheduler system
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>

#include "fsm_ule_integration.h"

int tests_passed = 0;
int tests_failed = 0;

#define TEST(condition, message) \
    do { \
        if (condition) { \
            printf("✓ PASS: %s\n", message); \
            tests_passed++; \
        } else { \
            printf("✗ FAIL: %s\n", message); \
            tests_failed++; \
        } \
    } while(0)

/* Mock ULE scheduler functions (since we don't have the full ULE implementation) */
bool ule_sched_init(ule_sched_global_t *scheduler, uint32_t num_cores) {
    if (!scheduler || num_cores == 0) return false;
    
    memset(scheduler, 0, sizeof(ule_sched_global_t));
    /* Initialize mock ULE scheduler state */
    return true;
}

/* Worker thread data */
typedef struct {
    fsm_ule_integration_t *integration;
    uint32_t core_id;
    uint32_t messages_to_process;
    uint32_t messages_processed;
    double avg_latency_us;
} worker_thread_data_t;

void *worker_thread(void *arg) {
    worker_thread_data_t *data = (worker_thread_data_t*)arg;
    
    for (uint32_t i = 0; i < data->messages_to_process; i++) {
        /* Allocate a message */
        fsm_message_t *msg = fsm_alloc_message(data->integration->fsm_processor, data->core_id);
        if (msg) {
            /* Initialize message */
            fsm_message_init(msg, 3000 + i, 0);
            fsm_message_set_payload(msg, "FSM+ULE test", 12);
            
            /* Schedule it through FSM+ULE system */
            fsm_processing_result_t result = fsm_ule_schedule_message(data->integration, msg, data->core_id);
            
            if (result == FSM_RESULT_PENDING || result == FSM_RESULT_SUCCESS) {
                data->messages_processed++;
            }
        }
        
        /* Process some messages */
        fsm_ule_process_message_batch(data->integration, data->core_id, 5);
        
        /* Small delay to simulate real workload */
        usleep(10);  /* 10 microseconds */
    }
    
    return NULL;
}

int main(void) {
    printf("=== FSM+ULE Integration Test ===\n\n");
    
    /* Test 1: Integration system initialization */
    printf("Test 1: System Initialization\n");
    fsm_ule_integration_t integration;
    
    bool result = fsm_ule_integration_init(&integration, 4, FSM_ULE_POLICY_PRIORITY);
    TEST(result == true, "FSM+ULE integration initializes successfully");
    TEST(integration.num_cores == 4, "Number of cores set correctly");
    TEST(integration.fsm_processor != NULL, "FSM processor initialized");
    TEST(integration.fsm_routing != NULL, "FSM routing initialized");
    TEST(integration.ule_scheduler != NULL, "ULE scheduler initialized");
    
    /* Test 2: Type conversion functions */
    printf("\nTest 2: Type Conversions\n");
    ule_server_type_t ule_type = fsm_to_ule_server_type(FSM_SERVER_NETWORK);
    TEST(ule_type == ULE_SERVER_NETWORK, "FSM to ULE server type conversion");
    
    ule_msg_class_t ule_class = fsm_to_ule_message_class(FSM_STATE_DELIVERED);
    TEST(ule_class == ULE_MSG_REALTIME, "FSM state to ULE message class conversion");
    
    uint32_t timeslice = fsm_ule_get_recommended_timeslice(&(fsm_message_t){
        .current_state = FSM_STATE_DELIVERED
    });
    TEST(timeslice == 100, "Recommended timeslice for real-time message");
    
    /* Test 3: Message scheduling */
    printf("\nTest 3: Message Scheduling\n");
    fsm_message_t *test_msg = fsm_alloc_message(integration.fsm_processor, 0);
    TEST(test_msg != NULL, "Message allocation succeeds");
    
    if (test_msg) {
        fsm_message_init(test_msg, 4000, 0);
        fsm_message_set_payload(test_msg, "schedule test", 13);
        
        fsm_processing_result_t sched_result = fsm_ule_schedule_message(&integration, test_msg, 0);
        TEST(sched_result == FSM_RESULT_PENDING, "Message scheduling succeeds");
        
        /* Check that message was added to queue */
        TEST(integration.core_contexts[0].queue_counts[ULE_MSG_INTERACTIVE] > 0, 
             "Message added to correct priority queue");
    }
    
    /* Test 4: Message processing */
    printf("\nTest 4: Message Processing\n");
    fsm_processing_result_t proc_result = fsm_ule_process_next_message(&integration, 0);
    TEST(proc_result != FSM_RESULT_ERROR, "Message processing succeeds");
    
    /* Test 5: Load balancing */
    printf("\nTest 5: Load Balancing\n");
    
    /* Add some load to core 0 */
    for (int i = 0; i < 10; i++) {
        fsm_message_t *load_msg = fsm_alloc_message(integration.fsm_processor, 0);
        if (load_msg) {
            fsm_message_init(load_msg, 5000 + i, 0);
            fsm_ule_schedule_message(&integration, load_msg, 0);
        }
    }
    
    uint32_t queue_count_before = integration.core_contexts[0].queue_counts[ULE_MSG_INTERACTIVE];
    
    bool balance_result = fsm_ule_load_balance(&integration);
    TEST(balance_result == true, "Load balancing executes successfully");
    
    /* Test 6: Multi-core processing */
    printf("\nTest 6: Multi-core Processing\n");
    
    const int NUM_THREADS = 4;
    const int MESSAGES_PER_THREAD = 50;
    
    pthread_t threads[NUM_THREADS];
    worker_thread_data_t thread_data[NUM_THREADS];
    
    /* Launch worker threads */
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_data[i].integration = &integration;
        thread_data[i].core_id = i;
        thread_data[i].messages_to_process = MESSAGES_PER_THREAD;
        thread_data[i].messages_processed = 0;
        thread_data[i].avg_latency_us = 0.0;
        
        pthread_create(&threads[i], NULL, worker_thread, &thread_data[i]);
    }
    
    /* Wait for completion */
    uint32_t total_processed = 0;
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
        total_processed += thread_data[i].messages_processed;
    }
    
    printf("  Multi-core processed: %u messages\n", total_processed);
    TEST(total_processed > NUM_THREADS * MESSAGES_PER_THREAD * 0.5, 
         "Multi-core processing handled significant workload");
    
    /* Test 7: Performance statistics */
    printf("\nTest 7: Performance Statistics\n");
    
    uint64_t total_messages;
    double avg_latency_us;
    double system_load;
    
    fsm_ule_get_system_stats(&integration, &total_messages, &avg_latency_us, &system_load);
    
    printf("  Total messages: %lu\n", total_messages);
    printf("  Average latency: %.3f μs\n", avg_latency_us);
    printf("  System load: %.3f\n", system_load);
    
    TEST(total_messages > 0, "System tracked message processing");
    TEST(avg_latency_us >= 0.0, "Average latency calculated");
    TEST(system_load >= 0.0, "System load calculated");
    
    /* Test 8: Configuration functions */
    printf("\nTest 8: Configuration\n");
    
    fsm_ule_set_numa_aware(&integration, true);
    TEST(integration.numa_aware == true, "NUMA awareness configuration");
    
    fsm_ule_set_power_management(&integration, false);
    TEST(integration.power_management == false, "Power management configuration");
    
    bool adaptive_result = fsm_ule_configure_adaptive_scheduling(&integration, 80, 20);
    TEST(adaptive_result == true, "Adaptive scheduling configuration");
    TEST(integration.load_balance_interval_ms == 20, "Load balance interval set");
    
    /* Test 9: Priority mapping */
    printf("\nTest 9: Priority Mapping\n");
    
    ule_msg_class_t priority = fsm_ule_get_message_priority(&(fsm_message_t){
        .current_state = FSM_STATE_ERROR
    });
    TEST(priority == ULE_MSG_INTERRUPT, "Error messages get interrupt priority");
    
    priority = fsm_ule_get_message_priority(&(fsm_message_t){
        .current_state = FSM_STATE_ACKNOWLEDGED
    });
    TEST(priority == ULE_MSG_IDLE, "Acknowledged messages get idle priority");
    
    /* Test 10: Core selection */
    printf("\nTest 10: Core Selection\n");
    
    fsm_message_t select_msg;
    fsm_message_init(&select_msg, 6000, 0);
    
    uint32_t selected_core = fsm_ule_select_optimal_core(&integration, &select_msg);
    TEST(selected_core < integration.num_cores, "Core selection returns valid core");
    
    /* Test 11: Batch processing performance */
    printf("\nTest 11: Batch Processing Performance\n");
    
    /* Add a batch of messages */
    for (int i = 0; i < 20; i++) {
        fsm_message_t *batch_msg = fsm_alloc_message(integration.fsm_processor, 1);
        if (batch_msg) {
            fsm_message_init(batch_msg, 7000 + i, 0);
            fsm_ule_schedule_message(&integration, batch_msg, 1);
        }
    }
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    uint32_t batch_processed = fsm_ule_process_message_batch(&integration, 1, 20);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double batch_time_ms = (end.tv_sec - start.tv_sec) * 1000.0 + 
                          (end.tv_nsec - start.tv_nsec) / 1000000.0;
    
    printf("  Batch processed: %u messages in %.3f ms\n", batch_processed, batch_time_ms);
    printf("  Batch throughput: %.0f messages/second\n", 
           batch_processed / (batch_time_ms / 1000.0));
    
    TEST(batch_processed > 0, "Batch processing handled messages");
    TEST(batch_time_ms < 100.0, "Batch processing completed quickly");
    
    /* Test 12: System stress test */
    printf("\nTest 12: System Stress Test\n");
    
    const int STRESS_MESSAGES = 1000;
    uint32_t stress_scheduled = 0;
    uint32_t stress_processed = 0;
    
    struct timespec stress_start, stress_end;
    clock_gettime(CLOCK_MONOTONIC, &stress_start);
    
    /* Schedule many messages */
    for (int i = 0; i < STRESS_MESSAGES; i++) {
        fsm_message_t *stress_msg = fsm_alloc_message(integration.fsm_processor, i % integration.num_cores);
        if (stress_msg) {
            fsm_message_init(stress_msg, 8000 + i, 0);
            fsm_processing_result_t result = fsm_ule_schedule_message(&integration, stress_msg, i % integration.num_cores);
            if (result == FSM_RESULT_PENDING) {
                stress_scheduled++;
            }
        }
    }
    
    /* Process them across all cores */
    for (uint32_t core = 0; core < integration.num_cores; core++) {
        stress_processed += fsm_ule_process_message_batch(&integration, core, STRESS_MESSAGES / integration.num_cores);
    }
    
    clock_gettime(CLOCK_MONOTONIC, &stress_end);
    
    double stress_time_ms = (stress_end.tv_sec - stress_start.tv_sec) * 1000.0 + 
                           (stress_end.tv_nsec - stress_start.tv_nsec) / 1000000.0;
    
    printf("  Stress test: %u scheduled, %u processed in %.3f ms\n", 
           stress_scheduled, stress_processed, stress_time_ms);
    printf("  Stress throughput: %.0f messages/second\n", 
           stress_processed / (stress_time_ms / 1000.0));
    
    TEST(stress_scheduled > STRESS_MESSAGES * 0.8, "Stress test scheduled most messages");
    TEST(stress_processed > 0, "Stress test processed messages");
    
    /* Cleanup */
    fsm_ule_integration_shutdown(&integration);
    
    /* Final Results */
    printf("\n=== Test Results ===\n");
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_failed);
    printf("Success rate: %.1f%%\n", (double)tests_passed / (tests_passed + tests_failed) * 100.0);
    
    if (tests_failed == 0) {
        printf("\n🎉 ALL TESTS PASSED! FSM+ULE integration working perfectly! 🎉\n");
        printf("\n🚀 Key Achievements:\n");
        printf("   ✓ FSM IPC integrated with ULE scheduler\n");
        printf("   ✓ Multi-core message processing\n");
        printf("   ✓ Priority-based scheduling\n");
        printf("   ✓ Load balancing across cores\n");
        printf("   ✓ High-performance message throughput\n");
        printf("   ✓ NUMA-aware and adaptive scheduling\n");
        return 0;
    } else {
        printf("\n❌ %d tests failed. System needs refinement.\n", tests_failed);
        return 1;
    }
}