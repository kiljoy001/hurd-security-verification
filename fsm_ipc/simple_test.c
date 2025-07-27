/* Simple FSM IPC Test
 * Basic functionality test that matches actual implementation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "fsm_message.h"
#include "fsm_routing.h"
#include "fsm_processor.h"

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

int main(void) {
    printf("=== Simple FSM IPC Test ===\n\n");
    
    /* Test 1: Basic message creation and initialization */
    printf("Test 1: Message Creation\n");
    fsm_message_t msg;
    fsm_message_init(&msg, 1000, 2000);
    
    TEST(msg.current_state == FSM_STATE_CREATED, "Message initialized with CREATED state");
    TEST(msg.next_state == FSM_STATE_ROUTED, "Next state set to ROUTED");
    TEST(msg.source_port == 1000, "Source port set correctly");
    TEST(msg.dest_server == 2000, "Destination server set correctly");
    TEST(msg.payload_length == 0, "Initial payload length is 0");
    
    /* Test 2: Payload handling */
    printf("\nTest 2: Payload Handling\n");
    const char *test_payload = "Hello FSM!";
    bool result = fsm_message_set_payload(&msg, test_payload, strlen(test_payload));
    
    TEST(result == true, "Payload set successfully");
    TEST(msg.payload_length == strlen(test_payload), "Payload length matches");
    TEST(memcmp(msg.payload, test_payload, strlen(test_payload)) == 0, "Payload data matches");
    
    /* Test oversized payload */
    uint8_t large_payload[100];
    memset(large_payload, 0xFF, sizeof(large_payload));
    result = fsm_message_set_payload(&msg, large_payload, sizeof(large_payload));
    TEST(result == false, "Oversized payload rejected");
    
    /* Test 3: Message validation */
    printf("\nTest 3: Message Validation\n");
    TEST(fsm_message_validate(&msg), "Valid message passes validation");
    
    /* Test invalid message */
    fsm_message_t invalid_msg = msg;
    invalid_msg.current_state = 255;  /* Invalid state */
    TEST(!fsm_message_validate(&invalid_msg), "Invalid state fails validation");
    
    /* Test 4: State transitions */
    printf("\nTest 4: State Transitions\n");
    TEST(fsm_valid_transition(FSM_STATE_CREATED, FSM_STATE_ROUTED), 
         "CREATED → ROUTED is valid");
    TEST(fsm_valid_transition(FSM_STATE_ROUTED, FSM_STATE_VALIDATED), 
         "ROUTED → VALIDATED is valid");
    TEST(fsm_valid_transition(FSM_STATE_VALIDATED, FSM_STATE_DELIVERED), 
         "VALIDATED → DELIVERED is valid");
    TEST(fsm_valid_transition(FSM_STATE_DELIVERED, FSM_STATE_ACKNOWLEDGED), 
         "DELIVERED → ACKNOWLEDGED is valid");
    
    /* Test invalid transitions */
    TEST(!fsm_valid_transition(FSM_STATE_CREATED, FSM_STATE_VALIDATED), 
         "CREATED → VALIDATED is invalid");
    TEST(!fsm_valid_transition(FSM_STATE_ACKNOWLEDGED, FSM_STATE_ROUTED), 
         "ACKNOWLEDGED → ROUTED is invalid");
    
    /* Test 5: Routing system basic initialization */
    printf("\nTest 5: Routing System\n");
    fsm_routing_system_t routing;
    result = fsm_routing_init(&routing);
    TEST(result == true, "Routing system initializes successfully");
    
    /* Test server registration */
    result = fsm_routing_register_server(&routing, 100, FSM_SERVER_PROCESS, 0);
    TEST(result == true, "Server registration succeeds");
    
    /* Test 6: Processor system basic initialization */
    printf("\nTest 6: Processor System\n");
    fsm_processor_system_t processor;
    result = fsm_processor_init(&processor, &routing, 1);
    TEST(result == true, "Processor system initializes successfully");
    TEST(processor.num_cores == 1, "Number of cores set correctly");
    
    /* Test message allocation from processor */
    fsm_message_t *allocated_msg = fsm_alloc_message(&processor, 0);
    TEST(allocated_msg != NULL, "Message allocation succeeds");
    
    if (allocated_msg) {
        fsm_message_init(allocated_msg, 1001, 0);  /* Auto-route destination */
        fsm_message_set_payload(allocated_msg, "test", 4);
        
        TEST(allocated_msg->current_state == FSM_STATE_CREATED, 
             "Allocated message initialized correctly");
        
        /* Test 7: Basic message processing */
        printf("\nTest 7: Message Processing\n");
        fsm_processing_result_t proc_result = fsm_process_message(&processor, allocated_msg, 0);
        TEST(proc_result != FSM_RESULT_ERROR, "Message processing succeeds");
        TEST(allocated_msg->current_state != FSM_STATE_CREATED, 
             "Message state advances from CREATED");
        
        /* Free the message */
        fsm_free_message(&processor, allocated_msg, 0);
    }
    
    /* Test 8: Performance timing */
    printf("\nTest 8: Performance Timing\n");
    struct timespec start, end;
    
    /* Allocate and process a batch of messages to test performance */
    const int NUM_MESSAGES = 1000;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    for (int i = 0; i < NUM_MESSAGES; i++) {
        fsm_message_t *perf_msg = fsm_alloc_message(&processor, 0);
        if (perf_msg) {
            fsm_message_init(perf_msg, 2000 + i, 0);
            fsm_process_message(&processor, perf_msg, 0);
            fsm_free_message(&processor, perf_msg, 0);
        }
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double elapsed_ms = (end.tv_sec - start.tv_sec) * 1000.0 + 
                       (end.tv_nsec - start.tv_nsec) / 1000000.0;
    double avg_latency_us = (elapsed_ms * 1000.0) / NUM_MESSAGES;
    double throughput = NUM_MESSAGES / (elapsed_ms / 1000.0);
    
    printf("  Processed %d messages in %.3f ms\n", NUM_MESSAGES, elapsed_ms);
    printf("  Average latency: %.3f μs per message\n", avg_latency_us);
    printf("  Throughput: %.0f messages/second\n", throughput);
    
    TEST(avg_latency_us < 100.0, "Average latency under 100 μs");
    TEST(throughput > 1000.0, "Throughput over 1K messages/second");
    
    /* Cleanup */
    fsm_processor_shutdown(&processor);
    
    /* Test 9: Memory safety check */
    printf("\nTest 9: Memory Safety\n");
    
    /* Test NULL pointer handling */
    TEST(!fsm_message_validate(NULL), "NULL message validation fails safely");
    
    fsm_message_t null_test;
    fsm_message_init(&null_test, 0, 0);  /* Port 0 should be invalid */
    TEST(!fsm_message_validate(&null_test), "Invalid port 0 fails validation");
    
    /* Test boundary conditions */
    fsm_message_t boundary_test;
    fsm_message_init(&boundary_test, 1, 1);
    uint8_t max_payload[56];
    memset(max_payload, 0xAA, sizeof(max_payload));
    
    result = fsm_message_set_payload(&boundary_test, max_payload, 56);
    TEST(result == true, "Maximum payload size (56 bytes) accepted");
    TEST(fsm_message_validate(&boundary_test), "Message with max payload validates");
    
    result = fsm_message_set_payload(&boundary_test, max_payload, 57);
    TEST(result == false, "Payload size 57 bytes rejected");
    
    /* Final Results */
    printf("\n=== Test Results ===\n");
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_failed);
    printf("Success rate: %.1f%%\n", (double)tests_passed / (tests_passed + tests_failed) * 100.0);
    
    if (tests_failed == 0) {
        printf("\n🎉 ALL TESTS PASSED! FSM IPC system working correctly! 🎉\n");
        return 0;
    } else {
        printf("\n❌ %d tests failed. System needs debugging.\n", tests_failed);
        return 1;
    }
}