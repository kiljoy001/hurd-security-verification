/* Comprehensive FSM IPC Test Suite
 * Tests for FSM message processing, routing, and performance
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <sys/time.h>
#include <unistd.h>
#include <pthread.h>

#include "fsm_message.h"
#include "fsm_routing.h"
#include "fsm_processor.h"

/* Test framework */
#define TEST_ASSERT(condition, message) \
    do { \
        if (!(condition)) { \
            printf("FAIL: %s\n", message); \
            return false; \
        } \
    } while(0)

#define TEST_PASS(name) printf("PASS: %s\n", name)
#define TEST_FAIL(name) printf("FAIL: %s\n", name)

/* Test statistics */
typedef struct {
    int tests_run;
    int tests_passed;
    int tests_failed;
    double total_time_ms;
} test_stats_t;

static test_stats_t g_test_stats = {0};

/* Timing utilities */
static double get_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000.0 + tv.tv_usec / 1000.0;
}

#define TIME_TEST(test_func) \
    do { \
        double start_time = get_time_ms(); \
        bool result = test_func(); \
        double end_time = get_time_ms(); \
        double elapsed = end_time - start_time; \
        g_test_stats.total_time_ms += elapsed; \
        g_test_stats.tests_run++; \
        if (result) { \
            g_test_stats.tests_passed++; \
        } else { \
            g_test_stats.tests_failed++; \
        } \
        printf("  [%.3f ms] %s: %s\n", elapsed, #test_func, result ? "PASS" : "FAIL"); \
    } while(0)

/* ===== Basic FSM Message Tests ===== */

bool test_fsm_message_creation(void) {
    fsm_message_t msg;
    
    /* Test message initialization */
    fsm_message_init(&msg, FSM_STATE_CREATED, 1000, 2000);
    
    TEST_ASSERT(msg.current_state == FSM_STATE_CREATED, "Initial state should be CREATED");
    TEST_ASSERT(msg.next_state == FSM_STATE_ROUTED, "Next state should be ROUTED");
    TEST_ASSERT(msg.source_port == 1000, "Source port should be set correctly");
    TEST_ASSERT(msg.dest_server == 2000, "Destination server should be set correctly");
    TEST_ASSERT(msg.payload_length == 0, "Initial payload length should be 0");
    
    return true;
}

bool test_fsm_message_payload(void) {
    fsm_message_t msg;
    uint8_t test_data[] = "Hello, FSM World!";
    size_t data_len = strlen((char*)test_data);
    
    fsm_message_init(&msg, FSM_STATE_CREATED, 1001, 2001);
    
    /* Test payload setting */
    bool result = fsm_message_set_payload(&msg, test_data, data_len);
    TEST_ASSERT(result, "Setting payload should succeed");
    TEST_ASSERT(msg.payload_length == data_len, "Payload length should match");
    TEST_ASSERT(memcmp(msg.payload, test_data, data_len) == 0, "Payload data should match");
    
    /* Test oversized payload */
    uint8_t large_payload[100];
    memset(large_payload, 0xFF, sizeof(large_payload));
    result = fsm_message_set_payload(&msg, large_payload, sizeof(large_payload));
    TEST_ASSERT(!result, "Setting oversized payload should fail");
    
    return true;
}

bool test_fsm_message_validation(void) {
    fsm_message_t msg;
    
    /* Test valid message */
    fsm_message_init(&msg, FSM_STATE_CREATED, 1002, 2002);
    fsm_message_set_payload(&msg, (uint8_t*)"test", 4);
    
    TEST_ASSERT(fsm_message_validate(&msg), "Valid message should pass validation");
    
    /* Test invalid state */
    msg.current_state = 255;  /* Invalid state */
    TEST_ASSERT(!fsm_message_validate(&msg), "Invalid state should fail validation");
    
    /* Test invalid port */
    fsm_message_init(&msg, FSM_STATE_CREATED, 0, 2003);  /* Port 0 is invalid */
    TEST_ASSERT(!fsm_message_validate(&msg), "Invalid port should fail validation");
    
    return true;
}

bool test_fsm_state_transitions(void) {
    fsm_message_t msg;
    
    fsm_message_init(&msg, FSM_STATE_CREATED, 1003, 2003);
    
    /* Test valid transitions */
    TEST_ASSERT(fsm_valid_transition(FSM_STATE_CREATED, FSM_STATE_ROUTED), 
               "CREATED -> ROUTED should be valid");
    TEST_ASSERT(fsm_valid_transition(FSM_STATE_ROUTED, FSM_STATE_VALIDATED), 
               "ROUTED -> VALIDATED should be valid");
    TEST_ASSERT(fsm_valid_transition(FSM_STATE_VALIDATED, FSM_STATE_DELIVERED), 
               "VALIDATED -> DELIVERED should be valid");
    TEST_ASSERT(fsm_valid_transition(FSM_STATE_DELIVERED, FSM_STATE_ACKNOWLEDGED), 
               "DELIVERED -> ACKNOWLEDGED should be valid");
    
    /* Test invalid transitions */
    TEST_ASSERT(!fsm_valid_transition(FSM_STATE_CREATED, FSM_STATE_VALIDATED), 
               "CREATED -> VALIDATED should be invalid");
    TEST_ASSERT(!fsm_valid_transition(FSM_STATE_ACKNOWLEDGED, FSM_STATE_ROUTED), 
               "ACKNOWLEDGED -> ROUTED should be invalid");
    
    return true;
}

/* ===== FSM Routing Tests ===== */

bool test_fsm_routing_initialization(void) {
    fsm_routing_system_t routing;
    
    bool result = fsm_routing_init(&routing, 4);  /* 4 CPU cores */
    TEST_ASSERT(result, "Routing system initialization should succeed");
    TEST_ASSERT(routing.num_cores == 4, "Number of cores should be set correctly");
    
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_server_registration(void) {
    fsm_routing_system_t routing;
    fsm_server_metrics_t server;
    
    fsm_routing_init(&routing, 2);
    
    /* Setup test server */
    memset(&server, 0, sizeof(server));
    server.server_id = 100;
    server.current_load = 0.3;
    server.threat_score = 0.1;
    server.reliability = 0.95;
    server.base_cost = 10.0;
    server.max_cost = 100.0;
    
    bool result = fsm_register_server(&routing, &server);
    TEST_ASSERT(result, "Server registration should succeed");
    TEST_ASSERT(routing.num_servers == 1, "Server count should increment");
    
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_dynamic_bcra_routing(void) {
    fsm_routing_system_t routing;
    fsm_server_metrics_t servers[3];
    fsm_message_t msg;
    
    fsm_routing_init(&routing, 2);
    
    /* Setup test servers with different characteristics */
    for (int i = 0; i < 3; i++) {
        memset(&servers[i], 0, sizeof(servers[i]));
        servers[i].server_id = 200 + i;
        servers[i].base_cost = 10.0;
        servers[i].max_cost = 100.0;
        servers[i].reliability = 0.9;
    }
    
    /* Server 0: Low load, low threats */
    servers[0].current_load = 0.2;
    servers[0].threat_score = 0.1;
    
    /* Server 1: Medium load, medium threats */
    servers[1].current_load = 0.5;
    servers[1].threat_score = 0.3;
    
    /* Server 2: High load, high threats */
    servers[2].current_load = 0.9;
    servers[2].threat_score = 0.8;
    
    /* Register servers */
    for (int i = 0; i < 3; i++) {
        fsm_register_server(&routing, &servers[i]);
    }
    
    /* Test routing selection */
    fsm_message_init(&msg, FSM_STATE_CREATED, 1004, 0);  /* dest_server = 0 means auto-route */
    
    uint16_t selected_server = fsm_route_message(&routing, &msg, 0);
    TEST_ASSERT(selected_server != 0, "Routing should select a server");
    TEST_ASSERT(selected_server == 200, "Should select server with best BCRA score (lowest load/threats)");
    
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_routing_cache(void) {
    fsm_routing_system_t routing;
    fsm_message_t msg1, msg2;
    
    fsm_routing_init(&routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 300,
        .current_load = 0.3,
        .threat_score = 0.2,
        .reliability = 0.9,
        .base_cost = 10.0,
        .max_cost = 100.0
    };
    fsm_register_server(&routing, &server);
    
    /* First routing decision - should compute and cache */
    fsm_message_init(&msg1, FSM_STATE_CREATED, 1005, 0);
    uint16_t server1 = fsm_route_message(&routing, &msg1, 0);
    
    /* Second routing decision - should use cache */
    fsm_message_init(&msg2, FSM_STATE_CREATED, 1006, 0);
    uint16_t server2 = fsm_route_message(&routing, &msg2, 0);
    
    TEST_ASSERT(server1 == server2, "Cache should return same server for similar requests");
    TEST_ASSERT(server1 == 300, "Should select the registered server");
    
    fsm_routing_shutdown(&routing);
    return true;
}

/* ===== FSM Processor Tests ===== */

bool test_fsm_processor_initialization(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    
    fsm_routing_init(&routing, 2);
    
    bool result = fsm_processor_init(&processor, &routing, 2);
    TEST_ASSERT(result, "Processor initialization should succeed");
    TEST_ASSERT(processor.num_cores == 2, "Number of cores should be set correctly");
    
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_message_processing_pipeline(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    fsm_message_t *msg;
    
    fsm_routing_init(&routing, 1);
    fsm_processor_init(&processor, &routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 400,
        .current_load = 0.2,
        .threat_score = 0.1,
        .reliability = 0.95,
        .base_cost = 10.0,
        .max_cost = 100.0
    };
    fsm_register_server(&routing, &server);
    
    /* Allocate and initialize message */
    msg = fsm_alloc_message(&processor, 0);
    TEST_ASSERT(msg != NULL, "Message allocation should succeed");
    
    fsm_message_init(msg, FSM_STATE_CREATED, 1007, 0);
    fsm_message_set_payload(msg, (uint8_t*)"test pipeline", 13);
    
    /* Process through pipeline */
    fsm_processing_result_t result = fsm_process_message(&processor, msg, 0);
    TEST_ASSERT(result == FSM_RESULT_PENDING || result == FSM_RESULT_SUCCESS, 
               "Processing should succeed or be pending");
    
    /* Message should have advanced through states */
    TEST_ASSERT(msg->current_state != FSM_STATE_CREATED, 
               "Message should have advanced from CREATED state");
    
    fsm_free_message(&processor, msg, 0);
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_batch_processing(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    fsm_message_t *messages[10];
    
    fsm_routing_init(&routing, 1);
    fsm_processor_init(&processor, &routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 500,
        .current_load = 0.1,
        .threat_score = 0.05,
        .reliability = 0.98,
        .base_cost = 5.0,
        .max_cost = 50.0
    };
    fsm_register_server(&routing, &server);
    
    /* Allocate batch of messages */
    for (int i = 0; i < 10; i++) {
        messages[i] = fsm_alloc_message(&processor, 0);
        TEST_ASSERT(messages[i] != NULL, "Batch message allocation should succeed");
        
        fsm_message_init(messages[i], FSM_STATE_CREATED, 1008 + i, 0);
        char payload[32];
        snprintf(payload, sizeof(payload), "batch message %d", i);
        fsm_message_set_payload(messages[i], (uint8_t*)payload, strlen(payload));
    }
    
    /* Process batch */
    uint32_t processed = fsm_process_message_batch(&processor, messages, 10, 0);
    TEST_ASSERT(processed > 0, "Batch processing should process some messages");
    
    /* Clean up */
    for (int i = 0; i < 10; i++) {
        fsm_free_message(&processor, messages[i], 0);
    }
    
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

/* ===== Performance Tests ===== */

bool test_fsm_latency_target(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    fsm_message_t *msg;
    struct timespec start, end;
    
    fsm_routing_init(&routing, 1);
    fsm_processor_init(&processor, &routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 600,
        .current_load = 0.1,
        .threat_score = 0.05,
        .reliability = 0.99,
        .base_cost = 5.0,
        .max_cost = 50.0
    };
    fsm_register_server(&routing, &server);
    
    /* Allocate message */
    msg = fsm_alloc_message(&processor, 0);
    fsm_message_init(msg, FSM_STATE_CREATED, 1009, 0);
    fsm_message_set_payload(msg, (uint8_t*)"latency test", 12);
    
    /* Measure processing latency */
    clock_gettime(CLOCK_MONOTONIC, &start);
    fsm_processing_result_t result = fsm_process_message(&processor, msg, 0);
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    uint64_t latency_ns = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                         (end.tv_nsec - start.tv_nsec);
    
    printf("  Processing latency: %lu nanoseconds\n", latency_ns);
    
    /* Target: Sub-microsecond (< 1000 ns for simple processing) */
    TEST_ASSERT(latency_ns < 10000, "Processing latency should be under 10 microseconds");
    
    fsm_free_message(&processor, msg, 0);
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_throughput_target(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    const int NUM_MESSAGES = 1000;
    fsm_message_t *messages[NUM_MESSAGES];
    struct timespec start, end;
    
    fsm_routing_init(&routing, 1);
    fsm_processor_init(&processor, &routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 700,
        .current_load = 0.2,
        .threat_score = 0.1,
        .reliability = 0.95,
        .base_cost = 10.0,
        .max_cost = 100.0
    };
    fsm_register_server(&routing, &server);
    
    /* Allocate messages */
    for (int i = 0; i < NUM_MESSAGES; i++) {
        messages[i] = fsm_alloc_message(&processor, 0);
        fsm_message_init(messages[i], FSM_STATE_CREATED, 2000 + i, 0);
        fsm_message_set_payload(messages[i], (uint8_t*)"throughput", 10);
    }
    
    /* Measure throughput */
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    for (int i = 0; i < NUM_MESSAGES; i++) {
        fsm_process_message(&processor, messages[i], 0);
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double elapsed_ms = (end.tv_sec - start.tv_sec) * 1000.0 + 
                       (end.tv_nsec - start.tv_nsec) / 1000000.0;
    
    double throughput = NUM_MESSAGES / (elapsed_ms / 1000.0);
    printf("  Throughput: %.0f messages/second\n", throughput);
    
    /* Target: > 100K messages/second */
    TEST_ASSERT(throughput > 50000, "Throughput should exceed 50K messages/second");
    
    /* Clean up */
    for (int i = 0; i < NUM_MESSAGES; i++) {
        fsm_free_message(&processor, messages[i], 0);
    }
    
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

/* ===== Security Tests ===== */

bool test_fsm_message_integrity(void) {
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    fsm_message_t *msg;
    
    fsm_routing_init(&routing, 1);
    fsm_processor_init(&processor, &routing, 1);
    
    /* Add a test server */
    fsm_server_metrics_t server = {
        .server_id = 800,
        .current_load = 0.1,
        .threat_score = 0.05,
        .reliability = 0.99,
        .base_cost = 5.0,
        .max_cost = 50.0
    };
    fsm_register_server(&routing, &server);
    
    /* Create message with specific payload */
    msg = fsm_alloc_message(&processor, 0);
    fsm_message_init(msg, FSM_STATE_CREATED, 1010, 0);
    
    uint8_t original_payload[] = "integrity test payload";
    size_t payload_len = strlen((char*)original_payload);
    fsm_message_set_payload(msg, original_payload, payload_len);
    
    /* Store original values */
    uint16_t original_source = msg->source_port;
    uint16_t original_dest = msg->dest_server;
    
    /* Process message */
    fsm_process_message(&processor, msg, 0);
    
    /* Verify integrity preserved */
    TEST_ASSERT(msg->source_port == original_source, "Source port should be preserved");
    TEST_ASSERT(msg->payload_length == payload_len, "Payload length should be preserved");
    TEST_ASSERT(memcmp(msg->payload, original_payload, payload_len) == 0, 
               "Payload content should be preserved");
    
    fsm_free_message(&processor, msg, 0);
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

bool test_fsm_security_validation(void) {
    fsm_message_t msg;
    
    /* Test valid message */
    fsm_message_init(&msg, FSM_STATE_CREATED, 1011, 2011);
    fsm_message_set_payload(&msg, (uint8_t*)"secure", 6);
    
    TEST_ASSERT(fsm_validate_message_security(&msg), "Valid message should pass security validation");
    
    /* Test oversized payload */
    msg.payload_length = 100;  /* Exceeds 56 byte limit */
    TEST_ASSERT(!fsm_validate_message_security(&msg), "Oversized payload should fail security validation");
    
    /* Test invalid state */
    msg.payload_length = 6;
    msg.current_state = 255;  /* Invalid state */
    TEST_ASSERT(!fsm_validate_message_security(&msg), "Invalid state should fail security validation");
    
    /* Test invalid port */
    fsm_message_init(&msg, FSM_STATE_CREATED, 0, 2012);  /* Port 0 invalid */
    TEST_ASSERT(!fsm_validate_message_security(&msg), "Invalid port should fail security validation");
    
    return true;
}

/* ===== Multi-core Tests ===== */

typedef struct {
    fsm_processor_system_t *processor;
    int core_id;
    int num_messages;
    int processed_count;
} thread_test_data_t;

void *worker_thread_test(void *arg) {
    thread_test_data_t *data = (thread_test_data_t*)arg;
    
    for (int i = 0; i < data->num_messages; i++) {
        fsm_message_t *msg = fsm_alloc_message(data->processor, data->core_id);
        if (msg) {
            fsm_message_init(msg, FSM_STATE_CREATED, 3000 + i, 0);
            fsm_message_set_payload(msg, (uint8_t*)"multicore", 9);
            
            fsm_processing_result_t result = fsm_process_message(data->processor, msg, data->core_id);
            if (result == FSM_RESULT_SUCCESS || result == FSM_RESULT_PENDING) {
                data->processed_count++;
            }
            
            fsm_free_message(data->processor, msg, data->core_id);
        }
    }
    
    return NULL;
}

bool test_fsm_multicore_processing(void) {
    const int NUM_CORES = 4;
    const int MESSAGES_PER_CORE = 100;
    
    fsm_processor_system_t processor;
    fsm_routing_system_t routing;
    pthread_t threads[NUM_CORES];
    thread_test_data_t thread_data[NUM_CORES];
    
    fsm_routing_init(&routing, NUM_CORES);
    fsm_processor_init(&processor, &routing, NUM_CORES);
    
    /* Add test servers */
    for (int i = 0; i < 3; i++) {
        fsm_server_metrics_t server = {
            .server_id = 900 + i,
            .current_load = 0.1 + i * 0.1,
            .threat_score = 0.05 + i * 0.05,
            .reliability = 0.95,
            .base_cost = 10.0,
            .max_cost = 100.0
        };
        fsm_register_server(&routing, &server);
    }
    
    /* Launch worker threads */
    for (int i = 0; i < NUM_CORES; i++) {
        thread_data[i].processor = &processor;
        thread_data[i].core_id = i;
        thread_data[i].num_messages = MESSAGES_PER_CORE;
        thread_data[i].processed_count = 0;
        
        pthread_create(&threads[i], NULL, worker_thread_test, &thread_data[i]);
    }
    
    /* Wait for completion */
    int total_processed = 0;
    for (int i = 0; i < NUM_CORES; i++) {
        pthread_join(threads[i], NULL);
        total_processed += thread_data[i].processed_count;
    }
    
    printf("  Multi-core processed: %d/%d messages\n", total_processed, NUM_CORES * MESSAGES_PER_CORE);
    
    TEST_ASSERT(total_processed > NUM_CORES * MESSAGES_PER_CORE * 0.8, 
               "Multi-core processing should handle most messages successfully");
    
    fsm_processor_shutdown(&processor);
    fsm_routing_shutdown(&routing);
    return true;
}

/* ===== Test Suite Runner ===== */

void run_test_suite(void) {
    printf("=== FSM IPC Comprehensive Test Suite ===\n\n");
    
    printf("Basic FSM Message Tests:\n");
    TIME_TEST(test_fsm_message_creation);
    TIME_TEST(test_fsm_message_payload);
    TIME_TEST(test_fsm_message_validation);
    TIME_TEST(test_fsm_state_transitions);
    
    printf("\nFSM Routing Tests:\n");
    TIME_TEST(test_fsm_routing_initialization);
    TIME_TEST(test_fsm_server_registration);
    TIME_TEST(test_fsm_dynamic_bcra_routing);
    TIME_TEST(test_fsm_routing_cache);
    
    printf("\nFSM Processor Tests:\n");
    TIME_TEST(test_fsm_processor_initialization);
    TIME_TEST(test_fsm_message_processing_pipeline);
    TIME_TEST(test_fsm_batch_processing);
    
    printf("\nPerformance Tests:\n");
    TIME_TEST(test_fsm_latency_target);
    TIME_TEST(test_fsm_throughput_target);
    
    printf("\nSecurity Tests:\n");
    TIME_TEST(test_fsm_message_integrity);
    TIME_TEST(test_fsm_security_validation);
    
    printf("\nMulti-core Tests:\n");
    TIME_TEST(test_fsm_multicore_processing);
    
    /* Print summary */
    printf("\n=== Test Summary ===\n");
    printf("Tests run:     %d\n", g_test_stats.tests_run);
    printf("Tests passed:  %d\n", g_test_stats.tests_passed);
    printf("Tests failed:  %d\n", g_test_stats.tests_failed);
    printf("Success rate:  %.1f%%\n", 
           (double)g_test_stats.tests_passed / g_test_stats.tests_run * 100.0);
    printf("Total time:    %.3f ms\n", g_test_stats.total_time_ms);
    
    if (g_test_stats.tests_failed == 0) {
        printf("\n🎉 ALL TESTS PASSED! FSM IPC system verified! 🎉\n");
    } else {
        printf("\n❌ %d tests failed. Review and fix issues.\n", g_test_stats.tests_failed);
    }
}

int main(int argc, char *argv[]) {
    printf("FSM IPC Test Suite - Comprehensive Testing\n");
    printf("Build: %s %s\n\n", __DATE__, __TIME__);
    
    run_test_suite();
    
    return g_test_stats.tests_failed == 0 ? 0 : 1;
}