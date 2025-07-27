/* GNU Hurd ULE+FSM Integration Stress Test
 * Comprehensive stress testing of ULE scheduler with FSM IPC integration
 * Tests message routing, state transitions, and scheduler coordination under load
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/sysinfo.h>
#include <sched.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <errno.h>
#include <signal.h>

/* Test configuration */
#define MAX_INTEGRATION_THREADS 128
#define MAX_FSM_MESSAGES 50000
#define TEST_DURATION_SECONDS 180
#define MESSAGE_BURST_SIZE 100
#define INTEGRATION_CHECK_INTERVAL 10

/* FSM States - matching formal verification */
typedef enum {
    FSM_CREATED = 1,
    FSM_ROUTED = 2,
    FSM_PROCESSED = 3
} fsm_state_t;

/* ULE Message Classes - matching formal verification */
typedef enum {
    ULE_MSG_INTERRUPT = 0,
    ULE_MSG_REALTIME = 1,
    ULE_MSG_INTERACTIVE = 2,
    ULE_MSG_BATCH = 3,
    ULE_MSG_IDLE = 4
} ule_msg_class_t;

/* ULE Server Types */
typedef enum {
    ULE_SERVER_FILESYSTEM = 0,
    ULE_SERVER_NETWORK = 1,
    ULE_SERVER_PROCESS = 2,
    ULE_SERVER_MEMORY = 3,
    ULE_SERVER_DEVICE = 4,
    ULE_SERVER_GUI = 5,
    ULE_SERVER_AUDIO = 6
} ule_server_type_t;

/* Integrated ULE+FSM message structure */
typedef struct {
    /* FSM fields */
    fsm_state_t fsm_current_state;
    fsm_state_t fsm_next_state;
    uint32_t fsm_source_port;
    uint32_t fsm_dest_server;
    uint32_t fsm_payload_length;
    uint8_t fsm_payload_valid;
    
    /* ULE fields */
    uint32_t ule_msg_id;
    uint32_t ule_sender_id;
    ule_server_type_t ule_target_service;
    ule_msg_class_t ule_msg_class;
    uint32_t ule_sleep_time;
    uint32_t ule_run_time;
    uint32_t ule_arrival_time;
    uint32_t ule_priority;
    
    /* Integration metadata */
    double creation_time_us;
    double processing_start_time_us;
    double processing_end_time_us;
    uint32_t cpu_affinity;
    uint8_t integration_valid;
} ule_fsm_message_t;

/* Integration stress test statistics */
typedef struct {
    uint64_t messages_created;
    uint64_t messages_processed;
    uint64_t messages_failed;
    uint64_t state_transitions;
    uint64_t interactivity_calculations;
    uint64_t routing_decisions;
    uint64_t integration_violations;
    uint64_t performance_violations;
    uint64_t scheduler_preemptions;
    uint64_t message_queue_overflows;
    
    double total_processing_time_us;
    double max_processing_time_us;
    double min_processing_time_us;
    double avg_message_latency_us;
    double max_message_latency_us;
    
    uint64_t interactive_messages;
    uint64_t batch_messages;
    uint64_t realtime_messages;
    uint64_t idle_messages;
    
    double start_time;
    double end_time;
} integration_stress_stats_t;

/* Thread context for integration testing */
typedef struct {
    uint32_t thread_id;
    uint32_t cpu_id;
    uint32_t thread_type; /* 0=producer, 1=consumer, 2=monitor */
    integration_stress_stats_t *shared_stats;
    pthread_mutex_t *stats_mutex;
    volatile int *test_running;
    
    /* Message queue */
    ule_fsm_message_t *message_queue;
    uint32_t queue_size;
    volatile uint32_t queue_head;
    volatile uint32_t queue_tail;
    pthread_mutex_t queue_mutex;
    
    /* Thread-specific stats */
    uint64_t thread_messages_processed;
    uint64_t thread_integration_errors;
    double thread_total_latency;
} integration_thread_context_t;

static integration_stress_stats_t global_stats = {0};
static pthread_mutex_t stats_mutex = PTHREAD_MUTEX_INITIALIZER;
static volatile int test_running = 1;

/* Message queue for cross-thread communication */
static ule_fsm_message_t shared_message_queue[MAX_FSM_MESSAGES];
static volatile uint32_t shared_queue_head = 0;
static volatile uint32_t shared_queue_tail = 0;
static pthread_mutex_t shared_queue_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Get current time in microseconds */
static double get_current_time_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000000.0 + tv.tv_usec;
}

/* ULE Interactivity Calculation - exactly matching Coq formal verification */
uint32_t ule_calculate_interactivity(uint32_t sleep_time, uint32_t run_time) {
    if (run_time > 0) {
        if (sleep_time <= run_time) {
            uint32_t result = 50 + (run_time * 50) / (sleep_time + 1);
            return (result > 100) ? 100 : result;
        } else {
            uint32_t result = (sleep_time * 50) / (run_time + 1);
            return (result > 100) ? 100 : result;
        }
    }
    return 0;
}

/* FSM Message Validation - exactly matching Coq formal verification */
uint8_t fsm_message_validate(const ule_fsm_message_t *msg) {
    return ((msg->fsm_current_state >= FSM_CREATED && msg->fsm_current_state <= FSM_PROCESSED) &&
            (msg->fsm_next_state >= FSM_CREATED && msg->fsm_next_state <= FSM_PROCESSED) &&
            (msg->fsm_source_port < 65536) &&
            (msg->fsm_dest_server < 65536) &&
            (msg->fsm_payload_length <= 56) &&
            (msg->fsm_payload_valid == 1));
}

/* FSM to ULE Message Class Mapping - exactly matching Coq formal verification */
ule_msg_class_t fsm_to_ule_msg_class(fsm_state_t state) {
    switch (state) {
        case FSM_CREATED: return ULE_MSG_INTERACTIVE;
        case FSM_ROUTED: return ULE_MSG_BATCH;
        case FSM_PROCESSED: return ULE_MSG_REALTIME;
        default: return ULE_MSG_IDLE;
    }
}

/* Create integrated ULE+FSM message */
static void create_ule_fsm_message(ule_fsm_message_t *msg, uint32_t msg_id, uint32_t thread_id) {
    /* Generate FSM component */
    msg->fsm_current_state = (rand() % 3) + 1; /* 1-3 */
    msg->fsm_next_state = (msg->fsm_current_state % 3) + 1;
    msg->fsm_source_port = 1000 + (rand() % 8000);
    msg->fsm_dest_server = 2000 + (rand() % 5000);
    msg->fsm_payload_length = 16 + (rand() % 41); /* 16-56 bytes */
    msg->fsm_payload_valid = 1;
    
    /* Generate ULE component */
    msg->ule_msg_id = msg_id;
    msg->ule_sender_id = msg->fsm_source_port;
    msg->ule_target_service = (msg->fsm_dest_server < 3000) ? ULE_SERVER_FILESYSTEM :
                             (msg->fsm_dest_server < 4000) ? ULE_SERVER_NETWORK :
                             (msg->fsm_dest_server < 5000) ? ULE_SERVER_PROCESS :
                             ULE_SERVER_DEVICE;
    msg->ule_sleep_time = 5 + (rand() % 25);
    msg->ule_run_time = 3 + (rand() % 15);
    msg->ule_arrival_time = (uint32_t)(get_current_time_us() / 1000);
    
    /* Calculate ULE interactivity and map FSM state */
    uint32_t interactivity = ule_calculate_interactivity(msg->ule_sleep_time, msg->ule_run_time);
    msg->ule_msg_class = fsm_to_ule_msg_class(msg->fsm_current_state);
    
    /* Set priority based on message class */
    switch (msg->ule_msg_class) {
        case ULE_MSG_INTERRUPT:
        case ULE_MSG_REALTIME:
            msg->ule_priority = 0; /* Highest */
            break;
        case ULE_MSG_INTERACTIVE:
            msg->ule_priority = 1;
            break;
        case ULE_MSG_BATCH:
            msg->ule_priority = 2;
            break;
        case ULE_MSG_IDLE:
            msg->ule_priority = 3; /* Lowest */
            break;
    }
    
    /* Integration metadata */
    msg->creation_time_us = get_current_time_us();
    msg->processing_start_time_us = 0;
    msg->processing_end_time_us = 0;
    msg->cpu_affinity = thread_id % get_nprocs();
    msg->integration_valid = 1;
}

/* Validate ULE+FSM integration - matching Coq theorems */
static uint8_t validate_ule_fsm_integration(const ule_fsm_message_t *msg) {
    /* Check FSM validation */
    if (!fsm_message_validate(msg)) {
        return 0;
    }
    
    /* Check ULE interactivity bounds */
    uint32_t calculated_interactivity = ule_calculate_interactivity(msg->ule_sleep_time, msg->ule_run_time);
    if (calculated_interactivity > 100) {
        return 0;
    }
    
    /* Check integration correspondence */
    if (msg->ule_sender_id != msg->fsm_source_port) {
        return 0;
    }
    
    /* Check message class correspondence */
    ule_msg_class_t expected_class = fsm_to_ule_msg_class(msg->fsm_current_state);
    if (msg->ule_msg_class != expected_class) {
        return 0;
    }
    
    return 1;
}

/* Process ULE+FSM message with scheduler integration */
static double process_ule_fsm_message(ule_fsm_message_t *msg, uint32_t processor_id) {
    double start_time = get_current_time_us();
    msg->processing_start_time_us = start_time;
    
    /* Validate integration */
    if (!validate_ule_fsm_integration(msg)) {
        msg->integration_valid = 0;
        return 0;
    }
    
    /* Simulate ULE scheduler decision making */
    uint32_t interactivity = ule_calculate_interactivity(msg->ule_sleep_time, msg->ule_run_time);
    
    /* Simulate processing time based on message class and scheduler priority */
    uint32_t processing_units = 0;
    switch (msg->ule_msg_class) {
        case ULE_MSG_INTERRUPT:
        case ULE_MSG_REALTIME:
            processing_units = 10 + (rand() % 20); /* Fast processing */
            break;
        case ULE_MSG_INTERACTIVE:
            processing_units = 20 + (rand() % 30); /* Medium processing */
            break;
        case ULE_MSG_BATCH:
            processing_units = 50 + (rand() % 100); /* Slower processing */
            break;
        case ULE_MSG_IDLE:
            processing_units = 100 + (rand() % 200); /* Slowest processing */
            break;
    }
    
    /* Simulate actual work with scheduler interaction */
    volatile double work_result = 0;
    for (uint32_t i = 0; i < processing_units * 100; i++) {
        work_result += sqrt(i * msg->ule_msg_id) * cos(i * 0.001);
        
        /* Periodic scheduler yield to test preemption */
        if (i % 1000 == 0) {
            sched_yield();
        }
    }
    
    /* Simulate FSM state transition */
    msg->fsm_current_state = msg->fsm_next_state;
    if (msg->fsm_current_state == FSM_PROCESSED) {
        msg->fsm_next_state = FSM_CREATED; /* Cycle back */
    } else {
        msg->fsm_next_state = (fsm_state_t)(msg->fsm_current_state + 1);
    }
    
    double end_time = get_current_time_us();
    msg->processing_end_time_us = end_time;
    
    /* Prevent optimization */
    (void)work_result;
    
    return end_time - start_time;
}

/* Message producer thread */
void* message_producer(void* arg) {
    integration_thread_context_t *ctx = (integration_thread_context_t*)arg;
    
    printf("Producer %u: Starting message generation on CPU %u\n", 
           ctx->thread_id, ctx->cpu_id);
    
    /* Set CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->cpu_id, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    uint32_t messages_created = 0;
    
    while (*ctx->test_running) {
        /* Create burst of messages */
        for (int burst = 0; burst < MESSAGE_BURST_SIZE && *ctx->test_running; burst++) {
            ule_fsm_message_t msg;
            create_ule_fsm_message(&msg, messages_created + ctx->thread_id * 100000, ctx->thread_id);
            
            /* Add to shared queue */
            pthread_mutex_lock(&shared_queue_mutex);
            uint32_t next_tail = (shared_queue_tail + 1) % MAX_FSM_MESSAGES;
            if (next_tail != shared_queue_head) {
                shared_message_queue[shared_queue_tail] = msg;
                shared_queue_tail = next_tail;
                
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->messages_created++;
                
                /* Update message class statistics */
                switch (msg.ule_msg_class) {
                    case ULE_MSG_INTERACTIVE:
                        ctx->shared_stats->interactive_messages++;
                        break;
                    case ULE_MSG_BATCH:
                        ctx->shared_stats->batch_messages++;
                        break;
                    case ULE_MSG_REALTIME:
                        ctx->shared_stats->realtime_messages++;
                        break;
                    case ULE_MSG_IDLE:
                        ctx->shared_stats->idle_messages++;
                        break;
                    default:
                        break;
                }
                pthread_mutex_unlock(ctx->stats_mutex);
                
                messages_created++;
            } else {
                /* Queue overflow */
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->message_queue_overflows++;
                pthread_mutex_unlock(ctx->stats_mutex);
            }
            pthread_mutex_unlock(&shared_queue_mutex);
        }
        
        /* Variable rate production to test different load conditions */
        if (messages_created % 1000 < 500) {
            /* High rate period */
            usleep(100 + rand() % 500);
        } else {
            /* Lower rate period */
            usleep(1000 + rand() % 2000);
        }
        
        /* Occasional burst of high-priority messages */
        if (messages_created % 5000 == 0) {
            for (int i = 0; i < 10; i++) {
                ule_fsm_message_t priority_msg;
                create_ule_fsm_message(&priority_msg, messages_created + i, ctx->thread_id);
                priority_msg.ule_msg_class = ULE_MSG_REALTIME;
                priority_msg.ule_priority = 0;
                
                pthread_mutex_lock(&shared_queue_mutex);
                uint32_t next_tail = (shared_queue_tail + 1) % MAX_FSM_MESSAGES;
                if (next_tail != shared_queue_head) {
                    shared_message_queue[shared_queue_tail] = priority_msg;
                    shared_queue_tail = next_tail;
                }
                pthread_mutex_unlock(&shared_queue_mutex);
            }
        }
    }
    
    printf("Producer %u: Created %u messages\n", ctx->thread_id, messages_created);
    return NULL;
}

/* Message consumer thread */
void* message_consumer(void* arg) {
    integration_thread_context_t *ctx = (integration_thread_context_t*)arg;
    
    printf("Consumer %u: Starting message processing on CPU %u\n", 
           ctx->thread_id, ctx->cpu_id);
    
    /* Set CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->cpu_id, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    uint64_t messages_processed = 0;
    uint64_t integration_errors = 0;
    double total_latency = 0;
    
    while (*ctx->test_running || shared_queue_head != shared_queue_tail) {
        ule_fsm_message_t msg;
        int has_message = 0;
        
        /* Get message from shared queue */
        pthread_mutex_lock(&shared_queue_mutex);
        if (shared_queue_head != shared_queue_tail) {
            msg = shared_message_queue[shared_queue_head];
            shared_queue_head = (shared_queue_head + 1) % MAX_FSM_MESSAGES;
            has_message = 1;
        }
        pthread_mutex_unlock(&shared_queue_mutex);
        
        if (has_message) {
            /* Process the message */
            double processing_time = process_ule_fsm_message(&msg, ctx->thread_id);
            double end_to_end_latency = msg.processing_end_time_us - msg.creation_time_us;
            
            if (processing_time > 0) {
                messages_processed++;
                total_latency += end_to_end_latency;
                
                /* Check for integration violations */
                if (!msg.integration_valid) {
                    integration_errors++;
                }
                
                /* Check for performance violations (>15μs per message target) */
                if (end_to_end_latency > 15.0) {
                    pthread_mutex_lock(ctx->stats_mutex);
                    ctx->shared_stats->performance_violations++;
                    pthread_mutex_unlock(ctx->stats_mutex);
                }
                
                /* Update global statistics */
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->messages_processed++;
                ctx->shared_stats->total_processing_time_us += processing_time;
                ctx->shared_stats->avg_message_latency_us = 
                    (ctx->shared_stats->avg_message_latency_us * (ctx->shared_stats->messages_processed - 1) + 
                     end_to_end_latency) / ctx->shared_stats->messages_processed;
                
                if (end_to_end_latency > ctx->shared_stats->max_message_latency_us) {
                    ctx->shared_stats->max_message_latency_us = end_to_end_latency;
                }
                if (processing_time > ctx->shared_stats->max_processing_time_us) {
                    ctx->shared_stats->max_processing_time_us = processing_time;
                }
                if (ctx->shared_stats->min_processing_time_us == 0 || 
                    processing_time < ctx->shared_stats->min_processing_time_us) {
                    ctx->shared_stats->min_processing_time_us = processing_time;
                }
                
                ctx->shared_stats->state_transitions++;
                ctx->shared_stats->interactivity_calculations++;
                ctx->shared_stats->integration_violations += integration_errors;
                pthread_mutex_unlock(ctx->stats_mutex);
            } else {
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->messages_failed++;
                pthread_mutex_unlock(ctx->stats_mutex);
            }
        } else {
            /* No message available, brief sleep */
            usleep(100);
        }
        
        /* Periodic scheduler yield */
        if (messages_processed % 100 == 0) {
            sched_yield();
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->scheduler_preemptions++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
    }
    
    ctx->thread_messages_processed = messages_processed;
    ctx->thread_integration_errors = integration_errors;
    ctx->thread_total_latency = total_latency;
    
    printf("Consumer %u: Processed %lu messages with %lu integration errors\n",
           ctx->thread_id, messages_processed, integration_errors);
    
    return NULL;
}

/* Integration monitor thread */
void* integration_monitor(void* arg) {
    integration_thread_context_t *ctx = (integration_thread_context_t*)arg;
    
    printf("Starting ULE+FSM integration monitor\n");
    
    while (*ctx->test_running) {
        sleep(INTEGRATION_CHECK_INTERVAL);
        
        pthread_mutex_lock(ctx->stats_mutex);
        uint64_t messages_created = ctx->shared_stats->messages_created;
        uint64_t messages_processed = ctx->shared_stats->messages_processed;
        uint64_t messages_failed = ctx->shared_stats->messages_failed;
        uint64_t integration_violations = ctx->shared_stats->integration_violations;
        uint64_t performance_violations = ctx->shared_stats->performance_violations;
        double avg_latency = ctx->shared_stats->avg_message_latency_us;
        double max_latency = ctx->shared_stats->max_message_latency_us;
        uint64_t queue_overflows = ctx->shared_stats->message_queue_overflows;
        pthread_mutex_unlock(ctx->stats_mutex);
        
        uint32_t queue_depth = (shared_queue_tail >= shared_queue_head) ? 
                              (shared_queue_tail - shared_queue_head) :
                              (MAX_FSM_MESSAGES - shared_queue_head + shared_queue_tail);
        
        printf("Integration Status: Created=%lu, Processed=%lu, Failed=%lu, Queue=%u\n",
               messages_created, messages_processed, messages_failed, queue_depth);
        printf("Performance: Avg=%.2fμs, Max=%.2fμs, IntViol=%lu, PerfViol=%lu, Overflows=%lu\n",
               avg_latency, max_latency, integration_violations, performance_violations, queue_overflows);
        
        /* Check for critical conditions */
        if (integration_violations > 1000) {
            printf("WARNING: High integration violations detected: %lu\n", integration_violations);
        }
        if (avg_latency > 20.0) {
            printf("WARNING: High average latency: %.2f μs\n", avg_latency);
        }
        if (queue_overflows > 100) {
            printf("WARNING: Frequent queue overflows: %lu\n", queue_overflows);
        }
    }
    
    return NULL;
}

/* Signal handler for graceful shutdown */
void shutdown_handler(int sig) {
    printf("\nReceived signal %d, initiating graceful shutdown...\n", sig);
    test_running = 0;
}

/* Print comprehensive integration test results */
void print_integration_test_results(void) {
    printf("\n=== ULE+FSM INTEGRATION STRESS TEST RESULTS ===\n");
    printf("Test duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
    
    printf("\nMessage Processing:\n");
    printf("Messages created: %lu\n", global_stats.messages_created);
    printf("Messages processed: %lu\n", global_stats.messages_processed);
    printf("Messages failed: %lu\n", global_stats.messages_failed);
    printf("Processing success rate: %.2f%%\n", 
           (100.0 * global_stats.messages_processed) / (global_stats.messages_created + 1));
    
    printf("\nMessage Classification:\n");
    printf("Interactive messages: %lu\n", global_stats.interactive_messages);
    printf("Batch messages: %lu\n", global_stats.batch_messages);
    printf("Real-time messages: %lu\n", global_stats.realtime_messages);
    printf("Idle messages: %lu\n", global_stats.idle_messages);
    
    printf("\nPerformance Metrics:\n");
    double duration_seconds = (global_stats.end_time - global_stats.start_time) / 1000000.0;
    if (duration_seconds > 0) {
        printf("Message throughput: %.2f msg/sec\n", global_stats.messages_processed / duration_seconds);
        printf("Creation rate: %.2f msg/sec\n", global_stats.messages_created / duration_seconds);
    }
    
    if (global_stats.messages_processed > 0) {
        printf("Average processing time: %.3f μs\n", 
               global_stats.total_processing_time_us / global_stats.messages_processed);
        printf("Maximum processing time: %.3f μs\n", global_stats.max_processing_time_us);
        printf("Minimum processing time: %.3f μs\n", global_stats.min_processing_time_us);
        printf("Average message latency: %.3f μs\n", global_stats.avg_message_latency_us);
        printf("Maximum message latency: %.3f μs\n", global_stats.max_message_latency_us);
    }
    
    printf("\nIntegration Health:\n");
    printf("State transitions: %lu\n", global_stats.state_transitions);
    printf("Interactivity calculations: %lu\n", global_stats.interactivity_calculations);
    printf("Routing decisions: %lu\n", global_stats.routing_decisions);
    printf("Integration violations: %lu\n", global_stats.integration_violations);
    printf("Performance violations: %lu\n", global_stats.performance_violations);
    printf("Queue overflows: %lu\n", global_stats.message_queue_overflows);
    printf("Scheduler preemptions: %lu\n", global_stats.scheduler_preemptions);
    
    /* Calculate integration quality score */
    double quality_score = 100.0;
    if (global_stats.messages_processed > 0) {
        double failure_rate = (double)global_stats.messages_failed / global_stats.messages_processed;
        double violation_rate = (double)global_stats.integration_violations / global_stats.messages_processed;
        double perf_violation_rate = (double)global_stats.performance_violations / global_stats.messages_processed;
        
        quality_score -= (failure_rate * 50.0);
        quality_score -= (violation_rate * 30.0);
        quality_score -= (perf_violation_rate * 20.0);
    }
    if (quality_score < 0) quality_score = 0;
    
    printf("\nULE+FSM INTEGRATION QUALITY: %.1f/100\n", quality_score);
    
    if (global_stats.integration_violations == 0 && 
        global_stats.performance_violations < (global_stats.messages_processed / 100) &&
        global_stats.avg_message_latency_us < 15.0) {
        printf("STATUS: ULE+FSM INTEGRATION EXCELLENT ✓\n");
    } else if (global_stats.integration_violations < 100 && 
               global_stats.avg_message_latency_us < 25.0) {
        printf("STATUS: ULE+FSM INTEGRATION GOOD ✓\n");
    } else {
        printf("STATUS: ULE+FSM INTEGRATION ISSUES DETECTED ⚠️\n");
    }
}

/* Main test execution */
int main(int argc, char *argv[]) {
    printf("GNU Hurd ULE+FSM Integration Stress Test\n");
    printf("========================================\n\n");
    
    /* Set up signal handlers */
    signal(SIGINT, shutdown_handler);
    signal(SIGTERM, shutdown_handler);
    
    /* Initialize test environment */
    global_stats.start_time = get_current_time_us();
    
    uint32_t num_cpus = get_nprocs();
    printf("Detected %u CPU cores\n", num_cpus);
    printf("Starting ULE+FSM integration stress test for %d seconds...\n", TEST_DURATION_SECONDS);
    
    /* Create thread contexts */
    pthread_t integration_threads[MAX_INTEGRATION_THREADS];
    integration_thread_context_t contexts[MAX_INTEGRATION_THREADS];
    int num_threads = 0;
    
    /* Start producer threads (1/3 of available threads) */
    int num_producers = (num_cpus * 2) / 3;
    if (num_producers < 2) num_producers = 2;
    printf("Starting %d message producer threads\n", num_producers);
    
    for (int i = 0; i < num_producers && num_threads < MAX_INTEGRATION_THREADS; i++) {
        contexts[num_threads] = (integration_thread_context_t){
            .thread_id = num_threads,
            .cpu_id = i % num_cpus,
            .thread_type = 0, /* Producer */
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .message_queue = NULL,
            .queue_size = 0,
            .queue_head = 0,
            .queue_tail = 0,
            .thread_messages_processed = 0,
            .thread_integration_errors = 0,
            .thread_total_latency = 0
        };
        pthread_mutex_init(&contexts[num_threads].queue_mutex, NULL);
        pthread_create(&integration_threads[num_threads], NULL, message_producer, &contexts[num_threads]);
        num_threads++;
    }
    
    /* Start consumer threads (2/3 of available threads) */
    int num_consumers = num_cpus;
    printf("Starting %d message consumer threads\n", num_consumers);
    
    for (int i = 0; i < num_consumers && num_threads < MAX_INTEGRATION_THREADS; i++) {
        contexts[num_threads] = (integration_thread_context_t){
            .thread_id = num_threads,
            .cpu_id = i % num_cpus,
            .thread_type = 1, /* Consumer */
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .message_queue = NULL,
            .queue_size = 0,
            .queue_head = 0,
            .queue_tail = 0,
            .thread_messages_processed = 0,
            .thread_integration_errors = 0,
            .thread_total_latency = 0
        };
        pthread_mutex_init(&contexts[num_threads].queue_mutex, NULL);
        pthread_create(&integration_threads[num_threads], NULL, message_consumer, &contexts[num_threads]);
        num_threads++;
    }
    
    /* Start integration monitor */
    contexts[num_threads] = (integration_thread_context_t){
        .thread_id = num_threads,
        .cpu_id = 0,
        .thread_type = 2, /* Monitor */
        .shared_stats = &global_stats,
        .stats_mutex = &stats_mutex,
        .test_running = &test_running,
        .message_queue = NULL,
        .queue_size = 0,
        .queue_head = 0,
        .queue_tail = 0,
        .thread_messages_processed = 0,
        .thread_integration_errors = 0,
        .thread_total_latency = 0
    };
    pthread_create(&integration_threads[num_threads], NULL, integration_monitor, &contexts[num_threads]);
    num_threads++;
    
    /* Run test for specified duration */
    printf("Running ULE+FSM integration stress test with %d threads...\n", num_threads);
    sleep(TEST_DURATION_SECONDS);
    
    /* Signal shutdown and wait for completion */
    test_running = 0;
    global_stats.end_time = get_current_time_us();
    
    printf("Stopping tests and waiting for completion...\n");
    
    /* Wait for all threads */
    for (int i = 0; i < num_threads; i++) {
        pthread_join(integration_threads[i], NULL);
    }
    
    /* Print comprehensive results */
    print_integration_test_results();
    
    /* Save results to file */
    FILE *results_file = fopen("ule_fsm_integration_stress_results.txt", "w");
    if (results_file) {
        fprintf(results_file, "ULE+FSM Integration Stress Test Results\n");
        fprintf(results_file, "Duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
        fprintf(results_file, "Messages Created: %lu\n", global_stats.messages_created);
        fprintf(results_file, "Messages Processed: %lu\n", global_stats.messages_processed);
        fprintf(results_file, "Messages Failed: %lu\n", global_stats.messages_failed);
        fprintf(results_file, "Average Latency: %.3f μs\n", global_stats.avg_message_latency_us);
        fprintf(results_file, "Integration Violations: %lu\n", global_stats.integration_violations);
        fprintf(results_file, "Performance Violations: %lu\n", global_stats.performance_violations);
        fprintf(results_file, "Queue Overflows: %lu\n", global_stats.message_queue_overflows);
        fclose(results_file);
    }
    
    /* Cleanup */
    for (int i = 0; i < num_threads - 1; i++) {
        pthread_mutex_destroy(&contexts[i].queue_mutex);
    }
    
    return (global_stats.integration_violations < 100 && 
            global_stats.avg_message_latency_us < 25.0) ? 0 : 1;
}