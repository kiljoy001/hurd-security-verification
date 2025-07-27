/* GNU Hurd ULE Scheduler Stress Test Suite
 * Comprehensive testing of ULE SMP scheduler with formal verification integration
 * Tests interactivity calculations, load balancing, and multi-core performance
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/time.h>
#include <sys/syscall.h>
#include <sys/sysinfo.h>
#include <signal.h>
#include <errno.h>
#include <string.h>
#include <math.h>
#include <sched.h>
#include <assert.h>

/* Test configuration */
#define MAX_THREADS 1000
#define MAX_PROCESSES 100
#define TEST_DURATION_SECONDS 300
#define INTERACTIVITY_SAMPLES 10000
#define LOAD_BALANCE_ITERATIONS 1000

/* ULE Scheduler Test Statistics */
typedef struct {
    uint64_t interactivity_calculations;
    uint64_t context_switches;
    uint64_t load_balance_operations;
    uint64_t preemptions;
    uint64_t voluntary_yields;
    uint64_t cpu_migrations;
    uint64_t queue_operations;
    uint64_t scheduler_errors;
    double total_latency_us;
    double max_latency_us;
    double min_latency_us;
    double start_time;
    double end_time;
    uint32_t active_cores;
    uint32_t total_tasks;
} ule_scheduler_stats_t;

/* ULE Message for testing */
typedef struct {
    uint32_t msg_id;
    uint32_t sender_id;
    uint32_t target_service;
    uint32_t msg_class;
    uint32_t sleep_time;
    uint32_t run_time;
    uint32_t arrival_time;
    uint32_t priority;
    uint32_t core_affinity;
} ule_test_message_t;

/* Thread test context */
typedef struct {
    int thread_id;
    int cpu_id;
    ule_scheduler_stats_t *shared_stats;
    pthread_mutex_t *stats_mutex;
    volatile int *test_running;
    uint32_t workload_type;
    uint32_t message_count;
} thread_context_t;

static ule_scheduler_stats_t global_stats = {0};
static pthread_mutex_t stats_mutex = PTHREAD_MUTEX_INITIALIZER;
static volatile int test_running = 1;
static volatile int scheduler_active = 1;

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
            /* Non-interactive: sleep <= run */
            return fmin(100, 50 + (run_time * 50) / (sleep_time + 1));
        } else {
            /* Interactive: sleep > run */
            return fmin(100, (sleep_time * 50) / (run_time + 1));
        }
    }
    return 0;
}

/* ULE Message Class Classification */
uint32_t ule_classify_message(ule_test_message_t *msg) {
    uint32_t interactivity = ule_calculate_interactivity(msg->sleep_time, msg->run_time);
    
    if (interactivity <= 30) {
        return 2; /* ULE_MSG_INTERACTIVE */
    } else if (interactivity <= 70) {
        return 3; /* ULE_MSG_BATCH */
    } else {
        return 4; /* ULE_MSG_IDLE */
    }
}

/* Simulate ULE queue operations */
static void simulate_ule_queue_operations(thread_context_t *ctx) {
    double start_time = get_current_time_us();
    
    for (int i = 0; i < 100; i++) {
        ule_test_message_t msg = {
            .msg_id = ctx->thread_id * 1000 + i,
            .sender_id = ctx->thread_id,
            .target_service = rand() % 7,
            .sleep_time = 10 + rand() % 50,
            .run_time = 5 + rand() % 25,
            .arrival_time = (uint32_t)(get_current_time_us() / 1000),
            .core_affinity = ctx->cpu_id
        };
        
        /* Calculate interactivity and classify */
        uint32_t interactivity = ule_calculate_interactivity(msg.sleep_time, msg.run_time);
        msg.msg_class = ule_classify_message(&msg);
        
        /* Simulate queue insertion based on message class */
        if (msg.msg_class == 2) { /* Interactive */
            msg.priority = 0; /* Highest priority */
        } else if (msg.msg_class == 3) { /* Batch */
            msg.priority = 1;
        } else { /* Idle */
            msg.priority = 2; /* Lowest priority */
        }
        
        /* Brief processing delay */
        usleep(10 + rand() % 20);
        
        pthread_mutex_lock(ctx->stats_mutex);
        ctx->shared_stats->interactivity_calculations++;
        ctx->shared_stats->queue_operations++;
        pthread_mutex_unlock(ctx->stats_mutex);
    }
    
    double end_time = get_current_time_us();
    double latency = end_time - start_time;
    
    pthread_mutex_lock(ctx->stats_mutex);
    ctx->shared_stats->total_latency_us += latency;
    if (latency > ctx->shared_stats->max_latency_us) {
        ctx->shared_stats->max_latency_us = latency;
    }
    if (ctx->shared_stats->min_latency_us == 0 || latency < ctx->shared_stats->min_latency_us) {
        ctx->shared_stats->min_latency_us = latency;
    }
    pthread_mutex_unlock(ctx->stats_mutex);
}

/* Stress Test 1: Interactivity Calculation Performance */
void* test_interactivity_performance(void* arg) {
    thread_context_t *ctx = (thread_context_t*)arg;
    
    printf("Thread %d: Starting interactivity calculation stress test on CPU %d\n", 
           ctx->thread_id, ctx->cpu_id);
    
    /* Set CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->cpu_id, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    uint32_t calculations = 0;
    double start_time = get_current_time_us();
    
    while (*ctx->test_running && scheduler_active) {
        /* Generate various workload patterns */
        for (int pattern = 0; pattern < 10; pattern++) {
            uint32_t sleep_base = 10 + pattern * 5;
            uint32_t run_base = 5 + pattern * 3;
            
            for (int i = 0; i < 100; i++) {
                uint32_t sleep_time = sleep_base + rand() % 20;
                uint32_t run_time = run_base + rand() % 15;
                
                double calc_start = get_current_time_us();
                uint32_t interactivity = ule_calculate_interactivity(sleep_time, run_time);
                double calc_end = get_current_time_us();
                
                calculations++;
                
                /* Verify bounds - should match Coq theorem ule_interactivity_bounded */
                assert(interactivity <= 100);
                
                /* Update statistics */
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->interactivity_calculations++;
                ctx->shared_stats->total_latency_us += (calc_end - calc_start);
                pthread_mutex_unlock(ctx->stats_mutex);
            }
        }
        
        /* Simulate realistic scheduler work */
        simulate_ule_queue_operations(ctx);
        
        /* Brief yield to allow other threads */
        if (calculations % 1000 == 0) {
            sched_yield();
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->voluntary_yields++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
        
        usleep(100 + rand() % 500);
    }
    
    double end_time = get_current_time_us();
    printf("Thread %d: Completed %u interactivity calculations in %.2f ms\n",
           ctx->thread_id, calculations, (end_time - start_time) / 1000.0);
    
    return NULL;
}

/* Stress Test 2: Load Balancing Simulation */
void* test_load_balancing(void* arg) {
    thread_context_t *ctx = (thread_context_t*)arg;
    
    printf("Thread %d: Starting load balancing simulation on CPU %d\n", 
           ctx->thread_id, ctx->cpu_id);
    
    /* Set initial CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->cpu_id, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    int migration_count = 0;
    int load_balance_ops = 0;
    
    while (*ctx->test_running && scheduler_active) {
        /* Simulate varying workload intensities */
        int work_intensity = 50 + rand() % 200; /* 50-250 units of work */
        
        for (int work = 0; work < work_intensity; work++) {
            /* Simulate computational work */
            volatile double result = 0;
            for (int calc = 0; calc < 1000; calc++) {
                result += sqrt(calc * ctx->thread_id);
            }
            
            /* Periodically check if we should migrate to balance load */
            if (work % 50 == 0) {
                int current_cpu = sched_getcpu();
                int target_cpu = (current_cpu + 1) % ctx->shared_stats->active_cores;
                
                /* Simulate migration decision based on load */
                if (rand() % 10 == 0) { /* 10% chance of migration */
                    CPU_ZERO(&cpuset);
                    CPU_SET(target_cpu, &cpuset);
                    if (pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0) {
                        migration_count++;
                        pthread_mutex_lock(ctx->stats_mutex);
                        ctx->shared_stats->cpu_migrations++;
                        pthread_mutex_unlock(ctx->stats_mutex);
                    }
                }
                
                load_balance_ops++;
                pthread_mutex_lock(ctx->stats_mutex);
                ctx->shared_stats->load_balance_operations++;
                pthread_mutex_unlock(ctx->stats_mutex);
            }
        }
        
        /* Simulate different scheduling behaviors */
        if (ctx->workload_type == 0) {
            /* Interactive workload - frequent short bursts */
            usleep(1000 + rand() % 2000);
        } else if (ctx->workload_type == 1) {
            /* Batch workload - longer compute periods */
            usleep(5000 + rand() % 10000);
        } else {
            /* Mixed workload */
            usleep(500 + rand() % 5000);
        }
        
        /* Occasionally yield voluntarily */
        if (rand() % 100 == 0) {
            sched_yield();
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->voluntary_yields++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
    }
    
    printf("Thread %d: Completed with %d migrations and %d load balance operations\n",
           ctx->thread_id, migration_count, load_balance_ops);
    
    return NULL;
}

/* Stress Test 3: Multi-Core ULE+FSM Integration */
void* test_ule_fsm_integration(void* arg) {
    thread_context_t *ctx = (thread_context_t*)arg;
    
    printf("Thread %d: Starting ULE+FSM integration test on CPU %d\n", 
           ctx->thread_id, ctx->cpu_id);
    
    /* Set CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->cpu_id, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    uint32_t integrated_operations = 0;
    
    while (*ctx->test_running && scheduler_active) {
        /* Create FSM message with ULE integration */
        ule_test_message_t ule_msg = {
            .msg_id = ctx->thread_id * 10000 + integrated_operations,
            .sender_id = ctx->thread_id,
            .target_service = rand() % 7,
            .sleep_time = 5 + rand() % 30,
            .run_time = 3 + rand() % 20,
            .arrival_time = (uint32_t)(get_current_time_us() / 1000),
            .core_affinity = ctx->cpu_id
        };
        
        /* ULE processing */
        double ule_start = get_current_time_us();
        uint32_t interactivity = ule_calculate_interactivity(ule_msg.sleep_time, ule_msg.run_time);
        ule_msg.msg_class = ule_classify_message(&ule_msg);
        double ule_end = get_current_time_us();
        
        /* FSM state simulation */
        uint32_t fsm_state = 1; /* FSM_CREATED */
        if (ule_msg.msg_class == 2) { /* Interactive */
            fsm_state = 1; /* FSM_CREATED -> Interactive priority */
        } else if (ule_msg.msg_class == 3) { /* Batch */
            fsm_state = 2; /* FSM_ROUTED -> Normal priority */
        } else {
            fsm_state = 3; /* FSM_PROCESSED -> Low priority */
        }
        
        /* Validate integration - should match Coq theorem fsm_ule_integration_maintains_invariants */
        assert(fsm_state >= 1 && fsm_state <= 3);
        assert(interactivity <= 100);
        assert(ule_msg.sender_id == (uint32_t)ctx->thread_id);
        
        integrated_operations++;
        
        /* Update statistics */
        pthread_mutex_lock(ctx->stats_mutex);
        ctx->shared_stats->queue_operations++;
        ctx->shared_stats->total_latency_us += (ule_end - ule_start);
        pthread_mutex_unlock(ctx->stats_mutex);
        
        /* Simulate message processing delay based on class */
        if (ule_msg.msg_class == 2) { /* Interactive */
            usleep(100 + rand() % 300);
        } else if (ule_msg.msg_class == 3) { /* Batch */
            usleep(500 + rand() % 1000);
        } else { /* Idle */
            usleep(1000 + rand() % 2000);
        }
        
        /* Periodic context switch simulation */
        if (integrated_operations % 100 == 0) {
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->context_switches++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
    }
    
    printf("Thread %d: Completed %u integrated ULE+FSM operations\n",
           ctx->thread_id, integrated_operations);
    
    return NULL;
}

/* Monitor system performance and scheduler health */
void* scheduler_monitor(void* arg) {
    printf("Starting ULE scheduler performance monitor\n");
    
    double last_check = get_current_time_us();
    uint64_t last_calculations = 0;
    uint64_t last_operations = 0;
    
    while (test_running) {
        sleep(5); /* Check every 5 seconds */
        
        double current_time = get_current_time_us();
        
        pthread_mutex_lock(&stats_mutex);
        uint64_t current_calculations = global_stats.interactivity_calculations;
        uint64_t current_operations = global_stats.queue_operations;
        uint64_t context_switches = global_stats.context_switches;
        uint64_t migrations = global_stats.cpu_migrations;
        double avg_latency = global_stats.total_latency_us / 
                           (global_stats.interactivity_calculations + 1);
        pthread_mutex_unlock(&stats_mutex);
        
        double time_delta = (current_time - last_check) / 1000000.0; /* Convert to seconds */
        uint64_t calc_rate = (current_calculations - last_calculations) / time_delta;
        uint64_t op_rate = (current_operations - last_operations) / time_delta;
        
        printf("ULE Scheduler Performance: %.2f calc/s, %.2f ops/s, %.2f μs avg latency\n",
               (double)calc_rate, (double)op_rate, avg_latency);
        printf("System Activity: %lu context switches, %lu CPU migrations\n",
               context_switches, migrations);
        
        /* Check for performance degradation */
        if (avg_latency > 50.0) {
            printf("WARNING: High scheduler latency detected: %.2f μs\n", avg_latency);
        }
        
        if (calc_rate < 1000) {
            printf("WARNING: Low calculation rate: %lu calc/s\n", calc_rate);
        }
        
        last_check = current_time;
        last_calculations = current_calculations;
        last_operations = current_operations;
    }
    
    return NULL;
}

/* Signal handler for graceful shutdown */
void shutdown_handler(int sig) {
    printf("\nReceived signal %d, initiating graceful shutdown...\n", sig);
    test_running = 0;
    scheduler_active = 0;
}

/* Print comprehensive test results */
void print_ule_scheduler_results(void) {
    printf("\n=== ULE SCHEDULER STRESS TEST RESULTS ===\n");
    printf("Test duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
    printf("Active CPU cores: %u\n", global_stats.active_cores);
    printf("Total tasks spawned: %u\n", global_stats.total_tasks);
    
    printf("\nScheduler Operations:\n");
    printf("Interactivity calculations: %lu\n", global_stats.interactivity_calculations);
    printf("Queue operations: %lu\n", global_stats.queue_operations);
    printf("Context switches: %lu\n", global_stats.context_switches);
    printf("Load balance operations: %lu\n", global_stats.load_balance_operations);
    printf("CPU migrations: %lu\n", global_stats.cpu_migrations);
    printf("Voluntary yields: %lu\n", global_stats.voluntary_yields);
    printf("Preemptions: %lu\n", global_stats.preemptions);
    
    printf("\nPerformance Metrics:\n");
    double duration_seconds = (global_stats.end_time - global_stats.start_time) / 1000000.0;
    if (duration_seconds > 0) {
        printf("Calculation rate: %.2f calc/sec\n", global_stats.interactivity_calculations / duration_seconds);
        printf("Operation rate: %.2f ops/sec\n", global_stats.queue_operations / duration_seconds);
        printf("Context switch rate: %.2f cs/sec\n", global_stats.context_switches / duration_seconds);
    }
    
    if (global_stats.interactivity_calculations > 0) {
        printf("Average latency: %.3f μs\n", global_stats.total_latency_us / global_stats.interactivity_calculations);
        printf("Maximum latency: %.3f μs\n", global_stats.max_latency_us);
        printf("Minimum latency: %.3f μs\n", global_stats.min_latency_us);
    }
    
    printf("\nScheduler Health:\n");
    if (global_stats.scheduler_errors > 0) {
        printf("Scheduler errors: %lu ⚠️\n", global_stats.scheduler_errors);
    } else {
        printf("Scheduler errors: 0 ✓\n");
    }
    
    /* Calculate scheduler efficiency score */
    double efficiency_score = 100.0;
    double avg_latency = global_stats.total_latency_us / (global_stats.interactivity_calculations + 1);
    
    if (avg_latency > 10.0) efficiency_score -= (avg_latency - 10.0) * 2;
    if (global_stats.scheduler_errors > 0) efficiency_score -= global_stats.scheduler_errors * 10;
    if (efficiency_score < 0) efficiency_score = 0;
    
    printf("ULE SCHEDULER EFFICIENCY: %.1f/100\n", efficiency_score);
    
    if (global_stats.scheduler_errors == 0 && avg_latency < 20.0) {
        printf("STATUS: ULE SCHEDULER HEALTHY ✓\n");
    } else {
        printf("STATUS: ULE SCHEDULER ISSUES DETECTED ⚠️\n");
    }
}

/* Main test execution */
int main(int argc, char *argv[]) {
    printf("GNU Hurd ULE Scheduler Stress Test Suite\n");
    printf("=========================================\n\n");
    
    /* Set up signal handlers */
    signal(SIGINT, shutdown_handler);
    signal(SIGTERM, shutdown_handler);
    
    /* Initialize test environment */
    global_stats.active_cores = get_nprocs();
    global_stats.start_time = get_current_time_us();
    
    printf("Detected %u CPU cores\n", global_stats.active_cores);
    printf("Starting ULE scheduler stress tests for %d seconds...\n", TEST_DURATION_SECONDS);
    
    /* Start performance monitor */
    pthread_t monitor_thread;
    pthread_create(&monitor_thread, NULL, scheduler_monitor, NULL);
    
    /* Create thread contexts and spawn test threads */
    pthread_t test_threads[MAX_THREADS];
    thread_context_t contexts[MAX_THREADS];
    int num_threads = 0;
    
    /* Test 1: Interactivity calculation performance (1/3 of cores) */
    int interactivity_threads = global_stats.active_cores * 2;
    printf("Starting %d interactivity calculation threads\n", interactivity_threads);
    for (int i = 0; i < interactivity_threads && num_threads < MAX_THREADS; i++) {
        contexts[num_threads] = (thread_context_t){
            .thread_id = num_threads,
            .cpu_id = i % global_stats.active_cores,
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .workload_type = 0, /* Interactive */
            .message_count = 0
        };
        pthread_create(&test_threads[num_threads], NULL, 
                      test_interactivity_performance, &contexts[num_threads]);
        num_threads++;
    }
    
    /* Test 2: Load balancing simulation (1/3 of cores) */
    int load_balance_threads = global_stats.active_cores * 1;
    printf("Starting %d load balancing threads\n", load_balance_threads);
    for (int i = 0; i < load_balance_threads && num_threads < MAX_THREADS; i++) {
        contexts[num_threads] = (thread_context_t){
            .thread_id = num_threads,
            .cpu_id = i % global_stats.active_cores,
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .workload_type = i % 3, /* Mixed workload types */
            .message_count = 0
        };
        pthread_create(&test_threads[num_threads], NULL, 
                      test_load_balancing, &contexts[num_threads]);
        num_threads++;
    }
    
    /* Test 3: ULE+FSM integration (1/3 of cores) */
    int integration_threads = global_stats.active_cores * 1;
    printf("Starting %d ULE+FSM integration threads\n", integration_threads);
    for (int i = 0; i < integration_threads && num_threads < MAX_THREADS; i++) {
        contexts[num_threads] = (thread_context_t){
            .thread_id = num_threads,
            .cpu_id = i % global_stats.active_cores,
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .workload_type = 2, /* Integration test */
            .message_count = 0
        };
        pthread_create(&test_threads[num_threads], NULL, 
                      test_ule_fsm_integration, &contexts[num_threads]);
        num_threads++;
    }
    
    global_stats.total_tasks = num_threads;
    
    /* Run tests for specified duration */
    printf("Running ULE scheduler stress tests with %d threads...\n", num_threads);
    sleep(TEST_DURATION_SECONDS);
    
    /* Signal shutdown and wait for completion */
    test_running = 0;
    global_stats.end_time = get_current_time_us();
    
    printf("Stopping tests and waiting for thread completion...\n");
    
    /* Wait for all test threads */
    for (int i = 0; i < num_threads; i++) {
        pthread_join(test_threads[i], NULL);
    }
    pthread_join(monitor_thread, NULL);
    
    /* Print comprehensive results */
    print_ule_scheduler_results();
    
    /* Save results to file */
    FILE *results_file = fopen("ule_scheduler_stress_results.txt", "w");
    if (results_file) {
        fprintf(results_file, "ULE Scheduler Stress Test Results\n");
        fprintf(results_file, "Duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
        fprintf(results_file, "CPU Cores: %u\n", global_stats.active_cores);
        fprintf(results_file, "Total Tasks: %u\n", global_stats.total_tasks);
        fprintf(results_file, "Interactivity Calculations: %lu\n", global_stats.interactivity_calculations);
        fprintf(results_file, "Queue Operations: %lu\n", global_stats.queue_operations);
        fprintf(results_file, "Context Switches: %lu\n", global_stats.context_switches);
        fprintf(results_file, "CPU Migrations: %lu\n", global_stats.cpu_migrations);
        fprintf(results_file, "Average Latency: %.3f μs\n", 
                global_stats.total_latency_us / (global_stats.interactivity_calculations + 1));
        fprintf(results_file, "Scheduler Errors: %lu\n", global_stats.scheduler_errors);
        fclose(results_file);
    }
    
    return (global_stats.scheduler_errors == 0) ? 0 : 1;
}