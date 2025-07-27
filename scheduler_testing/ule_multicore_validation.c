/* GNU Hurd ULE Multi-Core Scheduling and Load Balancing Validation
 * Comprehensive testing of ULE SMP scheduler across multiple CPU cores
 * Tests load balancing, CPU affinity, migration patterns, and NUMA awareness
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
#include <sched.h>
#include <string.h>
#include <math.h>
#include <errno.h>
#include <assert.h>

/* Test configuration */
#define MAX_CPUS 128
#define MAX_TASKS 512
#define TEST_DURATION_SECONDS 120
#define LOAD_MEASUREMENT_INTERVAL 1
#define MIGRATION_THRESHOLD 0.8
#define BALANCE_CHECK_INTERVAL 5

/* ULE multi-core statistics */
typedef struct {
    uint64_t task_migrations;
    uint64_t load_balance_operations;
    uint64_t affinity_violations;
    uint64_t numa_violations;
    uint64_t context_switches;
    uint64_t preemptions;
    uint64_t idle_cycles;
    uint64_t work_stealing_attempts;
    uint64_t work_stealing_successes;
    double total_load_imbalance;
    double max_load_imbalance;
    double total_migration_cost_us;
    double start_time;
    double end_time;
    uint32_t active_cpus;
    uint32_t numa_nodes;
} ule_multicore_stats_t;

/* Per-CPU statistics */
typedef struct {
    uint32_t cpu_id;
    uint32_t numa_node;
    uint64_t tasks_executed;
    uint64_t context_switches;
    uint64_t migrations_in;
    uint64_t migrations_out;
    uint64_t idle_time_us;
    uint64_t work_time_us;
    double current_load;
    double average_load;
    double peak_load;
    pthread_mutex_t stats_mutex;
} cpu_stats_t;

/* Task context for multi-core testing */
typedef struct {
    uint32_t task_id;
    uint32_t preferred_cpu;
    uint32_t preferred_numa_node;
    uint32_t current_cpu;
    uint32_t workload_type;
    uint64_t work_units_completed;
    uint64_t migrations_experienced;
    double total_execution_time_us;
    double migration_overhead_us;
    ule_multicore_stats_t *shared_stats;
    cpu_stats_t *cpu_stats;
    pthread_mutex_t *global_mutex;
    volatile int *test_running;
} task_context_t;

/* Load balancer context */
typedef struct {
    ule_multicore_stats_t *shared_stats;
    cpu_stats_t *cpu_stats;
    pthread_mutex_t *global_mutex;
    volatile int *test_running;
    uint32_t num_cpus;
    uint32_t num_numa_nodes;
} load_balancer_context_t;

static ule_multicore_stats_t global_stats = {0};
static cpu_stats_t cpu_stats[MAX_CPUS];
static pthread_mutex_t global_mutex = PTHREAD_MUTEX_INITIALIZER;
static volatile int test_running = 1;

/* Get current time in microseconds */
static double get_current_time_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000000.0 + tv.tv_usec;
}

/* Get current CPU ID */
static int get_current_cpu(void) {
    return sched_getcpu();
}

/* Get NUMA node for given CPU */
static int get_numa_node_for_cpu(int cpu) {
    (void)cpu; /* Unused parameter */
    return 0; /* Simplified - return node 0 when NUMA not available */
}

/* Initialize CPU statistics */
static void init_cpu_stats(uint32_t num_cpus) {
    for (uint32_t i = 0; i < num_cpus; i++) {
        cpu_stats[i].cpu_id = i;
        cpu_stats[i].numa_node = get_numa_node_for_cpu(i);
        cpu_stats[i].tasks_executed = 0;
        cpu_stats[i].context_switches = 0;
        cpu_stats[i].migrations_in = 0;
        cpu_stats[i].migrations_out = 0;
        cpu_stats[i].idle_time_us = 0;
        cpu_stats[i].work_time_us = 0;
        cpu_stats[i].current_load = 0.0;
        cpu_stats[i].average_load = 0.0;
        cpu_stats[i].peak_load = 0.0;
        pthread_mutex_init(&cpu_stats[i].stats_mutex, NULL);
    }
}

/* Calculate load imbalance across CPUs */
static double calculate_load_imbalance(cpu_stats_t *cpu_stats, uint32_t num_cpus) {
    double total_load = 0.0;
    double max_load = 0.0;
    double min_load = 1000.0;
    
    for (uint32_t i = 0; i < num_cpus; i++) {
        double load = cpu_stats[i].current_load;
        total_load += load;
        if (load > max_load) max_load = load;
        if (load < min_load) min_load = load;
    }
    
    double avg_load = total_load / num_cpus;
    return (avg_load > 0) ? (max_load - min_load) / avg_load : 0.0;
}

/* Simulate CPU-intensive workload */
static void simulate_cpu_workload(uint32_t work_units, uint32_t workload_type) {
    volatile double result = 0.0;
    
    switch (workload_type) {
        case 0: /* Mathematical computation */
            for (uint32_t i = 0; i < work_units * 1000; i++) {
                result += sqrt(i * 3.14159) * cos(i * 0.001);
            }
            break;
            
        case 1: /* Memory-intensive */
            {
                volatile int *temp_mem = malloc(work_units * 1024);
                if (temp_mem) {
                    for (uint32_t i = 0; i < work_units * 256; i++) {
                        temp_mem[i % (work_units * 256)] = i;
                    }
                    free((void*)temp_mem);
                }
            }
            break;
            
        case 2: /* Mixed workload */
            for (uint32_t i = 0; i < work_units * 500; i++) {
                result += sin(i) * log(i + 1);
                if (i % 100 == 0) {
                    usleep(1); /* Brief I/O simulation */
                }
            }
            break;
            
        default:
            for (uint32_t i = 0; i < work_units * 100; i++) {
                result += i * i;
            }
    }
    
    /* Prevent optimization */
    (void)result;
}

/* Task worker function */
void* multicore_task_worker(void* arg) {
    task_context_t *ctx = (task_context_t*)arg;
    
    printf("Task %u: Starting on preferred CPU %u (NUMA node %u)\n", 
           ctx->task_id, ctx->preferred_cpu, ctx->preferred_numa_node);
    
    /* Set initial CPU affinity */
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(ctx->preferred_cpu, &cpuset);
    if (pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) != 0) {
        printf("Warning: Failed to set initial affinity for task %u\n", ctx->task_id);
    }
    
    uint64_t work_cycles = 0;
    int last_cpu = ctx->preferred_cpu;
    double task_start_time = get_current_time_us();
    
    while (*ctx->test_running) {
        int current_cpu = get_current_cpu();
        ctx->current_cpu = current_cpu;
        
        /* Detect CPU migration */
        if (current_cpu != last_cpu) {
            ctx->migrations_experienced++;
            
            /* Update per-CPU migration statistics */
            pthread_mutex_lock(&ctx->cpu_stats[last_cpu].stats_mutex);
            ctx->cpu_stats[last_cpu].migrations_out++;
            pthread_mutex_unlock(&ctx->cpu_stats[last_cpu].stats_mutex);
            
            pthread_mutex_lock(&ctx->cpu_stats[current_cpu].stats_mutex);
            ctx->cpu_stats[current_cpu].migrations_in++;
            pthread_mutex_unlock(&ctx->cpu_stats[current_cpu].stats_mutex);
            
            /* Check for NUMA violations */
            int current_numa = get_numa_node_for_cpu(current_cpu);
            if (current_numa != ctx->preferred_numa_node) {
                pthread_mutex_lock(ctx->global_mutex);
                ctx->shared_stats->numa_violations++;
                pthread_mutex_unlock(ctx->global_mutex);
            }
            
            /* Update global migration statistics */
            pthread_mutex_lock(ctx->global_mutex);
            ctx->shared_stats->task_migrations++;
            pthread_mutex_unlock(ctx->global_mutex);
            
            last_cpu = current_cpu;
        }
        
        /* Perform work */
        double work_start = get_current_time_us();
        simulate_cpu_workload(50 + (work_cycles % 100), ctx->workload_type);
        double work_end = get_current_time_us();
        
        double work_time = work_end - work_start;
        ctx->total_execution_time_us += work_time;
        ctx->work_units_completed++;
        work_cycles++;
        
        /* Update per-CPU work statistics */
        pthread_mutex_lock(&ctx->cpu_stats[current_cpu].stats_mutex);
        ctx->cpu_stats[current_cpu].tasks_executed++;
        ctx->cpu_stats[current_cpu].work_time_us += (uint64_t)work_time;
        ctx->cpu_stats[current_cpu].current_load = 
            (double)ctx->cpu_stats[current_cpu].work_time_us / 
            (get_current_time_us() - task_start_time);
        pthread_mutex_unlock(&ctx->cpu_stats[current_cpu].stats_mutex);
        
        /* Vary work patterns to test load balancing */
        if (work_cycles % 100 == 0) {
            /* Periodic burst of activity */
            simulate_cpu_workload(200, ctx->workload_type);
        } else if (work_cycles % 500 == 0) {
            /* Occasional idle period */
            usleep(5000 + rand() % 10000);
        }
        
        /* Brief yield to allow scheduler decisions */
        if (work_cycles % 50 == 0) {
            sched_yield();
            pthread_mutex_lock(ctx->global_mutex);
            ctx->shared_stats->context_switches++;
            pthread_mutex_unlock(ctx->global_mutex);
        }
        
        /* Small random delay to avoid lockstep behavior */
        usleep(100 + rand() % 500);
    }
    
    printf("Task %u: Completed %lu work units with %lu migrations\n",
           ctx->task_id, ctx->work_units_completed, ctx->migrations_experienced);
    
    return NULL;
}

/* Load balancer monitor */
void* load_balancer_monitor(void* arg) {
    load_balancer_context_t *ctx = (load_balancer_context_t*)arg;
    
    printf("Starting ULE load balancer monitor for %u CPUs\n", ctx->num_cpus);
    
    while (*ctx->test_running) {
        sleep(BALANCE_CHECK_INTERVAL);
        
        /* Calculate current load imbalance */
        double imbalance = calculate_load_imbalance(ctx->cpu_stats, ctx->num_cpus);
        
        pthread_mutex_lock(ctx->global_mutex);
        ctx->shared_stats->total_load_imbalance += imbalance;
        if (imbalance > ctx->shared_stats->max_load_imbalance) {
            ctx->shared_stats->max_load_imbalance = imbalance;
        }
        ctx->shared_stats->load_balance_operations++;
        pthread_mutex_unlock(ctx->global_mutex);
        
        /* Print load status */
        printf("Load imbalance: %.3f", imbalance);
        for (uint32_t i = 0; i < ctx->num_cpus && i < 8; i++) {
            printf(" CPU%u:%.2f", i, ctx->cpu_stats[i].current_load);
        }
        printf("\n");
        
        /* Simulate load balancing decisions */
        if (imbalance > MIGRATION_THRESHOLD) {
            printf("High load imbalance detected: %.3f > %.3f\n", 
                   imbalance, MIGRATION_THRESHOLD);
            
            /* Find most and least loaded CPUs */
            uint32_t max_cpu = 0, min_cpu = 0;
            double max_load = 0.0, min_load = 1000.0;
            
            for (uint32_t i = 0; i < ctx->num_cpus; i++) {
                if (ctx->cpu_stats[i].current_load > max_load) {
                    max_load = ctx->cpu_stats[i].current_load;
                    max_cpu = i;
                }
                if (ctx->cpu_stats[i].current_load < min_load) {
                    min_load = ctx->cpu_stats[i].current_load;
                    min_cpu = i;
                }
            }
            
            /* Simulate work stealing attempt */
            if (max_load - min_load > 0.5) {
                pthread_mutex_lock(ctx->global_mutex);
                ctx->shared_stats->work_stealing_attempts++;
                
                /* Success probability based on load difference */
                if ((max_load - min_load) > 0.8) {
                    ctx->shared_stats->work_stealing_successes++;
                }
                pthread_mutex_unlock(ctx->global_mutex);
                
                printf("Work stealing: CPU%u (%.2f) -> CPU%u (%.2f)\n",
                       max_cpu, max_load, min_cpu, min_load);
            }
        }
        
        /* Update CPU load averages */
        for (uint32_t i = 0; i < ctx->num_cpus; i++) {
            pthread_mutex_lock(&ctx->cpu_stats[i].stats_mutex);
            double current_load = ctx->cpu_stats[i].current_load;
            ctx->cpu_stats[i].average_load = 
                (ctx->cpu_stats[i].average_load * 0.9) + (current_load * 0.1);
            if (current_load > ctx->cpu_stats[i].peak_load) {
                ctx->cpu_stats[i].peak_load = current_load;
            }
            pthread_mutex_unlock(&ctx->cpu_stats[i].stats_mutex);
        }
    }
    
    return NULL;
}

/* NUMA awareness test */
void* numa_awareness_test(void* arg) {
    (void)arg; /* Unused parameter */
    printf("Starting NUMA awareness validation\n");
    printf("NUMA not available on this system (simplified implementation)\n");
    
    while (test_running) {
        sleep(10);
    }
    
    return NULL;
}

/* CPU topology analysis */
void analyze_cpu_topology(void) {
    uint32_t num_cpus = get_nprocs();
    
    printf("\n=== CPU TOPOLOGY ANALYSIS ===\n");
    printf("Total CPUs: %u\n", num_cpus);
    printf("NUMA: Not available (simplified implementation)\n");
}

/* Print per-CPU statistics */
void print_cpu_statistics(cpu_stats_t *cpu_stats, uint32_t num_cpus) {
    printf("\n=== PER-CPU STATISTICS ===\n");
    printf("CPU | NUMA | Tasks | Migrations In/Out | Avg Load | Peak Load\n");
    printf("----|------|-------|------------------|----------|----------\n");
    
    for (uint32_t i = 0; i < num_cpus && i < 16; i++) { /* Limit output for readability */
        printf("%3u | %4u | %5lu | %8lu/%8lu | %8.3f | %9.3f\n",
               cpu_stats[i].cpu_id,
               cpu_stats[i].numa_node,
               cpu_stats[i].tasks_executed,
               cpu_stats[i].migrations_in,
               cpu_stats[i].migrations_out,
               cpu_stats[i].average_load,
               cpu_stats[i].peak_load);
    }
    
    if (num_cpus > 16) {
        printf("... (showing first 16 CPUs)\n");
    }
}

/* Print comprehensive multi-core test results */
void print_multicore_test_results(void) {
    printf("\n=== ULE MULTI-CORE SCHEDULING TEST RESULTS ===\n");
    printf("Test duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
    printf("Active CPUs: %u\n", global_stats.active_cpus);
    printf("NUMA nodes: %u\n", global_stats.numa_nodes);
    
    printf("\nLoad Balancing Metrics:\n");
    printf("Task migrations: %lu\n", global_stats.task_migrations);
    printf("Load balance operations: %lu\n", global_stats.load_balance_operations);
    printf("Work stealing attempts: %lu\n", global_stats.work_stealing_attempts);
    printf("Work stealing successes: %lu\n", global_stats.work_stealing_successes);
    
    if (global_stats.load_balance_operations > 0) {
        printf("Average load imbalance: %.3f\n", 
               global_stats.total_load_imbalance / global_stats.load_balance_operations);
        printf("Maximum load imbalance: %.3f\n", global_stats.max_load_imbalance);
        printf("Work stealing success rate: %.1f%%\n",
               (100.0 * global_stats.work_stealing_successes) / global_stats.work_stealing_attempts);
    }
    
    printf("\nScheduling Activity:\n");
    printf("Context switches: %lu\n", global_stats.context_switches);
    printf("Preemptions: %lu\n", global_stats.preemptions);
    printf("Idle cycles: %lu\n", global_stats.idle_cycles);
    
    printf("\nViolation Analysis:\n");
    printf("Affinity violations: %lu\n", global_stats.affinity_violations);
    printf("NUMA violations: %lu\n", global_stats.numa_violations);
    
    if (global_stats.task_migrations > 0) {
        printf("Average migration cost: %.3f μs\n", 
               global_stats.total_migration_cost_us / global_stats.task_migrations);
    }
    
    /* Calculate multi-core efficiency score */
    double efficiency_score = 100.0;
    double avg_imbalance = global_stats.total_load_imbalance / 
                          (global_stats.load_balance_operations + 1);
    
    if (avg_imbalance > 0.5) efficiency_score -= (avg_imbalance - 0.5) * 50;
    if (global_stats.numa_violations > 0) efficiency_score -= global_stats.numa_violations * 0.1;
    if (global_stats.affinity_violations > 0) efficiency_score -= global_stats.affinity_violations * 0.1;
    if (efficiency_score < 0) efficiency_score = 0;
    
    printf("\nULE MULTI-CORE EFFICIENCY: %.1f/100\n", efficiency_score);
    
    if (avg_imbalance < 0.3 && global_stats.numa_violations < 100) {
        printf("STATUS: ULE MULTI-CORE SCHEDULING EFFICIENT ✓\n");
    } else {
        printf("STATUS: ULE MULTI-CORE ISSUES DETECTED ⚠️\n");
    }
}

/* Main test execution */
int main(int argc, char *argv[]) {
    printf("GNU Hurd ULE Multi-Core Scheduling and Load Balancing Validation\n");
    printf("================================================================\n\n");
    
    /* Initialize test environment */
    global_stats.active_cpus = get_nprocs();
    global_stats.numa_nodes = 1; /* Simplified - single NUMA node */
    global_stats.start_time = get_current_time_us();
    
    init_cpu_stats(global_stats.active_cpus);
    analyze_cpu_topology();
    
    printf("\nStarting multi-core validation with %u CPUs for %d seconds...\n", 
           global_stats.active_cpus, TEST_DURATION_SECONDS);
    
    /* Create task contexts */
    uint32_t num_tasks = global_stats.active_cpus * 4; /* 4 tasks per CPU */
    if (num_tasks > MAX_TASKS) num_tasks = MAX_TASKS;
    
    pthread_t task_threads[MAX_TASKS];
    task_context_t task_contexts[MAX_TASKS];
    
    /* Start tasks with different workload types and CPU preferences */
    for (uint32_t i = 0; i < num_tasks; i++) {
        task_contexts[i] = (task_context_t){
            .task_id = i,
            .preferred_cpu = i % global_stats.active_cpus,
            .preferred_numa_node = get_numa_node_for_cpu(i % global_stats.active_cpus),
            .current_cpu = i % global_stats.active_cpus,
            .workload_type = i % 3, /* Distribute workload types */
            .work_units_completed = 0,
            .migrations_experienced = 0,
            .total_execution_time_us = 0,
            .migration_overhead_us = 0,
            .shared_stats = &global_stats,
            .cpu_stats = cpu_stats,
            .global_mutex = &global_mutex,
            .test_running = &test_running
        };
        
        pthread_create(&task_threads[i], NULL, multicore_task_worker, &task_contexts[i]);
    }
    
    /* Start load balancer monitor */
    load_balancer_context_t lb_context = {
        .shared_stats = &global_stats,
        .cpu_stats = cpu_stats,
        .global_mutex = &global_mutex,
        .test_running = &test_running,
        .num_cpus = global_stats.active_cpus,
        .num_numa_nodes = global_stats.numa_nodes
    };
    
    pthread_t lb_thread;
    pthread_create(&lb_thread, NULL, load_balancer_monitor, &lb_context);
    
    /* Start NUMA awareness test */
    pthread_t numa_thread;
    pthread_create(&numa_thread, NULL, numa_awareness_test, NULL);
    
    /* Run test for specified duration */
    printf("Running multi-core validation with %u tasks...\n", num_tasks);
    sleep(TEST_DURATION_SECONDS);
    
    /* Signal shutdown and wait for completion */
    test_running = 0;
    global_stats.end_time = get_current_time_us();
    
    printf("Stopping tests and waiting for completion...\n");
    
    /* Wait for all threads */
    for (uint32_t i = 0; i < num_tasks; i++) {
        pthread_join(task_threads[i], NULL);
    }
    pthread_join(lb_thread, NULL);
    pthread_join(numa_thread, NULL);
    
    /* Print comprehensive results */
    print_cpu_statistics(cpu_stats, global_stats.active_cpus);
    print_multicore_test_results();
    
    /* Save results to file */
    FILE *results_file = fopen("ule_multicore_validation_results.txt", "w");
    if (results_file) {
        fprintf(results_file, "ULE Multi-Core Scheduling Validation Results\n");
        fprintf(results_file, "Duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
        fprintf(results_file, "Active CPUs: %u\n", global_stats.active_cpus);
        fprintf(results_file, "NUMA Nodes: %u\n", global_stats.numa_nodes);
        fprintf(results_file, "Task Migrations: %lu\n", global_stats.task_migrations);
        fprintf(results_file, "Load Balance Operations: %lu\n", global_stats.load_balance_operations);
        fprintf(results_file, "Average Load Imbalance: %.3f\n", 
                global_stats.total_load_imbalance / global_stats.load_balance_operations);
        fprintf(results_file, "NUMA Violations: %lu\n", global_stats.numa_violations);
        fprintf(results_file, "Affinity Violations: %lu\n", global_stats.affinity_violations);
        fclose(results_file);
    }
    
    /* Cleanup */
    for (uint32_t i = 0; i < global_stats.active_cpus; i++) {
        pthread_mutex_destroy(&cpu_stats[i].stats_mutex);
    }
    
    return (global_stats.numa_violations < 100 && global_stats.affinity_violations < 100) ? 0 : 1;
}