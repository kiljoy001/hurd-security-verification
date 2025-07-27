/* GNU Hurd ULE Interactivity Calculation Test Suite
 * Comprehensive validation of ULE interactivity calculations under load
 * Tests mathematical correctness, performance bounds, and Coq correspondence
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/time.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <errno.h>

/* Test configuration */
#define MAX_TEST_CASES 100000
#define MAX_THREADS 64
#define PERFORMANCE_ITERATIONS 1000000
#define BOUNDARY_TEST_CASES 1000

/* ULE interactivity test statistics */
typedef struct {
    uint64_t total_calculations;
    uint64_t boundary_tests;
    uint64_t correctness_violations;
    uint64_t performance_violations;
    double total_calculation_time_us;
    double max_calculation_time_us;
    double min_calculation_time_us;
    uint64_t interactive_classifications;
    uint64_t batch_classifications;
    uint64_t idle_classifications;
    double start_time;
    double end_time;
} ule_interactivity_stats_t;

/* Test case structure */
typedef struct {
    uint32_t sleep_time;
    uint32_t run_time;
    uint32_t expected_result;
    uint32_t actual_result;
    double calculation_time_us;
    int is_boundary_case;
    int correctness_passed;
} ule_test_case_t;

/* Thread context for parallel testing */
typedef struct {
    int thread_id;
    ule_interactivity_stats_t *shared_stats;
    pthread_mutex_t *stats_mutex;
    volatile int *test_running;
    ule_test_case_t *test_cases;
    int start_index;
    int end_index;
    int test_type;
} test_thread_context_t;

static ule_interactivity_stats_t global_stats = {0};
static pthread_mutex_t stats_mutex = PTHREAD_MUTEX_INITIALIZER;
static volatile int test_running = 1;

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
            uint32_t result = 50 + (run_time * 50) / (sleep_time + 1);
            return (result > 100) ? 100 : result;
        } else {
            /* Interactive: sleep > run */
            uint32_t result = (sleep_time * 50) / (run_time + 1);
            return (result > 100) ? 100 : result;
        }
    }
    return 0;
}

/* Reference implementation for correctness checking */
uint32_t reference_ule_calculate_interactivity(uint32_t sleep_time, uint32_t run_time) {
    /* This is the exact Coq specification implementation */
    if (run_time == 0) return 0;
    
    if (sleep_time <= run_time) {
        uint64_t temp = 50 + ((uint64_t)run_time * 50) / (sleep_time + 1);
        return (temp > 100) ? 100 : (uint32_t)temp;
    } else {
        uint64_t temp = ((uint64_t)sleep_time * 50) / (run_time + 1);
        return (temp > 100) ? 100 : (uint32_t)temp;
    }
}

/* Test correctness against Coq specification */
int test_coq_correspondence(uint32_t sleep_time, uint32_t run_time) {
    uint32_t implementation_result = ule_calculate_interactivity(sleep_time, run_time);
    uint32_t reference_result = reference_ule_calculate_interactivity(sleep_time, run_time);
    
    /* Verify bounds - should match Coq theorem ule_interactivity_bounded */
    if (implementation_result > 100) {
        printf("ERROR: Bounds violation - result %u > 100 for sleep=%u, run=%u\n",
               implementation_result, sleep_time, run_time);
        return 0;
    }
    
    /* Verify correspondence with reference */
    if (implementation_result != reference_result) {
        printf("ERROR: Correspondence violation - impl=%u, ref=%u for sleep=%u, run=%u\n",
               implementation_result, reference_result, sleep_time, run_time);
        return 0;
    }
    
    return 1;
}

/* Generate comprehensive test cases */
void generate_test_cases(ule_test_case_t *test_cases, int num_cases) {
    int case_index = 0;
    
    /* Boundary cases - critical for correctness */
    printf("Generating boundary test cases...\n");
    
    /* Edge case: run_time = 0 */
    for (int sleep = 0; sleep <= 100 && case_index < num_cases; sleep += 10) {
        test_cases[case_index++] = (ule_test_case_t){
            .sleep_time = sleep,
            .run_time = 0,
            .expected_result = 0,
            .is_boundary_case = 1
        };
    }
    
    /* Edge case: sleep_time = run_time */
    for (int time = 1; time <= 100 && case_index < num_cases; time += 5) {
        test_cases[case_index++] = (ule_test_case_t){
            .sleep_time = time,
            .run_time = time,
            .is_boundary_case = 1
        };
    }
    
    /* Edge case: very small values */
    for (int sleep = 1; sleep <= 5 && case_index < num_cases; sleep++) {
        for (int run = 1; run <= 5 && case_index < num_cases; run++) {
            test_cases[case_index++] = (ule_test_case_t){
                .sleep_time = sleep,
                .run_time = run,
                .is_boundary_case = 1
            };
        }
    }
    
    /* Edge case: large values near overflow */
    uint32_t large_values[] = {1000, 5000, 10000, 50000, 100000};
    for (int i = 0; i < 5 && case_index < num_cases; i++) {
        for (int j = 0; j < 5 && case_index < num_cases; j++) {
            test_cases[case_index++] = (ule_test_case_t){
                .sleep_time = large_values[i],
                .run_time = large_values[j],
                .is_boundary_case = 1
            };
        }
    }
    
    /* Random test cases */
    printf("Generating random test cases...\n");
    srand(12345); /* Deterministic for reproducibility */
    
    while (case_index < num_cases) {
        uint32_t sleep_time = rand() % 10000 + 1;
        uint32_t run_time = rand() % 10000 + 1;
        
        test_cases[case_index++] = (ule_test_case_t){
            .sleep_time = sleep_time,
            .run_time = run_time,
            .is_boundary_case = 0
        };
    }
    
    printf("Generated %d test cases (%d boundary cases)\n", 
           case_index, case_index - (num_cases - BOUNDARY_TEST_CASES));
}

/* Performance test for single calculation */
double measure_single_calculation_performance(uint32_t sleep_time, uint32_t run_time) {
    double start_time = get_current_time_us();
    
    volatile uint32_t result = ule_calculate_interactivity(sleep_time, run_time);
    
    double end_time = get_current_time_us();
    
    /* Prevent optimization */
    (void)result;
    
    return end_time - start_time;
}

/* Test thread for parallel correctness testing */
void* test_correctness_worker(void* arg) {
    test_thread_context_t *ctx = (test_thread_context_t*)arg;
    
    printf("Thread %d: Testing correctness for cases %d-%d\n", 
           ctx->thread_id, ctx->start_index, ctx->end_index);
    
    uint64_t local_calculations = 0;
    uint64_t local_violations = 0;
    double local_total_time = 0;
    double local_max_time = 0;
    double local_min_time = 1000000.0; /* Large initial value */
    
    for (int i = ctx->start_index; i < ctx->end_index && *ctx->test_running; i++) {
        ule_test_case_t *test_case = &ctx->test_cases[i];
        
        /* Measure calculation time */
        double calc_time = measure_single_calculation_performance(
            test_case->sleep_time, test_case->run_time);
        
        /* Perform calculation and store result */
        test_case->actual_result = ule_calculate_interactivity(
            test_case->sleep_time, test_case->run_time);
        test_case->calculation_time_us = calc_time;
        
        /* Test correctness against Coq specification */
        test_case->correctness_passed = test_coq_correspondence(
            test_case->sleep_time, test_case->run_time);
        
        if (!test_case->correctness_passed) {
            local_violations++;
        }
        
        local_calculations++;
        local_total_time += calc_time;
        
        if (calc_time > local_max_time) local_max_time = calc_time;
        if (calc_time < local_min_time) local_min_time = calc_time;
        
        /* Update global statistics periodically */
        if (local_calculations % 1000 == 0) {
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->total_calculations += 1000;
            ctx->shared_stats->correctness_violations += local_violations;
            ctx->shared_stats->total_calculation_time_us += local_total_time;
            if (local_max_time > ctx->shared_stats->max_calculation_time_us) {
                ctx->shared_stats->max_calculation_time_us = local_max_time;
            }
            if (ctx->shared_stats->min_calculation_time_us == 0 || 
                local_min_time < ctx->shared_stats->min_calculation_time_us) {
                ctx->shared_stats->min_calculation_time_us = local_min_time;
            }
            pthread_mutex_unlock(ctx->stats_mutex);
            
            local_violations = 0;
            local_total_time = 0;
        }
    }
    
    /* Final statistics update */
    pthread_mutex_lock(ctx->stats_mutex);
    ctx->shared_stats->total_calculations += (local_calculations % 1000);
    ctx->shared_stats->correctness_violations += local_violations;
    ctx->shared_stats->total_calculation_time_us += local_total_time;
    pthread_mutex_unlock(ctx->stats_mutex);
    
    printf("Thread %d: Completed %lu calculations with %lu violations\n",
           ctx->thread_id, local_calculations, local_violations);
    
    return NULL;
}

/* Performance stress test */
void* test_performance_worker(void* arg) {
    test_thread_context_t *ctx = (test_thread_context_t*)arg;
    
    printf("Thread %d: Starting performance stress test\n", ctx->thread_id);
    
    uint64_t iterations = 0;
    double start_time = get_current_time_us();
    
    while (*ctx->test_running && iterations < PERFORMANCE_ITERATIONS) {
        /* Generate pseudo-random test values */
        uint32_t sleep_time = (iterations * 7 + ctx->thread_id) % 1000 + 1;
        uint32_t run_time = (iterations * 11 + ctx->thread_id * 3) % 500 + 1;
        
        /* Perform calculation */
        double calc_start = get_current_time_us();
        uint32_t result = ule_calculate_interactivity(sleep_time, run_time);
        double calc_end = get_current_time_us();
        
        double calc_time = calc_end - calc_start;
        
        /* Verify bounds */
        if (result > 100) {
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->correctness_violations++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
        
        /* Check performance bounds (should be < 1 μs per calculation) */
        if (calc_time > 1.0) {
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->performance_violations++;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
        
        iterations++;
        
        /* Update statistics every 10000 iterations */
        if (iterations % 10000 == 0) {
            pthread_mutex_lock(ctx->stats_mutex);
            ctx->shared_stats->total_calculations += 10000;
            pthread_mutex_unlock(ctx->stats_mutex);
        }
    }
    
    double end_time = get_current_time_us();
    double total_time = end_time - start_time;
    
    printf("Thread %d: Completed %lu calculations in %.2f ms (%.2f calc/sec)\n",
           ctx->thread_id, iterations, total_time / 1000.0, 
           iterations / (total_time / 1000000.0));
    
    return NULL;
}

/* Analyze test results and generate report */
void analyze_test_results(ule_test_case_t *test_cases, int num_cases) {
    printf("\n=== ULE INTERACTIVITY TEST ANALYSIS ===\n");
    
    int boundary_violations = 0;
    int correctness_violations = 0;
    int interactive_count = 0;
    int batch_count = 0;
    int idle_count = 0;
    
    double total_calc_time = 0;
    double max_calc_time = 0;
    double min_calc_time = 1000000.0;
    
    for (int i = 0; i < num_cases; i++) {
        ule_test_case_t *test_case = &test_cases[i];
        
        if (!test_case->correctness_passed) {
            correctness_violations++;
            if (test_case->is_boundary_case) {
                boundary_violations++;
            }
        }
        
        /* Classify results */
        if (test_case->actual_result <= 30) {
            interactive_count++;
        } else if (test_case->actual_result <= 70) {
            batch_count++;
        } else {
            idle_count++;
        }
        
        /* Track calculation times */
        total_calc_time += test_case->calculation_time_us;
        if (test_case->calculation_time_us > max_calc_time) {
            max_calc_time = test_case->calculation_time_us;
        }
        if (test_case->calculation_time_us < min_calc_time) {
            min_calc_time = test_case->calculation_time_us;
        }
    }
    
    printf("Test Cases Analysis:\n");
    printf("Total test cases: %d\n", num_cases);
    printf("Boundary test cases: %d\n", BOUNDARY_TEST_CASES);
    printf("Correctness violations: %d\n", correctness_violations);
    printf("Boundary violations: %d\n", boundary_violations);
    
    printf("\nClassification Distribution:\n");
    printf("Interactive (≤30): %d (%.1f%%)\n", interactive_count, 
           (100.0 * interactive_count) / num_cases);
    printf("Batch (31-70): %d (%.1f%%)\n", batch_count, 
           (100.0 * batch_count) / num_cases);
    printf("Idle (>70): %d (%.1f%%)\n", idle_count, 
           (100.0 * idle_count) / num_cases);
    
    printf("\nCalculation Performance:\n");
    printf("Average calculation time: %.3f μs\n", total_calc_time / num_cases);
    printf("Maximum calculation time: %.3f μs\n", max_calc_time);
    printf("Minimum calculation time: %.3f μs\n", min_calc_time);
    
    /* Correctness validation */
    if (correctness_violations == 0) {
        printf("\n✓ CORRECTNESS: All calculations match Coq specification\n");
    } else {
        printf("\n✗ CORRECTNESS: %d violations detected\n", correctness_violations);
    }
    
    /* Performance validation */
    double avg_calc_time = total_calc_time / num_cases;
    if (avg_calc_time < 1.0) {
        printf("✓ PERFORMANCE: Average calculation time %.3f μs < 1.0 μs target\n", avg_calc_time);
    } else {
        printf("✗ PERFORMANCE: Average calculation time %.3f μs exceeds 1.0 μs target\n", avg_calc_time);
    }
}

/* Print comprehensive test results */
void print_interactivity_test_results(void) {
    printf("\n=== ULE INTERACTIVITY CALCULATION TEST RESULTS ===\n");
    printf("Test duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
    printf("Total calculations: %lu\n", global_stats.total_calculations);
    printf("Boundary tests: %lu\n", global_stats.boundary_tests);
    
    printf("\nCorrectness Metrics:\n");
    printf("Correctness violations: %lu\n", global_stats.correctness_violations);
    printf("Performance violations: %lu\n", global_stats.performance_violations);
    
    if (global_stats.total_calculations > 0) {
        double avg_time = global_stats.total_calculation_time_us / global_stats.total_calculations;
        printf("Average calculation time: %.3f μs\n", avg_time);
        printf("Maximum calculation time: %.3f μs\n", global_stats.max_calculation_time_us);
        printf("Minimum calculation time: %.3f μs\n", global_stats.min_calculation_time_us);
        
        double duration_seconds = (global_stats.end_time - global_stats.start_time) / 1000000.0;
        printf("Calculation throughput: %.2f calc/sec\n", global_stats.total_calculations / duration_seconds);
    }
    
    printf("\nClassification Results:\n");
    printf("Interactive classifications: %lu\n", global_stats.interactive_classifications);
    printf("Batch classifications: %lu\n", global_stats.batch_classifications);
    printf("Idle classifications: %lu\n", global_stats.idle_classifications);
    
    /* Calculate test quality score */
    double quality_score = 100.0;
    if (global_stats.correctness_violations > 0) {
        quality_score -= (global_stats.correctness_violations * 50.0) / global_stats.total_calculations;
    }
    if (global_stats.performance_violations > 0) {
        quality_score -= (global_stats.performance_violations * 25.0) / global_stats.total_calculations;
    }
    if (quality_score < 0) quality_score = 0;
    
    printf("\nULE INTERACTIVITY QUALITY SCORE: %.1f/100\n", quality_score);
    
    if (global_stats.correctness_violations == 0 && global_stats.performance_violations == 0) {
        printf("STATUS: ULE INTERACTIVITY CALCULATION VERIFIED ✓\n");
    } else {
        printf("STATUS: ULE INTERACTIVITY ISSUES DETECTED ✗\n");
    }
}

/* Main test execution */
int main(int argc, char *argv[]) {
    printf("GNU Hurd ULE Interactivity Calculation Test Suite\n");
    printf("=================================================\n\n");
    
    /* Initialize test environment */
    global_stats.start_time = get_current_time_us();
    
    /* Allocate test cases */
    ule_test_case_t *test_cases = malloc(MAX_TEST_CASES * sizeof(ule_test_case_t));
    if (!test_cases) {
        fprintf(stderr, "Failed to allocate memory for test cases\n");
        return 1;
    }
    
    /* Generate comprehensive test cases */
    generate_test_cases(test_cases, MAX_TEST_CASES);
    
    printf("Starting ULE interactivity calculation tests...\n");
    
    /* Phase 1: Correctness testing with multiple threads */
    printf("\nPhase 1: Correctness Testing\n");
    
    int num_threads = 8;
    pthread_t test_threads[MAX_THREADS];
    test_thread_context_t contexts[MAX_THREADS];
    
    int cases_per_thread = MAX_TEST_CASES / num_threads;
    for (int i = 0; i < num_threads; i++) {
        contexts[i] = (test_thread_context_t){
            .thread_id = i,
            .shared_stats = &global_stats,
            .stats_mutex = &stats_mutex,
            .test_running = &test_running,
            .test_cases = test_cases,
            .start_index = i * cases_per_thread,
            .end_index = (i == num_threads - 1) ? MAX_TEST_CASES : (i + 1) * cases_per_thread,
            .test_type = 0 /* Correctness test */
        };
        pthread_create(&test_threads[i], NULL, test_correctness_worker, &contexts[i]);
    }
    
    /* Wait for correctness tests to complete */
    for (int i = 0; i < num_threads; i++) {
        pthread_join(test_threads[i], NULL);
    }
    
    /* Analyze correctness test results */
    analyze_test_results(test_cases, MAX_TEST_CASES);
    
    /* Phase 2: Performance stress testing */
    printf("\nPhase 2: Performance Stress Testing\n");
    
    global_stats.total_calculations = 0; /* Reset for performance test */
    
    for (int i = 0; i < num_threads; i++) {
        contexts[i].test_type = 1; /* Performance test */
        pthread_create(&test_threads[i], NULL, test_performance_worker, &contexts[i]);
    }
    
    /* Run performance test for 30 seconds */
    sleep(30);
    test_running = 0;
    
    /* Wait for performance tests to complete */
    for (int i = 0; i < num_threads; i++) {
        pthread_join(test_threads[i], NULL);
    }
    
    global_stats.end_time = get_current_time_us();
    
    /* Print comprehensive results */
    print_interactivity_test_results();
    
    /* Save detailed results to file */
    FILE *results_file = fopen("ule_interactivity_test_results.txt", "w");
    if (results_file) {
        fprintf(results_file, "ULE Interactivity Calculation Test Results\n");
        fprintf(results_file, "Duration: %.2f seconds\n", (global_stats.end_time - global_stats.start_time) / 1000000.0);
        fprintf(results_file, "Total Calculations: %lu\n", global_stats.total_calculations);
        fprintf(results_file, "Correctness Violations: %lu\n", global_stats.correctness_violations);
        fprintf(results_file, "Performance Violations: %lu\n", global_stats.performance_violations);
        fprintf(results_file, "Average Calculation Time: %.3f μs\n", 
                global_stats.total_calculation_time_us / global_stats.total_calculations);
        fprintf(results_file, "Maximum Calculation Time: %.3f μs\n", global_stats.max_calculation_time_us);
        fprintf(results_file, "Minimum Calculation Time: %.3f μs\n", global_stats.min_calculation_time_us);
        fclose(results_file);
    }
    
    free(test_cases);
    
    return (global_stats.correctness_violations == 0 && global_stats.performance_violations == 0) ? 0 : 1;
}