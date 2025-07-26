#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <stdint.h>
#include <string.h>

/* Benchmark to measure overhead of simple vs complex CA formula */

#define ITERATIONS 1000000
#define MAX_ACTIVE_THREATS 10

typedef struct {
    double p;  // probability of malicious intent
    double E;  // defense effectiveness
} threat_data_t;

typedef struct {
    uint32_t base_cost;
    double attack_load;
    double defense_strength;
    
    // Complex formula components
    uint32_t max_cost;
    threat_data_t active_threats[MAX_ACTIVE_THREATS];
    int num_active_threats;
    double nash_multiplier;
} ca_data_t;

/* Simple formula (current implementation) */
double simple_ca_formula(ca_data_t *ca) {
    return ca->base_cost * (1.0 + ca->attack_load * (2.0 - ca->defense_strength));
}

/* Growth function g(p, E) for complex formula */
double growth_function(double p, double E) {
    // g(p,E) = 1 + k1 * p * (2 - E)^k2
    const double k1 = 1.5;
    const double k2 = 2.0;
    return 1.0 + k1 * p * pow(2.0 - E, k2);
}

/* Complex formula (your original Dynamic BCRA) */
double complex_ca_formula(ca_data_t *ca) {
    // Calculate sum of growth functions for active threats
    double threat_sum = 0.0;
    for (int i = 0; i < ca->num_active_threats; i++) {
        threat_sum += growth_function(ca->active_threats[i].p, 
                                    ca->active_threats[i].E);
    }
    
    // CA(t) = max(10, min(C_max, C_base * sum * nash))
    double raw_cost = ca->base_cost * threat_sum * ca->nash_multiplier;
    double bounded_cost = fmin(ca->max_cost, raw_cost);
    return fmax(10.0, bounded_cost);
}

/* Cached version with 90% hit rate simulation */
static double cached_result = 0.0;
static int cache_hits = 0;
static int cache_total = 0;

double cached_ca_formula(ca_data_t *ca) {
    cache_total++;
    
    // Simulate 90% cache hit rate
    if (cache_total % 10 != 0) {
        cache_hits++;
        return cached_result;
    }
    
    // Cache miss - calculate and store
    cached_result = complex_ca_formula(ca);
    return cached_result;
}

/* Hybrid approach - use complex only for "strategic" decisions */
double hybrid_ca_formula(ca_data_t *ca, int is_strategic) {
    if (is_strategic) {
        return complex_ca_formula(ca);
    } else {
        return simple_ca_formula(ca);
    }
}

/* Initialize test data */
void init_test_data(ca_data_t *ca) {
    ca->base_cost = 100;
    ca->attack_load = 0.3;
    ca->defense_strength = 0.8;
    ca->max_cost = 1000;
    ca->nash_multiplier = 1.2;
    ca->num_active_threats = 5;
    
    for (int i = 0; i < ca->num_active_threats; i++) {
        ca->active_threats[i].p = 0.1 + (i * 0.15);
        ca->active_threats[i].E = 0.5 + (i * 0.1);
    }
}

/* Benchmark function */
typedef double (*formula_func_t)(ca_data_t *);

void benchmark_formula(const char *name, formula_func_t func, ca_data_t *ca) {
    struct timespec start, end;
    double total_time, calls_per_sec;
    double result;
    
    printf("Benchmarking %s formula...\n", name);
    
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    for (int i = 0; i < ITERATIONS; i++) {
        result = func(ca);
        // Prevent compiler optimization
        asm volatile("" : : "g" (result) : "memory");
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    total_time = (end.tv_sec - start.tv_sec) + 
                 (end.tv_nsec - start.tv_nsec) / 1e9;
    calls_per_sec = ITERATIONS / total_time;
    
    printf("  Result: %.2f\n", result);
    printf("  Time: %.4f seconds\n", total_time);
    printf("  Rate: %.0f calls/second\n", calls_per_sec);
    printf("  Overhead: %.2f ns/call\n", (total_time * 1e9) / ITERATIONS);
    printf("\n");
}

/* Simulate message routing load */
void simulate_message_load(ca_data_t *ca) {
    printf("=== Message Routing Load Simulation ===\n");
    
    const int message_rates[] = {1000, 10000, 50000, 100000};
    const int num_rates = sizeof(message_rates) / sizeof(message_rates[0]);
    
    for (int i = 0; i < num_rates; i++) {
        int rate = message_rates[i];
        printf("\nSimulating %d messages/second:\n", rate);
        
        // Calculate overhead for different approaches
        double simple_overhead = rate * 4; // 4 cycles per call
        double complex_overhead = rate * 100; // ~100 cycles per call
        double cached_overhead = rate * 10; // 90% cache hit, 10 cycles average
        
        printf("  Simple formula: %.0f cycles/sec (%.3f%% CPU @ 1GHz)\n", 
               simple_overhead, (simple_overhead / 1e9) * 100);
        printf("  Complex formula: %.0f cycles/sec (%.3f%% CPU @ 1GHz)\n", 
               complex_overhead, (complex_overhead / 1e9) * 100);
        printf("  Cached complex: %.0f cycles/sec (%.3f%% CPU @ 1GHz)\n", 
               cached_overhead, (cached_overhead / 1e9) * 100);
    }
}

int main() {
    ca_data_t ca_data;
    init_test_data(&ca_data);
    
    printf("CA Formula Overhead Analysis\n");
    printf("============================\n\n");
    
    printf("Test configuration:\n");
    printf("  Iterations: %d\n", ITERATIONS);
    printf("  Active threats: %d\n", ca_data.num_active_threats);
    printf("  Base cost: %d\n", ca_data.base_cost);
    printf("\n");
    
    // Benchmark different approaches
    benchmark_formula("Simple", simple_ca_formula, &ca_data);
    benchmark_formula("Complex", complex_ca_formula, &ca_data);
    benchmark_formula("Cached", cached_ca_formula, &ca_data);
    
    printf("Cache statistics:\n");
    printf("  Hit rate: %.1f%% (%d/%d)\n", 
           (cache_hits * 100.0) / cache_total, cache_hits, cache_total);
    printf("\n");
    
    // Hybrid simulation
    printf("=== Hybrid Approach Simulation ===\n");
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    for (int i = 0; i < ITERATIONS; i++) {
        // 10% strategic decisions use complex formula
        int is_strategic = (i % 10 == 0);
        double result = hybrid_ca_formula(&ca_data, is_strategic);
        asm volatile("" : : "g" (result) : "memory");
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double hybrid_time = (end.tv_sec - start.tv_sec) + 
                         (end.tv_nsec - start.tv_nsec) / 1e9;
    
    printf("Hybrid (10%% complex): %.4f seconds, %.0f calls/sec\n", 
           hybrid_time, ITERATIONS / hybrid_time);
    printf("\n");
    
    simulate_message_load(&ca_data);
    
    printf("\n=== Recommendations ===\n");
    printf("1. Simple formula: Use for high-frequency routing decisions\n");
    printf("2. Complex formula: Use for strategic server selection\n");  
    printf("3. Caching: Reduces complex formula overhead by 90%%\n");
    printf("4. Hybrid approach: Best balance of security and performance\n");
    
    return 0;
}