/* Test Suite for Full Dynamic BCRA Formula Implementation
 * Tests Scott J. Guyton's complete Dynamic BCRA formula
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include "ule_smp_scheduler_test.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <time.h>

/* Test framework macros */
#define TEST_ASSERT(condition, message) \
    do { \
        if (!(condition)) { \
            printf("FAIL: %s - %s\n", __func__, message); \
            return 0; \
        } \
    } while(0)

#define TEST_ASSERT_DOUBLE_EQ(expected, actual, tolerance, message) \
    do { \
        if (fabs((expected) - (actual)) > (tolerance)) { \
            printf("FAIL: %s - %s (expected: %.6f, actual: %.6f)\n", \
                   __func__, message, expected, actual); \
            return 0; \
        } \
    } while(0)

#define TEST_PASS() \
    do { \
        printf("PASS: %s\n", __func__); \
        return 1; \
    } while(0)

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;

/* Helper to run a test */
#define RUN_TEST(test_func) \
    do { \
        tests_run++; \
        if (test_func()) { \
            tests_passed++; \
        } \
    } while(0)

/*
 * Test 1: Growth function basic properties
 * Verify g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2
 */
int test_growth_function_basic()
{
    double k1 = 1.5;
    double k2 = 2.0;
    
    /* Test with zero probability */
    double result = ule_growth_function(0.0, 0.5, k1, k2);
    TEST_ASSERT_DOUBLE_EQ(1.0, result, 1e-6, "Zero probability should give g = 1");
    
    /* Test with maximum probability and minimum effectiveness */
    result = ule_growth_function(1.0, 0.0, k1, k2);
    double expected = 1.0 + k1 * 1.0 * pow(2.0 - 0.0, k2);
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Max probability, min effectiveness");
    
    /* Test with known values: p=0.5, E=0.5 */
    result = ule_growth_function(0.5, 0.5, k1, k2);
    expected = 1.0 + 1.5 * 0.5 * pow(1.5, 2.0);
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Known test case p=0.5, E=0.5");
    
    TEST_PASS();
}

/*
 * Test 2: Growth function monotonicity
 * Higher probability should increase growth, lower effectiveness should increase growth
 */
int test_growth_function_monotonicity()
{
    double k1 = 1.5, k2 = 2.0;
    
    /* Test probability monotonicity */
    double g1 = ule_growth_function(0.2, 0.8, k1, k2);
    double g2 = ule_growth_function(0.8, 0.8, k1, k2);
    TEST_ASSERT(g2 > g1, "Higher probability should increase growth");
    
    /* Test effectiveness monotonicity (inverse) */
    double g3 = ule_growth_function(0.6, 0.9, k1, k2);
    double g4 = ule_growth_function(0.6, 0.1, k1, k2);
    TEST_ASSERT(g4 > g3, "Lower effectiveness should increase growth");
    
    TEST_PASS();
}

/*
 * Test 3: Threat sum calculation
 * Test ∑_{i∈active} g(p_i, E_i)
 */
int test_threat_sum()
{
    ule_threat_data_t threats[3];
    
    /* Setup test threats */
    threats[0].threat_probability = 0.2;
    threats[0].defense_effectiveness = 0.8;
    threats[1].threat_probability = 0.5;
    threats[1].defense_effectiveness = 0.6;
    threats[2].threat_probability = 0.8;
    threats[2].defense_effectiveness = 0.3;
    
    /* Test empty threat list */
    double sum = ule_threat_sum(NULL, 0);
    TEST_ASSERT_DOUBLE_EQ(1.0, sum, 1e-6, "Empty threat list should return 1.0");
    
    /* Test single threat */
    sum = ule_threat_sum(threats, 1);
    double expected = ule_growth_function(0.2, 0.8, ULE_DYNAMIC_BCRA_K1, ULE_DYNAMIC_BCRA_K2);
    TEST_ASSERT_DOUBLE_EQ(expected, sum, 1e-6, "Single threat sum");
    
    /* Test multiple threats */
    sum = ule_threat_sum(threats, 3);
    expected = ule_growth_function(0.2, 0.8, ULE_DYNAMIC_BCRA_K1, ULE_DYNAMIC_BCRA_K2) +
               ule_growth_function(0.5, 0.6, ULE_DYNAMIC_BCRA_K1, ULE_DYNAMIC_BCRA_K2) +
               ule_growth_function(0.8, 0.3, ULE_DYNAMIC_BCRA_K1, ULE_DYNAMIC_BCRA_K2);
    TEST_ASSERT_DOUBLE_EQ(expected, sum, 1e-6, "Multiple threats sum");
    
    TEST_PASS();
}

/*
 * Test 4: Nash equilibrium multiplier
 * Test Π_nash = w1*π_eq + w2*π_comp + w3*π_rep + w4*π_bayes + w5*π_signal
 */
int test_nash_multiplier()
{
    ule_nash_components_t nash;
    
    /* Test with unit values */
    nash.equilibrium_factor = 1.0;
    nash.competition_factor = 1.0;
    nash.reputation_factor = 1.0;
    nash.bayesian_factor = 1.0;
    nash.signaling_factor = 1.0;
    
    double result = ule_nash_multiplier(&nash);
    double expected = ULE_NASH_WEIGHT_EQUILIBRIUM + ULE_NASH_WEIGHT_COMPETITION + 
                     ULE_NASH_WEIGHT_REPUTATION + ULE_NASH_WEIGHT_BAYESIAN + 
                     ULE_NASH_WEIGHT_SIGNALING;
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Unit Nash components");
    
    /* Test with known values */
    nash.equilibrium_factor = 2.0;
    nash.competition_factor = 1.5;
    nash.reputation_factor = 0.8;
    nash.bayesian_factor = 1.2;
    nash.signaling_factor = 0.9;
    
    result = ule_nash_multiplier(&nash);
    expected = 0.3 * 2.0 + 0.2 * 1.5 + 0.2 * 0.8 + 0.15 * 1.2 + 0.15 * 0.9;
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Known Nash values");
    
    TEST_PASS();
}

/*
 * Test 5: Dynamic routing cost bounds
 * Test CA(t) = max(10, min(C_max, C_base × ∑g(p_i,E_i) × Π_nash))
 */
int test_dynamic_routing_cost_bounds()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    
    /* Initialize basic parameters */
    ca.base_cost = 100;
    ca.max_cost = 1000;
    ca.num_active_threats = 0;  /* No threats */
    ca.k1 = ULE_DYNAMIC_BCRA_K1;
    ca.k2 = ULE_DYNAMIC_BCRA_K2;
    
    /* Initialize Nash components to 1.0 */
    ca.nash_context.equilibrium_factor = 1.0;
    ca.nash_context.competition_factor = 1.0;
    ca.nash_context.reputation_factor = 1.0;
    ca.nash_context.bayesian_factor = 1.0;
    ca.nash_context.signaling_factor = 1.0;
    
    /* Test minimum bound (should be at least 10) */
    ca.base_cost = 1;  /* Very low base cost */
    double result = ule_dynamic_routing_cost(&ca);
    TEST_ASSERT(result >= ULE_DYNAMIC_BCRA_MIN_COST, "Should enforce minimum cost of 10");
    
    /* Test maximum bound */
    ca.base_cost = 2000;  /* Very high base cost */
    ca.max_cost = 500;    /* Lower max cost */
    result = ule_dynamic_routing_cost(&ca);
    TEST_ASSERT(result <= ca.max_cost, "Should enforce maximum cost bound");
    
    TEST_PASS();
}

/*
 * Test 6: Full Dynamic BCRA formula integration
 * Test complete formula with multiple threats and Nash components
 */
int test_full_dynamic_bcra_formula()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    
    /* Setup test case */
    ca.base_cost = 100;
    ca.max_cost = 2000;
    ca.k1 = ULE_DYNAMIC_BCRA_K1;
    ca.k2 = ULE_DYNAMIC_BCRA_K2;
    
    /* Add some threats */
    ca.num_active_threats = 2;
    ca.active_threats[0].threat_probability = 0.3;
    ca.active_threats[0].defense_effectiveness = 0.7;
    ca.active_threats[1].threat_probability = 0.6;
    ca.active_threats[1].defense_effectiveness = 0.4;
    
    /* Set Nash components */
    ca.nash_context.equilibrium_factor = 1.2;
    ca.nash_context.competition_factor = 0.9;
    ca.nash_context.reputation_factor = 1.1;
    ca.nash_context.bayesian_factor = 1.0;
    ca.nash_context.signaling_factor = 0.8;
    
    /* Calculate manually for verification */
    double threat_sum = ule_threat_sum(ca.active_threats, ca.num_active_threats);
    double nash_mult = ule_nash_multiplier(&ca.nash_context);
    double raw_cost = ca.base_cost * threat_sum * nash_mult;
    double expected = fmax(ULE_DYNAMIC_BCRA_MIN_COST, fmin(ca.max_cost, raw_cost));
    
    /* Test the full formula */
    double result = ule_dynamic_routing_cost(&ca);
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Full Dynamic BCRA formula");
    
    /* Verify it's greater than simple formula result */
    ca.simple_attack_load = 0.3;
    ca.simple_defense_strength = 0.7;
    double simple_result = ule_simple_routing_cost(&ca);
    
    printf("Dynamic BCRA result: %.2f, Simple result: %.2f\n", result, simple_result);
    TEST_ASSERT(result > simple_result, "Dynamic BCRA should be more sophisticated");
    
    TEST_PASS();
}

/*
 * Test 7: Threat management functions
 */
int test_threat_management()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    ca.num_active_threats = 0;
    
    /* Test adding threats */
    kern_return_t kr = ule_add_threat(&ca, 0.5, 0.8);
    TEST_ASSERT(kr == KERN_SUCCESS, "Should successfully add threat");
    TEST_ASSERT(ca.num_active_threats == 1, "Threat count should increase");
    
    /* Add more threats */
    ule_add_threat(&ca, 0.3, 0.9);
    ule_add_threat(&ca, 0.7, 0.5);
    TEST_ASSERT(ca.num_active_threats == 3, "Should have 3 threats");
    
    /* Test threat overflow */
    for (int i = 0; i < ULE_MAX_ACTIVE_THREATS; i++) {
        ule_add_threat(&ca, 0.1, 0.9);
    }
    kr = ule_add_threat(&ca, 0.1, 0.9);  /* Should fail */
    TEST_ASSERT(kr == KERN_RESOURCE_SHORTAGE, "Should reject when threat list is full");
    
    /* Test threat expiration (simulate future time) */
    uint64_t future_time = UINT64_MAX;  /* Far future */
    kr = ule_remove_expired_threats(&ca, future_time);
    TEST_ASSERT(kr == KERN_SUCCESS, "Should successfully remove expired threats");
    TEST_ASSERT(ca.num_active_threats == 0, "All threats should be expired");
    
    TEST_PASS();
}

/*
 * Test 8: Cache functionality
 */
int test_cache_functionality()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    
    /* Initialize CA */
    ca.base_cost = 100;
    ca.max_cost = 1000;
    ca.num_active_threats = 1;
    ca.active_threats[0].threat_probability = 0.5;
    ca.active_threats[0].defense_effectiveness = 0.7;
    ca.nash_context.equilibrium_factor = 1.0;
    ca.nash_context.competition_factor = 1.0;
    ca.nash_context.reputation_factor = 1.0;
    ca.nash_context.bayesian_factor = 1.0;
    ca.nash_context.signaling_factor = 1.0;
    
    /* First calculation should populate cache */
    double result1 = ule_dynamic_routing_cost(&ca);
    TEST_ASSERT(ca.cache_valid, "Cache should be valid after calculation");
    
    /* Second calculation should use cache (same result) */
    double result2 = ule_dynamic_routing_cost(&ca);
    TEST_ASSERT_DOUBLE_EQ(result1, result2, 1e-10, "Cached results should be identical");
    
    /* Invalidate cache and verify */
    ule_invalidate_cache(&ca);
    TEST_ASSERT(!ca.cache_valid, "Cache should be invalid after invalidation");
    
    /* Adding threat should invalidate cache */
    ca.cache_valid = true;  /* Manually set valid */
    ule_add_threat(&ca, 0.3, 0.8);
    TEST_ASSERT(!ca.cache_valid, "Adding threat should invalidate cache");
    
    TEST_PASS();
}

/*
 * Test 9: Performance comparison
 * Compare Dynamic BCRA vs Simple formula performance
 */
int test_performance_comparison()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    
    /* Setup complex scenario */
    ca.base_cost = 100;
    ca.max_cost = 1000;
    ca.num_active_threats = 5;
    ca.simple_attack_load = 0.5;
    ca.simple_defense_strength = 0.7;
    
    for (int i = 0; i < 5; i++) {
        ca.active_threats[i].threat_probability = 0.1 + i * 0.2;
        ca.active_threats[i].defense_effectiveness = 0.9 - i * 0.1;
    }
    
    ca.nash_context.equilibrium_factor = 1.2;
    ca.nash_context.competition_factor = 0.8;
    ca.nash_context.reputation_factor = 1.1;
    ca.nash_context.bayesian_factor = 0.9;
    ca.nash_context.signaling_factor = 1.0;
    
    /* Time simple formula */
    clock_t start = clock();
    for (int i = 0; i < 10000; i++) {
        ule_simple_routing_cost(&ca);
    }
    clock_t simple_time = clock() - start;
    
    /* Time dynamic formula (first run - no cache) */
    ule_invalidate_cache(&ca);
    start = clock();
    for (int i = 0; i < 10000; i++) {
        ule_invalidate_cache(&ca);  /* Force recalculation each time */
        ule_dynamic_routing_cost(&ca);
    }
    clock_t dynamic_time = clock() - start;
    
    /* Time dynamic formula with cache - use test time for consistent caching */
    ule_test_set_time(1000);  /* Set a fixed time */
    ule_dynamic_routing_cost(&ca);  /* Prime the cache */
    
    start = clock();
    for (int i = 0; i < 10000; i++) {
        ule_dynamic_routing_cost(&ca);  /* Should use cache consistently */
    }
    clock_t cached_time = clock() - start;
    
    ule_test_use_real_time();  /* Restore real time */
    
    printf("Performance results:\n");
    printf("  Simple formula: %ld cycles\n", simple_time);
    printf("  Dynamic formula (no cache): %ld cycles\n", dynamic_time);
    printf("  Dynamic formula (cached): %ld cycles\n", cached_time);
    printf("  Overhead ratio: %.2fx\n", (double)dynamic_time / simple_time);
    printf("  Cache speedup: %.2fx\n", (double)dynamic_time / cached_time);
    
    /* Verify overhead is reasonable (less than 100x) */
    double overhead = (double)dynamic_time / simple_time;
    TEST_ASSERT(overhead < 100.0, "Dynamic formula overhead should be reasonable");
    
    /* Verify cache provides significant speedup */
    double cache_speedup = (double)dynamic_time / cached_time;
    TEST_ASSERT(cache_speedup > 5.0, "Cache should provide significant speedup (>5x)");
    
    TEST_PASS();
}

/*
 * Test 10: Backward compatibility
 * Ensure simple formula still works correctly
 */
int test_backward_compatibility()
{
    ule_route_ca_t ca;
    memset(&ca, 0, sizeof(ca));
    
    /* Test cases from original simple formula */
    ca.base_cost = 100;
    ca.simple_attack_load = 0.0;
    ca.simple_defense_strength = 1.0;
    
    double result = ule_simple_routing_cost(&ca);
    TEST_ASSERT_DOUBLE_EQ(100.0, result, 1e-6, "Clean user should get base cost");
    
    /* Test with attack load */
    ca.simple_attack_load = 0.5;
    ca.simple_defense_strength = 0.8;
    result = ule_simple_routing_cost(&ca);
    double expected = 100.0 * (1.0 + 0.5 * (2.0 - 0.8));
    TEST_ASSERT_DOUBLE_EQ(expected, result, 1e-6, "Simple formula calculation");
    
    /* Test primary interface still works */
    result = ule_calculate_routing_cost(&ca);
    TEST_ASSERT(result > 0, "Primary interface should return positive cost");
    
    TEST_PASS();
}

/*
 * Main test runner
 */
int main(void)
{
    printf("=== Dynamic BCRA Formula Test Suite ===\n");
    printf("Testing Scott J. Guyton's full Dynamic BCRA implementation\n\n");
    
    /* Run all tests */
    RUN_TEST(test_growth_function_basic);
    RUN_TEST(test_growth_function_monotonicity);
    RUN_TEST(test_threat_sum);
    RUN_TEST(test_nash_multiplier);
    RUN_TEST(test_dynamic_routing_cost_bounds);
    RUN_TEST(test_full_dynamic_bcra_formula);
    RUN_TEST(test_threat_management);
    RUN_TEST(test_cache_functionality);
    RUN_TEST(test_performance_comparison);
    RUN_TEST(test_backward_compatibility);
    
    /* Print results */
    printf("\n=== Test Results ===\n");
    printf("Tests run: %d\n", tests_run);
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_run - tests_passed);
    printf("Success rate: %.1f%%\n", (double)tests_passed / tests_run * 100);
    
    if (tests_passed == tests_run) {
        printf("\n✅ ALL TESTS PASSED - Full Dynamic BCRA formula implementation verified!\n");
        printf("Ready for production deployment.\n");
        return 0;
    } else {
        printf("\n❌ SOME TESTS FAILED - Review implementation before deployment.\n");
        return 1;
    }
}