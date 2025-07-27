/* ULE-based SMP Scheduler Test Implementation
 * Simplified version for testing Dynamic BCRA formula
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include "ule_smp_scheduler_test.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <sys/time.h>

/* Test-friendly time management */
static uint64_t test_current_time_ms = 0;
static bool use_test_time = false;

/* Helper to get current time in milliseconds */
static uint64_t ule_get_current_time_ms(void)
{
    if (use_test_time) {
        return test_current_time_ms;
    }
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000 + (uint64_t)tv.tv_usec / 1000;
}

/* Test helper functions */
void ule_test_set_time(uint64_t time_ms) {
    test_current_time_ms = time_ms;
    use_test_time = true;
}

void ule_test_advance_time(uint64_t delta_ms) {
    test_current_time_ms += delta_ms;
}

void ule_test_use_real_time(void) {
    use_test_time = false;
}

/*
 * Growth function g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2
 */
double ule_growth_function(double threat_probability, double defense_effectiveness, double k1, double k2)
{
    assert(threat_probability >= 0.0 && threat_probability <= 1.0);
    assert(defense_effectiveness >= 0.0 && defense_effectiveness <= 1.0);
    assert(k1 > 0.0 && k2 > 0.0);
    
    double effectiveness_term = 2.0 - defense_effectiveness;
    double power_term = pow(effectiveness_term, k2);
    return 1.0 + k1 * threat_probability * power_term;
}

/*
 * Product of growth functions for all active threats: ∏_{i∈active} g(p_i, E_i)
 */
double ule_threat_product(ule_threat_data_t *threats, uint32_t num_threats)
{
    if (num_threats == 0 || threats == NULL) {
        return 1.0;  /* Default to 1.0 if no active threats */
    }
    
    double product = 1.0;
    for (uint32_t i = 0; i < num_threats; i++) {
        product *= ule_growth_function(threats[i].threat_probability,
                                     threats[i].defense_effectiveness,
                                     ULE_DYNAMIC_BCRA_K1,
                                     ULE_DYNAMIC_BCRA_K2);
    }
    return product;
}

/*
 * Nash equilibrium multiplier Π_nash
 */
double ule_nash_multiplier(ule_nash_components_t *nash)
{
    assert(nash != NULL);
    
    return ULE_NASH_WEIGHT_EQUILIBRIUM * nash->equilibrium_factor +
           ULE_NASH_WEIGHT_COMPETITION * nash->competition_factor +
           ULE_NASH_WEIGHT_REPUTATION * nash->reputation_factor +
           ULE_NASH_WEIGHT_BAYESIAN * nash->bayesian_factor +
           ULE_NASH_WEIGHT_SIGNALING * nash->signaling_factor;
}

/*
 * Full Dynamic BCRA formula implementation
 * CA(t) = max(10, min(C_max, C_base × ∑_{i∈active} g(p_i, E_i) × Π_nash))
 */
double ule_dynamic_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    
    /* Quick cache check first - avoid time call if cache is invalid */
    if (ca->cache_valid) {
        uint64_t current_time = ule_get_current_time_ms();
        if ((current_time - ca->cache_timestamp) < ULE_CACHE_VALIDITY_MS) {
            return ca->cached_result;
        }
        /* Cache expired - mark as invalid */
        ca->cache_valid = false;
    }
    
    /* Calculate threat component: ∏_{i∈active} g(p_i, E_i) */
    double threat_component = ule_threat_product(ca->active_threats, ca->num_active_threats);
    
    /* Calculate Nash equilibrium component: Π_nash */
    double nash_component = ule_nash_multiplier(&ca->nash_context);
    
    /* Calculate raw cost: CA₀ × exp(∏g(p_i, E_i)) × Π_nash */
    double raw_cost = (double)ca->base_cost * exp(threat_component) * nash_component;
    
    /* Apply upper bound: min(C_max, raw_cost) */
    double final_cost = fmin((double)ca->max_cost, raw_cost);
    
    /* Cache the result */
    ca->cached_result = final_cost;
    ca->cache_timestamp = ule_get_current_time_ms();
    ca->cache_valid = true;
    
    return final_cost;
}

/*
 * Simplified routing cost for backward compatibility
 */
double ule_simple_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    assert(ca->simple_attack_load >= 0.0 && ca->simple_attack_load <= 1.0);
    assert(ca->simple_defense_strength >= 0.0 && ca->simple_defense_strength <= 1.0);
    
    double cost_multiplier = 1.0 + ca->simple_attack_load * (2.0 - ca->simple_defense_strength);
    return (double)ca->base_cost * cost_multiplier;
}

/*
 * Primary routing cost function - uses full Dynamic BCRA formula
 */
double ule_calculate_routing_cost(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    return ule_dynamic_routing_cost(ca);
}

/*
 * Add a new threat to the CA routing context
 */
kern_return_t ule_add_threat(ule_route_ca_t *ca, double probability, double effectiveness)
{
    assert(ca != NULL);
    assert(probability >= 0.0 && probability <= 1.0);
    assert(effectiveness >= 0.0 && effectiveness <= 1.0);
    
    if (ca->num_active_threats >= ULE_MAX_ACTIVE_THREATS) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    ule_threat_data_t *threat = &ca->active_threats[ca->num_active_threats];
    threat->threat_probability = probability;
    threat->defense_effectiveness = effectiveness;
    threat->timestamp = ule_get_current_time_ms();
    
    /* Calculate decay time using Scott J. Guyton's formula */
    double alpha = 1.0;
    double beta = 2.0;
    double T_base = 365.0 * 24.0 * 60.0 * 60.0 * 1000.0;  /* 365 days in ms */
    threat->decay_time = T_base + alpha * pow(probability, beta) * T_base;
    
    ca->num_active_threats++;
    ule_invalidate_cache(ca);
    
    return KERN_SUCCESS;
}

/*
 * Remove expired threats from the CA routing context
 */
kern_return_t ule_remove_expired_threats(ule_route_ca_t *ca, uint64_t current_time)
{
    assert(ca != NULL);
    
    uint32_t active_count = 0;
    bool threats_removed = false;
    
    for (uint32_t i = 0; i < ca->num_active_threats; i++) {
        ule_threat_data_t *threat = &ca->active_threats[i];
        
        /* Check if threat has expired */
        if ((current_time - threat->timestamp) <= threat->decay_time) {
            /* Threat is still active - keep it */
            if (active_count != i) {
                ca->active_threats[active_count] = *threat;
            }
            active_count++;
        } else {
            threats_removed = true;
        }
    }
    
    ca->num_active_threats = active_count;
    
    if (threats_removed) {
        ule_invalidate_cache(ca);
    }
    
    return KERN_SUCCESS;
}

/*
 * Update Nash equilibrium components
 */
void ule_update_nash_components(ule_route_ca_t *ca, ule_nash_components_t *nash)
{
    assert(ca != NULL);
    assert(nash != NULL);
    
    ca->nash_context = *nash;
    ule_invalidate_cache(ca);
}

/*
 * Invalidate the routing cost cache
 */
void ule_invalidate_cache(ule_route_ca_t *ca)
{
    assert(ca != NULL);
    ca->cache_valid = false;
    ca->cache_timestamp = 0;
    ca->cached_result = 0.0;
}

/*
 * Check if cache is valid (within 1 second)
 */
bool ule_is_cache_valid(ule_route_ca_t *ca, uint64_t current_time)
{
    assert(ca != NULL);
    
    if (!ca->cache_valid) {
        return false;
    }
    
    return (current_time - ca->cache_timestamp) < ULE_CACHE_VALIDITY_MS;
}