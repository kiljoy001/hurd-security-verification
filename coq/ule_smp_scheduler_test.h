/* ULE-based SMP Scheduler Test Header
 * Test-friendly version without kernel dependencies
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _ULE_SMP_SCHEDULER_TEST_H_
#define _ULE_SMP_SCHEDULER_TEST_H_

#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>

/* Test-friendly type definitions */
typedef int kern_return_t;
#define KERN_SUCCESS 0
#define KERN_FAILURE 1
#define KERN_RESOURCE_SHORTAGE 2

/* Mock lock type for testing */
#define decl_simple_lock_data(class, name) int name##_placeholder

/* Server types corresponding to Coq sched_server_type */
typedef enum {
    ULE_SERVER_FILESYSTEM = 0,
    ULE_SERVER_NETWORK    = 1,
    ULE_SERVER_PROCESS    = 2,
    ULE_SERVER_MEMORY     = 3,
    ULE_SERVER_DEVICE     = 4,
    ULE_SERVER_GUI        = 5,
    ULE_SERVER_AUDIO      = 6,
    ULE_SERVER_COUNT      = 7
} ule_server_type_t;

/* Message classes corresponding to Coq sched_msg_class */
typedef enum {
    ULE_MSG_INTERRUPT   = 0,
    ULE_MSG_REALTIME    = 1,
    ULE_MSG_INTERACTIVE = 2,
    ULE_MSG_BATCH       = 3,
    ULE_MSG_IDLE        = 4
} ule_msg_class_t;

/* Individual threat characteristics for Dynamic BCRA formula */
typedef struct ule_threat_data {
    double threat_probability;     /* p_i: probability of malicious intent [0,1] */
    double defense_effectiveness;  /* E_i: defense effectiveness [0,1] */
    uint64_t timestamp;           /* Time of threat detection */
    double decay_time;            /* Calculated decay period T_decay(i) */
} ule_threat_data_t;

/* Nash equilibrium components for Dynamic BCRA */
typedef struct ule_nash_components {
    double equilibrium_factor;    /* π_eq: Nash equilibrium factor */
    double competition_factor;    /* π_comp: competition factor */
    double reputation_factor;     /* π_rep: reputation factor */
    double bayesian_factor;       /* π_bayes: Bayesian factor */
    double signaling_factor;      /* π_signal: signaling factor */
} ule_nash_components_t;

/* CA-based routing metric with full Dynamic BCRA formula support */
typedef struct ule_route_ca {
    /* Core formula parameters */
    uint32_t base_cost;                    /* C_base: base routing cost */
    uint32_t max_cost;                     /* C_max(t): maximum cost bound */
    
    /* Active threat set for ∑_{i∈active} g(p_i, E_i) */
    ule_threat_data_t active_threats[16];  /* Active threats (up to 16) */
    uint32_t num_active_threats;           /* Number of active threats */
    
    /* Nash equilibrium context Π_nash(t) */
    ule_nash_components_t nash_context;    /* Nash equilibrium components */
    
    /* Growth function parameters */
    double k1;                             /* Linear scaling factor (1.5) */
    double k2;                             /* Exponential scaling factor (2.0) */
    
    /* Backward compatibility - simple formula components */
    double simple_attack_load;             /* Legacy: attack load (0.0 - 1.0) */
    double simple_defense_strength;        /* Legacy: defense strength (0.0 - 1.0) */
    
    /* Cache for performance optimization */
    double cached_result;                  /* Cached routing cost */
    uint64_t cache_timestamp;              /* Cache validity timestamp */
    bool cache_valid;                      /* Cache validity flag */
} ule_route_ca_t;

/* Dynamic BCRA formula constants */
#define ULE_DYNAMIC_BCRA_K1             1.5     /* Linear scaling factor */
#define ULE_DYNAMIC_BCRA_K2             2.0     /* Exponential scaling factor */
#define ULE_DYNAMIC_BCRA_MIN_COST       10.0    /* Minimum cost bound */
#define ULE_MAX_ACTIVE_THREATS          16      /* Maximum active threats */
#define ULE_CACHE_VALIDITY_MS           1000    /* Cache validity: 1 second */

/* Nash equilibrium weights */
#define ULE_NASH_WEIGHT_EQUILIBRIUM     0.3     /* w1: equilibrium factor weight */
#define ULE_NASH_WEIGHT_COMPETITION     0.2     /* w2: competition factor weight */
#define ULE_NASH_WEIGHT_REPUTATION      0.2     /* w3: reputation factor weight */
#define ULE_NASH_WEIGHT_BAYESIAN        0.15    /* w4: Bayesian factor weight */
#define ULE_NASH_WEIGHT_SIGNALING       0.15    /* w5: signaling factor weight */

/* Function prototypes for Dynamic BCRA formula */
double ule_growth_function(double threat_probability, double defense_effectiveness, double k1, double k2);
double ule_threat_product(ule_threat_data_t *threats, uint32_t num_threats);
double ule_nash_multiplier(ule_nash_components_t *nash);
double ule_dynamic_routing_cost(ule_route_ca_t *ca);
double ule_simple_routing_cost(ule_route_ca_t *ca);
double ule_calculate_routing_cost(ule_route_ca_t *ca);

/* Threat management functions */
kern_return_t ule_add_threat(ule_route_ca_t *ca, double probability, double effectiveness);
kern_return_t ule_remove_expired_threats(ule_route_ca_t *ca, uint64_t current_time);
void ule_update_nash_components(ule_route_ca_t *ca, ule_nash_components_t *nash);

/* Performance optimization */
void ule_invalidate_cache(ule_route_ca_t *ca);
bool ule_is_cache_valid(ule_route_ca_t *ca, uint64_t current_time);

/* Test helper functions for time management */
void ule_test_set_time(uint64_t time_ms);
void ule_test_advance_time(uint64_t delta_ms);
void ule_test_use_real_time(void);

#endif /* _ULE_SMP_SCHEDULER_TEST_H_ */