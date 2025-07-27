/* FSM-Based Dynamic BCRA Routing System
 * High-performance routing with economic defense
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _FSM_ROUTING_H_
#define _FSM_ROUTING_H_

#include "fsm_message.h"
#include <stdint.h>
#include <stdbool.h>

/* Maximum number of servers and threats */
#define FSM_MAX_SERVERS         256
#define FSM_MAX_ACTIVE_THREATS  16
#define FSM_MAX_CACHE_ENTRIES   128

/* Cache TTL in milliseconds (1 second) */
#define FSM_CACHE_TTL_MS        1000

/* BCRA formula constants */
#define FSM_BCRA_K1             1.5     /* Linear scaling factor */
#define FSM_BCRA_K2             2.0     /* Exponential scaling factor */

/* Nash equilibrium weights */
#define FSM_NASH_W_EQUILIBRIUM  0.3     /* Equilibrium factor weight */
#define FSM_NASH_W_COMPETITION  0.2     /* Competition factor weight */
#define FSM_NASH_W_REPUTATION   0.2     /* Reputation factor weight */
#define FSM_NASH_W_BAYESIAN     0.15    /* Bayesian factor weight */
#define FSM_NASH_W_SIGNALING    0.15    /* Signaling factor weight */

/* Server types for routing */
typedef enum {
    FSM_SERVER_FILESYSTEM   = 0,
    FSM_SERVER_NETWORK      = 1,
    FSM_SERVER_PROCESS      = 2,
    FSM_SERVER_MEMORY       = 3,
    FSM_SERVER_DEVICE       = 4,
    FSM_SERVER_GUI          = 5,
    FSM_SERVER_AUDIO        = 6,
    FSM_SERVER_COUNT        = 7
} fsm_server_type_t;

/* Threat characteristics for Dynamic BCRA */
typedef struct {
    double   threat_probability;     /* p_i: attack probability [0,1] */
    double   defense_effectiveness;  /* E_i: defense effectiveness [0,1] */
    uint64_t timestamp;             /* When threat was detected */
    uint64_t decay_time;            /* Calculated threat lifetime */
} fsm_threat_t;

/* Nash equilibrium components */
typedef struct {
    double equilibrium_factor;      /* π_eq: Nash equilibrium factor */
    double competition_factor;      /* π_comp: competition factor */
    double reputation_factor;       /* π_rep: reputation factor */
    double bayesian_factor;         /* π_bayes: Bayesian factor */
    double signaling_factor;        /* π_signal: signaling factor */
} fsm_nash_components_t;

/* Server metrics for routing decisions */
typedef struct {
    uint16_t server_id;             /* Unique server identifier */
    fsm_server_type_t server_type;  /* Type of service provided */
    
    /* Load metrics */
    double   current_load;          /* CPU/memory utilization [0,1] */
    double   queue_depth;           /* Pending message count */
    uint64_t last_response_time;    /* Last message processing time (μs) */
    
    /* BCRA cost parameters */
    double   base_cost;             /* C_base: base routing cost */
    double   max_cost;              /* C_max: maximum cost bound */
    
    /* Threat tracking */
    fsm_threat_t active_threats[FSM_MAX_ACTIVE_THREATS];
    uint32_t     num_active_threats;
    
    /* Nash equilibrium context */
    fsm_nash_components_t nash_context;
    
    /* Performance optimization */
    double   cached_bcra_score;     /* Last calculated BCRA score */
    uint64_t cache_timestamp;       /* When score was calculated */
    bool     cache_valid;           /* Cache validity flag */
    
    /* Statistics */
    uint64_t messages_processed;    /* Total messages handled */
    uint64_t total_processing_time; /* Cumulative processing time (μs) */
    
    /* NUMA/SMP optimization */
    uint32_t preferred_cpu_core;    /* Preferred CPU for this server */
    uint32_t numa_node;             /* NUMA node assignment */
    
} fsm_server_metrics_t;

/* Routing cache entry */
typedef struct {
    fsm_server_type_t service_type; /* Service being cached */
    uint16_t          best_server_id; /* Selected server */
    double            bcra_score;     /* Best BCRA score found */
    uint64_t          cache_expiry;   /* When cache expires */
    uint32_t          cpu_core;       /* Core that created this cache */
} fsm_routing_cache_t;

/* Global routing system state */
typedef struct {
    /* Server registry */
    fsm_server_metrics_t servers[FSM_MAX_SERVERS];
    uint32_t             server_count;
    
    /* Per-core routing caches for scalability */
    fsm_routing_cache_t  routing_cache[FSM_MAX_CACHE_ENTRIES];
    uint32_t             cache_count;
    
    /* System-wide statistics */
    uint64_t total_routes_calculated;
    uint64_t cache_hits;
    uint64_t cache_misses;
    uint64_t threats_detected;
    uint64_t attacks_deterred;
    
    /* Performance metrics */
    uint64_t avg_routing_time_ns;   /* Average routing decision time */
    uint64_t peak_routing_time_ns;  /* Peak routing time observed */
    
    /* Configuration */
    bool     numa_optimization_enabled;
    bool     economic_defense_enabled;
    uint32_t cache_ttl_ms;          /* Cache time-to-live */
    
} fsm_routing_system_t;

/* Core routing functions */

/* Initialize the routing system */
bool fsm_routing_init(fsm_routing_system_t *routing);

/* Register a new server */
bool fsm_routing_register_server(fsm_routing_system_t *routing,
                                uint16_t server_id,
                                fsm_server_type_t server_type,
                                uint32_t cpu_core);

/* Unregister a server */
bool fsm_routing_unregister_server(fsm_routing_system_t *routing,
                                  uint16_t server_id);

/* Update server metrics (called periodically) */
bool fsm_routing_update_metrics(fsm_routing_system_t *routing,
                               uint16_t server_id,
                               double load,
                               double queue_depth,
                               uint64_t response_time);

/* Main routing function - find best server for message */
uint16_t fsm_route_message(fsm_routing_system_t *routing,
                          const fsm_message_t *msg,
                          uint32_t current_cpu_core);

/* BCRA calculation functions */

/* Growth function: g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2 */
double fsm_growth_function(double threat_probability, 
                          double defense_effectiveness);

/* Product of growth functions: ∏_{i∈active} g(p_i, E_i) */
double fsm_threat_product(const fsm_threat_t *threats, uint32_t count);

/* Nash equilibrium multiplier: Π_nash */
double fsm_nash_multiplier(const fsm_nash_components_t *nash);

/* Dynamic BCRA routing cost (CORRECTED exponential product formula) */
double fsm_dynamic_routing_cost(const fsm_server_metrics_t *server);

/* BCRA benefit-to-cost ratio for server selection */
double fsm_bcra_score(const fsm_server_metrics_t *server);

/* Threat management functions */

/* Add a detected threat to server */
bool fsm_add_threat(fsm_server_metrics_t *server,
                   double probability,
                   double effectiveness);

/* Remove expired threats */
uint32_t fsm_remove_expired_threats(fsm_server_metrics_t *server,
                                   uint64_t current_time);

/* Update Nash equilibrium components */
bool fsm_update_nash_components(fsm_server_metrics_t *server,
                               const fsm_nash_components_t *nash);

/* Cache management functions */

/* Check if cache entry is valid */
bool fsm_cache_valid(const fsm_routing_cache_t *entry, uint64_t current_time);

/* Find cached routing decision */
uint16_t fsm_cache_lookup(fsm_routing_system_t *routing,
                         fsm_server_type_t service_type,
                         uint32_t cpu_core);

/* Update routing cache */
bool fsm_cache_update(fsm_routing_system_t *routing,
                     fsm_server_type_t service_type,
                     uint16_t server_id,
                     double bcra_score,
                     uint32_t cpu_core);

/* Invalidate cache entries for a server */
void fsm_cache_invalidate_server(fsm_routing_system_t *routing,
                                uint16_t server_id);

/* Performance and statistics functions */

/* Get routing system statistics */
void fsm_routing_get_stats(const fsm_routing_system_t *routing,
                          uint64_t *total_routes,
                          uint64_t *cache_hits,
                          uint64_t *cache_misses,
                          double *cache_hit_ratio);

/* Reset statistics counters */
void fsm_routing_reset_stats(fsm_routing_system_t *routing);

/* Get server performance metrics */
bool fsm_get_server_stats(const fsm_routing_system_t *routing,
                         uint16_t server_id,
                         uint64_t *messages_processed,
                         uint64_t *avg_processing_time,
                         uint32_t *active_threats);

/* Advanced features */

/* NUMA-aware server selection */
uint16_t fsm_numa_aware_route(fsm_routing_system_t *routing,
                             fsm_server_type_t service_type,
                             uint32_t cpu_core);

/* Load balancing with economic factors */
uint16_t fsm_load_balanced_route(fsm_routing_system_t *routing,
                                fsm_server_type_t service_type,
                                double load_weight,
                                double cost_weight);

/* Attack response automation */
bool fsm_automatic_threat_response(fsm_routing_system_t *routing,
                                  uint16_t server_id,
                                  double threat_threshold);

/* Configuration and tuning */

/* Set BCRA formula parameters */
bool fsm_set_bcra_params(double k1, double k2);

/* Set Nash equilibrium weights */
bool fsm_set_nash_weights(double w_eq, double w_comp, double w_rep,
                         double w_bayes, double w_signal);

/* Enable/disable features */
void fsm_enable_numa_optimization(fsm_routing_system_t *routing, bool enable);
void fsm_enable_economic_defense(fsm_routing_system_t *routing, bool enable);
void fsm_set_cache_ttl(fsm_routing_system_t *routing, uint32_t ttl_ms);

/* Utility functions */

/* Get current timestamp in milliseconds */
uint64_t fsm_get_current_time_ms(void);

/* Get current CPU core ID */
uint32_t fsm_get_current_cpu_core(void);

/* Convert service type to string (for debugging) */
const char *fsm_service_type_string(fsm_server_type_t type);

/* Validate routing system integrity */
bool fsm_routing_validate(const fsm_routing_system_t *routing);

/* Debug and monitoring */
#ifdef FSM_DEBUG
void fsm_routing_dump_state(const fsm_routing_system_t *routing);
void fsm_routing_dump_server(const fsm_server_metrics_t *server);
void fsm_routing_dump_cache(const fsm_routing_system_t *routing);
#endif

#endif /* _FSM_ROUTING_H_ */