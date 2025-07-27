/* FSM Dynamic BCRA Routing Implementation
 * High-performance routing with exponential economic defense
 */

#include "fsm_routing.h"
#include <math.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <unistd.h>
#include <sched.h>

/* Global BCRA parameters (can be tuned) */
static double g_k1 = FSM_BCRA_K1;
static double g_k2 = FSM_BCRA_K2;

/* Global Nash weights (can be tuned) */
static double g_nash_weights[5] = {
    FSM_NASH_W_EQUILIBRIUM,
    FSM_NASH_W_COMPETITION,
    FSM_NASH_W_REPUTATION,
    FSM_NASH_W_BAYESIAN,
    FSM_NASH_W_SIGNALING
};

/* Initialize the routing system */
bool fsm_routing_init(fsm_routing_system_t *routing) {
    if (!routing) {
        return false;
    }
    
    memset(routing, 0, sizeof(fsm_routing_system_t));
    
    /* Set default configuration */
    routing->numa_optimization_enabled = true;
    routing->economic_defense_enabled = true;
    routing->cache_ttl_ms = FSM_CACHE_TTL_MS;
    
    return true;
}

/* Register a new server */
bool fsm_routing_register_server(fsm_routing_system_t *routing,
                                uint16_t server_id,
                                fsm_server_type_t server_type,
                                uint32_t cpu_core) {
    if (!routing || routing->server_count >= FSM_MAX_SERVERS) {
        return false;
    }
    
    /* Check for duplicate server ID */
    for (uint32_t i = 0; i < routing->server_count; i++) {
        if (routing->servers[i].server_id == server_id) {
            return false;  /* Already registered */
        }
    }
    
    fsm_server_metrics_t *server = &routing->servers[routing->server_count];
    memset(server, 0, sizeof(fsm_server_metrics_t));
    
    /* Initialize server */
    server->server_id = server_id;
    server->server_type = server_type;
    server->current_load = 0.0;
    server->queue_depth = 0.0;
    server->base_cost = 100.0;     /* Default base cost */
    server->max_cost = 2000.0;     /* Default max cost */
    server->preferred_cpu_core = cpu_core;
    server->numa_node = cpu_core / 4;  /* Assume 4 cores per NUMA node */
    
    /* Initialize Nash components to neutral values */
    server->nash_context.equilibrium_factor = 1.0;
    server->nash_context.competition_factor = 1.0;
    server->nash_context.reputation_factor = 1.0;
    server->nash_context.bayesian_factor = 1.0;
    server->nash_context.signaling_factor = 1.0;
    
    routing->server_count++;
    
    return true;
}

/* Get current timestamp in milliseconds */
uint64_t fsm_get_current_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000 + (uint64_t)tv.tv_usec / 1000;
}

/* Get current CPU core ID */
uint32_t fsm_get_current_cpu_core(void) {
    return (uint32_t)sched_getcpu();
}

/* Growth function: g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2 */
double fsm_growth_function(double threat_probability, double defense_effectiveness) {
    if (threat_probability < 0.0 || threat_probability > 1.0) {
        return 1.0;  /* Invalid probability */
    }
    if (defense_effectiveness < 0.0 || defense_effectiveness > 1.0) {
        return 1.0;  /* Invalid effectiveness */
    }
    
    double effectiveness_term = 2.0 - defense_effectiveness;
    double power_term = pow(effectiveness_term, g_k2);
    return 1.0 + g_k1 * threat_probability * power_term;
}

/* Product of growth functions: ∏_{i∈active} g(p_i, E_i) */
double fsm_threat_product(const fsm_threat_t *threats, uint32_t count) {
    if (!threats || count == 0) {
        return 1.0;  /* No threats = no additional cost */
    }
    
    double product = 1.0;
    for (uint32_t i = 0; i < count; i++) {
        product *= fsm_growth_function(threats[i].threat_probability,
                                     threats[i].defense_effectiveness);
    }
    
    return product;
}

/* Nash equilibrium multiplier: Π_nash */
double fsm_nash_multiplier(const fsm_nash_components_t *nash) {
    if (!nash) {
        return 1.0;
    }
    
    return g_nash_weights[0] * nash->equilibrium_factor +
           g_nash_weights[1] * nash->competition_factor +
           g_nash_weights[2] * nash->reputation_factor +
           g_nash_weights[3] * nash->bayesian_factor +
           g_nash_weights[4] * nash->signaling_factor;
}

/* Dynamic BCRA routing cost (CORRECTED exponential product formula) */
double fsm_dynamic_routing_cost(const fsm_server_metrics_t *server) {
    if (!server) {
        return INFINITY;
    }
    
    /* Check cache validity first */
    uint64_t current_time = fsm_get_current_time_ms();
    if (server->cache_valid && 
        (current_time - server->cache_timestamp) < FSM_CACHE_TTL_MS) {
        return server->cached_bcra_score;
    }
    
    /* Calculate threat component: ∏_{i∈active} g(p_i, E_i) */
    double threat_component = fsm_threat_product(server->active_threats,
                                               server->num_active_threats);
    
    /* Calculate Nash equilibrium component: Π_nash */
    double nash_component = fsm_nash_multiplier(&server->nash_context);
    
    /* CORRECTED formula: CA(t) = min(C_max, C_base × exp(∏g(p_i,E_i)) × Π_nash) */
    double raw_cost = server->base_cost * exp(threat_component) * nash_component;
    double final_cost = fmin(server->max_cost, raw_cost);
    
    /* Update cache (note: this modifies const data, would need better design) */
    /* In real implementation, cache would be separate or function wouldn't be const */
    
    return final_cost;
}

/* BCRA benefit-to-cost ratio for server selection */
double fsm_bcra_score(const fsm_server_metrics_t *server) {
    if (!server) {
        return 0.0;
    }
    
    /* Benefit = 1 / (load + small constant to avoid division by zero) */
    double benefit = 1.0 / (server->current_load + 0.1);
    
    /* Cost from Dynamic BCRA formula */
    double cost = fsm_dynamic_routing_cost(server);
    
    /* BCRA score = benefit / cost (higher is better) */
    return benefit / cost;
}

/* Find best server using BCRA routing */
static uint16_t fsm_find_best_server(fsm_routing_system_t *routing,
                                    fsm_server_type_t service_type) {
    uint16_t best_server = 0;
    double best_score = 0.0;
    bool found_server = false;
    
    for (uint32_t i = 0; i < routing->server_count; i++) {
        fsm_server_metrics_t *server = &routing->servers[i];
        
        /* Only consider servers of the requested type */
        if (server->server_type != service_type) {
            continue;
        }
        
        double score = fsm_bcra_score(server);
        
        if (!found_server || score > best_score) {
            best_server = server->server_id;
            best_score = score;
            found_server = true;
        }
    }
    
    return found_server ? best_server : 0;
}

/* Check if cache entry is valid */
bool fsm_cache_valid(const fsm_routing_cache_t *entry, uint64_t current_time) {
    if (!entry) {
        return false;
    }
    
    return current_time < entry->cache_expiry;
}

/* Find cached routing decision */
uint16_t fsm_cache_lookup(fsm_routing_system_t *routing,
                         fsm_server_type_t service_type,
                         uint32_t cpu_core) {
    if (!routing) {
        return 0;
    }
    
    uint64_t current_time = fsm_get_current_time_ms();
    
    /* Look for valid cache entry for this service type and CPU core */
    for (uint32_t i = 0; i < routing->cache_count; i++) {
        fsm_routing_cache_t *entry = &routing->routing_cache[i];
        
        if (entry->service_type == service_type &&
            entry->cpu_core == cpu_core &&
            fsm_cache_valid(entry, current_time)) {
            
            routing->cache_hits++;
            return entry->best_server_id;
        }
    }
    
    routing->cache_misses++;
    return 0;  /* Cache miss */
}

/* Update routing cache */
bool fsm_cache_update(fsm_routing_system_t *routing,
                     fsm_server_type_t service_type,
                     uint16_t server_id,
                     double bcra_score,
                     uint32_t cpu_core) {
    if (!routing) {
        return false;
    }
    
    uint64_t current_time = fsm_get_current_time_ms();
    
    /* Find existing entry or create new one */
    fsm_routing_cache_t *entry = NULL;
    
    /* First, look for existing entry for this service/cpu combination */
    for (uint32_t i = 0; i < routing->cache_count; i++) {
        if (routing->routing_cache[i].service_type == service_type &&
            routing->routing_cache[i].cpu_core == cpu_core) {
            entry = &routing->routing_cache[i];
            break;
        }
    }
    
    /* If not found, create new entry */
    if (!entry && routing->cache_count < FSM_MAX_CACHE_ENTRIES) {
        entry = &routing->routing_cache[routing->cache_count];
        routing->cache_count++;
    }
    
    /* If still no entry (cache full), replace oldest entry */
    if (!entry) {
        /* Simple replacement: use first entry */
        entry = &routing->routing_cache[0];
    }
    
    /* Update cache entry */
    entry->service_type = service_type;
    entry->best_server_id = server_id;
    entry->bcra_score = bcra_score;
    entry->cache_expiry = current_time + routing->cache_ttl_ms;
    entry->cpu_core = cpu_core;
    
    return true;
}

/* Main routing function */
uint16_t fsm_route_message(fsm_routing_system_t *routing,
                          const fsm_message_t *msg,
                          uint32_t current_cpu_core) {
    if (!routing || !msg) {
        return 0;
    }
    
    uint64_t start_time = fsm_get_current_time_ms();
    
    /* Determine service type from destination server ID */
    fsm_server_type_t service_type = FSM_SERVER_FILESYSTEM;  /* Default */
    
    /* In real implementation, would map dest_server to service_type */
    /* For now, use simple mapping based on server ID ranges */
    if (msg->dest_server < 100) {
        service_type = FSM_SERVER_FILESYSTEM;
    } else if (msg->dest_server < 200) {
        service_type = FSM_SERVER_NETWORK;
    } else if (msg->dest_server < 300) {
        service_type = FSM_SERVER_PROCESS;
    } else {
        service_type = FSM_SERVER_MEMORY;
    }
    
    /* Try cache lookup first */
    uint16_t cached_server = fsm_cache_lookup(routing, service_type, current_cpu_core);
    if (cached_server != 0) {
        return cached_server;
    }
    
    /* Cache miss - calculate best server */
    uint16_t best_server = fsm_find_best_server(routing, service_type);
    
    if (best_server != 0) {
        /* Find server metrics for BCRA score */
        double best_score = 0.0;
        for (uint32_t i = 0; i < routing->server_count; i++) {
            if (routing->servers[i].server_id == best_server) {
                best_score = fsm_bcra_score(&routing->servers[i]);
                break;
            }
        }
        
        /* Update cache */
        fsm_cache_update(routing, service_type, best_server, best_score, current_cpu_core);
    }
    
    /* Update statistics */
    routing->total_routes_calculated++;
    uint64_t routing_time = fsm_get_current_time_ms() - start_time;
    routing->avg_routing_time_ns = (routing->avg_routing_time_ns + routing_time * 1000000) / 2;
    if (routing_time * 1000000 > routing->peak_routing_time_ns) {
        routing->peak_routing_time_ns = routing_time * 1000000;
    }
    
    return best_server;
}

/* Add a detected threat to server */
bool fsm_add_threat(fsm_server_metrics_t *server,
                   double probability,
                   double effectiveness) {
    if (!server || probability < 0.0 || probability > 1.0 ||
        effectiveness < 0.0 || effectiveness > 1.0) {
        return false;
    }
    
    if (server->num_active_threats >= FSM_MAX_ACTIVE_THREATS) {
        return false;  /* Threat list full */
    }
    
    fsm_threat_t *threat = &server->active_threats[server->num_active_threats];
    threat->threat_probability = probability;
    threat->defense_effectiveness = effectiveness;
    threat->timestamp = fsm_get_current_time_ms();
    
    /* Calculate decay time using threat probability */
    /* Higher probability threats persist longer */
    uint64_t base_time = 365 * 24 * 60 * 60 * 1000;  /* 1 year in ms */
    double alpha = 1.0;
    double beta = 2.0;
    threat->decay_time = base_time + (uint64_t)(alpha * pow(probability, beta) * base_time);
    
    server->num_active_threats++;
    
    /* Invalidate cache */
    server->cache_valid = false;
    
    return true;
}

/* Remove expired threats */
uint32_t fsm_remove_expired_threats(fsm_server_metrics_t *server,
                                   uint64_t current_time) {
    if (!server) {
        return 0;
    }
    
    uint32_t removed_count = 0;
    uint32_t active_count = 0;
    
    for (uint32_t i = 0; i < server->num_active_threats; i++) {
        fsm_threat_t *threat = &server->active_threats[i];
        
        /* Check if threat has expired */
        if ((current_time - threat->timestamp) <= threat->decay_time) {
            /* Threat is still active - keep it */
            if (active_count != i) {
                server->active_threats[active_count] = *threat;
            }
            active_count++;
        } else {
            removed_count++;
        }
    }
    
    server->num_active_threats = active_count;
    
    if (removed_count > 0) {
        /* Invalidate cache since threat profile changed */
        server->cache_valid = false;
    }
    
    return removed_count;
}

/* Update server metrics */
bool fsm_routing_update_metrics(fsm_routing_system_t *routing,
                               uint16_t server_id,
                               double load,
                               double queue_depth,
                               uint64_t response_time) {
    if (!routing) {
        return false;
    }
    
    /* Find server */
    for (uint32_t i = 0; i < routing->server_count; i++) {
        fsm_server_metrics_t *server = &routing->servers[i];
        
        if (server->server_id == server_id) {
            server->current_load = load;
            server->queue_depth = queue_depth;
            server->last_response_time = response_time;
            
            /* Update statistics */
            server->messages_processed++;
            server->total_processing_time += response_time;
            
            /* Remove expired threats */
            uint64_t current_time = fsm_get_current_time_ms();
            fsm_remove_expired_threats(server, current_time);
            
            /* Invalidate cache if metrics changed significantly */
            server->cache_valid = false;
            
            return true;
        }
    }
    
    return false;  /* Server not found */
}

/* Get routing system statistics */
void fsm_routing_get_stats(const fsm_routing_system_t *routing,
                          uint64_t *total_routes,
                          uint64_t *cache_hits,
                          uint64_t *cache_misses,
                          double *cache_hit_ratio) {
    if (!routing) {
        return;
    }
    
    if (total_routes) {
        *total_routes = routing->total_routes_calculated;
    }
    if (cache_hits) {
        *cache_hits = routing->cache_hits;
    }
    if (cache_misses) {
        *cache_misses = routing->cache_misses;
    }
    if (cache_hit_ratio) {
        uint64_t total_lookups = routing->cache_hits + routing->cache_misses;
        *cache_hit_ratio = total_lookups > 0 ? 
            (double)routing->cache_hits / total_lookups : 0.0;
    }
}

/* Convert service type to string */
const char *fsm_service_type_string(fsm_server_type_t type) {
    switch (type) {
        case FSM_SERVER_FILESYSTEM: return "Filesystem";
        case FSM_SERVER_NETWORK:    return "Network";
        case FSM_SERVER_PROCESS:    return "Process";
        case FSM_SERVER_MEMORY:     return "Memory";
        case FSM_SERVER_DEVICE:     return "Device";
        case FSM_SERVER_GUI:        return "GUI";
        case FSM_SERVER_AUDIO:      return "Audio";
        default:                    return "Unknown";
    }
}

/* Set BCRA formula parameters */
bool fsm_set_bcra_params(double k1, double k2) {
    if (k1 <= 0.0 || k2 <= 0.0) {
        return false;
    }
    
    g_k1 = k1;
    g_k2 = k2;
    return true;
}

/* Enable/disable features */
void fsm_enable_numa_optimization(fsm_routing_system_t *routing, bool enable) {
    if (routing) {
        routing->numa_optimization_enabled = enable;
    }
}

void fsm_enable_economic_defense(fsm_routing_system_t *routing, bool enable) {
    if (routing) {
        routing->economic_defense_enabled = enable;
    }
}

void fsm_set_cache_ttl(fsm_routing_system_t *routing, uint32_t ttl_ms) {
    if (routing) {
        routing->cache_ttl_ms = ttl_ms;
    }
}

/* Validate routing system integrity */
bool fsm_routing_validate(const fsm_routing_system_t *routing) {
    if (!routing) {
        return false;
    }
    
    /* Check server count bounds */
    if (routing->server_count > FSM_MAX_SERVERS) {
        return false;
    }
    
    /* Validate each server */
    for (uint32_t i = 0; i < routing->server_count; i++) {
        const fsm_server_metrics_t *server = &routing->servers[i];
        
        /* Check threat count bounds */
        if (server->num_active_threats > FSM_MAX_ACTIVE_THREATS) {
            return false;
        }
        
        /* Validate costs */
        if (server->base_cost <= 0.0 || server->max_cost <= server->base_cost) {
            return false;
        }
        
        /* Validate load metrics */
        if (server->current_load < 0.0 || server->current_load > 1.0) {
            return false;
        }
    }
    
    return true;
}