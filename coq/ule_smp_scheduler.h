/* ULE-based SMP Scheduler for GNU Hurd
 * Implementation based on formally verified Coq specifications
 * Copyright (C) 2025 Free Software Foundation, Inc.
 *
 * This file is part of the GNU Hurd.
 *
 * The GNU Hurd is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2, or (at
 * your option) any later version.
 *
 * The GNU Hurd is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

#ifndef _ULE_SMP_SCHEDULER_H_
#define _ULE_SMP_SCHEDULER_H_

#include <mach/kern_return.h>
#include <mach/thread_status.h>
#include <kern/thread.h>
#include <kern/lock.h>
#include <sys/types.h>

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

/* CA-based routing metric corresponding to Coq route_ca 
 * Original formula by Scott J. Guyton:
 * routing_cost = base_cost * (1 + attack_load * (2 - defense_strength))
 */
typedef struct ule_route_ca {
    uint32_t base_cost;        /* Base routing cost */
    double attack_load;        /* Current attack load (0.0 - 1.0) */
    double defense_strength;   /* Defense strength (0.0 - 1.0) */
} ule_route_ca_t;

/* Message structure corresponding to Coq message */
typedef struct ule_message {
    uint32_t msg_id;           /* Unique message identifier */
    uint32_t sender_id;        /* Sender server ID */
    ule_server_type_t target_service; /* Target service type */
    ule_msg_class_t msg_class; /* Message classification */
    uint32_t sleep_time;       /* Sleep time for interactivity calc */
    uint32_t run_time;         /* Run time for interactivity calc */
    uint32_t arrival_time;     /* Message arrival timestamp */
    
    /* Implementation-specific fields */
    struct thread *thread;     /* Associated thread (if any) */
    void *msg_data;           /* Message payload */
    size_t msg_size;          /* Message size */
    
    /* List management */
    struct ule_message *next;
    struct ule_message *prev;
} ule_message_t;

/* Message queue structure */
typedef struct ule_message_queue {
    ule_message_t *head;
    ule_message_t *tail;
    uint32_t count;
    decl_simple_lock_data(, lock) /* Queue lock */
} ule_message_queue_t;

/* Server queue corresponding to Coq server_queue */
typedef struct ule_server_queue {
    uint32_t server_id;        /* Unique server identifier */
    
    /* ULE queues - corresponding to Coq model */
    ule_message_queue_t current_queue;    /* High priority messages */
    ule_message_queue_t next_queue;       /* Next batch messages */
    ule_message_queue_t idle_queue;       /* Idle/low priority messages */
    
    /* Scheduler parameters */
    uint32_t interactive_threshold;       /* Interactivity threshold (30) */
    uint32_t queue_load;                 /* Current load metric */
    
    /* CA-based routing */
    ule_route_ca_t server_ca;            /* CA routing metric */
    ule_server_type_t server_type;       /* Server type */
    
    /* SMP support */
    uint32_t dedicated_core;             /* Dedicated core (-1 if none) */
    
    /* Statistics and history */
    struct {
        uint32_t msg_id;
        uint32_t timestamp;
    } message_history[16];               /* Recent message history */
    uint32_t history_index;
    
    /* Implementation locks */
    decl_simple_lock_data(, lock)        /* Server queue lock */
    
    /* List management for global server list */
    struct ule_server_queue *next;
    struct ule_server_queue *prev;
    
} ule_server_queue_t;

/* Global microkernel scheduler state corresponding to Coq microkernel_state */
typedef struct ule_microkernel_state {
    /* Server management */
    ule_server_queue_t *servers;        /* List of server queues */
    uint32_t server_count;
    
    /* Global message pool */
    ule_message_t *pending_messages;    /* Unassigned messages */
    uint32_t pending_count;
    
    /* System state */
    uint32_t global_time;               /* System time counter */
    uint32_t core_count;                /* Number of CPU cores */
    
    /* SMP synchronization */
    decl_simple_lock_data(, global_lock) /* Global scheduler lock */
    
    /* Statistics */
    struct {
        uint64_t messages_processed;
        uint64_t context_switches;
        uint64_t interactive_promotions;
        uint32_t avg_response_time;
    } stats;
    
} ule_microkernel_state_t;

/* Scheduler configuration */
typedef struct ule_scheduler_config {
    uint32_t time_quantum_ms;           /* Base time quantum in ms */  
    uint32_t interactive_threshold;     /* Interactive classification threshold */
    uint32_t max_message_history;       /* Maximum message history entries */
    double ca_attack_decay;             /* Attack load decay rate */
    double ca_defense_boost;            /* Defense strength boost rate */
    bool enable_smp_affinity;           /* Enable SMP core affinity */
    bool enable_ca_routing;             /* Enable CA-based routing */
} ule_scheduler_config_t;

/* Function prototypes - Core scheduler interface */

/* Initialization and cleanup */
kern_return_t ule_scheduler_init(ule_scheduler_config_t *config);
void ule_scheduler_cleanup(void);

/* Server management - corresponding to Coq theorems */
kern_return_t ule_server_register(uint32_t server_id, 
                                  ule_server_type_t server_type,
                                  uint32_t dedicated_core);
kern_return_t ule_server_unregister(uint32_t server_id);

/* Message scheduling - based on verified properties */
kern_return_t ule_message_enqueue(ule_message_t *msg);
ule_message_t *ule_message_dequeue(ule_server_type_t server_type);
ule_message_t *ule_message_dequeue_core(uint32_t core_id);

/* Interactivity calculation - implements verified calculate_interactivity */
uint32_t ule_calculate_interactivity(uint32_t sleep_time, uint32_t run_time);
bool ule_is_interactive(ule_message_t *msg);

/* CA-based routing - implements verified routing_cost and ca_routing_optimal */
double ule_calculate_routing_cost(ule_route_ca_t *ca);
ule_server_queue_t *ule_find_min_cost_server(ule_server_type_t server_type);

/* Queue management - implements verified queue operations */
kern_return_t ule_queue_switch(ule_server_queue_t *server);
uint32_t ule_get_queue_length(ule_server_queue_t *server);

/* SMP and thread integration */
kern_return_t ule_scheduler_run_core(uint32_t core_id);
void ule_scheduler_yield(struct thread *thread);
void ule_scheduler_block(struct thread *thread);
void ule_scheduler_unblock(struct thread *thread);

/* Statistics and monitoring */
void ule_scheduler_get_stats(struct ule_scheduler_stats *stats);
void ule_scheduler_reset_stats(void);

/* Debug and verification support */
#ifdef ULE_DEBUG
void ule_scheduler_verify_invariants(void);
void ule_scheduler_dump_state(void);
#endif

/* Global scheduler instance */
extern ule_microkernel_state_t *ule_global_scheduler;

/* Scheduler configuration defaults */
#define ULE_DEFAULT_TIME_QUANTUM_MS     20
#define ULE_DEFAULT_INTERACTIVE_THRESH  30
#define ULE_DEFAULT_MAX_HISTORY         16
#define ULE_DEFAULT_CA_ATTACK_DECAY     0.95
#define ULE_DEFAULT_CA_DEFENSE_BOOST    1.05

/* Interactivity bounds - from verified proof */
#define ULE_INTERACTIVITY_MAX           100
#define ULE_INTERACTIVITY_BASE          50

/* Priority levels */
#define ULE_PRIORITY_INTERRUPT          0
#define ULE_PRIORITY_REALTIME           1  
#define ULE_PRIORITY_INTERACTIVE        2
#define ULE_PRIORITY_BATCH              3
#define ULE_PRIORITY_IDLE               4

#endif /* _ULE_SMP_SCHEDULER_H_ */