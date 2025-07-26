/* ULE Scheduler Integration with Mach Kernel
 * Provides thread scheduling integration for GNU Hurd
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include "ule_smp_scheduler.h"
#include <mach/mach_types.h>
#include <kern/sched_prim.h>
#include <kern/thread.h>
#include <kern/processor.h>
#include <kern/cpu_number.h>
#include <kern/machine.h>
#include <mach/policy.h>

/* Thread state tracking for ULE scheduler */
typedef struct ule_thread_state {
    uint32_t sleep_time;        /* Accumulated sleep time */
    uint32_t run_time;          /* Accumulated run time */
    uint32_t last_schedule;     /* Last schedule timestamp */
    ule_server_type_t server_type; /* Associated server type */
    bool is_server_thread;      /* True if this is a server thread */
    uint32_t server_id;         /* Server ID if server thread */
} ule_thread_state_t;

/* Per-CPU scheduler state for SMP */
typedef struct ule_cpu_state {
    uint32_t cpu_id;
    ule_message_t *current_message;     /* Currently executing message */
    uint32_t time_slice_remaining;      /* Time slice left in ms */
    uint64_t last_context_switch;       /* Timestamp of last switch */
    
    /* CPU-specific statistics */
    uint64_t messages_processed;
    uint64_t context_switches;
    uint32_t utilization_percent;
    
} ule_cpu_state_t;

/* Per-CPU state array */
static ule_cpu_state_t ule_cpu_states[MAX_CPUS];
static bool ule_integration_initialized = false;

/* Forward declarations */
static void ule_thread_timer_expired(thread_t thread);
static void ule_update_thread_stats(thread_t thread, bool was_running);
static ule_message_t *ule_thread_to_message(thread_t thread);
static kern_return_t ule_setup_cpu_state(uint32_t cpu_id);

/*
 * Convert thread to ULE message for scheduling
 */
static ule_message_t *
ule_thread_to_message(thread_t thread)
{
    assert(thread != NULL);
    
    ule_thread_state_t *thread_state = (ule_thread_state_t *)thread->ule_state;
    if (!thread_state) {
        return NULL;
    }
    
    /* Allocate ULE message */
    ule_message_t *msg = (ule_message_t *)kalloc(sizeof(ule_message_t));
    if (!msg) {
        return NULL;
    }
    
    memset(msg, 0, sizeof(ule_message_t));
    
    /* Fill message from thread state */
    msg->msg_id = (uint32_t)(uintptr_t)thread; /* Use thread address as ID */
    msg->sender_id = thread_state->server_id;
    msg->target_service = thread_state->server_type;
    msg->sleep_time = thread_state->sleep_time;
    msg->run_time = thread_state->run_time;
    msg->thread = thread;
    
    /* Classify message based on thread policy and state */
    if (thread->policy == POLICY_TIMESHARE) {
        if (thread->sched_mode & TH_MODE_REALTIME) {
            msg->msg_class = ULE_MSG_REALTIME;
        } else if (ule_is_interactive(msg)) {
            msg->msg_class = ULE_MSG_INTERACTIVE;
        } else {
            msg->msg_class = ULE_MSG_BATCH;
        }
    } else if (thread->policy == POLICY_FIXEDPRI) {
        if (thread->sched_pri > MAXPRI_SYSTEM) {
            msg->msg_class = ULE_MSG_REALTIME;
        } else {
            msg->msg_class = ULE_MSG_BATCH;
        }
    } else {
        msg->msg_class = ULE_MSG_IDLE;
    }
    
    return msg;
}

/*
 * Update thread statistics for ULE scheduling
 */
static void 
ule_update_thread_stats(thread_t thread, bool was_running)
{
    assert(thread != NULL);
    
    ule_thread_state_t *thread_state = (ule_thread_state_t *)thread->ule_state;
    if (!thread_state) {
        return;
    }
    
    uint32_t current_time = ule_global_scheduler->global_time;
    uint32_t delta = current_time - thread_state->last_schedule;
    
    if (was_running) {
        thread_state->run_time += delta;
    } else {
        thread_state->sleep_time += delta;
    }
    
    thread_state->last_schedule = current_time;
    
    /* Decay old statistics to emphasize recent behavior */
    if (thread_state->run_time > 1000 || thread_state->sleep_time > 1000) {
        thread_state->run_time = (thread_state->run_time * 7) / 8;
        thread_state->sleep_time = (thread_state->sleep_time * 7) / 8;
    }
}

/*
 * Setup per-CPU state for SMP operation
 */
static kern_return_t 
ule_setup_cpu_state(uint32_t cpu_id)
{
    assert(cpu_id < MAX_CPUS);
    
    ule_cpu_state_t *cpu_state = &ule_cpu_states[cpu_id];
    
    memset(cpu_state, 0, sizeof(ule_cpu_state_t));
    cpu_state->cpu_id = cpu_id;
    cpu_state->current_message = NULL;
    cpu_state->time_slice_remaining = ule_config.time_quantum_ms;
    cpu_state->last_context_switch = 0;
    
    return KERN_SUCCESS;
}

/*
 * Main SMP scheduler run loop for a CPU core
 * This implements the ULE scheduling algorithm per-core
 */
kern_return_t 
ule_scheduler_run_core(uint32_t core_id)
{
    assert(core_id < ule_global_scheduler->core_count);
    assert(core_id < MAX_CPUS);
    
    ule_cpu_state_t *cpu_state = &ule_cpu_states[core_id];
    
    while (true) {
        /* Get next message to process */
        ule_message_t *msg = ule_message_dequeue_core(core_id);
        
        if (!msg) {
            /* No work available, idle this CPU */
            cpu_idle();
            continue;
        }
        
        /* Update CPU state */
        cpu_state->current_message = msg;
        cpu_state->time_slice_remaining = ule_config.time_quantum_ms;
        cpu_state->last_context_switch = ule_global_scheduler->global_time;
        
        if (msg->thread) {
            /* Thread-based message: resume the thread */
            thread_t thread = msg->thread;
            
            /* Update thread statistics */
            ule_update_thread_stats(thread, false);
            
            /* Set up thread for execution */
            thread->processor_set = &default_pset;
            thread->bound_processor = cpu_to_processor(core_id);
            
            /* Context switch to the thread */
            thread_block_reason(THREAD_CONTINUE_NULL, NULL, AST_NONE);
            
            /* Thread has finished or blocked */
            ule_update_thread_stats(thread, true);
            cpu_state->context_switches++;
            
        } else {
            /* Message-based work: process the message directly */
            /* This would be extended based on specific message types */
            
            /* For now, simulate message processing */
            delay(1); /* Simulate work */
        }
        
        /* Update statistics */
        cpu_state->messages_processed++;
        ule_global_scheduler->stats.messages_processed++;
        
        /* Free the message */
        kfree((vm_offset_t)msg, sizeof(ule_message_t));
        cpu_state->current_message = NULL;
    }
    
    return KERN_SUCCESS;
}

/*
 * Thread yield - called when a thread voluntarily gives up CPU
 */
void 
ule_scheduler_yield(struct thread *thread)
{
    assert(thread != NULL);
    
    if (!ule_integration_initialized) {
        return;
    }
    
    uint32_t cpu_id = cpu_number();
    ule_cpu_state_t *cpu_state = &ule_cpu_states[cpu_id];
    
    /* Update thread statistics */
    ule_update_thread_stats(thread, true);
    
    /* Convert thread back to message and re-enqueue */
    ule_message_t *msg = ule_thread_to_message(thread);
    if (msg) {
        /* Reduce priority slightly for yielding threads */
        if (msg->msg_class == ULE_MSG_INTERACTIVE) {
            msg->msg_class = ULE_MSG_BATCH;
        }
        
        ule_message_enqueue(msg);
    }
    
    /* Clear current message */
    if (cpu_state->current_message && cpu_state->current_message->thread == thread) {
        cpu_state->current_message = NULL;
    }
    
    /* Let the scheduler pick the next thread */
    thread_block_reason(THREAD_CONTINUE_NULL, NULL, AST_YIELD);
}

/*
 * Thread block - called when a thread blocks on a resource
 */
void 
ule_scheduler_block(struct thread *thread)
{
    assert(thread != NULL);
    
    if (!ule_integration_initialized) {
        return;
    }
    
    uint32_t cpu_id = cpu_number();
    ule_cpu_state_t *cpu_state = &ule_cpu_states[cpu_id];
    
    /* Update thread statistics - this was NOT running time */
    ule_update_thread_stats(thread, false);
    
    /* Clear current message if this thread is running */
    if (cpu_state->current_message && cpu_state->current_message->thread == thread) {
        /* Free the message since thread is blocking */
        kfree((vm_offset_t)cpu_state->current_message, sizeof(ule_message_t));
        cpu_state->current_message = NULL;
    }
    
    /* Thread will be re-enqueued when it unblocks */
}

/*
 * Thread unblock - called when a blocked thread becomes runnable
 */
void 
ule_scheduler_unblock(struct thread *thread)
{
    assert(thread != NULL);
    
    if (!ule_integration_initialized) {
        return;
    }
    
    /* Update thread statistics */
    ule_update_thread_stats(thread, false);
    
    /* Convert thread to message and enqueue */
    ule_message_t *msg = ule_thread_to_message(thread);
    if (msg) {
        /* Boost priority for threads that were blocked (interactive behavior) */
        if (msg->sleep_time > msg->run_time) {
            msg->msg_class = ULE_MSG_INTERACTIVE;
        }
        
        ule_message_enqueue(msg);
    }
}

/*
 * Timer callback for time slice expiration
 */
static void 
ule_thread_timer_expired(thread_t thread)
{
    assert(thread != NULL);
    
    uint32_t cpu_id = cpu_number();
    ule_cpu_state_t *cpu_state = &ule_cpu_states[cpu_id];
    
    /* Time slice expired - preempt the thread */
    ule_update_thread_stats(thread, true);
    
    /* Convert thread to message and re-enqueue with lower priority */
    ule_message_t *msg = ule_thread_to_message(thread);
    if (msg) {
        /* Demote CPU-bound threads */
        if (msg->msg_class == ULE_MSG_INTERACTIVE) {
            msg->msg_class = ULE_MSG_BATCH;
        }
        
        ule_message_enqueue(msg);
    }
    
    /* Clear current message */
    if (cpu_state->current_message && cpu_state->current_message->thread == thread) {
        kfree((vm_offset_t)cpu_state->current_message, sizeof(ule_message_t));
        cpu_state->current_message = NULL;
    }
    
    /* Trigger preemption */
    thread_block_reason(THREAD_CONTINUE_NULL, NULL, AST_PREEMPT);
}

/*
 * Initialize thread state for ULE scheduling
 */
kern_return_t 
ule_thread_init(thread_t thread, ule_server_type_t server_type, uint32_t server_id)
{
    assert(thread != NULL);
    assert(server_type < ULE_SERVER_COUNT);
    
    /* Allocate thread state */
    ule_thread_state_t *thread_state = (ule_thread_state_t *)kalloc(sizeof(ule_thread_state_t));
    if (!thread_state) {
        return KERN_RESOURCE_SHORTAGE;
    }
    
    memset(thread_state, 0, sizeof(ule_thread_state_t));
    
    /* Initialize thread state */
    thread_state->sleep_time = 0;
    thread_state->run_time = 0;
    thread_state->last_schedule = ule_global_scheduler ? ule_global_scheduler->global_time : 0;
    thread_state->server_type = server_type;
    thread_state->is_server_thread = (server_id != 0);
    thread_state->server_id = server_id;
    
    /* Attach to thread */
    thread->ule_state = (void *)thread_state;
    
    return KERN_SUCCESS;
}

/*
 * Cleanup thread state
 */
void 
ule_thread_cleanup(thread_t thread)
{
    assert(thread != NULL);
    
    if (thread->ule_state) {
        kfree((vm_offset_t)thread->ule_state, sizeof(ule_thread_state_t));
        thread->ule_state = NULL;
    }
}

/*
 * Server thread creation helper
 */
kern_return_t 
ule_create_server_thread(ule_server_type_t server_type, uint32_t server_id, 
                        thread_t *out_thread)
{
    assert(out_thread != NULL);
    assert(server_type < ULE_SERVER_COUNT);
    
    /* Create a new kernel thread */
    thread_t thread;
    kern_return_t result = kernel_thread_create(THREAD_CONTINUE_NULL, NULL, 
                                               MAXPRI_SYSTEM, &thread);
    if (result != KERN_SUCCESS) {
        return result;
    }
    
    /* Initialize ULE state for the thread */
    result = ule_thread_init(thread, server_type, server_id);
    if (result != KERN_SUCCESS) {
        thread_deallocate(thread);
        return result;
    }
    
    /* Set thread properties */
    thread_policy_set(thread, THREAD_STANDARD_POLICY, NULL, 0);
    
    *out_thread = thread;
    return KERN_SUCCESS;
}

/*
 * Integration initialization
 */
kern_return_t 
ule_mach_integration_init(void)
{
    if (ule_integration_initialized) {
        return KERN_FAILURE;
    }
    
    /* Initialize per-CPU states */
    for (uint32_t i = 0; i < real_ncpus && i < MAX_CPUS; i++) {
        kern_return_t result = ule_setup_cpu_state(i);
        if (result != KERN_SUCCESS) {
            return result;
        }
    }
    
    /* Hook into Mach scheduler callbacks */
    /* Note: In a real implementation, this would involve modifying
     * the Mach scheduler to call our functions at appropriate points */
    
    ule_integration_initialized = true;
    return KERN_SUCCESS;
}

/*
 * Integration cleanup
 */
void 
ule_mach_integration_cleanup(void)
{
    if (!ule_integration_initialized) {
        return;
    }
    
    /* Clear per-CPU states */
    for (uint32_t i = 0; i < MAX_CPUS; i++) {
        ule_cpu_state_t *cpu_state = &ule_cpu_states[i];
        if (cpu_state->current_message) {
            kfree((vm_offset_t)cpu_state->current_message, sizeof(ule_message_t));
            cpu_state->current_message = NULL;
        }
    }
    
    ule_integration_initialized = false;
}

/*
 * Get CPU-specific statistics
 */
kern_return_t 
ule_get_cpu_stats(uint32_t cpu_id, ule_cpu_state_t *stats)
{
    assert(stats != NULL);
    
    if (cpu_id >= MAX_CPUS || !ule_integration_initialized) {
        return KERN_INVALID_ARGUMENT;
    }
    
    *stats = ule_cpu_states[cpu_id];
    return KERN_SUCCESS;
}

/*
 * Load balancing hint - migrate threads between cores
 */
kern_return_t 
ule_migrate_thread(thread_t thread, uint32_t target_cpu)
{
    assert(thread != NULL);
    assert(target_cpu < ule_global_scheduler->core_count);
    
    if (!ule_integration_initialized) {
        return KERN_FAILURE;
    }
    
    /* Convert thread to message */
    ule_message_t *msg = ule_thread_to_message(thread);
    if (!msg) {
        return KERN_FAILURE;
    }
    
    /* Block current thread */
    ule_scheduler_block(thread);
    
    /* Re-enqueue message (scheduler will pick optimal server) */
    kern_return_t result = ule_message_enqueue(msg);
    if (result == KERN_SUCCESS) {
        /* Wake up target CPU if it's idle */
        if (target_cpu != cpu_number()) {
            cpu_signal(target_cpu, SIGPcpureq, (void *)NULL, NULL);
        }
    }
    
    return result;
}