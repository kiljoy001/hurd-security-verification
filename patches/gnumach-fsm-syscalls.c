/* FSM IPC System Call Implementation for GNU Mach
 * Integrates FSM-based IPC with real kernel syscall interface
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include <mach/kern_return.h>
#include <mach/port.h>
#include <mach/message.h>
#include <kern/thread.h>
#include <kern/ipc_kobject.h>
#include <kern/processor.h>
#include <vm/vm_map.h>
#include <vm/vm_kern.h>
#include <fsm_ipc/fsm_message.h>
#include <fsm_ipc/fsm_processor.h>
#include <fsm_ipc/fsm_routing.h>
#include <fsm_ipc/fsm_ule_integration.h>

/* Global FSM IPC system - initialized at boot */
static fsm_ule_integration_t *global_fsm_system = NULL;
static boolean_t fsm_ipc_initialized = FALSE;

/* Performance measurement structure */
typedef struct {
    uint64_t syscall_entry_cycles;
    uint64_t memory_copy_cycles;
    uint64_t fsm_processing_cycles;
    uint64_t scheduling_cycles;
    uint64_t syscall_exit_cycles;
    uint64_t total_cycles;
} fsm_perf_trace_t;

/* Initialize FSM IPC subsystem */
kern_return_t fsm_ipc_init(void)
{
    if (fsm_ipc_initialized)
        return KERN_SUCCESS;
    
    /* Allocate kernel memory for FSM system */
    global_fsm_system = (fsm_ule_integration_t *)kalloc(sizeof(fsm_ule_integration_t));
    if (!global_fsm_system)
        return KERN_RESOURCE_SHORTAGE;
    
    /* Initialize with number of processors and real-time policy */
    if (!fsm_ule_integration_init(global_fsm_system, 
                                  processor_count, 
                                  FSM_ULE_POLICY_REALTIME)) {
        kfree((vm_offset_t)global_fsm_system, sizeof(fsm_ule_integration_t));
        return KERN_FAILURE;
    }
    
    /* Configure for kernel operation */
    fsm_ule_set_numa_aware(global_fsm_system, TRUE);
    fsm_ule_apply_performance_defaults(global_fsm_system);
    
    fsm_ipc_initialized = TRUE;
    printf("FSM IPC system initialized with %d cores\n", processor_count);
    
    return KERN_SUCCESS;
}

/* Helper: Copy FSM message from user space to kernel space */
static kern_return_t fsm_copyin_message(
    vm_map_t user_map,
    vm_address_t user_addr,
    fsm_message_t *kernel_msg,
    fsm_perf_trace_t *perf)
{
    uint64_t start_cycles = rdtsc();
    
    /* Validate user address */
    if (!user_addr || user_addr & 0x3) {  /* Check alignment */
        return KERN_INVALID_ADDRESS;
    }
    
    /* Copy message structure from user space */
    kern_return_t kr = copyin((void*)user_addr, kernel_msg, sizeof(fsm_message_t));
    if (kr != KERN_SUCCESS) {
        return kr;
    }
    
    /* Validate message structure */
    if (!fsm_message_validate(kernel_msg)) {
        return KERN_INVALID_ARGUMENT;
    }
    
    /* Validate payload size */
    if (kernel_msg->payload_length > FSM_MAX_PAYLOAD_SIZE) {
        return KERN_INVALID_ARGUMENT;
    }
    
    perf->memory_copy_cycles = rdtsc() - start_cycles;
    return KERN_SUCCESS;
}

/* Helper: Copy FSM message from kernel space to user space */
static kern_return_t fsm_copyout_message(
    vm_map_t user_map,
    const fsm_message_t *kernel_msg,
    vm_address_t user_addr,
    fsm_perf_trace_t *perf)
{
    uint64_t start_cycles = rdtsc();
    
    /* Validate user address */
    if (!user_addr || user_addr & 0x3) {
        return KERN_INVALID_ADDRESS;
    }
    
    /* Copy message to user space */
    kern_return_t kr = copyout(kernel_msg, (void*)user_addr, sizeof(fsm_message_t));
    
    perf->memory_copy_cycles += rdtsc() - start_cycles;
    return kr;
}

/* FSM Message Send System Call */
kern_return_t fsm_msg_send_trap(
    mach_port_name_t dest_port,
    vm_address_t msg_addr,
    mach_msg_size_t msg_size,
    mach_msg_timeout_t timeout)
{
    fsm_perf_trace_t perf = {0};
    perf.syscall_entry_cycles = rdtsc();
    
    /* Check if FSM IPC is initialized */
    if (!fsm_ipc_initialized) {
        kern_return_t kr = fsm_ipc_init();
        if (kr != KERN_SUCCESS)
            return kr;
    }
    
    /* Validate parameters */
    if (msg_size != sizeof(fsm_message_t)) {
        return KERN_INVALID_ARGUMENT;
    }
    
    /* Get current thread and processor */
    thread_t current_thread = current_thread();
    if (!current_thread)
        return KERN_FAILURE;
    
    processor_t current_processor = current_processor();
    uint32_t core_id = current_processor->slot_num;
    
    /* Copy message from user space */
    fsm_message_t kernel_msg;
    kern_return_t kr = fsm_copyin_message(current_thread->map, 
                                          msg_addr, 
                                          &kernel_msg, 
                                          &perf);
    if (kr != KERN_SUCCESS)
        return kr;
    
    /* Set destination port in message */
    kernel_msg.dest_server = (uint16_t)dest_port;
    
    /* FSM processing */
    uint64_t fsm_start = rdtsc();
    
    /* Route message through FSM system */
    fsm_processing_result_t result = fsm_ule_schedule_message(global_fsm_system,
                                                              &kernel_msg,
                                                              core_id);
    
    perf.fsm_processing_cycles = rdtsc() - fsm_start;
    
    /* Handle scheduling integration */
    uint64_t sched_start = rdtsc();
    
    if (result == FSM_RESULT_SUCCESS) {
        /* Process the message immediately if possible */
        result = fsm_ule_process_next_message(global_fsm_system, core_id);
    }
    
    perf.scheduling_cycles = rdtsc() - sched_start;
    perf.syscall_exit_cycles = rdtsc() - perf.syscall_entry_cycles;
    perf.total_cycles = rdtsc() - perf.syscall_entry_cycles;
    
    /* Log performance data for analysis */
    #ifdef FSM_PERF_TRACE
    printf("FSM send: entry=%llu, copy=%llu, fsm=%llu, sched=%llu, total=%llu cycles\n",
           perf.syscall_entry_cycles, perf.memory_copy_cycles, 
           perf.fsm_processing_cycles, perf.scheduling_cycles, perf.total_cycles);
    #endif
    
    /* Convert FSM result to Mach kernel return code */
    switch (result) {
        case FSM_RESULT_SUCCESS:
            return KERN_SUCCESS;
        case FSM_RESULT_PENDING:
            return KERN_SUCCESS;  /* Message queued successfully */
        case FSM_RESULT_NO_MEMORY:
            return KERN_RESOURCE_SHORTAGE;
        case FSM_RESULT_INVALID_MESSAGE:
            return KERN_INVALID_ARGUMENT;
        default:
            return KERN_FAILURE;
    }
}

/* FSM Message Receive System Call */
kern_return_t fsm_msg_receive_trap(
    mach_port_name_t source_port,
    vm_address_t msg_addr,
    mach_msg_size_t max_size,
    mach_msg_timeout_t timeout)
{
    fsm_perf_trace_t perf = {0};
    perf.syscall_entry_cycles = rdtsc();
    
    /* Check if FSM IPC is initialized */
    if (!fsm_ipc_initialized) {
        kern_return_t kr = fsm_ipc_init();
        if (kr != KERN_SUCCESS)
            return kr;
    }
    
    /* Validate parameters */
    if (max_size < sizeof(fsm_message_t)) {
        return KERN_INVALID_ARGUMENT;
    }
    
    /* Get current processor */
    processor_t current_processor = current_processor();
    uint32_t core_id = current_processor->slot_num;
    
    /* FSM message processing */
    uint64_t fsm_start = rdtsc();
    
    /* Try to process next message from FSM queue */
    fsm_processing_result_t result = fsm_ule_process_next_message(global_fsm_system, 
                                                                  core_id);
    
    perf.fsm_processing_cycles = rdtsc() - fsm_start;
    
    if (result == FSM_RESULT_SUCCESS) {
        /* Get the processed message */
        fsm_message_t *processed_msg = fsm_get_last_processed_message(global_fsm_system, core_id);
        if (processed_msg) {
            /* Copy message to user space */
            thread_t current_thread = current_thread();
            kern_return_t kr = fsm_copyout_message(current_thread->map,
                                                   processed_msg,
                                                   msg_addr,
                                                   &perf);
            if (kr != KERN_SUCCESS)
                return kr;
        }
    }
    
    perf.total_cycles = rdtsc() - perf.syscall_entry_cycles;
    
    /* Log performance data */
    #ifdef FSM_PERF_TRACE
    printf("FSM recv: entry=%llu, fsm=%llu, copy=%llu, total=%llu cycles\n",
           perf.syscall_entry_cycles, perf.fsm_processing_cycles, 
           perf.memory_copy_cycles, perf.total_cycles);
    #endif
    
    /* Convert result */
    switch (result) {
        case FSM_RESULT_SUCCESS:
            return KERN_SUCCESS;
        case FSM_RESULT_NO_MESSAGE:
            return KERN_NO_MESSAGE;  /* No message available */
        case FSM_RESULT_PENDING:
            return KERN_NOT_READY;   /* Message being processed */
        default:
            return KERN_FAILURE;
    }
}

/* Get FSM IPC performance statistics - debug interface */
kern_return_t fsm_get_performance_stats(
    vm_address_t stats_addr,
    mach_msg_size_t stats_size)
{
    if (!fsm_ipc_initialized)
        return KERN_NOT_SUPPORTED;
    
    if (stats_size < sizeof(fsm_ule_integration_t))
        return KERN_INVALID_ARGUMENT;
    
    /* Copy system stats to user space */
    thread_t current_thread = current_thread();
    return copyout(global_fsm_system, (void*)stats_addr, sizeof(fsm_ule_integration_t));
}

/* FSM IPC system shutdown */
void fsm_ipc_shutdown(void)
{
    if (fsm_ipc_initialized && global_fsm_system) {
        fsm_ule_integration_shutdown(global_fsm_system);
        kfree((vm_offset_t)global_fsm_system, sizeof(fsm_ule_integration_t));
        global_fsm_system = NULL;
        fsm_ipc_initialized = FALSE;
    }
}