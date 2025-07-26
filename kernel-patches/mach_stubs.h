/*
 * Mach System Call Stubs for Testing
 * Simulates Mach port operations for test framework
 */

#ifndef _MACH_STUBS_H_
#define _MACH_STUBS_H_

#include <stdint.h>

/* Boolean type */
typedef int boolean_t;

/* Basic Mach types */
typedef int kern_return_t;
typedef uint32_t mach_port_t;
typedef uint32_t mach_port_name_t;
typedef uint32_t mach_port_right_t;
typedef uint32_t mach_port_type_t;
typedef void* ipc_space_t;
typedef void* ipc_port_t;
typedef void* task_t;

/* Return codes */
#define KERN_SUCCESS            0
#define KERN_INVALID_ARGUMENT   4
#define KERN_FAILURE            5
#define KERN_RESOURCE_SHORTAGE  6
#define KERN_INVALID_RIGHT      17
#define KERN_RIGHT_EXISTS       21
#define KERN_INVALID_NAME       15
#define KERN_NO_ACCESS          8

/* Port rights */
#define MACH_PORT_RIGHT_SEND        0
#define MACH_PORT_RIGHT_RECEIVE     1
#define MACH_PORT_RIGHT_SEND_ONCE   2
#define MACH_PORT_RIGHT_PORT_SET    3
#define MACH_PORT_RIGHT_DEAD_NAME   4

/* Port types */
#define MACH_PORT_TYPE_SEND         (1 << MACH_PORT_RIGHT_SEND)
#define MACH_PORT_TYPE_RECEIVE      (1 << MACH_PORT_RIGHT_RECEIVE)
#define MACH_PORT_TYPE_SEND_ONCE    (1 << MACH_PORT_RIGHT_SEND_ONCE)

/* Special port names */
#define MACH_PORT_NULL              0
#define MACH_PORT_DEAD              ((mach_port_t) ~0)

/* Function prototypes for simulation */
kern_return_t mach_port_allocate(task_t task, mach_port_right_t right, mach_port_t *name);
kern_return_t mach_port_insert_right(task_t task, mach_port_name_t name, mach_port_t poly, mach_port_right_t polyPoly);
kern_return_t mach_port_extract_right(task_t task, mach_port_name_t name, mach_port_right_t msgt_name, mach_port_t *poly, mach_port_type_t *polyPoly);
kern_return_t mach_port_destroy(task_t task, mach_port_name_t name);
kern_return_t mach_port_deallocate(task_t task, mach_port_name_t name);

/* Task operations */
task_t mach_task_self(void);
kern_return_t task_create(task_t parent_task, boolean_t inherit_memory, task_t *child_task);
kern_return_t task_terminate(task_t target_task);

/* Test control functions */
void mach_stubs_init(void);
void mach_stubs_cleanup(void);
void mach_stubs_enable_security_fix(int enable);
int mach_stubs_get_violation_count(void);

#endif /* _MACH_STUBS_H_ */