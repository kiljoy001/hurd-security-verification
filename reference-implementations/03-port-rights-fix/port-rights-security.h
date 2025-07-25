/* Port rights security enforcement for GNU Hurd
   Implements port_rights_task_exclusive theorem from formal verification.
   Copyright (C) 2025 Free Software Foundation, Inc.

   This file is part of the GNU Hurd.

   The GNU Hurd is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2, or (at
   your option) any later version.

   The GNU Hurd is distributed in the hope that it will be useful, 
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#ifndef _HURD_PORT_RIGHTS_SECURITY_H
#define _HURD_PORT_RIGHTS_SECURITY_H

#include <sys/types.h>
#include <stdint.h>
#include <pthread.h>
/* #include <mach.h> */
/* #include <hurd/hurd_types.h> */

/* Basic types for demonstration */
typedef uint32_t mach_port_t;

/* Port right types from formal model */
typedef enum {
  PORT_RIGHT_SEND = 0,
  PORT_RIGHT_RECEIVE = 1
} port_right_type_t;

/* Port information for security tracking */
struct secure_port_info {
  mach_port_t port_id;             /* Port identifier */
  pid_t owner_task;                /* Task that owns this port instance */
  int rights;                      /* Bitmask of rights held */
  struct secure_port_info *next;   /* For hash table chaining */
  pthread_mutex_t lock;            /* Per-port lock */
  time_t created_time;
  int flags;
};

/* Port rights flags */
#define PORT_HAS_SEND_RIGHT    0x01
#define PORT_HAS_RECEIVE_RIGHT 0x02
#define PORT_RIGHTS_VERIFIED   0x04

/* Global port rights registry */
struct port_rights_registry {
  struct secure_port_info **hash_table;
  size_t table_size;
  pthread_mutex_t global_lock;
  size_t num_ports;
  int initialized;
};

/* Function prototypes */

/* Initialize the port rights security system */
error_t port_rights_security_init(void);

/* Cleanup port rights security system */
void port_rights_security_cleanup(void);

/* Register port with security system */
error_t port_rights_register(mach_port_t port_id, 
                             pid_t owner_task,
                             port_right_type_t right_type);

/* Unregister port from security system */
error_t port_rights_unregister(mach_port_t port_id, pid_t owner_task);

/* Check if port rights assignment violates exclusivity
   Implements the port_rights_task_exclusive theorem check */
error_t port_rights_check_exclusive(mach_port_t port_id,
                                   pid_t requesting_task,
                                   port_right_type_t right_type);

/* Verify receive rights exclusivity property
   Implements receive_rights_exclusive_property from formal model */
int port_rights_verify_receive_exclusive(mach_port_t port_id);

/* Check if task can send RPC on port
   Implements can_send_rpc property */
int port_rights_can_send_rpc(mach_port_t port_id, pid_t task);

/* Check if task can receive RPC on port
   Implements can_receive_rpc property */
int port_rights_can_receive_rpc(mach_port_t port_id, pid_t task);

/* Transfer port right between tasks
   Implements transfer_right property with validation */
error_t port_rights_transfer(mach_port_t port_id,
                            port_right_type_t right_type,
                            pid_t from_task,
                            pid_t to_task);

/* Get port owner for a specific right type */
pid_t port_rights_get_owner(mach_port_t port_id, port_right_type_t right_type);

/* Verification functions */

/* Verify that the port_rights_task_exclusive theorem holds
   This checks: if p1 and p2 have same port ID, p1 has receive rights,
   p2 has send rights, and they have different owners, then p2 cannot
   also have receive rights */
int verify_port_rights_task_exclusive(mach_port_t port_id);

/* Audit all ports for rights violations */
error_t port_rights_audit_all(void);

/* Statistics and debugging */
struct port_rights_stats {
  size_t total_ports;
  size_t ports_with_send_rights;
  size_t ports_with_receive_rights;
  size_t exclusivity_violations;
  size_t failed_transfers;
};

void port_rights_get_stats(struct port_rights_stats *stats);
void port_rights_print_registry(void);

/* Test functions for formal verification */
error_t port_rights_run_tests(void);

#endif /* _HURD_PORT_RIGHTS_SECURITY_H */