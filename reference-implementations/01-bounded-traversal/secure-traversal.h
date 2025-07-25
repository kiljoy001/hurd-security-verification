/* Secure filesystem traversal protection for GNU Hurd
   Implements the bounded_traversal property from the formal verification.
   
   Human Operator: Scott J. Guyton
   AI-Generated Implementation via Claude Code
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

#ifndef _HURD_SECURE_TRAVERSAL_H
#define _HURD_SECURE_TRAVERSAL_H

#include <sys/types.h>
#include <stdint.h>
/* #include <hurd/hurd_types.h> */

/* Basic types for demonstration */
typedef int error_t;

/* Default maximum traversal depth to prevent DOS attacks */
#define DEFAULT_MAX_TRAVERSAL_DEPTH 100

/* Resource bounds for filesystem operations */
struct resource_bounds {
  size_t max_memory;      /* Maximum memory consumption */
  size_t max_operations;  /* Maximum number of operations */
  time_t max_time;        /* Maximum time for operation */
  size_t allocated_memory;    /* Currently allocated memory */
  size_t performed_operations; /* Operations performed so far */
  time_t start_time;          /* Operation start time */
};

/* Secure filesystem node - implements SecureNode from formal model */
struct secure_fsnode {
  ino_t node_id;              /* Node identifier */
  int node_type;              /* 0 = file, 1 = directory */
  
  /* Security properties from formal model */
  size_t max_depth;           /* Maximum traversal depth (bounded_traversal) */
  struct resource_bounds *bounds; /* Resource consumption bounds */
  
  /* Implementation fields */
  size_t current_depth;       /* Current traversal depth */
  struct secure_fsnode *parent; /* Parent node for traversal tracking */
  pthread_mutex_t lock;       /* Protection for concurrent access */
};

/* Traversal context for secure operations */
struct traversal_context {
  size_t current_depth;
  size_t max_allowed_depth;
  struct resource_bounds *resource_limits;
  error_t last_error;
  int flags;
};

/* Context flags */
#define TRAVERSAL_CHECK_DEPTH    0x01
#define TRAVERSAL_CHECK_RESOURCES 0x02
#define TRAVERSAL_STRICT_MODE    0x04

/* Function prototypes */

/* Initialize a secure filesystem node
   Maps to SecureNode constructor from formal model */
error_t secure_fsnode_init(struct secure_fsnode *node,
                          ino_t node_id,
                          int node_type,
                          size_t max_depth,
                          struct resource_bounds *bounds);

/* Clean up a secure filesystem node */
void secure_fsnode_cleanup(struct secure_fsnode *node);

/* Check if traversal to a node is allowed
   Implements bounded_traversal property verification */
error_t secure_traversal_check(struct secure_fsnode *from_node,
                              struct secure_fsnode *to_node,
                              struct traversal_context *ctx);

/* Begin a secure traversal operation
   Implements malicious_fs_dos_prevention theorem preconditions */
error_t secure_traversal_begin(struct traversal_context *ctx,
                              size_t max_depth,
                              struct resource_bounds *limits);

/* Complete a traversal operation and update resource usage */
error_t secure_traversal_complete(struct traversal_context *ctx,
                                 struct secure_fsnode *node,
                                 size_t resources_consumed);

/* Check if current operation violates resource bounds
   Implements bounded_resource_consumption property */
error_t secure_check_resource_bounds(struct resource_bounds *bounds);

/* Create resource bounds structure with limits */
struct resource_bounds *secure_create_resource_bounds(size_t max_memory,
                                                     size_t max_operations,
                                                     time_t max_time);

/* Free resource bounds structure */
void secure_free_resource_bounds(struct resource_bounds *bounds);

/* Verification functions for formal properties */

/* Verify bounded_traversal property holds for a node */
int verify_bounded_traversal(struct secure_fsnode *node);

/* Verify bounded_resource_consumption property holds */
int verify_bounded_resource_consumption(struct secure_fsnode *node);

/* Test that malicious_fs_dos_prevention theorem conditions are met */
error_t verify_dos_prevention(struct secure_fsnode *node, 
                             size_t requested_depth,
                             struct traversal_context *ctx);

#endif /* _HURD_SECURE_TRAVERSAL_H */