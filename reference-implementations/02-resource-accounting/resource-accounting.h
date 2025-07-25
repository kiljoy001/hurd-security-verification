/* Resource accounting system for GNU Hurd
   Implements ResourcePrincipal and resource management from formal verification.
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

#ifndef _HURD_RESOURCE_ACCOUNTING_H
#define _HURD_RESOURCE_ACCOUNTING_H

#include <sys/types.h>
#include <stdint.h>
#include <pthread.h>
/* #include <hurd/hurd_types.h> */

/* Resource types from formal model */
typedef enum {
  RESOURCE_MEMORY = 0,     /* Amount of memory in bytes */
  RESOURCE_CPU = 1,        /* CPU cycles or time slices */
  RESOURCE_STORAGE = 2,    /* Storage blocks */
  RESOURCE_FILE_HANDLES = 3, /* Number of file handles */
  RESOURCE_TYPE_COUNT      /* Number of resource types */
} resource_type_t;

/* Single resource allocation entry */
struct resource_entry {
  resource_type_t type;
  size_t amount;
  time_t allocated_time;
  struct resource_entry *next;
};

/* Resource principal - implements ResourcePrincipal from formal model */
struct resource_principal {
  pid_t principal_id;              /* Principal identifier */
  
  /* Resource lists from formal model */
  struct resource_entry *allocated_resources; /* Currently allocated */
  struct resource_entry *resource_limits;     /* Maximum allowed */
  
  /* Implementation fields */
  pthread_mutex_t lock;            /* Protection for concurrent access */
  size_t total_allocations[RESOURCE_TYPE_COUNT]; /* Fast lookup totals */
  size_t limit_amounts[RESOURCE_TYPE_COUNT];     /* Fast lookup limits */
  int flags;                       /* Operational flags */
  
  /* Statistics */
  size_t allocation_failures;
  size_t successful_allocations;
  time_t created_time;
};

/* Principal flags */
#define PRINCIPAL_ACTIVE       0x01
#define PRINCIPAL_QUOTA_STRICT 0x02  /* Fail allocations that exceed quota */
#define PRINCIPAL_ACCOUNTING_ON 0x04 /* Track all resource usage */

/* Resource allocation result from formal model allocate_resource function */
struct allocation_result {
  error_t status;                  /* Success/failure code */
  struct resource_principal *updated_principal; /* Updated principal or NULL */
  size_t allocated_amount;         /* Amount actually allocated */
};

/* Function prototypes */

/* Create a new resource principal
   Maps to mkResourcePrincipal constructor from formal model */
struct resource_principal *resource_principal_create(pid_t principal_id);

/* Destroy a resource principal */
void resource_principal_destroy(struct resource_principal *principal);

/* Set resource limit for a principal
   Updates the resource_limit list from formal model */
error_t resource_principal_set_limit(struct resource_principal *principal,
                                    resource_type_t type,
                                    size_t limit);

/* Allocate resource with principal - implements allocate_resource from formal model
   Definition allocate_resource (rp : ResourcePrincipal) (r : resource_type) : 
     option ResourcePrincipal */
struct allocation_result resource_allocate(struct resource_principal *principal,
                                          resource_type_t type,
                                          size_t amount);

/* Free previously allocated resource */
error_t resource_free(struct resource_principal *principal,
                     resource_type_t type,
                     size_t amount);

/* Check if allocation would exceed quota - implements respects_quota property
   Definition respects_quota (allocator : ResourcePrincipal -> resource_type -> 
     option ResourcePrincipal) : Prop */
int resource_check_quota(struct resource_principal *principal,
                        resource_type_t type, 
                        size_t requested_amount);

/* Get current resource usage */
size_t resource_get_usage(struct resource_principal *principal,
                         resource_type_t type);

/* Get resource limit */
size_t resource_get_limit(struct resource_principal *principal,
                         resource_type_t type);

/* Verification functions for formal properties */

/* Verify resource_allocation_length_property:
   forall rp r rp', allocate_resource rp r = Some rp' ->
   length rp'.(allocated_resources) <= length rp'.(resource_limit) */
int verify_allocation_length_property(struct resource_principal *principal);

/* Verify respects_quota property from formal model */
int verify_respects_quota(struct resource_principal *principal,
                         resource_type_t type,
                         size_t amount);

/* Resource iterator for examining allocations */
typedef void (*resource_iterator_func)(resource_type_t type, 
                                      size_t amount, 
                                      time_t allocated_time,
                                      void *user_data);

void resource_iterate_allocations(struct resource_principal *principal,
                                 resource_iterator_func iterator,
                                 void *user_data);

/* Resource statistics */
struct resource_stats {
  size_t total_allocations;
  size_t total_deallocations;
  size_t allocation_failures;
  size_t peak_usage[RESOURCE_TYPE_COUNT];
  double utilization_percent[RESOURCE_TYPE_COUNT];
};

void resource_get_stats(struct resource_principal *principal,
                       struct resource_stats *stats);

/* System-wide resource management */
struct resource_system {
  pthread_mutex_t global_lock;
  struct resource_principal **principals;
  size_t num_principals;
  size_t max_principals;
  size_t system_limits[RESOURCE_TYPE_COUNT];
};

/* Initialize global resource system */
error_t resource_system_init(struct resource_system *system,
                            size_t max_principals);

/* Register a principal with the system */
error_t resource_system_register(struct resource_system *system,
                                struct resource_principal *principal);

/* Unregister a principal */
error_t resource_system_unregister(struct resource_system *system,
                                  pid_t principal_id);

/* Find principal by ID */
struct resource_principal *resource_system_find(struct resource_system *system,
                                               pid_t principal_id);

/* Set system-wide resource limits */
error_t resource_system_set_limit(struct resource_system *system,
                                 resource_type_t type,
                                 size_t limit);

/* Cleanup global resource system */
void resource_system_cleanup(struct resource_system *system);

/* Utility functions */
const char *resource_type_name(resource_type_t type);
void resource_print_usage(struct resource_principal *principal);

#endif /* _HURD_RESOURCE_ACCOUNTING_H */