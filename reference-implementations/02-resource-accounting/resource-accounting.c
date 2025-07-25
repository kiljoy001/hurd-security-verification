/* Resource accounting system implementation
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

#include "resource-accounting.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <assert.h>
#include <stdio.h>

/* Resource type names for debugging */
static const char *resource_names[RESOURCE_TYPE_COUNT] = {
  "Memory", "CPU", "Storage", "FileHandles"
};

/* Create resource entry */
static struct resource_entry *
create_resource_entry(resource_type_t type, size_t amount)
{
  struct resource_entry *entry = malloc(sizeof(*entry));
  if (!entry)
    return NULL;
    
  entry->type = type;
  entry->amount = amount;
  entry->allocated_time = time(NULL);
  entry->next = NULL;
  
  return entry;
}

/* Free resource entry list */
static void
free_resource_list(struct resource_entry *head)
{
  while (head) {
    struct resource_entry *next = head->next;
    free(head);
    head = next;
  }
}

/* Add resource to list */
static error_t
add_resource_to_list(struct resource_entry **head, 
                     resource_type_t type, 
                     size_t amount)
{
  struct resource_entry *entry = create_resource_entry(type, amount);
  if (!entry)
    return ENOMEM;
    
  entry->next = *head;
  *head = entry;
  
  return 0;
}

/* Calculate total usage for resource type in list */
static size_t
calculate_usage_in_list(struct resource_entry *head, resource_type_t type)
{
  size_t total = 0;
  
  for (struct resource_entry *entry = head; entry; entry = entry->next) {
    if (entry->type == type) {
      total += entry->amount;
    }
  }
  
  return total;
}

/* Create resource principal - implements mkResourcePrincipal constructor */
struct resource_principal *
resource_principal_create(pid_t principal_id)
{
  struct resource_principal *principal = malloc(sizeof(*principal));
  if (!principal)
    return NULL;
    
  principal->principal_id = principal_id;
  principal->allocated_resources = NULL;
  principal->resource_limits = NULL;
  principal->flags = PRINCIPAL_ACTIVE | PRINCIPAL_ACCOUNTING_ON;
  principal->allocation_failures = 0;
  principal->successful_allocations = 0;
  principal->created_time = time(NULL);
  
  /* Initialize arrays */
  memset(principal->total_allocations, 0, sizeof(principal->total_allocations));
  memset(principal->limit_amounts, 0, sizeof(principal->limit_amounts));
  
  /* Initialize mutex */
  int err = pthread_mutex_init(&principal->lock, NULL);
  if (err) {
    free(principal);
    return NULL;
  }
  
  return principal;
}

/* Destroy resource principal */
void 
resource_principal_destroy(struct resource_principal *principal)
{
  if (!principal)
    return;
    
  pthread_mutex_lock(&principal->lock);
  
  free_resource_list(principal->allocated_resources);
  free_resource_list(principal->resource_limits);
  
  pthread_mutex_unlock(&principal->lock);
  pthread_mutex_destroy(&principal->lock);
  
  free(principal);
}

/* Set resource limit - updates resource_limit list from formal model */
error_t 
resource_principal_set_limit(struct resource_principal *principal,
                            resource_type_t type,
                            size_t limit)
{
  if (!principal || type >= RESOURCE_TYPE_COUNT)
    return EINVAL;
    
  pthread_mutex_lock(&principal->lock);
  
  /* Update fast lookup array */
  principal->limit_amounts[type] = limit;
  
  /* Add to formal model's resource_limit list */
  error_t err = add_resource_to_list(&principal->resource_limits, type, limit);
  
  pthread_mutex_unlock(&principal->lock);
  
  return err;
}

/* Allocate resource - implements allocate_resource from formal model */
struct allocation_result 
resource_allocate(struct resource_principal *principal,
                  resource_type_t type,
                  size_t amount)
{
  struct allocation_result result = {0};
  
  if (!principal || type >= RESOURCE_TYPE_COUNT) {
    result.status = EINVAL;
    return result;
  }
  
  pthread_mutex_lock(&principal->lock);
  
  /* Check quota if strict mode enabled */
  if (principal->flags & PRINCIPAL_QUOTA_STRICT) {
    size_t current_usage = principal->total_allocations[type];
    size_t limit = principal->limit_amounts[type];
    
    if (limit > 0 && current_usage + amount > limit) {
      result.status = EDQUOT; /* Quota exceeded */
      principal->allocation_failures++;
      goto cleanup;
    }
  }
  
  /* Perform allocation - add to allocated_resources list */
  error_t err = add_resource_to_list(&principal->allocated_resources, 
                                    type, amount);
  if (err) {
    result.status = err;
    principal->allocation_failures++;
    goto cleanup;
  }
  
  /* Update fast lookup totals */
  principal->total_allocations[type] += amount;
  principal->successful_allocations++;
  
  /* Return updated principal (formal model requirement) */
  result.status = 0;
  result.updated_principal = principal;
  result.allocated_amount = amount;
  
cleanup:
  pthread_mutex_unlock(&principal->lock);
  return result;
}

/* Free resource */
error_t 
resource_free(struct resource_principal *principal,
              resource_type_t type,
              size_t amount)
{
  if (!principal || type >= RESOURCE_TYPE_COUNT)
    return EINVAL;
    
  pthread_mutex_lock(&principal->lock);
  
  /* Check if we have enough allocated to free */
  if (principal->total_allocations[type] < amount) {
    pthread_mutex_unlock(&principal->lock);
    return EINVAL; /* Cannot free more than allocated */
  }
  
  /* Update fast lookup totals */
  principal->total_allocations[type] -= amount;
  
  /* Note: For simplicity, we don't remove from the linked list here.
     In a production system, you'd want to properly manage the list. */
  
  pthread_mutex_unlock(&principal->lock);
  return 0;
}

/* Check quota - implements respects_quota property verification */
int 
resource_check_quota(struct resource_principal *principal,
                     resource_type_t type,
                     size_t requested_amount)
{
  if (!principal || type >= RESOURCE_TYPE_COUNT)
    return 0; /* False - invalid parameters */
    
  pthread_mutex_lock(&principal->lock);
  
  size_t current_usage = principal->total_allocations[type];
  size_t limit = principal->limit_amounts[type];
  
  int result;
  if (limit == 0) {
    result = 1; /* True - no limit set */
  } else {
    result = (current_usage + requested_amount <= limit) ? 1 : 0;
  }
  
  pthread_mutex_unlock(&principal->lock);
  
  return result;
}

/* Get current usage */
size_t 
resource_get_usage(struct resource_principal *principal,
                   resource_type_t type)
{
  if (!principal || type >= RESOURCE_TYPE_COUNT)
    return 0;
    
  pthread_mutex_lock(&principal->lock);
  size_t usage = principal->total_allocations[type];
  pthread_mutex_unlock(&principal->lock);
  
  return usage;
}

/* Get resource limit */
size_t 
resource_get_limit(struct resource_principal *principal,
                   resource_type_t type)
{
  if (!principal || type >= RESOURCE_TYPE_COUNT)
    return 0;
    
  pthread_mutex_lock(&principal->lock);
  size_t limit = principal->limit_amounts[type];
  pthread_mutex_unlock(&principal->lock);
  
  return limit;
}

/* VERIFICATION FUNCTIONS */

/* Verify resource_allocation_length_property from formal model:
   forall rp r rp', allocate_resource rp r = Some rp' ->
   length rp'.(allocated_resources) <= length rp'.(resource_limit) */
int 
verify_allocation_length_property(struct resource_principal *principal)
{
  if (!principal)
    return 0; /* False - no principal */
    
  pthread_mutex_lock(&principal->lock);
  
  /* Count entries in allocated_resources list */
  size_t allocated_count = 0;
  for (struct resource_entry *entry = principal->allocated_resources; 
       entry; entry = entry->next) {
    allocated_count++;
  }
  
  /* Count entries in resource_limit list */
  size_t limit_count = 0;
  for (struct resource_entry *entry = principal->resource_limits;
       entry; entry = entry->next) {
    limit_count++;
  }
  
  int result = (allocated_count <= limit_count) ? 1 : 0;
  
  pthread_mutex_unlock(&principal->lock);
  
  return result;
}

/* Verify respects_quota property */
int 
verify_respects_quota(struct resource_principal *principal,
                      resource_type_t type,
                      size_t amount)
{
  return resource_check_quota(principal, type, amount);
}

/* Resource iteration */
void 
resource_iterate_allocations(struct resource_principal *principal,
                             resource_iterator_func iterator,
                             void *user_data)
{
  if (!principal || !iterator)
    return;
    
  pthread_mutex_lock(&principal->lock);
  
  for (struct resource_entry *entry = principal->allocated_resources;
       entry; entry = entry->next) {
    iterator(entry->type, entry->amount, entry->allocated_time, user_data);
  }
  
  pthread_mutex_unlock(&principal->lock);
}

/* Get statistics */
void 
resource_get_stats(struct resource_principal *principal,
                   struct resource_stats *stats)
{
  if (!principal || !stats)
    return;
    
  memset(stats, 0, sizeof(*stats));
  
  pthread_mutex_lock(&principal->lock);
  
  stats->total_allocations = principal->successful_allocations;
  stats->allocation_failures = principal->allocation_failures;
  
  /* Calculate utilization */
  for (int i = 0; i < RESOURCE_TYPE_COUNT; i++) {
    size_t usage = principal->total_allocations[i];
    size_t limit = principal->limit_amounts[i];
    
    stats->peak_usage[i] = usage; /* Simplified - should track historical peak */
    
    if (limit > 0) {
      stats->utilization_percent[i] = (100.0 * usage) / limit;
    }
  }
  
  pthread_mutex_unlock(&principal->lock);
}

/* Utility functions */
const char *
resource_type_name(resource_type_t type)
{
  if (type >= RESOURCE_TYPE_COUNT)
    return "Unknown";
  return resource_names[type];
}

void 
resource_print_usage(struct resource_principal *principal)
{
  if (!principal)
    return;
    
  printf("Resource Principal %d Usage:\n", principal->principal_id);
  
  for (int i = 0; i < RESOURCE_TYPE_COUNT; i++) {
    size_t usage = resource_get_usage(principal, i);
    size_t limit = resource_get_limit(principal, i);
    
    printf("  %s: %zu", resource_type_name(i), usage);
    if (limit > 0) {
      printf(" / %zu (%.1f%%)", limit, (100.0 * usage) / limit);
    }
    printf("\n");
  }
}

/* System-wide resource management */

error_t 
resource_system_init(struct resource_system *system, size_t max_principals)
{
  if (!system || max_principals == 0)
    return EINVAL;
    
  memset(system, 0, sizeof(*system));
  
  system->principals = malloc(max_principals * sizeof(struct resource_principal *));
  if (!system->principals)
    return ENOMEM;
    
  system->max_principals = max_principals;
  
  int err = pthread_mutex_init(&system->global_lock, NULL);
  if (err) {
    free(system->principals);
    return err;
  }
  
  return 0;
}

error_t 
resource_system_register(struct resource_system *system,
                         struct resource_principal *principal)
{
  if (!system || !principal)
    return EINVAL;
    
  pthread_mutex_lock(&system->global_lock);
  
  if (system->num_principals >= system->max_principals) {
    pthread_mutex_unlock(&system->global_lock);
    return ENOSPC;
  }
  
  system->principals[system->num_principals++] = principal;
  
  pthread_mutex_unlock(&system->global_lock);
  return 0;
}

struct resource_principal *
resource_system_find(struct resource_system *system, pid_t principal_id)
{
  if (!system)
    return NULL;
    
  pthread_mutex_lock(&system->global_lock);
  
  struct resource_principal *found = NULL;
  for (size_t i = 0; i < system->num_principals; i++) {
    if (system->principals[i]->principal_id == principal_id) {
      found = system->principals[i];
      break;
    }
  }
  
  pthread_mutex_unlock(&system->global_lock);
  return found;
}

void 
resource_system_cleanup(struct resource_system *system)
{
  if (!system)
    return;
    
  pthread_mutex_lock(&system->global_lock);
  
  /* Note: Principals should be destroyed by their owners */
  free(system->principals);
  system->principals = NULL;
  system->num_principals = 0;
  
  pthread_mutex_unlock(&system->global_lock);
  pthread_mutex_destroy(&system->global_lock);
}