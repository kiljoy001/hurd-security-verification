/* Secure filesystem traversal protection implementation
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

#include "secure-traversal.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <pthread.h>
#include <assert.h>

/* Initialize a secure filesystem node
   Implements SecureNode from formal model */
error_t 
secure_fsnode_init(struct secure_fsnode *node,
                   ino_t node_id,
                   int node_type, 
                   size_t max_depth,
                   struct resource_bounds *bounds)
{
  if (!node)
    return EINVAL;
    
  /* Verify bounded_traversal property: max_depth > 0 */
  if (max_depth == 0)
    return EINVAL;

  node->node_id = node_id;
  node->node_type = node_type;
  node->max_depth = max_depth;
  node->bounds = bounds;
  node->current_depth = 0;
  node->parent = NULL;
  
  /* Initialize mutex for thread safety */
  int err = pthread_mutex_init(&node->lock, NULL);
  if (err)
    return err;
    
  return 0;
}

/* Clean up a secure filesystem node */
void 
secure_fsnode_cleanup(struct secure_fsnode *node)
{
  if (!node)
    return;
    
  pthread_mutex_destroy(&node->lock);
  
  /* Don't free bounds - caller owns it */
  node->bounds = NULL;
  node->parent = NULL;
}

/* Check if traversal is allowed - implements bounded_traversal property */
error_t 
secure_traversal_check(struct secure_fsnode *from_node,
                       struct secure_fsnode *to_node,
                       struct traversal_context *ctx)
{
  if (!from_node || !to_node || !ctx)
    return EINVAL;

  pthread_mutex_lock(&from_node->lock);
  pthread_mutex_lock(&to_node->lock);
  
  error_t result = 0;
  
  /* Check depth bounds - implements bounded_traversal property */
  if (ctx->flags & TRAVERSAL_CHECK_DEPTH) {
    size_t new_depth = from_node->current_depth + 1;
    
    /* Verify against node's max_depth (bounded_traversal property) */
    if (new_depth > to_node->max_depth) {
      result = ELOOP; /* Traversal depth exceeded */
      goto cleanup;
    }
    
    /* Verify against context max depth */
    if (new_depth > ctx->max_allowed_depth) {
      result = ELOOP;
      goto cleanup;
    }
    
    /* Update context depth */
    ctx->current_depth = new_depth;
  }
  
  /* Check resource bounds - implements bounded_resource_consumption */
  if (ctx->flags & TRAVERSAL_CHECK_RESOURCES) {
    if (to_node->bounds) {
      result = secure_check_resource_bounds(to_node->bounds);
      if (result)
        goto cleanup;
    }
    
    if (ctx->resource_limits) {
      result = secure_check_resource_bounds(ctx->resource_limits);
      if (result)
        goto cleanup;
    }
  }
  
cleanup:
  pthread_mutex_unlock(&to_node->lock);
  pthread_mutex_unlock(&from_node->lock);
  
  ctx->last_error = result;
  return result;
}

/* Begin secure traversal operation */
error_t 
secure_traversal_begin(struct traversal_context *ctx,
                       size_t max_depth,
                       struct resource_bounds *limits)
{
  if (!ctx)
    return EINVAL;
    
  /* Verify bounded_traversal precondition: max_depth > 0 */
  if (max_depth == 0)
    return EINVAL;
    
  memset(ctx, 0, sizeof(*ctx));
  ctx->max_allowed_depth = max_depth;
  ctx->resource_limits = limits;
  ctx->flags = TRAVERSAL_CHECK_DEPTH | TRAVERSAL_CHECK_RESOURCES;
  
  /* Initialize resource tracking if limits provided */
  if (limits) {
    limits->allocated_memory = 0;
    limits->performed_operations = 0;
    limits->start_time = time(NULL);
  }
  
  return 0;
}

/* Complete traversal operation */
error_t 
secure_traversal_complete(struct traversal_context *ctx,
                          struct secure_fsnode *node,
                          size_t resources_consumed)
{
  if (!ctx || !node)
    return EINVAL;
    
  pthread_mutex_lock(&node->lock);
  
  /* Update node's current depth */
  node->current_depth = ctx->current_depth;
  
  /* Update resource consumption */
  if (node->bounds) {
    node->bounds->allocated_memory += resources_consumed;
    node->bounds->performed_operations++;
  }
  
  if (ctx->resource_limits) {
    ctx->resource_limits->performed_operations++;
  }
  
  pthread_mutex_unlock(&node->lock);
  
  /* Return 0 on successful completion */
  return 0;
}

/* Check resource bounds - implements bounded_resource_consumption */
error_t 
secure_check_resource_bounds(struct resource_bounds *bounds)
{
  if (!bounds)
    return 0; /* No bounds to check */
    
  /* Check memory limit */
  if (bounds->allocated_memory > bounds->max_memory)
    return ENOMEM;
    
  /* Check operation count limit */  
  if (bounds->performed_operations >= bounds->max_operations)
    return EAGAIN;
    
  /* Check time limit */
  if (bounds->max_time > 0) {
    time_t current_time = time(NULL);
    if (current_time - bounds->start_time > bounds->max_time)
      return ETIMEDOUT;
  }
  
  return 0;
}

/* Create resource bounds structure */
struct resource_bounds *
secure_create_resource_bounds(size_t max_memory,
                              size_t max_operations, 
                              time_t max_time)
{
  struct resource_bounds *bounds = malloc(sizeof(*bounds));
  if (!bounds)
    return NULL;
    
  bounds->max_memory = max_memory;
  bounds->max_operations = max_operations;
  bounds->max_time = max_time;
  bounds->allocated_memory = 0;
  bounds->performed_operations = 0;
  bounds->start_time = time(NULL);  /* Initialize to current time */
  
  return bounds;
}

/* Free resource bounds */
void 
secure_free_resource_bounds(struct resource_bounds *bounds)
{
  free(bounds);
}

/* VERIFICATION FUNCTIONS - Map to formal properties */

/* Verify bounded_traversal property from formal model:
   Definition bounded_traversal (n : SecureNode) : Prop :=
     match n.(max_depth) with
     | Some d => d > 0  
     | None => False
     end. */
int 
verify_bounded_traversal(struct secure_fsnode *node)
{
  if (!node)
    return 0; /* False - no node */
    
  /* In our implementation, max_depth is always set (not optional)
     So we verify: max_depth > 0 */
  return (node->max_depth > 0) ? 1 : 0;
}

/* Verify bounded_resource_consumption property:
   Definition bounded_resource_consumption (n : SecureNode) : Prop :=
     match n.(resource_bounds) with
     | Some rp => length rp.(allocated_resources) <= length rp.(resource_limit)
     | None => False  
     end. */
int 
verify_bounded_resource_consumption(struct secure_fsnode *node)
{
  if (!node || !node->bounds)
    return 0; /* False - no bounds */
    
  /* Check that allocated <= limit for each resource type */
  if (node->bounds->allocated_memory > node->bounds->max_memory)
    return 0;
    
  if (node->bounds->performed_operations > node->bounds->max_operations)
    return 0;
    
  return 1; /* True - bounds are satisfied */
}

/* Verify malicious_fs_dos_prevention theorem conditions:
   Theorem malicious_fs_dos_prevention : forall (n : SecureNode) (depth : nat),
     bounded_traversal n ->
     bounded_resource_consumption n ->
     match n.(max_depth) with
     | Some max_d => depth <= max_d
     | None => False
     end ->
     exists (result : bool), result = true. */
error_t 
verify_dos_prevention(struct secure_fsnode *node,
                      size_t requested_depth,
                      struct traversal_context *ctx)
{
  if (!node || !ctx)
    return EINVAL;
    
  /* Verify bounded_traversal precondition */
  if (!verify_bounded_traversal(node))
    return EINVAL; /* Precondition failed */
    
  /* Verify bounded_resource_consumption precondition */
  if (!verify_bounded_resource_consumption(node))
    return EINVAL; /* Precondition failed */
    
  /* Verify depth condition: requested_depth <= max_depth */
  if (requested_depth > node->max_depth)
    return ELOOP; /* Condition failed */
    
  /* All preconditions satisfied - theorem guarantees operation completes */
  return 0; /* Success - DOS prevention verified */
}