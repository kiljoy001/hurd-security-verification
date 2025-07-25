/* Port rights security enforcement implementation
   Copyright (C) 2025 Free Software Foundation, Inc. */

#include "port-rights-security.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>

/* Global registry instance */
static struct port_rights_registry g_registry = {0};

/* Hash function for port IDs */
static size_t 
hash_port_id(mach_port_t port_id, size_t table_size)
{
  return (size_t)port_id % table_size;
}

/* Find port info in registry (must hold global lock) */
static struct secure_port_info *
find_port_info_locked(mach_port_t port_id, pid_t owner_task)
{
  if (!g_registry.initialized)
    return NULL;
    
  size_t hash = hash_port_id(port_id, g_registry.table_size);
  struct secure_port_info *info = g_registry.hash_table[hash];
  
  while (info) {
    if (info->port_id == port_id && info->owner_task == owner_task) {
      return info;
    }
    info = info->next;
  }
  
  return NULL;
}

/* Initialize port rights security system */
error_t 
port_rights_security_init(void)
{
  if (g_registry.initialized)
    return 0; /* Already initialized */
    
  g_registry.table_size = 1024; /* Hash table size */
  g_registry.hash_table = calloc(g_registry.table_size, 
                                sizeof(struct secure_port_info *));
  if (!g_registry.hash_table)
    return ENOMEM;
    
  int err = pthread_mutex_init(&g_registry.global_lock, NULL);
  if (err) {
    free(g_registry.hash_table);
    return err;
  }
  
  g_registry.num_ports = 0;
  g_registry.initialized = 1;
  
  return 0;
}

/* Cleanup port rights security system */
void 
port_rights_security_cleanup(void)
{
  if (!g_registry.initialized)
    return;
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  /* Free all port info structures */
  for (size_t i = 0; i < g_registry.table_size; i++) {
    struct secure_port_info *info = g_registry.hash_table[i];
    while (info) {
      struct secure_port_info *next = info->next;
      pthread_mutex_destroy(&info->lock);
      free(info);
      info = next;
    }
  }
  
  free(g_registry.hash_table);
  g_registry.hash_table = NULL;
  g_registry.initialized = 0;
  
  pthread_mutex_unlock(&g_registry.global_lock);
  pthread_mutex_destroy(&g_registry.global_lock);
}

/* Register port with security system */
error_t 
port_rights_register(mach_port_t port_id,
                     pid_t owner_task,
                     port_right_type_t right_type)
{
  if (!g_registry.initialized) {
    error_t err = port_rights_security_init();
    if (err)
      return err;
  }
  
  pthread_mutex_lock(&g_registry.global_lock);
  
  /* Check for existing port info */
  struct secure_port_info *existing = find_port_info_locked(port_id, owner_task);
  if (existing) {
    /* Update existing rights */
    pthread_mutex_lock(&existing->lock);
    
    if (right_type == PORT_RIGHT_SEND) {
      existing->rights |= PORT_HAS_SEND_RIGHT;
    } else {
      existing->rights |= PORT_HAS_RECEIVE_RIGHT;
    }
    
    pthread_mutex_unlock(&existing->lock);
    pthread_mutex_unlock(&g_registry.global_lock);
    return 0;
  }
  
  /* Create new port info */
  struct secure_port_info *info = malloc(sizeof(*info));
  if (!info) {
    pthread_mutex_unlock(&g_registry.global_lock);
    return ENOMEM;
  }
  
  info->port_id = port_id;
  info->owner_task = owner_task;
  info->rights = (right_type == PORT_RIGHT_SEND) ? 
                 PORT_HAS_SEND_RIGHT : PORT_HAS_RECEIVE_RIGHT;
  info->created_time = time(NULL);
  info->flags = 0;
  
  int err = pthread_mutex_init(&info->lock, NULL);
  if (err) {
    free(info);
    pthread_mutex_unlock(&g_registry.global_lock);
    return err;
  }
  
  /* Add to hash table */
  size_t hash = hash_port_id(port_id, g_registry.table_size);
  info->next = g_registry.hash_table[hash];
  g_registry.hash_table[hash] = info;
  g_registry.num_ports++;
  
  pthread_mutex_unlock(&g_registry.global_lock);
  return 0;
}

/* Check port rights exclusivity - implements port_rights_task_exclusive theorem */
error_t 
port_rights_check_exclusive(mach_port_t port_id,
                           pid_t requesting_task,
                           port_right_type_t right_type)
{
  if (!g_registry.initialized)
    return ENOENT;
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  /* If requesting receive rights, check that no other task has receive rights */
  if (right_type == PORT_RIGHT_RECEIVE) {
    size_t hash = hash_port_id(port_id, g_registry.table_size);
    struct secure_port_info *info = g_registry.hash_table[hash];
    
    while (info) {
      if (info->port_id == port_id && 
          info->owner_task != requesting_task &&
          (info->rights & PORT_HAS_RECEIVE_RIGHT)) {
        
        /* VIOLATION: Another task already has receive rights
           This implements the port_rights_task_exclusive theorem:
           receive rights are exclusive per port */
        pthread_mutex_unlock(&g_registry.global_lock);
        return EACCES; /* Access denied - exclusivity violation */
      }
      info = info->next;
    }
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
  return 0; /* No exclusivity violation */
}

/* Verify receive rights exclusive property from formal model */
int 
port_rights_verify_receive_exclusive(mach_port_t port_id)
{
  if (!g_registry.initialized)
    return 1; /* Vacuously true - no registry */
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  pid_t receive_owner = -1;
  int receive_count = 0;
  
  /* Count tasks with receive rights for this port */
  size_t hash = hash_port_id(port_id, g_registry.table_size);
  struct secure_port_info *info = g_registry.hash_table[hash];
  
  while (info) {
    if (info->port_id == port_id && 
        (info->rights & PORT_HAS_RECEIVE_RIGHT)) {
      
      if (receive_owner == -1) {
        receive_owner = info->owner_task;
      } else if (receive_owner != info->owner_task) {
        /* Multiple different tasks have receive rights - violation! */
        pthread_mutex_unlock(&g_registry.global_lock);
        return 0; /* False - exclusivity violated */
      }
      receive_count++;
    }
    info = info->next;
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
  
  /* Property holds if at most one task has receive rights */
  return (receive_count <= 1) ? 1 : 0;
}

/* Check if task can send RPC - implements can_send_rpc property */
int 
port_rights_can_send_rpc(mach_port_t port_id, pid_t task)
{
  if (!g_registry.initialized)
    return 0; /* False - no registry */
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  struct secure_port_info *info = find_port_info_locked(port_id, task);
  int can_send = 0;
  
  if (info) {
    pthread_mutex_lock(&info->lock);
    can_send = (info->rights & PORT_HAS_SEND_RIGHT) ? 1 : 0;
    pthread_mutex_unlock(&info->lock);
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
  return can_send;
}

/* Check if task can receive RPC - implements can_receive_rpc property */
int 
port_rights_can_receive_rpc(mach_port_t port_id, pid_t task)
{
  if (!g_registry.initialized)
    return 0; /* False - no registry */
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  struct secure_port_info *info = find_port_info_locked(port_id, task);
  int can_receive = 0;
  
  if (info) {
    pthread_mutex_lock(&info->lock);
    can_receive = (info->rights & PORT_HAS_RECEIVE_RIGHT) ? 1 : 0;
    pthread_mutex_unlock(&info->lock);
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
  return can_receive;
}

/* Transfer port right - implements transfer_right property with validation */
error_t 
port_rights_transfer(mach_port_t port_id,
                     port_right_type_t right_type,
                     pid_t from_task,
                     pid_t to_task)
{
  if (!g_registry.initialized)
    return ENOENT;
    
  /* First check if transfer would violate exclusivity */
  error_t err = port_rights_check_exclusive(port_id, to_task, right_type);
  if (err)
    return err;
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  /* Find source port info */
  struct secure_port_info *from_info = find_port_info_locked(port_id, from_task);
  if (!from_info) {
    pthread_mutex_unlock(&g_registry.global_lock);
    return ENOENT; /* Source doesn't have the port */
  }
  
  pthread_mutex_lock(&from_info->lock);
  
  /* Verify source has the right to transfer */
  int required_right = (right_type == PORT_RIGHT_SEND) ? 
                       PORT_HAS_SEND_RIGHT : PORT_HAS_RECEIVE_RIGHT;
  
  if (!(from_info->rights & required_right)) {
    pthread_mutex_unlock(&from_info->lock);
    pthread_mutex_unlock(&g_registry.global_lock);
    return EACCES; /* Source doesn't have this right */
  }
  
  /* Remove right from source (for receive rights, since they're exclusive) */
  if (right_type == PORT_RIGHT_RECEIVE) {
    from_info->rights &= ~PORT_HAS_RECEIVE_RIGHT;
  }
  
  pthread_mutex_unlock(&from_info->lock);
  
  /* Register right with destination */
  err = port_rights_register(port_id, to_task, right_type);
  
  pthread_mutex_unlock(&g_registry.global_lock);
  
  return err;
}

/* VERIFICATION FUNCTIONS */

/* Verify port_rights_task_exclusive theorem holds for a port */
int 
verify_port_rights_task_exclusive(mach_port_t port_id)
{
  if (!g_registry.initialized)
    return 1; /* Vacuously true */
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  struct secure_port_info *p1 = NULL, *p2 = NULL;
  
  /* Find two different tasks with rights to this port */
  size_t hash = hash_port_id(port_id, g_registry.table_size);
  struct secure_port_info *info = g_registry.hash_table[hash];
  
  while (info) {
    if (info->port_id == port_id) {
      if (!p1) {
        p1 = info;
      } else if (info->owner_task != p1->owner_task) {
        p2 = info;
        break;
      }
    }
    info = info->next;
  }
  
  int result = 1; /* Default: theorem holds */
  
  if (p1 && p2) {
    /* Check theorem conditions:
       p1.(id) = p2.(id) -> TRUE (same port_id)
       can_receive_rpc p1 -> p1 has receive rights
       can_send_rpc p2 -> p2 has send rights  
       p1.(owner_task) <> p2.(owner_task) -> TRUE (different tasks)
       
       Conclusion: ~ (can_receive_rpc p2) -> p2 should NOT have receive rights
    */
    
    pthread_mutex_lock(&p1->lock);
    pthread_mutex_lock(&p2->lock);
    
    int p1_has_receive = (p1->rights & PORT_HAS_RECEIVE_RIGHT) ? 1 : 0;
    int p2_has_send = (p2->rights & PORT_HAS_SEND_RIGHT) ? 1 : 0;
    int p2_has_receive = (p2->rights & PORT_HAS_RECEIVE_RIGHT) ? 1 : 0;
    
    /* If p1 has receive rights and p2 has send rights, 
       then p2 should NOT have receive rights */
    if (p1_has_receive && p2_has_send && p2_has_receive) {
      result = 0; /* Theorem violated! */
    }
    
    pthread_mutex_unlock(&p2->lock);
    pthread_mutex_unlock(&p1->lock);
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
  
  return result;
}

/* Get statistics */
void 
port_rights_get_stats(struct port_rights_stats *stats)
{
  if (!stats || !g_registry.initialized) {
    if (stats) memset(stats, 0, sizeof(*stats));
    return;
  }
    
  memset(stats, 0, sizeof(*stats));
  
  pthread_mutex_lock(&g_registry.global_lock);
  
  stats->total_ports = g_registry.num_ports;
  
  /* Count rights and violations */
  for (size_t i = 0; i < g_registry.table_size; i++) {
    struct secure_port_info *info = g_registry.hash_table[i];
    while (info) {
      if (info->rights & PORT_HAS_SEND_RIGHT) {
        stats->ports_with_send_rights++;
      }
      if (info->rights & PORT_HAS_RECEIVE_RIGHT) {
        stats->ports_with_receive_rights++;
      }
      
      /* Check for exclusivity violations */
      if (!verify_port_rights_task_exclusive(info->port_id)) {
        stats->exclusivity_violations++;
      }
      
      info = info->next;
    }
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
}

/* Print registry for debugging */
void 
port_rights_print_registry(void)
{
  if (!g_registry.initialized) {
    printf("Port rights registry not initialized\n");
    return;
  }
    
  pthread_mutex_lock(&g_registry.global_lock);
  
  printf("Port Rights Registry (%zu ports):\n", g_registry.num_ports);
  printf("====================================\n");
  
  for (size_t i = 0; i < g_registry.table_size; i++) {
    struct secure_port_info *info = g_registry.hash_table[i];
    while (info) {
      printf("Port %u, Task %d: ", info->port_id, info->owner_task);
      if (info->rights & PORT_HAS_SEND_RIGHT) printf("SEND ");
      if (info->rights & PORT_HAS_RECEIVE_RIGHT) printf("RECEIVE ");
      printf("\n");
      info = info->next;
    }
  }
  
  pthread_mutex_unlock(&g_registry.global_lock);
}