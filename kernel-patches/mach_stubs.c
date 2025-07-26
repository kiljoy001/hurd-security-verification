/*
 * Mach System Call Stubs Implementation
 * Simulates Mach port operations with security fix testing
 */

#include "mach_stubs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#ifndef boolean_t
#define boolean_t int
#endif

/* Port registry entry */
struct port_entry {
    mach_port_t port;
    task_t owner_task;
    mach_port_right_t rights;
    struct port_entry *next;
};

/* Global state */
static struct {
    struct port_entry *ports;
    pthread_mutex_t lock;
    int security_fix_enabled;
    int violation_count;
    uint32_t next_port_id;
    uint32_t next_task_id;
} g_state = {
    .ports = NULL,
    .lock = PTHREAD_MUTEX_INITIALIZER,
    .security_fix_enabled = 1,  /* Security fix enabled by default */
    .violation_count = 0,
    .next_port_id = 1000,
    .next_task_id = 100
};

/* Find port entry */
static struct port_entry* find_port(mach_port_t port) {
    struct port_entry *entry = g_state.ports;
    while (entry) {
        if (entry->port == port) return entry;
        entry = entry->next;
    }
    return NULL;
}

/* Check if any task already has receive rights */
static int has_receive_rights(mach_port_t port, task_t requesting_task) {
    struct port_entry *entry = g_state.ports;
    while (entry) {
        if (entry->port == port && 
            entry->rights == MACH_PORT_RIGHT_RECEIVE) {
            /* Port already has receive rights - even from same task */
            return 1;
        }
        entry = entry->next;
    }
    return 0;
}

/* Initialize stubs */
void mach_stubs_init(void) {
    pthread_mutex_lock(&g_state.lock);
    g_state.violation_count = 0;
    pthread_mutex_unlock(&g_state.lock);
}

/* Cleanup stubs */
void mach_stubs_cleanup(void) {
    pthread_mutex_lock(&g_state.lock);
    struct port_entry *entry = g_state.ports;
    while (entry) {
        struct port_entry *next = entry->next;
        free(entry);
        entry = next;
    }
    g_state.ports = NULL;
    pthread_mutex_unlock(&g_state.lock);
}

/* Enable/disable security fix */
void mach_stubs_enable_security_fix(int enable) {
    pthread_mutex_lock(&g_state.lock);
    g_state.security_fix_enabled = enable;
    pthread_mutex_unlock(&g_state.lock);
}

/* Get violation count */
int mach_stubs_get_violation_count(void) {
    int count;
    pthread_mutex_lock(&g_state.lock);
    count = g_state.violation_count;
    pthread_mutex_unlock(&g_state.lock);
    return count;
}

/* Get current task */
task_t mach_task_self(void) {
    static __thread task_t current_task = NULL;
    if (!current_task) {
        pthread_mutex_lock(&g_state.lock);
        current_task = (task_t)(uintptr_t)(g_state.next_task_id++);
        pthread_mutex_unlock(&g_state.lock);
    }
    return current_task;
}

/* Allocate a port */
kern_return_t mach_port_allocate(task_t task, mach_port_right_t right, mach_port_t *name) {
    if (!task || !name) return KERN_INVALID_ARGUMENT;
    
    pthread_mutex_lock(&g_state.lock);
    
    /* Allocate new port */
    *name = g_state.next_port_id++;
    
    /* Create port entry */
    struct port_entry *entry = malloc(sizeof(struct port_entry));
    entry->port = *name;
    entry->owner_task = task;
    entry->rights = right;
    entry->next = g_state.ports;
    g_state.ports = entry;
    
    pthread_mutex_unlock(&g_state.lock);
    return KERN_SUCCESS;
}

/* Insert port right */
kern_return_t mach_port_insert_right(task_t task, mach_port_name_t name, 
                                    mach_port_t poly, mach_port_right_t right) {
    if (!task) return KERN_INVALID_ARGUMENT;
    
    pthread_mutex_lock(&g_state.lock);
    
    /* Security check: If inserting receive right, check exclusivity */
    if (right == MACH_PORT_RIGHT_RECEIVE && g_state.security_fix_enabled) {
        if (has_receive_rights(name, task)) {
            g_state.violation_count++;
            pthread_mutex_unlock(&g_state.lock);
            return KERN_RIGHT_EXISTS;  /* Security violation prevented */
        }
    }
    
    /* Create new entry for this task */
    struct port_entry *entry = malloc(sizeof(struct port_entry));
    entry->port = name;
    entry->owner_task = task;
    entry->rights = right;
    entry->next = g_state.ports;
    g_state.ports = entry;
    
    pthread_mutex_unlock(&g_state.lock);
    return KERN_SUCCESS;
}

/* Extract port right */
kern_return_t mach_port_extract_right(task_t task, mach_port_name_t name,
                                     mach_port_right_t msgt_name, mach_port_t *poly,
                                     mach_port_type_t *polyPoly) {
    pthread_mutex_lock(&g_state.lock);
    
    /* Find and remove the right */
    struct port_entry **prev = &g_state.ports;
    struct port_entry *entry = g_state.ports;
    
    while (entry) {
        if (entry->port == name && entry->owner_task == task) {
            *prev = entry->next;
            if (poly) *poly = entry->port;
            if (polyPoly) *polyPoly = (1 << entry->rights);
            free(entry);
            pthread_mutex_unlock(&g_state.lock);
            return KERN_SUCCESS;
        }
        prev = &entry->next;
        entry = entry->next;
    }
    
    pthread_mutex_unlock(&g_state.lock);
    return KERN_INVALID_NAME;
}

/* Destroy port */
kern_return_t mach_port_destroy(task_t task, mach_port_name_t name) {
    pthread_mutex_lock(&g_state.lock);
    
    /* Remove all rights for this task/port combination */
    struct port_entry **prev = &g_state.ports;
    struct port_entry *entry = g_state.ports;
    int found = 0;
    
    while (entry) {
        if (entry->port == name && entry->owner_task == task) {
            struct port_entry *to_delete = entry;
            *prev = entry->next;
            entry = entry->next;
            free(to_delete);
            found = 1;
        } else {
            prev = &entry->next;
            entry = entry->next;
        }
    }
    
    pthread_mutex_unlock(&g_state.lock);
    return found ? KERN_SUCCESS : KERN_INVALID_NAME;
}

/* Deallocate port */
kern_return_t mach_port_deallocate(task_t task, mach_port_name_t name) {
    /* For simplicity, same as destroy in this simulation */
    return mach_port_destroy(task, name);
}

/* Create task */
kern_return_t task_create(task_t parent_task, boolean_t inherit_memory, task_t *child_task) {
    if (!child_task) return KERN_INVALID_ARGUMENT;
    
    pthread_mutex_lock(&g_state.lock);
    *child_task = (task_t)(uintptr_t)(g_state.next_task_id++);
    pthread_mutex_unlock(&g_state.lock);
    
    return KERN_SUCCESS;
}

/* Terminate task */
kern_return_t task_terminate(task_t target_task) {
    if (!target_task) return KERN_INVALID_ARGUMENT;
    
    pthread_mutex_lock(&g_state.lock);
    
    /* Remove all ports owned by this task */
    struct port_entry **prev = &g_state.ports;
    struct port_entry *entry = g_state.ports;
    
    while (entry) {
        if (entry->owner_task == target_task) {
            struct port_entry *to_delete = entry;
            *prev = entry->next;
            entry = entry->next;
            free(to_delete);
        } else {
            prev = &entry->next;
            entry = entry->next;
        }
    }
    
    pthread_mutex_unlock(&g_state.lock);
    return KERN_SUCCESS;
}