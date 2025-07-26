/* Minimal Mach stubs for testing simulation */
#ifndef MACH_STUBS_H
#define MACH_STUBS_H

#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>

/* Basic types */
typedef uint32_t mach_port_t;
typedef uint32_t kern_return_t;
typedef uint32_t task_t;
typedef uint32_t mach_port_type_t;

/* Constants */
#define MACH_PORT_NULL ((mach_port_t) 0)
#define KERN_SUCCESS 0
#define KERN_FAILURE 1

#define MACH_PORT_RIGHT_RECEIVE 1
#define MACH_PORT_RIGHT_SEND 2
#define MACH_PORT_TYPE_RECEIVE 1
#define MACH_MSG_TYPE_MAKE_SEND 1
#define MACH_MSG_TYPE_MOVE_RECEIVE 2

/* Port receive rights tracking for simulation */
struct sim_port_entry {
    mach_port_t port;
    task_t owner_task;
    struct sim_port_entry *next;
};

static struct sim_port_entry *sim_port_table = NULL;
static int simulation_allocated_ports = 0;
static pthread_mutex_t sim_port_mutex = PTHREAD_MUTEX_INITIALIZER;

static inline task_t mach_task_self(void) {
    return (task_t)getpid();
}

/* Helper functions for simulation */
static inline int sim_port_has_receive_rights(mach_port_t port) {
    struct sim_port_entry *entry;
    int has_rights = 0;
    
    pthread_mutex_lock(&sim_port_mutex);
    for (entry = sim_port_table; entry != NULL; entry = entry->next) {
        if (entry->port == port) {
            has_rights = 1; /* Port already has receive rights allocated */
            break;
        }
    }
    pthread_mutex_unlock(&sim_port_mutex);
    return has_rights;
}

static inline void sim_port_record_receive_rights(mach_port_t port, task_t owner_task) {
    struct sim_port_entry *entry, *new_entry;
    
    pthread_mutex_lock(&sim_port_mutex);
    
    /* Check if entry already exists */
    for (entry = sim_port_table; entry != NULL; entry = entry->next) {
        if (entry->port == port) {
            entry->owner_task = owner_task;
            pthread_mutex_unlock(&sim_port_mutex);
            return;
        }
    }
    
    /* Create new entry */
    new_entry = malloc(sizeof(struct sim_port_entry));
    if (new_entry) {
        new_entry->port = port;
        new_entry->owner_task = owner_task;
        new_entry->next = sim_port_table;
        sim_port_table = new_entry;
    }
    pthread_mutex_unlock(&sim_port_mutex);
}

static inline void sim_port_remove_receive_rights(mach_port_t port) {
    struct sim_port_entry *entry, *prev = NULL;
    
    pthread_mutex_lock(&sim_port_mutex);
    for (entry = sim_port_table; entry != NULL; prev = entry, entry = entry->next) {
        if (entry->port == port) {
            if (prev) {
                prev->next = entry->next;
            } else {
                sim_port_table = entry->next;
            }
            free(entry);
            break;
        }
    }
    pthread_mutex_unlock(&sim_port_mutex);
}

static inline kern_return_t mach_port_allocate(task_t task, uint32_t right, mach_port_t *name) {
    *name = ++simulation_allocated_ports;
    
    if (right == MACH_PORT_RIGHT_RECEIVE) {
        sim_port_record_receive_rights(*name, task);
    }
    return KERN_SUCCESS;
}

static inline kern_return_t mach_port_allocate_name(task_t task, uint32_t right, mach_port_t name) {
    if (right == MACH_PORT_RIGHT_RECEIVE) {
        /* Security fix: Check if port already has receive rights */
        if (sim_port_has_receive_rights(name)) {
            return KERN_FAILURE; /* Prevent duplicate receive rights */
        }
        sim_port_record_receive_rights(name, task);
    }
    return KERN_SUCCESS;
}

static inline kern_return_t mach_port_deallocate(task_t task, mach_port_t name) {
    sim_port_remove_receive_rights(name);
    return KERN_SUCCESS;
}

static inline kern_return_t mach_port_insert_right(task_t task, mach_port_t name, mach_port_t poly, uint32_t polyPoly) {
    if (polyPoly == MACH_MSG_TYPE_MOVE_RECEIVE) {
        /* Move receive rights from poly to name */
        sim_port_remove_receive_rights(poly);
        sim_port_record_receive_rights(name, task);
    }
    return KERN_SUCCESS;
}

static inline kern_return_t mach_port_type(task_t task, mach_port_t name, mach_port_type_t *ptype) {
    struct sim_port_entry *entry;
    *ptype = 0;
    
    pthread_mutex_lock(&sim_port_mutex);
    /* Check if this task has receive rights to the port */
    for (entry = sim_port_table; entry != NULL; entry = entry->next) {
        if (entry->port == name && entry->owner_task == task) {
            *ptype = MACH_PORT_TYPE_RECEIVE;
            break;
        }
    }
    pthread_mutex_unlock(&sim_port_mutex);
    return KERN_SUCCESS;
}

#endif /* MACH_STUBS_H */