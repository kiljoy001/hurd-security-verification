/* GNU Hurd Port Rights Stress Test Suite
 * Tests scenarios that historically crash Hurd related to port management
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <signal.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>
#include <mach.h>
#include <mach/mach_traps.h>
#include <mach/message.h>
#include <mach/port.h>
#include <assert.h>

/* Test configuration */
#define MAX_PROCESSES 1000
#define MAX_PORTS_PER_PROCESS 100
#define TEST_DURATION_SECONDS 300
#define CRASH_DETECTION_INTERVAL 5

/* Test statistics */
typedef struct {
    uint64_t ports_created;
    uint64_t ports_destroyed;
    uint64_t ownership_transfers;
    uint64_t race_conditions_detected;
    uint64_t crashes;
    uint64_t hangs;
    uint64_t ipc_errors;
    uint64_t memory_errors;
    double start_time;
    double end_time;
} port_stress_stats_t;

static port_stress_stats_t global_stats = {0};
static volatile int test_running = 1;
static volatile int crash_detected = 0;

/* Crash detection and logging */
void crash_handler(int sig) {
    printf("CRASH DETECTED: Signal %d (%s) at time %.2f\n", 
           sig, strsignal(sig), get_current_time());
    global_stats.crashes++;
    crash_detected = 1;
    
    /* Log crash details */
    FILE *crash_log = fopen("port_stress_crashes.log", "a");
    if (crash_log) {
        fprintf(crash_log, "CRASH: Signal %d at %.2f seconds\n", 
                sig, get_current_time() - global_stats.start_time);
        fprintf(crash_log, "Stats: created=%lu destroyed=%lu transfers=%lu\n",
                global_stats.ports_created, global_stats.ports_destroyed,
                global_stats.ownership_transfers);
        fclose(crash_log);
    }
    
    exit(1);
}

/* Get current time in seconds */
static double get_current_time(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec / 1000000.0;
}

/* Stress Test 1: Port Creation/Destruction Storm */
void* port_creation_storm(void* arg) {
    int process_id = *(int*)arg;
    mach_port_t ports[MAX_PORTS_PER_PROCESS];
    int port_count = 0;
    
    printf("Process %d: Starting port creation storm\n", process_id);
    
    while (test_running && !crash_detected) {
        /* Create burst of ports */
        for (int i = 0; i < 10 && port_count < MAX_PORTS_PER_PROCESS; i++) {
            kern_return_t kr = mach_port_allocate(mach_task_self(), 
                                                 MACH_PORT_RIGHT_RECEIVE,
                                                 &ports[port_count]);
            if (kr == KERN_SUCCESS) {
                port_count++;
                __sync_fetch_and_add(&global_stats.ports_created, 1);
            } else {
                __sync_fetch_and_add(&global_stats.ipc_errors, 1);
                printf("Process %d: Port allocation failed: %s\n", 
                       process_id, mach_error_string(kr));
            }
        }
        
        /* Destroy random ports */
        if (port_count > 0) {
            int destroy_count = rand() % (port_count / 2 + 1);
            for (int i = 0; i < destroy_count; i++) {
                int idx = rand() % port_count;
                kern_return_t kr = mach_port_deallocate(mach_task_self(), ports[idx]);
                if (kr == KERN_SUCCESS) {
                    __sync_fetch_and_add(&global_stats.ports_destroyed, 1);
                    /* Remove from array */
                    ports[idx] = ports[port_count - 1];
                    port_count--;
                } else {
                    __sync_fetch_and_add(&global_stats.ipc_errors, 1);
                }
            }
        }
        
        /* Brief pause to let other processes work */
        usleep(1000 + rand() % 5000);
    }
    
    /* Cleanup remaining ports */
    for (int i = 0; i < port_count; i++) {
        mach_port_deallocate(mach_task_self(), ports[i]);
        __sync_fetch_and_add(&global_stats.ports_destroyed, 1);
    }
    
    printf("Process %d: Finished port creation storm\n", process_id);
    return NULL;
}

/* Stress Test 2: Port Ownership Transfer Races */
void* port_ownership_races(void* arg) {
    int process_id = *(int*)arg;
    
    printf("Process %d: Starting ownership transfer races\n", process_id);
    
    while (test_running && !crash_detected) {
        mach_port_t source_port, dest_port;
        
        /* Create source port with receive right */
        kern_return_t kr = mach_port_allocate(mach_task_self(), 
                                             MACH_PORT_RIGHT_RECEIVE,
                                             &source_port);
        if (kr != KERN_SUCCESS) {
            __sync_fetch_and_add(&global_stats.ipc_errors, 1);
            continue;
        }
        __sync_fetch_and_add(&global_stats.ports_created, 1);
        
        /* Create destination port */
        kr = mach_port_allocate(mach_task_self(), 
                               MACH_PORT_RIGHT_RECEIVE,
                               &dest_port);
        if (kr != KERN_SUCCESS) {
            mach_port_deallocate(mach_task_self(), source_port);
            __sync_fetch_and_add(&global_stats.ipc_errors, 1);
            continue;
        }
        __sync_fetch_and_add(&global_stats.ports_created, 1);
        
        /* Attempt rapid ownership transfers */
        for (int i = 0; i < 10; i++) {
            mach_port_t send_right;
            
            /* Extract send right */
            kr = mach_port_extract_right(mach_task_self(), source_port,
                                        MACH_MSG_TYPE_MAKE_SEND,
                                        &send_right, &mach_msg_type_name_t);
            if (kr == KERN_SUCCESS) {
                /* Try to insert into destination */
                kr = mach_port_insert_right(mach_task_self(), dest_port,
                                           send_right, MACH_MSG_TYPE_PORT_SEND);
                if (kr == KERN_SUCCESS) {
                    __sync_fetch_and_add(&global_stats.ownership_transfers, 1);
                } else {
                    __sync_fetch_and_add(&global_stats.race_conditions_detected, 1);
                    mach_port_deallocate(mach_task_self(), send_right);
                }
            } else {
                __sync_fetch_and_add(&global_stats.race_conditions_detected, 1);
            }
        }
        
        /* Cleanup */
        mach_port_deallocate(mach_task_self(), source_port);
        mach_port_deallocate(mach_task_self(), dest_port);
        __sync_fetch_and_add(&global_stats.ports_destroyed, 2);
        
        usleep(100 + rand() % 1000);
    }
    
    printf("Process %d: Finished ownership transfer races\n", process_id);
    return NULL;
}

/* Stress Test 3: Multiple Tasks Acquiring Same Receive Rights */
void* receive_rights_contention(void* arg) {
    int process_id = *(int*)arg;
    static mach_port_t shared_ports[10] = {0};
    static int shared_ports_initialized = 0;
    
    printf("Process %d: Starting receive rights contention\n", process_id);
    
    /* Initialize shared ports (race condition by design) */
    if (!shared_ports_initialized) {
        for (int i = 0; i < 10; i++) {
            kern_return_t kr = mach_port_allocate(mach_task_self(),
                                                 MACH_PORT_RIGHT_RECEIVE,
                                                 &shared_ports[i]);
            if (kr == KERN_SUCCESS) {
                __sync_fetch_and_add(&global_stats.ports_created, 1);
            }
        }
        shared_ports_initialized = 1;
    }
    
    while (test_running && !crash_detected) {
        for (int i = 0; i < 10; i++) {
            if (shared_ports[i] == MACH_PORT_NULL) continue;
            
            /* Try to get port status (tests receive right access) */
            mach_port_status_t status;
            mach_msg_type_number_t count = MACH_PORT_STATUS_COUNT;
            
            kern_return_t kr = mach_port_get_attributes(mach_task_self(),
                                                       shared_ports[i],
                                                       MACH_PORT_STATUS,
                                                       (mach_port_info_t)&status,
                                                       &count);
            if (kr != KERN_SUCCESS) {
                __sync_fetch_and_add(&global_stats.race_conditions_detected, 1);
                
                /* Port might be dead, try to reallocate */
                kr = mach_port_allocate(mach_task_self(),
                                       MACH_PORT_RIGHT_RECEIVE,
                                       &shared_ports[i]);
                if (kr == KERN_SUCCESS) {
                    __sync_fetch_and_add(&global_stats.ports_created, 1);
                }
            }
            
            /* Brief contention period */
            usleep(10);
        }
        
        usleep(1000 + rand() % 2000);
    }
    
    printf("Process %d: Finished receive rights contention\n", process_id);
    return NULL;
}

/* Stress Test 4: Process Termination with Port Cleanup */
void test_process_termination_cleanup(void) {
    printf("Starting process termination cleanup test\n");
    
    for (int round = 0; round < 50 && test_running; round++) {
        pid_t child_pids[20];
        int num_children = 10 + rand() % 10;
        
        /* Fork multiple children that create ports then exit */
        for (int i = 0; i < num_children; i++) {
            child_pids[i] = fork();
            if (child_pids[i] == 0) {
                /* Child process */
                mach_port_t ports[50];
                int port_count = 0;
                
                /* Create many ports */
                for (int j = 0; j < 50; j++) {
                    kern_return_t kr = mach_port_allocate(mach_task_self(),
                                                         MACH_PORT_RIGHT_RECEIVE,
                                                         &ports[port_count]);
                    if (kr == KERN_SUCCESS) {
                        port_count++;
                        __sync_fetch_and_add(&global_stats.ports_created, 1);
                    }
                }
                
                /* Do some port operations */
                for (int j = 0; j < port_count; j++) {
                    mach_port_status_t status;
                    mach_msg_type_number_t count = MACH_PORT_STATUS_COUNT;
                    mach_port_get_attributes(mach_task_self(), ports[j],
                                           MACH_PORT_STATUS,
                                           (mach_port_info_t)&status, &count);
                }
                
                /* Exit without explicit cleanup (tests kernel cleanup) */
                if (rand() % 3 == 0) {
                    /* Clean exit */
                    for (int j = 0; j < port_count; j++) {
                        mach_port_deallocate(mach_task_self(), ports[j]);
                        __sync_fetch_and_add(&global_stats.ports_destroyed, 1);
                    }
                    exit(0);
                } else {
                    /* Abrupt exit - kernel must clean up */
                    exit(1);
                }
            } else if (child_pids[i] < 0) {
                perror("fork failed");
                global_stats.ipc_errors++;
            }
        }
        
        /* Wait for children with timeout */
        for (int i = 0; i < num_children; i++) {
            if (child_pids[i] > 0) {
                int status;
                pid_t result = waitpid(child_pids[i], &status, WNOHANG);
                if (result == 0) {
                    /* Child still running, give it more time */
                    sleep(1);
                    result = waitpid(child_pids[i], &status, WNOHANG);
                    if (result == 0) {
                        /* Child hung, kill it */
                        kill(child_pids[i], SIGKILL);
                        waitpid(child_pids[i], &status, 0);
                        __sync_fetch_and_add(&global_stats.hangs, 1);
                    }
                }
            }
        }
        
        printf("Completed process termination round %d\n", round + 1);
        usleep(100000); /* 100ms between rounds */
    }
}

/* Monitor system for crashes and hangs */
void* crash_monitor(void* arg) {
    printf("Starting crash monitor\n");
    
    while (test_running) {
        sleep(CRASH_DETECTION_INTERVAL);
        
        if (crash_detected) {
            printf("CRASH DETECTED BY MONITOR\n");
            test_running = 0;
            break;
        }
        
        /* Check for system responsiveness */
        double start_time = get_current_time();
        mach_port_t test_port;
        kern_return_t kr = mach_port_allocate(mach_task_self(),
                                             MACH_PORT_RIGHT_RECEIVE,
                                             &test_port);
        double end_time = get_current_time();
        
        if (kr == KERN_SUCCESS) {
            mach_port_deallocate(mach_task_self(), test_port);
            if ((end_time - start_time) > 1.0) {
                printf("WARNING: System slowdown detected (%.2fs for port alloc)\n",
                       end_time - start_time);
            }
        } else {
            printf("WARNING: Basic port allocation failing: %s\n",
                   mach_error_string(kr));
            global_stats.ipc_errors++;
        }
    }
    
    return NULL;
}

/* Print test statistics */
void print_statistics(void) {
    printf("\n=== PORT RIGHTS STRESS TEST RESULTS ===\n");
    printf("Test duration: %.2f seconds\n", global_stats.end_time - global_stats.start_time);
    printf("Ports created: %lu\n", global_stats.ports_created);
    printf("Ports destroyed: %lu\n", global_stats.ports_destroyed);
    printf("Port leak: %ld\n", (long)(global_stats.ports_created - global_stats.ports_destroyed));
    printf("Ownership transfers: %lu\n", global_stats.ownership_transfers);
    printf("Race conditions detected: %lu\n", global_stats.race_conditions_detected);
    printf("Crashes: %lu\n", global_stats.crashes);
    printf("Process hangs: %lu\n", global_stats.hangs);
    printf("IPC errors: %lu\n", global_stats.ipc_errors);
    printf("Memory errors: %lu\n", global_stats.memory_errors);
    
    /* Calculate rates */
    double duration = global_stats.end_time - global_stats.start_time;
    if (duration > 0) {
        printf("Port creation rate: %.2f ports/sec\n", global_stats.ports_created / duration);
        printf("Error rate: %.2f errors/sec\n", global_stats.ipc_errors / duration);
        printf("Race condition rate: %.2f races/sec\n", global_stats.race_conditions_detected / duration);
    }
    
    /* Stability score (higher is better) */
    double stability_score = 100.0;
    if (global_stats.crashes > 0) stability_score -= global_stats.crashes * 50.0;
    if (global_stats.hangs > 0) stability_score -= global_stats.hangs * 10.0;
    if (global_stats.ipc_errors > 0) stability_score -= (global_stats.ipc_errors / 100.0);
    if (stability_score < 0) stability_score = 0;
    
    printf("STABILITY SCORE: %.1f/100\n", stability_score);
    
    if (global_stats.crashes == 0 && global_stats.hangs == 0) {
        printf("STATUS: STABLE ✓\n");
    } else {
        printf("STATUS: UNSTABLE ✗\n");
    }
}

/* Main test execution */
int main(int argc, char *argv[]) {
    printf("GNU Hurd Port Rights Stress Test Suite\n");
    printf("=====================================\n\n");
    
    /* Set up crash detection */
    signal(SIGSEGV, crash_handler);
    signal(SIGBUS, crash_handler);
    signal(SIGABRT, crash_handler);
    signal(SIGILL, crash_handler);
    signal(SIGFPE, crash_handler);
    
    global_stats.start_time = get_current_time();
    
    /* Start crash monitor thread */
    pthread_t monitor_thread;
    pthread_create(&monitor_thread, NULL, crash_monitor, NULL);
    
    /* Start stress test threads */
    pthread_t stress_threads[MAX_PROCESSES];
    int thread_ids[MAX_PROCESSES];
    int num_threads = 0;
    
    /* Test 1: Port creation/destruction storm */
    printf("Starting port creation/destruction storm with %d threads\n", MAX_PROCESSES/4);
    for (int i = 0; i < MAX_PROCESSES/4 && i < 250; i++) {
        thread_ids[num_threads] = i;
        pthread_create(&stress_threads[num_threads], NULL, 
                      port_creation_storm, &thread_ids[num_threads]);
        num_threads++;
    }
    
    /* Test 2: Ownership transfer races */
    printf("Starting ownership transfer races with %d threads\n", MAX_PROCESSES/4);
    for (int i = 0; i < MAX_PROCESSES/4 && i < 250; i++) {
        thread_ids[num_threads] = i + 250;
        pthread_create(&stress_threads[num_threads], NULL,
                      port_ownership_races, &thread_ids[num_threads]);
        num_threads++;
    }
    
    /* Test 3: Receive rights contention */
    printf("Starting receive rights contention with %d threads\n", MAX_PROCESSES/4);
    for (int i = 0; i < MAX_PROCESSES/4 && i < 250; i++) {
        thread_ids[num_threads] = i + 500;
        pthread_create(&stress_threads[num_threads], NULL,
                      receive_rights_contention, &thread_ids[num_threads]);
        num_threads++;
    }
    
    /* Test 4: Process termination cleanup (main thread) */
    pthread_t cleanup_thread;
    pthread_create(&cleanup_thread, NULL, 
                  (void*(*)(void*))test_process_termination_cleanup, NULL);
    
    /* Run for specified duration */
    printf("Running stress tests for %d seconds...\n", TEST_DURATION_SECONDS);
    sleep(TEST_DURATION_SECONDS);
    
    /* Stop all tests */
    test_running = 0;
    global_stats.end_time = get_current_time();
    
    printf("Stopping stress tests and waiting for cleanup...\n");
    
    /* Wait for all threads to complete */
    for (int i = 0; i < num_threads; i++) {
        pthread_join(stress_threads[i], NULL);
    }
    pthread_join(cleanup_thread, NULL);
    pthread_join(monitor_thread, NULL);
    
    /* Print final statistics */
    print_statistics();
    
    /* Save results to file */
    FILE *results_file = fopen("port_stress_results.txt", "w");
    if (results_file) {
        fprintf(results_file, "Port Rights Stress Test Results\n");
        fprintf(results_file, "Duration: %.2f seconds\n", global_stats.end_time - global_stats.start_time);
        fprintf(results_file, "Ports Created: %lu\n", global_stats.ports_created);
        fprintf(results_file, "Ports Destroyed: %lu\n", global_stats.ports_destroyed);
        fprintf(results_file, "Ownership Transfers: %lu\n", global_stats.ownership_transfers);
        fprintf(results_file, "Race Conditions: %lu\n", global_stats.race_conditions_detected);
        fprintf(results_file, "Crashes: %lu\n", global_stats.crashes);
        fprintf(results_file, "Hangs: %lu\n", global_stats.hangs);
        fprintf(results_file, "IPC Errors: %lu\n", global_stats.ipc_errors);
        fprintf(results_file, "Stability Score: %.1f/100\n", 
                100.0 - (global_stats.crashes * 50.0) - (global_stats.hangs * 10.0) - (global_stats.ipc_errors / 100.0));
        fclose(results_file);
    }
    
    return (global_stats.crashes == 0 && global_stats.hangs == 0) ? 0 : 1;
}