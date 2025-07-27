/* Real Kernel FSM IPC Performance Test
 * Tests actual kernel syscall performance vs userspace simulation
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <errno.h>
#include <stdint.h>

/* FSM IPC syscall numbers - must match kernel implementation */
#define SYS_fsm_msg_send    90
#define SYS_fsm_msg_receive 91

/* FSM message structure - must match kernel */
typedef struct __attribute__((packed)) {
    uint8_t  current_state;
    uint8_t  next_state;
    uint16_t source_port;
    uint16_t dest_server;
    uint16_t payload_length;
    uint8_t  payload[56];
} fsm_message_t;

/* Performance measurement structure */
typedef struct {
    uint64_t cycles_per_message;
    uint64_t nanoseconds_per_message;
    uint32_t messages_per_second;
    uint64_t total_cycles;
    uint64_t total_nanoseconds;
    uint32_t successful_messages;
    uint32_t failed_messages;
} fsm_perf_stats_t;

/* High-resolution cycle counter */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ volatile ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

/* Get nanosecond timestamp */
static uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

/* FSM IPC syscall wrappers */
static int fsm_msg_send(uint16_t dest_port, fsm_message_t *msg, uint32_t timeout) {
    return syscall(SYS_fsm_msg_send, dest_port, msg, sizeof(fsm_message_t), timeout);
}

static int fsm_msg_receive(uint16_t source_port, fsm_message_t *msg, uint32_t timeout) {
    return syscall(SYS_fsm_msg_receive, source_port, msg, sizeof(fsm_message_t), timeout);
}

/* Initialize test message */
static void init_test_message(fsm_message_t *msg, uint16_t src, uint16_t dst) {
    memset(msg, 0, sizeof(fsm_message_t));
    msg->current_state = 1;  /* FSM_STATE_CREATED */
    msg->next_state = 2;     /* FSM_STATE_ROUTED */
    msg->source_port = src;
    msg->dest_server = dst;
    msg->payload_length = 32;
    strcpy((char*)msg->payload, "Real kernel IPC test message");
}

/* Single message latency test */
static void test_single_message_latency(fsm_perf_stats_t *stats) {
    printf("=== Single Message Latency Test ===\n");
    
    fsm_message_t send_msg, recv_msg;
    uint64_t start_cycles, end_cycles;
    uint64_t start_ns, end_ns;
    
    init_test_message(&send_msg, 1000, 2000);
    
    /* Warm up - ensure kernel FSM IPC is initialized */
    fsm_msg_send(2000, &send_msg, 0);
    fsm_msg_receive(2000, &recv_msg, 0);
    
    /* Measure round-trip latency */
    start_cycles = rdtsc();
    start_ns = get_time_ns();
    
    int send_result = fsm_msg_send(2000, &send_msg, 0);
    int recv_result = fsm_msg_receive(2000, &recv_msg, 0);
    
    end_cycles = rdtsc();
    end_ns = get_time_ns();
    
    if (send_result == 0 && recv_result == 0) {
        stats->successful_messages = 1;
        stats->failed_messages = 0;
        stats->total_cycles = end_cycles - start_cycles;
        stats->total_nanoseconds = end_ns - start_ns;
        stats->cycles_per_message = stats->total_cycles;
        stats->nanoseconds_per_message = stats->total_nanoseconds;
        
        printf("✓ Round-trip latency: %lu cycles (%.3f μs)\n", 
               stats->cycles_per_message, stats->nanoseconds_per_message / 1000.0);
        
        /* Verify message content */
        if (memcmp(send_msg.payload, recv_msg.payload, send_msg.payload_length) == 0) {
            printf("✓ Message content preserved\n");
        } else {
            printf("✗ Message content corrupted\n");
        }
    } else {
        stats->successful_messages = 0;
        stats->failed_messages = 1;
        printf("✗ FSM IPC syscalls failed: send=%d, recv=%d (errno=%d)\n", 
               send_result, recv_result, errno);
    }
}

/* Throughput test */
static void test_throughput(fsm_perf_stats_t *stats, uint32_t num_messages) {
    printf("\n=== Throughput Test (%u messages) ===\n", num_messages);
    
    fsm_message_t *messages = malloc(num_messages * sizeof(fsm_message_t));
    if (!messages) {
        printf("✗ Failed to allocate message buffer\n");
        return;
    }
    
    /* Initialize test messages */
    for (uint32_t i = 0; i < num_messages; i++) {
        init_test_message(&messages[i], 1000 + i, 2000 + (i % 100));
    }
    
    uint64_t start_cycles = rdtsc();
    uint64_t start_ns = get_time_ns();
    
    uint32_t successful = 0;
    uint32_t failed = 0;
    
    /* Send all messages */
    for (uint32_t i = 0; i < num_messages; i++) {
        if (fsm_msg_send(messages[i].dest_server, &messages[i], 0) == 0) {
            successful++;
        } else {
            failed++;
        }
    }
    
    uint64_t end_cycles = rdtsc();
    uint64_t end_ns = get_time_ns();
    
    stats->successful_messages = successful;
    stats->failed_messages = failed;
    stats->total_cycles = end_cycles - start_cycles;
    stats->total_nanoseconds = end_ns - start_ns;
    
    if (successful > 0) {
        stats->cycles_per_message = stats->total_cycles / successful;
        stats->nanoseconds_per_message = stats->total_nanoseconds / successful;
        stats->messages_per_second = (uint32_t)((successful * 1000000000ULL) / stats->total_nanoseconds);
        
        printf("✓ Processed %u/%u messages successfully\n", successful, num_messages);
        printf("  Average latency: %lu cycles (%.3f μs)\n", 
               stats->cycles_per_message, stats->nanoseconds_per_message / 1000.0);
        printf("  Throughput: %u messages/second\n", stats->messages_per_second);
        printf("  Success rate: %.1f%%\n", (successful * 100.0) / num_messages);
    } else {
        printf("✗ No messages processed successfully\n");
    }
    
    free(messages);
}

/* Multi-process IPC test */
static void test_multiprocess_ipc(fsm_perf_stats_t *stats) {
    printf("\n=== Multi-Process IPC Test ===\n");
    
    pid_t child_pid = fork();
    if (child_pid == -1) {
        printf("✗ Failed to fork process\n");
        return;
    }
    
    if (child_pid == 0) {
        /* Child process - receiver */
        fsm_message_t recv_msg;
        uint64_t start_cycles = rdtsc();
        uint64_t start_ns = get_time_ns();
        
        int result = fsm_msg_receive(3000, &recv_msg, 1000);  /* 1 second timeout */
        
        uint64_t end_cycles = rdtsc();
        uint64_t end_ns = get_time_ns();
        
        if (result == 0) {
            printf("  Child: Received message in %lu cycles (%.3f μs)\n",
                   end_cycles - start_cycles, (end_ns - start_ns) / 1000.0);
            printf("  Content: '%.32s'\n", recv_msg.payload);
            exit(0);
        } else {
            printf("  Child: Failed to receive message (errno=%d)\n", errno);
            exit(1);
        }
    } else {
        /* Parent process - sender */
        fsm_message_t send_msg;
        init_test_message(&send_msg, 1000, 3000);
        strcpy((char*)send_msg.payload, "Multi-process IPC test");
        
        /* Give child time to start receiving */
        usleep(10000);  /* 10ms */
        
        uint64_t start_cycles = rdtsc();
        uint64_t start_ns = get_time_ns();
        
        int result = fsm_msg_send(3000, &send_msg, 0);
        
        uint64_t end_cycles = rdtsc();
        uint64_t end_ns = get_time_ns();
        
        if (result == 0) {
            printf("  Parent: Sent message in %lu cycles (%.3f μs)\n",
                   end_cycles - start_cycles, (end_ns - start_ns) / 1000.0);
            stats->successful_messages = 1;
            stats->cycles_per_message = end_cycles - start_cycles;
            stats->nanoseconds_per_message = end_ns - start_ns;
        } else {
            printf("  Parent: Failed to send message (errno=%d)\n", errno);
            stats->failed_messages = 1;
        }
        
        /* Wait for child */
        int status;
        wait(&status);
        if (WEXITSTATUS(status) == 0) {
            printf("✓ Multi-process IPC test successful\n");
        } else {
            printf("✗ Multi-process IPC test failed\n");
        }
    }
}

/* Compare with userspace simulation */
static void compare_with_userspace(void) {
    printf("\n=== Comparison with Userspace Simulation ===\n");
    printf("Previous userspace simulation results:\n");
    printf("  Average latency: 369 ns (0.369 μs)\n");
    printf("  Throughput: 11.4 million messages/second\n");
    printf("  Success rate: 85.7%%\n");
    printf("\nNote: Userspace measured function call overhead only.\n");
    printf("Real kernel IPC includes:\n");
    printf("  - Syscall entry/exit overhead\n");
    printf("  - Memory protection and validation\n");
    printf("  - Context switches (user ↔ kernel)\n");
    printf("  - Actual IPC between processes\n");
    printf("  - Scheduler integration overhead\n");
}

int main(int argc, char *argv[]) {
    printf("FSM IPC Real Kernel Performance Test\n");
    printf("====================================\n\n");
    
    printf("Testing real GNU Mach kernel with FSM IPC syscalls...\n");
    printf("Kernel should be patched with FSM IPC support.\n\n");
    
    fsm_perf_stats_t single_stats = {0};
    fsm_perf_stats_t throughput_stats = {0};
    fsm_perf_stats_t multiprocess_stats = {0};
    
    /* Run performance tests */
    test_single_message_latency(&single_stats);
    test_throughput(&throughput_stats, 1000);
    test_multiprocess_ipc(&multiprocess_stats);
    
    /* Show comparison */
    compare_with_userspace();
    
    /* Summary */
    printf("\n=== Real Kernel FSM IPC Performance Summary ===\n");
    
    if (single_stats.successful_messages > 0) {
        printf("Single message latency: %.3f μs (%lu cycles)\n",
               single_stats.nanoseconds_per_message / 1000.0,
               single_stats.cycles_per_message);
    }
    
    if (throughput_stats.successful_messages > 0) {
        printf("Throughput test:\n");
        printf("  Average latency: %.3f μs (%lu cycles)\n",
               throughput_stats.nanoseconds_per_message / 1000.0,
               throughput_stats.cycles_per_message);
        printf("  Throughput: %u messages/second\n", throughput_stats.messages_per_second);
        printf("  Success rate: %.1f%%\n", 
               (throughput_stats.successful_messages * 100.0) / 
               (throughput_stats.successful_messages + throughput_stats.failed_messages));
    }
    
    if (multiprocess_stats.successful_messages > 0) {
        printf("Multi-process IPC: %.3f μs (%lu cycles)\n",
               multiprocess_stats.nanoseconds_per_message / 1000.0,
               multiprocess_stats.cycles_per_message);
    }
    
    printf("\nComparison to initial projections:\n");
    printf("  Projected: 4-15 μs real kernel IPC\n");
    printf("  Userspace simulation: 0.369 μs function calls\n");
    printf("  Actual kernel IPC: [see results above]\n");
    
    return 0;
}