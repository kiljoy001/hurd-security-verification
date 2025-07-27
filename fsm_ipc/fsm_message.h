/* FSM-Based IPC Message Format
 * High-performance 64-byte fixed-size message structure
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _FSM_MESSAGE_H_
#define _FSM_MESSAGE_H_

#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>

/* FSM States for message processing pipeline */
typedef enum {
    FSM_STATE_CREATED         = 0x01,  /* Message just created */
    FSM_STATE_ROUTED          = 0x02,  /* Routing decision made */
    FSM_STATE_VALIDATED       = 0x03,  /* Security checks passed */
    FSM_STATE_DELIVERED       = 0x04,  /* Reached destination */
    FSM_STATE_ACKNOWLEDGED    = 0x05,  /* Receipt confirmed */
    FSM_STATE_ERROR           = 0x10,  /* Error condition */
    FSM_STATE_BULK_DATA       = 0x20,  /* Contains shared memory handle */
    FSM_STATE_STREAM_START    = 0x30,  /* Start of streaming data */
    FSM_STATE_STREAM_CONTINUE = 0x31,  /* Streaming continuation */
    FSM_STATE_STREAM_END      = 0x32   /* End of streaming data */
} fsm_state_t;

/* Fixed-size FSM message structure (exactly 64 bytes) */
typedef struct __attribute__((packed)) fsm_message {
    /* Header (8 bytes) */
    uint8_t  current_state;     /* Current FSM state */
    uint8_t  next_state;        /* Next expected state */
    uint16_t source_port;       /* Source port ID */
    uint16_t dest_server;       /* Destination server ID */
    uint16_t payload_length;    /* Actual payload size (0-56) */
    
    /* Payload data (56 bytes) */
    uint8_t  payload[56];       /* Message data or handle */
} fsm_message_t;

/* Compile-time assertion for message size */
_Static_assert(sizeof(fsm_message_t) == 64, "FSM message must be exactly 64 bytes");

/* Bulk data handle for large messages */
typedef struct __attribute__((packed)) bulk_handle {
    uint32_t shared_memory_id;  /* ID of shared memory region */
    uint32_t data_size;         /* Size of data in shared memory */
    uint16_t permissions;       /* Access permissions (R/W/X) */
    uint16_t checksum;          /* Data integrity checksum */
    uint64_t expiry_time;       /* When handle expires (ms) */
} bulk_handle_t;

/* Fragment header for streaming data */
typedef struct __attribute__((packed)) fragment_header {
    uint32_t total_size;        /* Total size of complete message */
    uint16_t fragment_count;    /* Total number of fragments */
    uint16_t current_fragment;  /* Current fragment number (0-based) */
    uint32_t fragment_id;       /* Unique ID for this fragment stream */
    uint64_t timestamp;         /* Fragment creation time */
} fragment_header_t;

/* Message validation and utility functions */

/* Check if FSM state transition is valid */
bool fsm_valid_transition(fsm_state_t from, fsm_state_t to);

/* Initialize a new FSM message */
void fsm_message_init(fsm_message_t *msg, uint16_t src_port, uint16_t dst_server);

/* Copy payload data into message (up to 56 bytes) */
bool fsm_message_set_payload(fsm_message_t *msg, const void *data, uint16_t size);

/* Get payload data from message */
const void *fsm_message_get_payload(const fsm_message_t *msg, uint16_t *size);

/* Create bulk data message with shared memory handle */
bool fsm_message_set_bulk_handle(fsm_message_t *msg, const bulk_handle_t *handle);

/* Extract bulk data handle from message */
bool fsm_message_get_bulk_handle(const fsm_message_t *msg, bulk_handle_t *handle);

/* Create streaming fragment message */
bool fsm_message_set_fragment(fsm_message_t *msg, const fragment_header_t *header, 
                             const void *data, uint16_t data_size);

/* Extract fragment information */
bool fsm_message_get_fragment(const fsm_message_t *msg, fragment_header_t *header,
                             void *data, uint16_t max_size, uint16_t *actual_size);

/* Validate message integrity */
bool fsm_message_validate(const fsm_message_t *msg);

/* Calculate message checksum */
uint16_t fsm_message_checksum(const fsm_message_t *msg);

/* Convert to/from Mach message format */
struct mach_msg_header;
bool fsm_from_mach_msg(fsm_message_t *fsm_msg, const struct mach_msg_header *mach_msg);
bool fsm_to_mach_msg(const fsm_message_t *fsm_msg, struct mach_msg_header *mach_msg);

/* Performance optimization flags */
#define FSM_FLAG_CACHE_HINT     0x01  /* Suggest caching this route */
#define FSM_FLAG_LOW_LATENCY    0x02  /* Priority processing */
#define FSM_FLAG_BULK_FOLLOWS   0x04  /* Bulk data message coming */
#define FSM_FLAG_AUTHENTICATED  0x08  /* Already authenticated */

#endif /* _FSM_MESSAGE_H_ */