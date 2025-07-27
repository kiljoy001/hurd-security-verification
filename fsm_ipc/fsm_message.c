/* FSM Message Implementation
 * Core message handling and validation functions
 */

#include "fsm_message.h"
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>

/* Valid FSM state transitions */
bool fsm_valid_transition(fsm_state_t from, fsm_state_t to) {
    switch (from) {
        case FSM_STATE_CREATED:
            return (to == FSM_STATE_ROUTED || to == FSM_STATE_ERROR);
        
        case FSM_STATE_ROUTED:
            return (to == FSM_STATE_VALIDATED || to == FSM_STATE_ERROR);
        
        case FSM_STATE_VALIDATED:
            return (to == FSM_STATE_DELIVERED || to == FSM_STATE_ERROR);
        
        case FSM_STATE_DELIVERED:
            return (to == FSM_STATE_ACKNOWLEDGED || to == FSM_STATE_ERROR);
        
        case FSM_STATE_ACKNOWLEDGED:
            return false;  /* Terminal state */
        
        case FSM_STATE_ERROR:
            return false;  /* Terminal state */
        
        case FSM_STATE_BULK_DATA:
            return (to == FSM_STATE_DELIVERED || to == FSM_STATE_ERROR);
        
        case FSM_STATE_STREAM_START:
            return (to == FSM_STATE_STREAM_CONTINUE || to == FSM_STATE_ERROR);
        
        case FSM_STATE_STREAM_CONTINUE:
            return (to == FSM_STATE_STREAM_CONTINUE || 
                    to == FSM_STATE_STREAM_END || 
                    to == FSM_STATE_ERROR);
        
        case FSM_STATE_STREAM_END:
            return (to == FSM_STATE_DELIVERED || to == FSM_STATE_ERROR);
        
        default:
            return false;
    }
}

/* Initialize a new FSM message */
void fsm_message_init(fsm_message_t *msg, uint16_t src_port, uint16_t dst_server) {
    if (!msg) return;
    
    memset(msg, 0, sizeof(fsm_message_t));
    msg->current_state = FSM_STATE_CREATED;
    msg->next_state = FSM_STATE_ROUTED;
    msg->source_port = src_port;
    msg->dest_server = dst_server;
    msg->payload_length = 0;
}

/* Copy payload data into message */
bool fsm_message_set_payload(fsm_message_t *msg, const void *data, uint16_t size) {
    if (!msg || !data || size > 56) {
        return false;
    }
    
    memcpy(msg->payload, data, size);
    msg->payload_length = size;
    
    /* Zero-pad remaining payload */
    if (size < 56) {
        memset(msg->payload + size, 0, 56 - size);
    }
    
    return true;
}

/* Get payload data from message */
const void *fsm_message_get_payload(const fsm_message_t *msg, uint16_t *size) {
    if (!msg || !size) {
        return NULL;
    }
    
    *size = msg->payload_length;
    return msg->payload;
}

/* Create bulk data message with shared memory handle */
bool fsm_message_set_bulk_handle(fsm_message_t *msg, const bulk_handle_t *handle) {
    if (!msg || !handle || sizeof(bulk_handle_t) > 56) {
        return false;
    }
    
    msg->current_state = FSM_STATE_BULK_DATA;
    msg->next_state = FSM_STATE_DELIVERED;
    
    memcpy(msg->payload, handle, sizeof(bulk_handle_t));
    msg->payload_length = sizeof(bulk_handle_t);
    
    /* Zero-pad remaining payload */
    memset(msg->payload + sizeof(bulk_handle_t), 0, 56 - sizeof(bulk_handle_t));
    
    return true;
}

/* Extract bulk data handle from message */
bool fsm_message_get_bulk_handle(const fsm_message_t *msg, bulk_handle_t *handle) {
    if (!msg || !handle || msg->current_state != FSM_STATE_BULK_DATA) {
        return false;
    }
    
    if (msg->payload_length < sizeof(bulk_handle_t)) {
        return false;
    }
    
    memcpy(handle, msg->payload, sizeof(bulk_handle_t));
    return true;
}

/* Create streaming fragment message */
bool fsm_message_set_fragment(fsm_message_t *msg, const fragment_header_t *header,
                             const void *data, uint16_t data_size) {
    if (!msg || !header || !data) {
        return false;
    }
    
    size_t header_size = sizeof(fragment_header_t);
    if (header_size + data_size > 56) {
        return false;
    }
    
    /* Set appropriate streaming state */
    if (header->current_fragment == 0) {
        msg->current_state = FSM_STATE_STREAM_START;
        msg->next_state = FSM_STATE_STREAM_CONTINUE;
    } else if (header->current_fragment == header->fragment_count - 1) {
        msg->current_state = FSM_STATE_STREAM_END;
        msg->next_state = FSM_STATE_DELIVERED;
    } else {
        msg->current_state = FSM_STATE_STREAM_CONTINUE;
        msg->next_state = FSM_STATE_STREAM_CONTINUE;
    }
    
    /* Copy header and data */
    memcpy(msg->payload, header, header_size);
    memcpy(msg->payload + header_size, data, data_size);
    msg->payload_length = header_size + data_size;
    
    /* Zero-pad remaining payload */
    if (msg->payload_length < 56) {
        memset(msg->payload + msg->payload_length, 0, 56 - msg->payload_length);
    }
    
    return true;
}

/* Extract fragment information */
bool fsm_message_get_fragment(const fsm_message_t *msg, fragment_header_t *header,
                             void *data, uint16_t max_size, uint16_t *actual_size) {
    if (!msg || !header || !data || !actual_size) {
        return false;
    }
    
    /* Check if this is a streaming message */
    if (msg->current_state != FSM_STATE_STREAM_START &&
        msg->current_state != FSM_STATE_STREAM_CONTINUE &&
        msg->current_state != FSM_STATE_STREAM_END) {
        return false;
    }
    
    size_t header_size = sizeof(fragment_header_t);
    if (msg->payload_length < header_size) {
        return false;
    }
    
    /* Extract header */
    memcpy(header, msg->payload, header_size);
    
    /* Extract data */
    uint16_t data_size = msg->payload_length - header_size;
    if (data_size > max_size) {
        return false;
    }
    
    memcpy(data, msg->payload + header_size, data_size);
    *actual_size = data_size;
    
    return true;
}

/* Get current timestamp in milliseconds */
static uint64_t get_timestamp_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000 + (uint64_t)tv.tv_usec / 1000;
}

/* Validate message integrity */
bool fsm_message_validate(const fsm_message_t *msg) {
    if (!msg) {
        return false;
    }
    
    /* Check payload length */
    if (msg->payload_length > 56) {
        return false;
    }
    
    /* Verify state transition */
    if (!fsm_valid_transition(msg->current_state, msg->next_state)) {
        return false;
    }
    
    /* Additional validation based on message type */
    switch (msg->current_state) {
        case FSM_STATE_BULK_DATA:
            /* Bulk data must have valid handle */
            if (msg->payload_length < sizeof(bulk_handle_t)) {
                return false;
            }
            break;
        
        case FSM_STATE_STREAM_START:
        case FSM_STATE_STREAM_CONTINUE:
        case FSM_STATE_STREAM_END:
            /* Streaming messages must have valid fragment header */
            if (msg->payload_length < sizeof(fragment_header_t)) {
                return false;
            }
            break;
        
        default:
            /* Standard message validation */
            break;
    }
    
    return true;
}

/* Simple checksum calculation */
uint16_t fsm_message_checksum(const fsm_message_t *msg) {
    if (!msg) {
        return 0;
    }
    
    uint16_t checksum = 0;
    const uint8_t *data = (const uint8_t *)msg;
    
    /* Calculate checksum over entire message except payload padding */
    size_t check_size = 8 + msg->payload_length;  /* Header + actual payload */
    
    for (size_t i = 0; i < check_size; i++) {
        checksum ^= data[i];
        checksum = (checksum << 1) | (checksum >> 15);  /* Rotate left */
    }
    
    return checksum;
}

/* Convert from Mach message format (simplified) */
bool fsm_from_mach_msg(fsm_message_t *fsm_msg, const struct mach_msg_header *mach_msg) {
    if (!fsm_msg || !mach_msg) {
        return false;
    }
    
    /* This is a simplified conversion - real implementation would need
     * complete Mach message parsing */
    memset(fsm_msg, 0, sizeof(fsm_message_t));
    
    fsm_msg->current_state = FSM_STATE_CREATED;
    fsm_msg->next_state = FSM_STATE_ROUTED;
    
    /* Extract port information from Mach message */
    /* Note: This is pseudo-code - actual Mach integration would be more complex */
    /*
    fsm_msg->source_port = mach_msg->msgh_local_port;
    fsm_msg->dest_server = mach_msg->msgh_remote_port;
    
    // Copy message data (up to 56 bytes)
    size_t data_size = mach_msg->msgh_size - sizeof(struct mach_msg_header);
    if (data_size > 56) {
        // Large message - would need bulk data handling
        return false;
    }
    
    fsm_msg->payload_length = data_size;
    memcpy(fsm_msg->payload, (uint8_t*)mach_msg + sizeof(struct mach_msg_header), data_size);
    */
    
    return true;
}

/* Convert to Mach message format (simplified) */
bool fsm_to_mach_msg(const fsm_message_t *fsm_msg, struct mach_msg_header *mach_msg) {
    if (!fsm_msg || !mach_msg) {
        return false;
    }
    
    /* This is a simplified conversion - real implementation would need
     * complete Mach message construction */
    
    /* Note: This is pseudo-code - actual Mach integration would be more complex */
    /*
    mach_msg->msgh_bits = MACH_MSGH_BITS(MACH_MSG_TYPE_COPY_SEND, 0);
    mach_msg->msgh_size = sizeof(struct mach_msg_header) + fsm_msg->payload_length;
    mach_msg->msgh_remote_port = fsm_msg->dest_server;
    mach_msg->msgh_local_port = fsm_msg->source_port;
    mach_msg->msgh_id = 0;
    
    // Copy payload data
    memcpy((uint8_t*)mach_msg + sizeof(struct mach_msg_header), 
           fsm_msg->payload, fsm_msg->payload_length);
    */
    
    return true;
}