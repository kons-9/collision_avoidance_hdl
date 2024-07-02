`ifndef SYSTEM_TYPES_SVH
`define SYSTEM_TYPES_SVH
`include "primitive_types.svh"
package system_types;
    // system_header + system_payload = 72 bits
    import primitive_types::*;

    // header 8 bits
    typedef enum logic [7:0] {
        S_NOPE = 0,
        S_HEARTBEAT,
        S_RESET,

        S_PARENT_REQUEST,
        S_PARENT_ACK,
        S_JOIN_REQUEST,
        S_JOIN_ACK,

        S_SEARCH_FUNCTION,
        S_SEARCH_FUNCTION_ACK,
        S_DEBUG
    } system_header_t;  // 8 bits

    // for payload
    typedef struct packed {
        // undefined
        logic is_init;
        logic [62:0] undefined;
    } parent_request_t;
    typedef struct packed {
        logic is_init;
        node_id_t parent_id;  // 8 bits
        node_id_t child_id;  // 8 bits
        node_id_t global_id;  // 8 bits
        // undefined
        logic [38:0] undefined;  // 40 bits
    } parent_ack_t;
    typedef struct packed {
        logic is_init;
        node_id_t parent_id;  // 8 bits
        node_id_t child_id;  // 8 bits
        // undefined
        logic [46:0] undefined;  // 48 bits
    } join_request_t;
    typedef struct packed {
        logic is_init;
        node_id_t current_child_id;  // 8 bits
        node_id_t parent_id;  // 8 bits
        node_id_t child_id;  // 8 bits
        // undefined
        logic [38:0] undefined;  // 48 bits
    } join_ack_t;
    typedef struct packed {
        logic [7:0]  function_id;  // 8 bits
        // undefined
        logic [55:0] undefined;    // 56 bits
    } search_function_t;
    typedef struct packed {
        node_id_t function_node_id;  // 8 bits
        flit_num_t function_flit_num;  // 8 bits
        // undefined
        logic [47:0] undefined;  // 48 bits
    } search_function_ack_t;
    typedef struct packed {
        node_id_t from_id;
        node_id_t to_id;
        // undefined
        logic [47:0] undefined;  // 48 bits
    } debug_t;

    // payload 56 bits
    typedef union packed {
        parent_request_t parent_request;
        parent_ack_t parent_ack;
        join_ack_t join_ack;
        join_request_t join_request;
        search_function_t search_function;
        search_function_ack_t search_function_ack;
    } system_payload_t;

    typedef enum {
        INIT,

        // for initializtion
        I_GENERATE_PARENT_REQUEST,
        I_WAIT_PARENT_ACK,
        I_GENERATE_JOIN_REQUEST,
        I_WAIT_JOIN_ACK,

        // for separation
        S_GENERATE_PARENT_REQUEST,
        S_WAIT_PARENT_ACK,
        S_GENERATE_JOIN_REQUEST,
        S_WAIT_JOIN_ACK,

        NORMAL,

        FATAL_ERROR
    } routing_state_t;
endpackage
`endif
