`ifndef PACKET_TYPES_SVH
`define PACKET_TYPES_SVH

`include "types.svh"
package packet_types;
    parameter int MAX_NUM_OF_FLIT = 8;
    parameter int EXPIRE_TIME = 100;
    typedef struct {
        logic is_complete;
        types::packet_id_t packet_id;
        logic [$clog2(EXPIRE_TIME)-1:0] timer;

        logic [$clog2(MAX_NUM_OF_FLIT)-1:0] tail_index;
        types::flit_t buffer[MAX_NUM_OF_FLIT];
    } packet_element_t;

    typedef struct {
        logic valid[$bits(types::node_id_t)];
        types::node_id_t routing_table[$bits(types::node_id_t)];
        logic this_node_valid;
        types::node_id_t this_node_id;
        logic parent_valid;
        types::node_id_t parent_node_id;
    } routing_table_t;

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
