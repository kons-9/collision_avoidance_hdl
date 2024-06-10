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

        types::flit_num_t counter;
        logic [$clog2(MAX_NUM_OF_FLIT)-1:0] tail_index;
        types::flit_t buffer[MAX_NUM_OF_FLIT];
    } packet_element_t;
endpackage

`endif
