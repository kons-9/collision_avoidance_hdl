`include "types.svh"
`include "packet_types.svh"

module decode_head_flit_comb (
    input types::flit_t head_flit,
    input types::node_id_t this_node_id,
    input logic is_from_cpu,

    output logic is_destination_self,
    output logic is_source_self,
    output types::node_id_t global_destination
);
    always_comb begin
        is_destination_self = head_flit.payload.head.global_dst_id == this_node_id;
        is_source_self = is_from_cpu;
        global_destination = head_flit.payload.head.global_dst_id;
    end
endmodule

