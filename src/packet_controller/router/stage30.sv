`include "types.svh"
`include "packet_types.svh"

module stage30 #(
) (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t in_flit,
    input logic in_flit_valid,
    input types::node_id_t in_next_destination,  // culculated by routing table using global_destination
    input logic in_next_destination_valid,
    input types::node_id_t in_this_node_id,
    input types::node_id_t in_parent_id,

    // system flit generator
    input logic in_is_system_flit,
    input packet_types::routing_state_t in_routing_state,
    input types::node_id_t in_global_destination_id,
    input types::node_id_t in_temporal_id,
    output logic out_update_temporal_id,

    input logic in_is_heartbeat_request,
    input logic in_is_root,
    input logic in_is_init,
    input logic in_is_join_ack_parent,
    input system_types::system_header_t in_system_header,
    input system_types::system_payload_t in_payload,

    input types::node_id_t in_node_id_counter,  // only for root
    output logic out_update_node_id_counter,  // only for root

    output logic out_next_routing_state_valid,
    output packet_types::routing_state_t out_next_routing_state,

    output logic out_sys_flit_out_valid,
    output types::flit_t out_sys_flit_out,

    // normal flit generator
    input logic in_is_destination_self,
    output logic out_normal_flit_out_valid,
    output types::flit_t out_normal_flit_out
);
    system_flit_generator_comb system_flit_generator_comb0 (
        .sys_flit(in_flit),
        .sys_flit_valid(in_flit_valid & in_is_system_flit),
        .routing_state(in_routing_state),
        .global_destination_id(in_global_destination_id),
        .next_destination(in_next_destination),
        .next_destination_valid(in_next_destination_valid),
        .temporal_id(in_temporal_id),
        .update_temporal_id(out_update_temporal_id),
        .parent_id(in_parent_id),
        .this_node_id(in_this_node_id),
        .is_heartbeat_request(in_is_heartbeat_request),
        .is_root(in_is_root),
        .is_init(in_is_init),
        .is_join_ack_parent(in_is_join_ack_parent),
        .system_header(in_system_header),
        .payload(in_payload),
        .node_id_counter(in_node_id_counter),
        .update_node_id_counter(out_update_node_id_counter),
        .next_routing_state_valid(out_next_routing_state_valid),
        .next_routing_state(out_next_routing_state),
        .flit_out_valid(out_sys_flit_out_valid),
        .flit_out(out_sys_flit_out)
    );

    normal_flit_generator_comb normal_flit_generator_comb0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .routing_state(in_routing_state),
        .flit(in_flit),
        .flit_valid(in_flit_valid & !in_is_system_flit),
        .next_destination(in_next_destination),
        .next_destination_valid(in_next_destination_valid),
        .this_node_id(in_this_node_id),
        .is_destination_self(in_is_destination_self),

        .flit_out_valid(out_normal_flit_out_valid),
        .flit_out(out_normal_flit_out)
    );
endmodule
