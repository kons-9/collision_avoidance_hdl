/// request heartbeat and decode headflit
`include "types.svh"
`include "packet_types.svh"

module stage10 #(
    parameter int MAX_HEARTBEAT_REQUEST_TIMER = 100,
    parameter logic IS_ROOT = 0
) (
    input logic nocclk,
    input logic rst_n,

    input system_types::routing_state_t in_routing_state,  // TODO
    input logic in_stage1_stall,  // TODO
    output logic stage1_ready,

    input  types::node_id_t in_this_node_id,
    output types::node_id_t out_global_destination,

    // heartbeat requester
    input logic in_parent_valid,
    input types::node_id_t in_parent_node_id,
    input types::node_id_t in_incoming_flit_node_id,
    output logic out_is_heartbeat_request,

    // decode head flit
    input types::flit_t in_head_flit,
    input logic in_is_from_cpu,
    output logic out_is_destination_self,
    output logic out_is_source_self,

    // system flit decoder
    input logic in_flit_valid,
    input types::flit_t in_flit,

    output logic out_is_system_flit,
    output logic out_is_init,
    output logic out_is_join_ack_parent,
    output system_types::system_header_t out_system_header,
    output system_types::system_payload_t out_system_payload,
    output logic out_update_parent_valid,
    output types::node_id_t out_update_parent_node_id,
    output logic out_update_this_node_valid,
    output types::node_id_t out_update_this_node_id,
    output logic out_update_neighbor_id_valid,
    output types::node_id_t out_update_neighbor_id,

    output logic out_update_routing_table_valid,
    output types::node_id_t out_update_routing_table_key,
    output logic out_is_raw_global_destination_used_to_update_routing_table,

    output logic out_update_next_state,
    output system_types::routing_state_t out_next_routing_state
);
    // priority: system flit > heartbeat request(it generate system flit in
    // 3rd stage) > head flit

    types::node_id_t head_global_destination;
    types::node_id_t system_global_destination;
    logic heartbeat_stall;

    always_comb begin
        out_global_destination = out_is_system_flit ? system_global_destination : head_global_destination;
        heartbeat_stall = in_stage1_stall || out_is_system_flit;
        // if stage1 generate a heartbeat request, then stage1 does not consume the flit
        stage1_ready = !(out_is_heartbeat_request && !heartbeat_stall);
    end

    decode_head_flit_comb decode_head_flit_comb_inst (
        .head_flit(in_head_flit),
        .this_node_id(in_this_node_id),
        .is_from_cpu(in_is_from_cpu),

        .is_destination_self(out_is_destination_self),
        .is_source_self(out_is_source_self),
        .global_destination(head_global_destination)
    );

    system_flit_decoder_comb #(
        .IS_ROOT(IS_ROOT)
    ) system_flit_decoder_comb_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .flit_in(in_flit),
        .flit_valid(in_flit_valid),
        .routing_state(in_routing_state),
        .this_node_id(in_this_node_id),

        .is_system_flit(out_is_system_flit),
        .is_init(out_is_init),
        .is_join_ack_parent(out_is_join_ack_parent),
        .system_header(out_system_header),
        .system_payload(out_system_payload),
        .update_parent_valid(out_update_parent_valid),
        .update_parent_node_id(out_update_parent_node_id),
        .update_this_node_valid(out_update_this_node_valid),
        .update_this_node_id(out_update_this_node_id),
        .update_neighbor_id_valid(out_update_neighbor_id_valid),
        .update_neighbor_id(out_update_neighbor_id),
        .update_routing_table_valid(out_update_routing_table_valid),
        .update_routing_table_key(out_update_routing_table_key),
        .is_raw_global_destination_used_to_update_routing_table(out_is_raw_global_destination_used_to_update_routing_table),
        .update_next_state(out_update_next_state),
        .next_routing_state(out_next_routing_state),
        .global_destination_id(system_global_destination)
    );

    heartbeat_requester #(
        .MAX_HEARTBEAT_REQUEST_TIMER(MAX_HEARTBEAT_REQUEST_TIMER)
    ) heartbeat_requester_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),
        .stall (heartbeat_stall),

        .parent_valid(in_parent_valid),
        .parent_node_id(in_parent_node_id),
        .incoming_flit_node_id(in_incoming_flit_node_id),

        .is_heartbeat_request(out_is_heartbeat_request)
    );
endmodule
