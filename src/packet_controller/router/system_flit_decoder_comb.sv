`include "types.svh"
`include "packet_types.svh"
`include "system_types.svh"

// update state and decode system flit
module system_flit_decoder_comb #(
    parameter logic IS_ROOT = 0
) (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t flit_in,
    input logic flit_valid,
    input system_types::routing_state_t routing_state,

    input types::node_id_t this_node_id,

    output logic is_system_flit,
    output logic is_init,
    output logic is_join_ack_parent,
    output system_types::system_header_t system_header,
    output system_types::system_payload_t system_payload,
    output logic update_parent_valid,
    output types::node_id_t update_parent_node_id,
    output logic update_this_node_valid,
    output types::node_id_t update_this_node_id,
    output logic update_neighbor_id_valid,
    output types::node_id_t update_neighbor_id,
    output logic update_routing_table_valid,
    output types::node_id_t update_routing_table_key,
    output logic is_raw_global_destination_used_to_update_routing_table,
    output logic update_next_state,
    output system_types::routing_state_t next_routing_state,
    output types::node_id_t global_destination_id
);

    wire is_root = IS_ROOT;
    always_comb begin
        system_payload = flit_in.payload.system.payload;
        system_header  = flit_in.payload.system.header;
        is_system_flit = flit_in.header.flittype == types::SYSTEM;
    end

    always_comb begin
        update_next_state = 0;
        next_routing_state = system_types::FATAL_ERROR;
        update_parent_valid = 0;
        update_parent_node_id = 0;
        update_this_node_valid = 0;
        update_this_node_id = 0;
        update_neighbor_id_valid = 0;
        update_neighbor_id = 0;
        update_routing_table_valid = 0;
        update_routing_table_key = 0;
        is_raw_global_destination_used_to_update_routing_table = 0;
        is_init = 0;
        is_join_ack_parent = 0;

        global_destination_id = 0;

        if (is_system_flit && flit_valid) begin
            case (routing_state)
                system_types::I_WAIT_PARENT_ACK: begin
                    if (system_header == system_types::S_PARENT_ACK) begin
                        // parent ackを受信
                        update_next_state = 1;
                        next_routing_state = system_types::I_GENERATE_JOIN_REQUEST;

                        update_parent_valid = 1;
                        update_parent_node_id = system_payload.parent_ack.parent_id;
                    end
                end
                system_types::I_WAIT_JOIN_ACK: begin
                    // update child id
                    if (system_header == system_types::S_JOIN_ACK) begin
                        // join ackを受信
                        update_next_state = 1;
                        next_routing_state = system_types::NORMAL;

                        update_this_node_valid = 1;
                        update_this_node_id = system_payload.join_ack.child_id;
                    end
                end
                system_types::S_WAIT_PARENT_ACK: begin
                    if (system_header == system_types::S_PARENT_ACK) begin
                        // parent ackを受信
                        update_next_state = 1;
                        next_routing_state = system_types::S_GENERATE_JOIN_REQUEST;

                        update_parent_valid = 1;
                        update_parent_node_id = system_payload.parent_ack.parent_id;
                    end
                end
                system_types::S_WAIT_JOIN_ACK: begin
                    // reuse the same child id
                    if (system_header == system_types::S_JOIN_ACK) begin
                        // join ackを受信
                        if (system_payload.join_ack.child_id == this_node_id) begin
                            update_next_state  = 1;
                            next_routing_state = system_types::NORMAL;
                        end else begin
                            // システム障害の場合がありそう
                            // TODO: 検証
                        end
                    end
                end
                system_types::NORMAL: begin
                    case (system_header)
                        system_types::S_NOPE, system_types::S_HEARTBEAT: begin
                            // nothing to do
                        end
                        system_types::S_RESET: begin
                            // TODO:
                        end
                        system_types::S_PARENT_REQUEST: begin
                            global_destination_id = flit_in.header.src_id;
                            is_init = system_payload.parent_request.is_init;
                        end
                        system_types::S_PARENT_ACK: begin
                            // unreachable(but if there is delay, it is possible)
                            // nothing to do
                        end
                        system_types::S_JOIN_REQUEST: begin
                            is_init = system_payload.join_request.is_init;
                            if (is_root) begin
                                global_destination_id = flit_in.header.src_id;
                                update_routing_table_valid = 1;
                                update_routing_table_key = system_payload.join_request.child_id;
                                is_raw_global_destination_used_to_update_routing_table = 1;
                            end else begin
                                // global_destination is parent
                            end
                        end
                        system_types::S_JOIN_ACK: begin
                            is_init = system_payload.join_ack.is_init;
                            update_routing_table_valid = 1;
                            update_routing_table_key = system_payload.join_ack.child_id;
                            if (system_payload.join_ack.parent_id == this_node_id) begin
                                // use random child id
                                global_destination_id = system_payload.join_ack.current_child_id;
                                update_neighbor_id_valid = 1;
                                update_neighbor_id = system_payload.join_ack.child_id;
                                is_join_ack_parent = 1;
                                is_raw_global_destination_used_to_update_routing_table = 1;
                            end else begin
                                global_destination_id = system_payload.join_ack.parent_id;
                            end
                        end
                        system_types::S_SEARCH_FUNCTION: begin
                            // TODO:
                        end
                        system_types::S_SEARCH_FUNCTION_ACK: begin
                            // TODO:
                        end
                        system_types::S_DEBUG: begin
                            // TODO:
                        end
                        default: begin
                        end
                    endcase
                end
                system_types::FATAL_ERROR: begin
                    // nothing to do
                end
                default: begin
                    // nothing to do
                end
            endcase
        end
    end

endmodule
