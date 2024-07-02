`include "types.svh"
`include "packet_types.svh"

module system_flit_generator_comb (
    input types::flit_t sys_flit,
    input logic sys_flit_valid,
    input packet_types::routing_state_t routing_state,
    input types::node_id_t global_destination_id,
    input types::node_id_t next_destination,  // culculated by routing table using global_destination
    input logic next_destination_valid,
    input types::node_id_t temporal_id,
    input types::node_id_t parent_id,
    input types::node_id_t this_node_id,

    input logic is_heartbeat_request,
    input logic is_root,
    input logic is_init,
    input logic is_join_ack_parent,
    input system_types::system_header_t system_header,
    input system_types::system_payload_t payload,

    input types::node_id_t node_id_counter,  // only for root
    output logic update_node_id_counter,  // only for root

    output logic next_routing_state_valid,
    output packet_types::routing_state_t next_routing_state,

    output logic flit_out_valid,
    output types::flit_t flit_out
);
    always_comb begin
        flit_out_valid = 0;
        flit_out = 0;
        update_node_id_counter = 0;
        if (sys_flit_valid) begin
            case (routing_state)
                packet_types::INIT: begin
                    // do nothing
                end
                packet_types::I_GENERATE_PARENT_REQUEST: begin
                    // generate parent request
                    flit_out_valid = 1;
                    flit_out.header.src_id = temporal_id;
                    flit_out.header.dst_id = types::BROADCAST_ID;
                    flit_out.header.flittype = types::SYSTEM;
                    flit_out.payload.system.header = system_types::S_PARENT_REQUEST;
                    flit_out.payload.system.payload.parent_request.is_init = 1;

                    next_routing_state_valid = 1;
                    next_routing_state = packet_types::I_WAIT_PARENT_ACK;
                end
                packet_types::I_WAIT_PARENT_ACK: begin
                    // do nothing
                end
                packet_types::I_GENERATE_JOIN_REQUEST: begin
                    // generate join request
                    flit_out_valid = 1;
                    flit_out.header.src_id = temporal_id;
                    flit_out.header.dst_id = parent_id;
                    flit_out.header.flittype = types::SYSTEM;
                    flit_out.payload.system.header = system_types::S_JOIN_REQUEST;

                    flit_out.payload.system.payload.join_request.is_init = 1;
                    flit_out.payload.system.payload.join_request.parent_id = parent_id;
                    flit_out.payload.system.payload.join_request.child_id = temporal_id;

                    next_routing_state_valid = 1;
                    next_routing_state = packet_types::I_WAIT_JOIN_ACK;
                end
                packet_types::I_WAIT_JOIN_ACK: begin
                    // do nothing
                end

                packet_types::S_GENERATE_PARENT_REQUEST: begin
                    flit_out_valid = 1;
                    flit_out.header.src_id = this_node_id;
                    flit_out.header.dst_id = types::BROADCAST_ID;
                    flit_out.header.flittype = types::SYSTEM;
                    flit_out.payload.system.header = system_types::S_PARENT_REQUEST;

                    flit_out.payload.system.payload.parent_request.is_init = 0;

                    next_routing_state_valid = 1;
                    next_routing_state = packet_types::S_WAIT_PARENT_ACK;
                end
                packet_types::S_WAIT_PARENT_ACK: begin
                    // do nothing
                end
                packet_types::S_GENERATE_JOIN_REQUEST: begin
                    flit_out_valid = 1;
                    flit_out.header.src_id = this_node_id;
                    flit_out.header.dst_id = global_destination_id;
                    flit_out.header.flittype = types::SYSTEM;
                    flit_out.payload.system.header = system_types::S_JOIN_REQUEST;

                    flit_out.payload.system.payload.join_request.is_init = 0;
                    flit_out.payload.system.payload.join_request.parent_id = parent_id;
                    flit_out.payload.system.payload.join_request.child_id = this_node_id;

                    next_routing_state_valid = 1;
                    next_routing_state = packet_types::S_WAIT_JOIN_ACK;
                end
                packet_types::S_WAIT_JOIN_ACK: begin
                    // do nothing
                end

                packet_types::NORMAL: begin
                    // this node is joined in the network.
                    case (system_header)
                        system_types::S_PARENT_REQUEST: begin
                            flit_out_valid = 1;
                            flit_out.header.src_id = this_node_id;
                            flit_out.header.dst_id = global_destination_id;
                            flit_out.header.flittype = types::SYSTEM;
                            flit_out.payload.system.header = system_types::S_PARENT_ACK;

                            flit_out.payload.system.payload.parent_ack.is_init = is_init;
                        end
                        system_types::S_PARENT_ACK: begin
                            // do nothing
                            // 基本的にはここには来ないが、バッファの関係で来ることがある
                            // その場合は何もしない
                        end
                        system_types::S_JOIN_REQUEST: begin
                            flit_out_valid = 1;
                            flit_out.header.src_id = this_node_id;
                            if (is_root) begin
                                flit_out.header.dst_id = global_destination_id;
                                flit_out.header.flittype = types::SYSTEM;
                                flit_out.payload.system.header = system_types::S_JOIN_ACK;
                                flit_out.payload.system.payload.join_ack.parent_id = payload.join_request.parent_id;
                                flit_out.payload.system.payload.join_ack.current_child_id = payload.join_request.child_id;
                                if (is_init) begin
                                    flit_out.payload.system.payload.join_ack.child_id = node_id_counter;
                                    update_node_id_counter = 1;
                                end else begin
                                    flit_out.payload.system.payload.join_ack.child_id = payload.join_request.child_id;
                                end

                            end else begin
                                flit_out.header.dst_id = parent_id;
                                flit_out.header.flittype = types::SYSTEM;

                                flit_out.payload.system.header = system_types::S_JOIN_REQUEST;
                                flit_out.payload.system.payload = payload;
                            end
                        end
                        system_types::S_JOIN_ACK: begin
                            flit_out.header.src_id = this_node_id;
                            flit_out.header.flittype = types::SYSTEM;
                            flit_out.payload.system.header = system_types::S_JOIN_ACK;
                            if (is_join_ack_parent) begin
                                flit_out_valid = 1;
                                flit_out.header.dst_id = global_destination_id;
                            end else begin
                                flit_out_valid = next_destination_valid;
                                flit_out.header.dst_id = next_destination;
                            end
                        end
                        system_types::S_SEARCH_FUNCTION: begin
                            // TODO:
                        end
                        system_types::S_SEARCH_ACK: begin
                            // TODO:
                        end
                        system_types::S_DEBUG: begin
                            // TODO:
                        end
                        default: begin
                        end
                    endcase
                end
                packet_types::FATAL_ERROR: begin
                    // nothing to do
                end
                default: begin
                    // nothing to do
                end
            endcase
        end else if (is_heartbeat_request) begin
            // generate heartbeat
            flit_out_valid = 1;
            flit_out.header.src_id = this_node_id;
            flit_out.header.dst_id = parent_id;
            flit_out.header.flittype = types::SYSTEM;
            flit_out.payload.system.header = system_types::S_HEARTBEAT;
        end
    end
endmodule
