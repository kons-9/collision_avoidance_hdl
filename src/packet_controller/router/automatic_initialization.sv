`include "packet_types.svh"
`include "types.svh"
module automatic_initialization #(
    parameter int PACK_TIME_OUT = 100,
    parameter int JACK_TIME_OUT = 300
) (
    input logic noc_clk,
    input logic rst_n,

    input logic is_flit_in_valid,
    input types::flit_t flit_in,

    input packet_types::routing_state_t routing_state,

    output logic is_next_state,
    output logic is_reset_state,
    output logic flit_valid,
    output types::flit_t flit_out
);
    logic [$clog2(JACK_TIME_OUT)-1:0] time_out_counter;
    logic [$clog2(JACK_TIME_OUT)-1:0] next_time_out_counter;

    always_comb @(posedge nocclk) begin
        flit_out = 0;
        flit_out.header.version = 0;
        flit_out.is_ack = 0;
        flit_out.flittype = types::flit_type_t::SYSTEM;
        flit_out.src_id = 0;
        flit_out.dst_id = types::BROADCAST_ID;
        flit_out.flit_id = 0;

        is_reset_state = 0;
        is_next_state = 0;
        flit_valid = 0;

        case (routing_state)
            packet_types::INIT: begin
                is_next_state = 1;
                flit_valid = 0;
                next_time_out_counter = 0;
            end
            packet_types::I_GENERATE_PARENT_REQUEST: begin
                is_next_state = 1;
                flit_valid = 1;
                flit_out.payload.system.header = system_types::S_PARENT_REQUEST_FROM_NEIGHBOR;
                flit_out.payload.system.payload = 0;
                next_time_out_counter = 0;
            end
            packet_types::I_WAIT_PARENT_ACK: begin
                if (is_flit_in_valid && flit_in.payload.system.header == system_types::S_PARENT_ACK_FROM_NEIGHBOR) begin
                    is_next_state = 1;
                end else if (timer_out_counter == PACK_TIME_OUT) begin
                    is_reset_state = 1;
                end else begin
                    // just wait
                    next_time_out_counter = time_out_counter + 1;
                end
            end
            packet_types::I_GENERATE_JOIN_REQUEST: begin
                is_next_state = 1;
                flit_valid = 1;
                flit_out.header.src_id = 0;
                flit_out.header.dst_id = types::BROADCAST_ID;
                flit_out.payload.system.header = system_types::S_GENERATE_JOIN_REQUEST;
                next_time_out_counter = 0;
            end
            packet_types::I_WAIT_JOIN_ACK: begin
                if (is_flit_in_valid && flit_in.payload.system.header == system_types::S_JOIN_ACK_FROM_NEIGHBOR) begin
                    is_next_state = 1;
                end else if (timer_out_counter == JACK_TIME_OUT) begin
                    is_reset_state = 1;
                end else begin
                    // just wait
                    next_time_out_counter = time_out_counter + 1;
                end
            end
            default: begin
                is_next_state = 0;
                flit_valid = 0;
            end
        endcase
    end

    always_ff @(posedge nocclk) begin
        time_out_counter <= next_time_out_counter;
    end

endmodule
