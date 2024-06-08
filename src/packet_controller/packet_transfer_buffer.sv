`include "types.svh"
`include "packet_types.svh"

// 完了したパケットの送信を担当する
module packet_transfer_buffer (
    input logic nocclk,
    input logic rst_n,

    input packet_types::packet_element_t transfered_packet,
    input logic transfered_packet_valid,
    // 転送が完了したら、indexをfreeするために使う
    // 1clkで消費される
    output logic transfered_packet_completed,

    input logic transfered_flit_ready,
    output logic transfered_flit_valid,
    output types::flit_t transfered_flit,
    output types::flit_t transfered_head_flit

);
    types::flit_num_t current_flit_num;
    types::flit_num_t next_flit_num = current_flit_num + 1;
    logic end_of_packet = transfered_packet.tail_index == next_flit_num;

    assign transfered_packet_completed = end_of_packet & transfered_packet_valid;
    assign transfered_flit_valid = transfered_packet_valid & !transfered_packet_completed;
    assign transfered_flit = transfered_packet.flit[current_flit_num];
    assign transfered_head_flit = transfered_packet.flit[0];

    logic is_sending_packet;

    always_ff @(posedge nocclk) begin
        if (rst_n) begin
            is_sending_packet <= 0;
        end else begin
            if (transfered_flit_ready & transfered_flit_valid) begin
                if (is_sending_packet) begin
                    if (end_of_packet) begin
                        is_sending_packet <= 0;
                    end
                    current_flit_num <= next_flit_num;
                end else begin
                    current_flit_num <= 0;
                    is_sending_packet <= 1;
                end
            end
        end
    end




endmodule
