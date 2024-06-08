`include "types.svh"
module packet_controller (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t next_flit,
    input logic next_flit_valid,
    output logic next_flit_ready,

    input logic noc_to_cpu_pushed_flit_ready,
    output logic noc_to_cpu_pushed_flit_valid,
    output types::flit_t noc_to_cpu_pushed_flit,

    input logic forwarded_flit_ready,
    output logic forwarded_flit_valid,
    output types::flit_t forwarded_flit
);

    logic transfered_packet_completed;
    packet_types::packet_element_t transfered_packet;
    logic transfered_packet_valid;

    packet_buffer packet_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .next_flit(next_flit),
        .next_flit_valid(next_flit_valid),
        .next_flit_ready(next_flit_ready),

        .transfered_packet_completed(transfered_packet_completed),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid)
    );

    logic transfered_flit_ready;
    logic transfered_flit_valid;
    types::flit_t transfered_flit;
    types::flit_t transfered_head_flit;

    // 完成しているパケットの送信を担当する
    packet_transfer_buffer packet_transfer_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid),
        .transfered_packet_completed(transfered_packet_completed),

        .transfered_flit_ready(transfered_flit_ready),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_flit(transfered_flit),
        .transfered_head_flit(transfered_head_flit)  // used for routing
    );

    router router (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .transfered_flit(transfered_flit),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_flit_ready(transfered_flit_ready),
        .transfered_head_flit(transfered_head_flit),

        .noc_to_cpu_pushed_flit_ready(noc_to_cpu_pushed_flit_ready),
        .noc_to_cpu_pushed_flit(noc_to_cpu_pushed_flit),
        .noc_to_cpu_pushed_flit_valid(noc_to_cpu_pushed_flit_valid),
        .forwarded_flit_ready(forwarded_flit_ready),
        .forwarded_flit(forwarded_flit),
        .forwarded_flit_valid(forwarded_flit_valid)
    );

endmodule
