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
    // MUST TODO

    flit_num_t next_flit_counter;


    packet_buffer packet_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .next_flit(next_flit),
        .next_flit_valid(next_flit_valid),
        .next_flit_ready(next_flit_ready),
        .poped_flit(),
        .poped_flit_valid()
    );
    // 完成しているパケットの送信を担当する
    packet_transfer_buffer packet_transfer_buffer ();

    router router ();

endmodule
