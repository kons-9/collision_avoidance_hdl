module packet_controller(
    input logic nocclk,
    input logic rst_n,

    input types::flit_t flit_in,
    input logic flit_in_valid,
    output logic flit_in_ready,

    input logic noc_to_cpu_pushed_flit_ready,
    output logic noc_to_cpu_pushed_flit_valid,
    output types::flit_t noc_to_cpu_pushed_flit,

    input logic forwarded_flit_ready,
    output logic forwarded_flit_valid,
    output types::flit_t forwarded_flit
);
// MUST TODO

packet_buffer packet_buffer();
check_if_complete_comb check_if_complete_comb();
check_if_self_comb check_if_self_comb();
router_comb router_comb();

// 完成しているパケットの送信を担当する
packet_transfer_buffer packet_transfer_buffer();

endmodule
