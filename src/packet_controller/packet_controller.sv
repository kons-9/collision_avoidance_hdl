`include "types.svh"
module packet_controller #(
    parameter logic IS_ROOT = 0,
    parameter int RANDOM_SEED = 0,
    parameter int MAX_HEARTBEAT_REQUEST_TIMER = 100,
    parameter int MAX_EXPIRE_TIME = 500,
    parameter int MAX_INTERNAL_SYSTEM_TIMER = 1000,
    parameter int MAX_NUM_OF_NEIGHBOR = 8,
    parameter int MAX_NUM_OF_NODE = 2 ** $bits(types::node_id_t)
) (
    input logic nocclk,
    input logic rst_n,

    input types::node_id_t incoming_flit_node_id,
    input logic incoming_flit_valid,

    input types::flit_t next_flit,
    input logic next_flit_valid,
    output logic next_flit_ready,

    input types::flit_t cpu_to_noc_pushed_flit_valid,
    input types::flit_t cpu_to_noc_pushed_flit,
    output logic cpu_to_noc_pushed_flit_ready,

    input logic noc_to_cpu_pushed_flit_ready,
    output logic noc_to_cpu_pushed_flit_valid,
    output types::flit_t noc_to_cpu_pushed_flit,

    input logic forwarded_flit_ready,
    output logic forwarded_flit_valid,
    output types::flit_t forwarded_flit,

    output types::node_id_t this_node_id
);

    logic transfered_packet_completed;
    packet_types::packet_element_t transfered_packet;
    logic transfered_packet_valid;

    // interdevice_flitをpacketに変換する
    packet_buffer #(
        .PACKET_BUFFER_NUM_ENTRIES(8)
    ) packet_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .next_flit(next_flit),
        .next_flit_valid(next_flit_valid),
        .next_flit_ready(next_flit_ready),

        .transfered_packet_completed(transfered_packet_completed),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid)
    );

    // cpu_to_noc_pushed_flitをpacketに変換する
    logic cpu_transfered_packet_completed;
    packet_types::packet_element_t cpu_transfered_packet;
    logic cpu_transfered_packet_valid;
    packet_buffer #(
        // 比較的小さなバッファで良い or TODO: 上のバッファと共有するでもいいかも
        .PACKET_BUFFER_NUM_ENTRIES(2)
    ) cpu_to_noc_packet_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .next_flit(cpu_to_noc_pushed_flit),
        .next_flit_valid(cpu_to_noc_pushed_flit_valid),
        .next_flit_ready(cpu_to_noc_pushed_flit_ready),

        .transfered_packet_completed(cpu_transfered_packet_completed),
        .transfered_packet(cpu_transfered_packet),
        .transfered_packet_valid(cpu_transfered_packet_valid)
    );

    logic transfered_flit_ready;
    logic transfered_flit_valid;
    types::flit_t transfered_flit;
    types::flit_t transfered_head_flit;
    logic is_flit_from_cpu;

    // 完成しているパケットの送信を担当する
    packet_transfer_buffer packet_transfer_buffer (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid),
        .transfered_packet_completed(transfered_packet_completed),
        .cpu_transfered_packet(cpu_transfered_packet),
        .cpu_transfered_packet_valid(cpu_transfered_packet_valid),
        .cpu_transfered_packet_completed(cpu_transfered_packet_completed),

        .transfered_flit_ready(transfered_flit_ready),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_flit(transfered_flit),
        .transfered_head_flit(transfered_head_flit),  // used for routing
        .is_flit_from_cpu(is_flit_from_cpu)
    );

    router #(
        .IS_ROOT(IS_ROOT),
        .RANDOM_SEED(RANDOM_SEED),
        .MAX_HEARTBEAT_REQUEST_TIMER(MAX_HEARTBEAT_REQUEST_TIMER),
        .MAX_EXPIRE_TIMER(MAX_EXPIRE_TIMER),
        .MAX_INTERNAL_SYSTEM_TIMER(MAX_INTERNAL_SYSTEM_TIMER),
        .MAX_NUM_OF_NEIGHBORS(MAX_NUM_OF_NEIGHBORS),
        .MAX_NUM_OF_NODES(MAX_NUM_OF_NODES)
    ) router_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .incoming_flit_node_id(incoming_flit_node_id),
        .incoming_flit_valid  (incoming_flit_valid),

        .transfered_flit(transfered_flit),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_flit_ready(transfered_flit_ready),

        .transfered_head_flit(transfered_head_flit),
        .is_from_cpu(is_flit_from_cpu),

        .noc_to_cpu_pushed_flit_ready(noc_to_cpu_pushed_flit_ready),
        .noc_to_cpu_pushed_flit(noc_to_cpu_pushed_flit),
        .noc_to_cpu_pushed_flit_valid(noc_to_cpu_pushed_flit_valid),
        .forwarded_flit_ready(forwarded_flit_ready),
        .forwarded_flit(forwarded_flit),
        .forwarded_flit_valid(forwarded_flit_valid),
        .this_node_id(this_node_id)
    );

endmodule
