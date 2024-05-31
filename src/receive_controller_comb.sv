module receive_controller_comb (
    input logic nocclk,
    input logic rst_n,
    input types::flit_t received_flit,
    input logic received_flit_valid,
    output logic received_flit_ready,
    input logic ack_buffer_ready,
    output logic ack_buffer_valid,
    input logic packet_buffer_ready,
    output logic packet_buffer_valid,

    output logic waiting_ack_buffer_valid
);

// ack, packet どちらのバッファも有効な場合、データを受け取る
  logic interdevice_rx_ready = packet_buffer_rx_ready & ack_buffer_rx_ready;

// decode and look header
// MUST TODO


endmodule
