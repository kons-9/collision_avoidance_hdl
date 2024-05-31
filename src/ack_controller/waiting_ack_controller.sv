module waiting_ack_controller (
    input logic nocclk,
    input logic rst_n,
    input types::flit_t waiting_ack_flit,
    input logic waiting_ack_flit_valid,
    output logic waiting_ack_flit_ready,
    input logic poped_waiting_ack_flit_ready,
    output logic poped_waiting_ack_flit_valid,
    output types::flit_t poped_waiting_ack_flit
);
  // MUST TODO
endmodule
