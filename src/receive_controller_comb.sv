`include "types.svh"

module receive_controller_comb (
    input types::flit_t received_flit,
    input logic received_flit_valid,
    output logic received_flit_ready,

    input  logic ack_buffer_ready,
    output logic ack_buffer_valid,
    input  logic packet_buffer_ready,
    output logic packet_buffer_valid,
    output logic waiting_ack_buffer_valid
);

  // decode and look header
  // ack field が立っている場合、waiting ack バッファにデータを入れる
  // ack field が立っていない場合、ack buffer, packet buffer にデータを入れる
  always_comb begin
    ack_buffer_valid = 0;
    packet_buffer_valid = 0;
    waiting_ack_buffer_valid = 0;
    received_flit_ready = 0;
    if (received_flit.header.is_ack) begin
      // ackを受信した場合はwaiting ack bufferにデータを入れる
      waiting_ack_buffer_valid = 1;
      received_flit_ready = 1;
    end else begin
      // ackを受信していない場合はack buffer, packet bufferにデータを入れる
      // このとき、ack buffer, packet bufferの両方が受領可能であることを確認する
      if (ack_buffer_ready & packet_buffer_ready) begin
        ack_buffer_valid = 1;
        packet_buffer_valid = 1;
        waiting_ack_buffer_valid = 0;
        received_flit_ready = 1;
      end
    end
  end

endmodule
