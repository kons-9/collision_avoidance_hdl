///@brief 適切なバッファ選択を行うモジュール
/// ack buffer, forwarding buffer, cpu_to_noc bufferの状態を監視し、適切な
//bufferからデータを取り出す。
module buffer_selecter_comb (
    input types::flit_t ack_flit,
    input logic ack_flit_valid,
    output logic ack_flit_ready,

    input types::flit_t waiting_ack_buffer_flit,
    input logic waiting_ack_buffer_valid,
    output logic waiting_ack_buffer_ready,

    input types::flit_t forwarding_flit,
    input logic forwarding_flit_valid,
    output logic forwarding_flit_ready,

    input types::flit_t cpu_to_noc_flit,
    input logic cpu_to_noc_flit_valid,
    output logic cpu_to_noc_flit_ready,

    input logic flit_out_ready,
    output types::flit_t flit_out,
    output logic flit_out_valid
);

  // 単純な優先度で選択する
  // ack buffer -> forwarding buffer -> cpu_to_noc buffer
  // ackはリアルタイム性が重要なため、最優先

  always_comb begin
    ack_flit_ready = 0;
    forwarding_flit_ready = 0;
    cpu_to_noc_flit_ready = 0;
    waiting_ack_buffer_ready = 0;
    flit_out = 0;
    flit_out_valid = 0;
    if (flit_out_ready) begin
      if (ack_flit_valid) begin
        ack_flit_ready = 1;
        forwarding_flit_ready = 0;
        cpu_to_noc_flit_ready = 0;
        waiting_ack_buffer_ready = 0;
        flit_out = ack_flit;
        flit_out_valid = 1;
      end else if (waiting_ack_buffer_valid) begin
        ack_flit_ready = 0;
        forwarding_flit_ready = 0;
        cpu_to_noc_flit_ready = 0;
        waiting_ack_buffer_ready = 1;
        flit_out = waiting_ack_buffer_flit;
        flit_out_valid = 1;
      end else if (forwarding_flit_valid) begin
        ack_flit_ready = 0;
        forwarding_flit_ready = 1;
        cpu_to_noc_flit_ready = 0;
        waiting_ack_buffer_ready = 0;
        flit_out = forwarding_flit;
        flit_out_valid = 1;
      end else if (cpu_to_noc_flit_valid) begin
        ack_flit_ready = 0;
        forwarding_flit_ready = 0;
        cpu_to_noc_flit_ready = 1;
        waiting_ack_buffer_ready = 0;
        flit_out = cpu_to_noc_flit;
        flit_out_valid = 1;
      end
    end

  end


endmodule
