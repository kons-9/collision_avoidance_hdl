`include "types.sv"
module uart_rx (
    input  logic  nocclk,
    input  logic  uart_clk,
    input  logic  rst_n,
    input  logic  uart_rx,
    output types::flit_t flit_out,
    output logic  flit_out_vld
);
  typedef enum logic [1:0] {
    RX_IDLE,
    RX_NOT_RECEIVING,
    RX_DATA,
    RX_END_BIT
  } uart_rx_state_t;

  uart_rx_state_t rx_state;
  types::flit_t flit_out_current;
  logic [$clog2(types::FLIT_WIDTH+1)-1:0] flit_out_current_position;

  assign flit_out_vld = rx_state == types::IDLE;

  always_ff @(posedge uart_clk or negedge rst_n) begin
    if (!rst_n) begin
      flit_out_current_position <= 0;
      rx_state <= types::NOT_RECEIVING;
      flit_out_vld <= 0;
    end else if (rx_state == types::IDLE | rx_state == types::NOT_RECEIVING) begin
      if (!uart_rx) begin
        rx_state <= types::DATA;
        flit_out_current_position <= 0;
      end
    end else if (rx_state == types::DATA) begin
      flit_out_current[flit_out_current_position] <= uart_rx;
      flit_out_current_position <= flit_out_current_position + 1;
      if (flit_out_current_position == types::FLIT_WIDTH - 1) begin
        rx_state <= types::END_BIT;
      end
    end else if (rx_state == types::END_BIT) begin
      if (!uart_rx) begin
        rx_state <= types::IDLE;
        flit_out <= flit_out_current;
        flit_out_vld <= 1;
      end else begin
        // invalid end bit
        rx_state <= types::NOT_RECEIVING;
        flit_out_vld <= 0;
      end
    end
  end

endmodule
