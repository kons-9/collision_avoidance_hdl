`include "types.sv"
module uart_tx (
    input logic  uart_clk,
    input logic  rst_n,
    input logic  flit_in_vld,
    input types::flit_t flit_in,

    output logic uart_tx,
    output logic flit_in_rdy
);
  // TODO: add uart parity
  //
  // flitは128bit
  types::flit_t flit_in_current;
  logic [$clog2(types::FLIT_WIDTH+1)-1:0] flit_in_current_position;
  logic current_bit = flit_in_current[flit_in_current_position];

  typedef enum logic [1:0] {
    TX_IDLE,
    TX_START_BIT,
    TX_DATA,
    TX_END_BIT
  } uart_tx_state_t;

  // state is only idle, sending or sending_system
  uart_tx_state_t tx_state;

  assign flit_in_rdy = tx_state == types::IDLE;

  // 一回の送信でstart bit, data, end bitを送信(130bits)
  always_ff @(posedge uart_clk or negedge rst_n) begin
    if (!rst_n) begin
      flit_in_current_position <= 0;
      tx_state <= types::IDLE;
      uart_tx <= 1; // idle
    end else if (flit_in_vld && flit_in_rdy) begin
      // if valid flit is received, start sending
      tx_state <= types::START_BIT;
      flit_in_current <= flit_in;
      flit_in_rdy <= 0;
    end else if (tx_state == types::START_BIT) begin
      // send start bit
      tx_state <= types::DATA;
      flit_in_current_position <= 0;
      uart_tx <= 0;
    end else if (tx_state == types::DATA) begin
      flit_in_current_position <= flit_in_current_position + 1;
      uart_tx <= current_bit;
      if (flit_in_current_position == types::FLIT_WIDTH - 1) begin
        tx_state <= types::END_BIT;
      end
    end else if (tx_state == types::END_BIT) begin
      // send end bit
      tx_state <= types::IDLE;
      uart_tx  <= 0;
    end else begin
      uart_tx <= 1; // idle
    end
  end


endmodule
