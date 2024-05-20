module uart (
    // cpu clock
    input logic clk,
    input logic rst,
    // uart clock
    input logic uart_clk,
    // for uart_tx
    input uart_data_t data,
    input logic trigger,  // if is_full, must be 0
    // for uart_rx
    input logic uart_rx,

    // for uart_tx
    output logic uart_tx,
    output logic is_full,
    // for uart_rx
    output uart_data_t rx_data,
    output logic rx_data_valid
);

  // *************************************************************
  //   --- Assertions ---
  // *************************************************************
  trigger_constraint :
  assert property (@(posedge clk) disable iff (rst) (trigger |-> !is_full))
  else $error("trigger_constraint");
  // *************************************************************

  parameter UART_DATA_NUM_MAX = 128;

  uart_data_t [UART_DATA_NUM_MAX-1:0] data_queue;
  // max is 4
  // logic [1:0] queue_process_ind;
  // logic [1:0] queue_empty_ind;
  logic [$clog2(UART_DATA_NUM_MAX+1)-1:0] queue_process_ind;
  logic [$clog2(UART_DATA_NUM_MAX+1)-1:0] queue_empty_ind;

  typedef enum logic[2:0] {
    IDLE,
    SENDING,
    RECEIVING
  } uart_state_t;

  uart_state_t state;
  uart_data_t sending_data;

  logic [2:0] count;  // 0-7

  // reset
  always_ff @(negedge rst) begin
    state <= uart_state_t::IDLE;
    uart_tx <= 1;
    rx_data_valid <= 0;
    is_full <= 0;
    queue_process_ind <= 3;
    queue_empty_ind <= 0;
  end

  // for uart_tx
  // push data to queue
  always_ff @(posedge clk) begin
    if (trigger) begin
      data_queue[queue_empty_ind] <= data;
      is_full <= (queue_empty_ind + 1 == queue_process_ind);
      queue_empty_ind <= queue_empty_ind + 1;
    end
  end
  // send data from queue
  logic executable = (state == uart_state_t::IDLE) & !uart_rx;
  logic any_data = is_full | (queue_empty_ind != queue_process_ind);
  always_ff @(posedge clk) begin
    if (uart_clk == 0) begin
      if (executable & any_data) begin
        // there is data in queue
        is_full <= 0;
        sending_data <= data_queue[queue_process_ind];
        queue_process_ind <= queue_process_ind + 1;
        state <= uart_state_t::SENDING;
        // start bit
        uart_tx <= 0;
      end else if (state == uart_state_t::SENDING) begin
        // NOTE: for now, not use parity bit
        if (count == UART_DATA_IND_MAX) begin
          state <= uart_state_t::IDLE;
        end
        // if count == 7, overflows to 0
        count   <= count + 1;
        uart_tx <= sending_data[count];
      end else begin
        uart_tx <= 1;
      end
    end
  end

  // for uart_rx
  always_ff @(posedge clk) begin
    if (uart_clk == 0) begin
      if (state == uart_state_t::RECEIVING) begin
        if (count == UART_DATA_IND_MAX) begin
          state <= uart_state_t::IDLE;
          rx_data_valid <= 1;
        end
        count   <= count + 1;
        rx_data <= rx_data | (uart_rx << count);
      end else if (!uart_rx) begin
        // start bit
        state <= uart_state_t::RECEIVING;
        rx_data_valid <= 0;
        uart_clk <= 0;
      end
    end
  end

endmodule
