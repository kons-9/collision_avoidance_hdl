// ホストからデータをmessage_bufferを通じて受取る。
// message_bufferはパケットの配列である
module network_interface
(
    input wire clk,
    input wire rst_n,

    // whether in or out port is valid
    input wire [FLIT_WIDTH-1:0] flit_in,
    input wire in_trigger,
    input wire have_read,

    output logic [FLIT_WIDTH-1:0] flit_out,
    output logic valid_out,
    output logic nic_we,

    output signal_t signal_info,
    output logic signal
);
 `include "types.sv"

  parameter NUM_ENTRIES = 1 << 6; // 64 entries

  types::buffer_t rx_buffer;
  types::buffer_t tx_buffer;

  assign nic_we = rx_buffer.state == VACANT || rx_buffer.state == EMPTY;
  assign valid_out = rx_buffer.state != EMPTY;
  assign flit_out = rx_buffer.data_buffer[rx_buffer.pop_index];

  // in
  logic next_next_push_index = in_trigger ? rx_buffer.push_index + 1 : rx_buffer.push_index;
  // out
  logic next_next_pop_index = have_read ? rx_buffer.pop_index + 1 : rx_buffer.pop_index;
  // flags
  logic full_flag = next_next_push_index + 1 == next_next_pop_index;
  logic overfull_flag = next_next_push_index == next_next_pop_index;
  logic empty_flag = next_next_push_index == next_next_pop_index;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rx_buffer.state <= VACANT;
    end
    else begin
        case (rx_buffer.state)
          EMPTY: begin
            rx_buffer.state <= empty_flag ? EMPTY : VACANT;
          end
          VACANT: begin
            rx_buffer.state <= empty_flag ? EMPTY :
                            full_flag ? FULL : VACANT;
          end
          FULL: begin
            rx_buffer.state <= overfull_flag ? OVERFULL :
                            full_flag ? FULL : VACANT;
          end
          OVERFULL: begin
            rx_buffer.state <= overfull_flag ? OVERFULL : FULL;
          end
        endcase
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    // reset
    if (!rst_n) begin
        rx_buffer.push_index <= 0;
        rx_buffer.pop_index <= 0;
    end
    else begin
        // data in
        rx_buffer.data_buffer[rx_buffer.push_index] <= flit_in;
        rx_buffer.push_index <= next_next_push_index;
        rx_buffer.pop_index <= next_next_pop_index;
    end
  end

  // *************************************************************
  //   --- Assertions ---
  // *************************************************************
  index_constraint :
  assert property (@(posedge clk) disable iff (rst) (last_index[vc] >= data_index))
  else $error("index_constraint");
  // *************************************************************


endmodule

