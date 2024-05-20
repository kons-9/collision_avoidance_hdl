module message_buffer (
    input logic clk,
    input logic rst_n,
    // whether in or out port is valid
    input logic valid_in,
    input logic [16:0] data_in,
    input logic [5:0] data_index_in,
    input logic [1:0] vc_in,
    input logic [5:0] data_index_out,
    input logic [1:0] vc_out,

    output logic [16:0] data_out,
    output logic valid_out,
    output logic is_last
);

  parameter NUM_VC = 4;
  parameter NUM_ENTRIES = 64;

  typedef struct packed {
    logic [5:0] last_index;
    logic [5:0] now_index; // used for sending
    // data buffer
    // each vc has 64 entries of 16 bit data = 1024 bits = 1KiB
    struct packed {
        packet_header_t header;
        logic [15:0] data_buffer[NUM_ENTRIES];
    } data_buffer;
    logic completed;
  } data_t;

  data_t data[NUM_VC];

  assign is_last = (data_index_out == data[vc_out].last_index);
  assign valid_out = (data[vc_out].completed);

  // reset
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        for (int i = 0; i < NUM_VC; i++) begin
            data[i].last_index <= 0;
            data[i].now_index <= 0;
            data[i].completed <= 0;
        end
    end
  end

  always_ff @(posedge clk) begin
    if (valid_in) begin
      data[vc_in].data_buffer[data_index_in] <= data_in;
      data[vc_in].last_index <= data_index_in;
    end else begin
      data_out <= data[vc_out].data_buffer[data_index_out];
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

