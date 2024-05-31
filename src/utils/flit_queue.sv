/// queue like buffer for flit
/// FIFO buffer for flit
module flit_queue #(
    parameter int NUM_ENTRIES = 8
) (
    input logic clk,
    input logic rst_n,

    // for push
    input types::flit_t pushed_flit,
    input logic pushed_flit_valid,
    output logic pushed_flit_ready,

    // for pop
    input logic poped_flit_ready,
    output logic poped_flit_valid,
    output types::flit_t poped_flit
);
  typedef enum logic [1:0] {
    EMPTY,   // head == tail
    VACANT,  // head != tail
    FULL,    // head == tail
    ERROR
  } buffer_state_t;
  typedef struct packed {
    logic [$clog2(NUM_ENTRIES)-1:0] head_index;
    logic [$clog2(NUM_ENTRIES)-1:0] tail_index;
    flit_t [NUM_ENTRIES-1:0] flit_buffer;
    buffer_state_t state;
  } flit_buffer_t;

  flit_buffer_t buffer;

  assign poped_flit = buffer.flit_buffer[buffer.tail_index];
  assign poped_flit_valid = buffer.state === VACANT || buffer.state === FULL;
  assign pushed_flit_ready = buffer.state === VACANT || buffer.state === EMPTY;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer.state <= EMPTY;
      buffer.head_index <= 0;
      buffer.tail_index <= 0;
    end else begin
      case (buffer.state)
        EMPTY: begin
          // pushed_flit_ready == 1 & poped_flit_valid == 0
          if (pushed_flit_valid) begin
            buffer.flit_buffer[buffer.head_index] <= pushed_flit;
            buffer.head_index <= buffer.head_index + 1;
            buffer.state <= VACANT;
          end
        end
        VACANT: begin
          // pushed_flit_ready == 1 & poped_flit_valid == 0
          if (push_flit_valid & poped_flit_ready) begin
            buffer.flit_buffer[buffer.head_index] <= pushed_flit;
            buffer.head_index <= buffer.head_index + 1;
            buffer.tail_index <= buffer.tail_index + 1;
          end else if (pushed_flit_valid) begin
            if (buffer.head_index + 1 === buffer.tail_index) begin
              buffer.state <= FULL;
            end
            buffer.flit_buffer[buffer.head_index] <= pushed_flit;
            buffer.head_index <= buffer.head_index + 1;
          end else if (poped_flit_ready) begin
            if (buffer.head_index === buffer.tail_index + 1) begin
              buffer.state <= EMPTY;
            end
            buffer.tail_index <= buffer.tail_index + 1;
          end
        end
        FULL: begin
          // pushed_flit_ready == 0 & poped_flit_valid == 1
          if (poped_flit_ready) begin
            buffer.tail_index <= buffer.tail_index + 1;
            buffer.state <= VACANT;
          end
        end
        default: begin
          // unreachable
          buffer.state <= ERROR;
        end
      endcase
    end
  end
  // *************************************************************
  //   --- Assertions ---
  // *************************************************************
  // TODO
  index_constraint :
  assert property (@(posedge clk) disable iff (rst) (last_index[vc] >= data_index))
  else $error("index_constraint");
  // *************************************************************
endmodule

