module flit_buffer (
    input logic clk,
    input logic rst_n,
    input types::flit_buffer_t buffer,
    input types::flit_t insert_flit,
    input logic insert_flit_valid,
    input logic is_pop,

    output types::flit_t next_flit,
    output types::buffer_state_t next_state
);
  // もしbuffer.stateがEMPTYならば、popはできない

  assign next_state = buffer.state;
  assign next_flit = buffer.flit_buffer[buffer.tail_index];

  // TODO
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer.state <= types::EMPTY;
      buffer.head_index <= 0;
      buffer.tail_index <= 0;
    end else begin
      case (buffer.state)
        types::EMPTY: begin
          if (insert_flit_valid) begin
            buffer.state <= types::VACANT;
            flit_buffer[buffer.head_index] <= insert_flit;
            buffer.head_index <= buffer.head_index + 1;
          end
        end
        types::VACANT: begin
          if (is_pop) begin
            buffer.state <= (buffer.head_index == buffer.tail_index+1) ?
                types::EMPTY : types::VACANT;
            buffer.tail_index <= buffer.tail_index + 1;
          end else if (insert_flit_valid) begin
            buffer.state <= (buffer.head_index == buffer.tail_index+1) ?
                types::FULL : types::VACANT;
            flit_buffer[buffer.head_index] <= insert_flit;
            buffer.head_index <= buffer.head_index + 1;
          end
        end
        types::ALMOST_FULL: begin
          if (is_pop) begin
            buffer.state <= types::VACANT;
          end else if (insert_flit_valid) begin
            buffer.state <= types::FULL;
          end
        end
        types::FULL: begin
          if (is_pop) begin
            buffer.state <= types::VACANT;
          end else if (insert_flit_valid) begin
            buffer.state <= types::FULL;
          end
        end
        default: begin
          // unreachable
          buffer.state <= types::EMPTY;
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

