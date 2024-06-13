/// FIFO buffer
module queue #(
    parameter int NUM_ENTRIES = 8,
    parameter int DATA_WIDTH  = 128
) (
    input logic clk,
    input logic rst_n,

    // for push
    input logic [DATA_WIDTH-1:0] pushed_element,
    input logic pushed_valid,
    output logic pushed_ready,

    // for pop
    input logic poped_ready,
    output logic poped_valid,
    output logic [DATA_WIDTH-1:0] poped_element
);
    typedef enum logic [1:0] {
        EMPTY,   // head == tail
        VACANT,  // head != tail
        FULL,    // head == tail
        ERROR
    } buffer_state_t;
    typedef struct {
        logic [$clog2(NUM_ENTRIES)-1:0] head_index;
        logic [$clog2(NUM_ENTRIES)-1:0] tail_index;
        logic [DATA_WIDTH-1:0] buffer[NUM_ENTRIES];
        buffer_state_t state;
    } buffer_t;

    buffer_t buffer;

    assign poped_element = buffer.buffer[buffer.tail_index];
    assign poped_valid   = buffer.state === VACANT || buffer.state === FULL;
    assign pushed_ready  = buffer.state === VACANT || buffer.state === EMPTY;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buffer.state <= EMPTY;
            buffer.head_index <= 0;
            buffer.tail_index <= 0;
        end else begin
            case (buffer.state)
                EMPTY: begin
                    // pushed_ready == 1 & poped_valid == 0
                    if (pushed_valid) begin
                        buffer.buffer[buffer.head_index] <= pushed_element;
                        buffer.head_index <= buffer.head_index + 1;
                        buffer.state <= VACANT;
                    end
                end
                VACANT: begin
                    // pushed_ready == 1 & poped_valid == 1
                    if (pushed_valid & poped_ready) begin
                        buffer.buffer[buffer.head_index] <= pushed_element;
                        buffer.head_index <= buffer.head_index + 1;
                        buffer.tail_index <= buffer.tail_index + 1;
                    end else if (pushed_valid) begin
                        if (buffer.head_index + 1 === buffer.tail_index) begin
                            buffer.state <= FULL;
                        end
                        buffer.buffer[buffer.head_index] <= pushed_element;
                        buffer.head_index <= buffer.head_index + 1;
                    end else if (poped_ready) begin
                        if (buffer.head_index === buffer.tail_index + 1) begin
                            buffer.state <= EMPTY;
                        end
                        buffer.tail_index <= buffer.tail_index + 1;
                    end
                end
                FULL: begin
                    // pushed_ready == 0 & poped_valid == 1
                    if (poped_ready) begin
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
    // index_constraint :
    // assert property (@(posedge clk) disable iff (rst) (last_index[vc] >= data_index))
    // else $error("index_constraint");
    // *************************************************************
endmodule

