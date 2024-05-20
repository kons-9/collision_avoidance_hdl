module router (
    input logic clk,
    input logic reset,
    input flit_t flit,
    input trigger,

    output logic flit_out,
    output logic flit_out_valid,
    output logic busy
);

uart_data_t uart_data;
logic uart_rx;
logic uart_tx;
logic uart_trigger;
logic uart_clk;

uart_data_t uart_data_out;
logic uart_data_valid;

uart_clk uc1 (
    .clk(clk),
    .rst_n(reset),

    .uart_clk(uart_clk)
);

uart u1(
    .clk(clk),
    .rst(reset),
    .uart_clk(uart_clk),
    .data(uart_data),
    .trigger(uart_trigger),
    .uart_rx(uart_rx),

    .uart_tx(uart_tx),
    .is_full(is_full),
    .rx_data(uart_data_out),
    .rx_data_valid(uart_data_valid)
);

// routing table that is used to determine the next hop

logic now_flit_index;

always_ff @(posedge clk or negedge reset) begin
    if (reset) begin
        now_flit_index <= 0;
    end 
end

always_ff @(posedge clk) begin
    if (flit.flittype == flit_type_t::HEAD) begin

    end
end

endmodule
