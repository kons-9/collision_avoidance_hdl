module dummy_top (
    input clk,
    input rst_n
);

wire [127:0] flit_rx;
wire flit_rx_vld;
wire [127:0] flit_tx;
wire flit_tx_vld;

shapechangeable_chip #(
    .IS_ROOT(1),
    .RANDOM_SEED(1000)
) shapechangeable_chip_inst0 (
    .clk  (clk),
    .rst_n(rst_n),
    .flit_rx(flit_rx),
    .flit_rx_vld(flit_rx_vld),
    .flit_tx(flit_tx),
    .flit_tx_vld(flit_tx_vld)
);

shapechangeable_chip #(
    .IS_ROOT(0),
    .RANDOM_SEED(0)
) shapechangeable_chip_inst1 (
    .clk  (clk),
    .rst_n(rst_n),
    .flit_rx(flit_tx),
    .flit_rx_vld(flit_tx_vld),
    .flit_tx(flit_rx),
    .flit_tx_vld(flit_rx_vld)
);
endmodule

