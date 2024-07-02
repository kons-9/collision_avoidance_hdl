module shapechangeable_chip (
    input clk,
    input rst_n,

    input [127:0] flit_rx,
    input flit_rx_vld,
    output [127:0] flit_tx,
    output flit_tx_vld
);

wire [31:0] nic_rx;
wire nic_rx_en;
wire nic_rx_rdy;

wire nic_tx_rdy;
wire [31:0] nic_tx;
wire nic_tx_en;

noc noc_inst (
    .cpuclk(clk),
    .nocclk(clk),
    .rst_n(rst_n),

    .data_in(nic_tx),
    .data_in_vld(nic_tx_en),
    .data_in_rdy(nic_tx_rdy),

    .data_out(nic_rx),
    .data_out_vld(nic_rx_en),
    .data_out_rdy(nic_rx_rdy),

    .flit_rx(flit_rx),
    .flit_rx_vld(flit_rx_vld),
    .flit_tx(flit_tx),
    .flit_tx_vld(flit_tx_vld)
);

cpu_top cpu_top_inst (
    .clk(clk),
    .rst(!rst_n),

    .nic_rx(nic_rx),
    .nic_rx_en(nic_rx_en),
    .nic_rx_rdy(nic_rx_rdy),

    .nic_tx_rdy(nic_tx_rdy),
    .nic_tx(nic_tx),
    .nic_tx_en(nic_tx_en)
);

endmodule
