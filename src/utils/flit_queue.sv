`include "types.svh"
import types::flit_t;
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

    queue #(
        .NUM_ENTRIES(NUM_ENTRIES),
        .DATA_WIDTH($bits(flit_t))
    ) flit_queue (
        .clk(clk),
        .rst_n(rst_n),

        .pushed_element(pushed_flit),
        .pushed_valid(pushed_flit_valid),
        .pushed_ready(pushed_flit_ready),

        .poped_ready(poped_flit_ready),
        .poped_valid(poped_flit_valid),
        .poped_element(poped_flit)
    );
endmodule

