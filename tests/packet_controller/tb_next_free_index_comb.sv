// module next_free_index_comb #(
//     parameter int NUM_ENTRIES = 8
// ) (
//     input logic [NUM_ENTRIES-1:0] free_index_bitmap,
//
//     output logic next_free_index_valid,
//     output logic [$clog2(NUM_ENTRIES)-1:0] next_free_index
// );
`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_next_free_index_comb;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    logic input_template;

    // output
    logic output_template;
    logic output_not_template;
    assign output_template = input_template;
    assign output_not_template = ~input_template;

    // expected
    logic expected_template;

`define LOCAL_TEST(__unused_args) \
@(posedge clk); \
`TEST_EXPECTED(expected_template, output_template, "output_template"); \
`TEST_UNEXPECTED(expected_template, output_not_template, "output_not_template"); \
#1;

    initial begin
        `TEST_START("tb_next_free_index_comb.log")
        $dumpfile("tb_next_free_index_comb.vcd");
        $dumpvars(0, tb_next_free_index_comb);
        @(posedge clk);
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;

        input_template = 1;
        expected_template = 1;
        `LOCAL_TEST

        repeat (10) @(posedge clk);

        `TEST_RESULT
        $finish(0);
    end

endmodule
