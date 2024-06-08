// module packet_controller (
//     input logic nocclk,
//     input logic rst_n,
//
//     input types::flit_t next_flit,
//     input logic next_flit_valid,
//     output logic next_flit_ready,
//
//     input logic noc_to_cpu_pushed_flit_ready,
//     output logic noc_to_cpu_pushed_flit_valid,
//     output types::flit_t noc_to_cpu_pushed_flit,
//
//     input logic forwarded_flit_ready,
//     output logic forwarded_flit_valid,
//     output types::flit_t forwarded_flit
// );
`include "types.svh"
`include "test_utils.svh"

import types::*;

module tb_packet_controller;

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
    #1

    initial begin
        `TEST_START("tb_template.log")
        $dumpfile("tb_template.vcd");
        $dumpvars(0, tb_template);
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
