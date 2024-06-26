`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_uart_clk;

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
        `TEST_START("tb_uart_clk.log")
        $dumpfile("tb_uart_clk.vcd");
        $dumpvars(0, tb_uart_clk);
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
