`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_TEMPLATE;

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

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        @(posedge clk);
        `TEST_EXPECTED(expected_template, output_template, "output_template", file, line);
        `TEST_UNEXPECTED(expected_template, output_not_template, "output_not_template", file, line);
        #1;
    endtask

    initial begin
        `TEST_START("tb_TEMPLATE.log")
        $dumpfile("tb_TEMPLATE.vcd");
        $dumpvars(0, tb_TEMPLATE);
        @(posedge clk);
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;

        input_template = 1;
        expected_template = 1;
        `LOCAL_TEST();

        repeat (10) @(posedge clk);

        `TEST_RESULT
        $finish(0);
    end

endmodule
