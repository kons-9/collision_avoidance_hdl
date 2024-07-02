`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_heartbeat_requester;

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

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        #1;
        `TEST_EXPECTED(expected_template, output_template, "output_template", file, line);
        `TEST_UNEXPECTED(expected_template, output_not_template, "output_not_template", file, line);
    endtask

    initial begin
        `TEST_START("tb_heartbeat_requester.log")
        $dumpfile("tb_heartbeat_requester.vcd");
        $dumpvars(0, tb_heartbeat_requester);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        input_template = 1;
        expected_template = 1;
        `LOCAL_TEST();

        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
