`include "types.svh"
`include "test_utils.svh"

import types::*;

module tb_template ();

  timeunit 10ps; timeprecision 10ps;

  // generate clk
  bit clk = 0;
  bit rst_n = 1;
  always begin
    #5 clk = ~clk;
  end

  // input
  logic input_tmplate;

  // output
  logic output_template;
  logic output_not_template;
  assign output_template = input_tmplate;
  assign output_not_template = ~input_tmplate;

  // expected
  logic expected_template;

  initial begin
    `TEST_START("tb_template.log")
    $dumpfile("tb_template.vcd");
    $dumpvars(0, tb_template);
    @(posedge clk);
    rst_n = 0;
    @(posedge clk);
    rst_n = 1;

    input_tmplate = 1;
    expected_template = 1;
    `TEST_EXPECTED(expected_template, output_template, "output_template");
    `TEST_UNEXPECTED(expected_template, output_not_template, "output_not_template");

    repeat (10) @(posedge clk);

    `TEST_RESULT
    $finish(0);
  end

endmodule
