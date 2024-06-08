`include "types.svh"
`include "packet_types.svh"

// module packet_buffer #(
//     parameter int PACKET_BUFFER_NUM_ENTRIES = 8,
//     parameter int MAX_NUM_OF_FLIT = 8,
//     parameter int EXPIRE_TIME = 100
// ) (
//     input logic nocclk,
//     input logic rst_n,
//
//     input types::flit_t next_flit,
//     input logic next_flit_valid,
//     output logic next_flit_ready,
//
//     input logic transfered_packet_completed,
//     output packet_types::packet_element_t transfered_packet,
//     output logic transfered_packet_valid
// );
`include "types.svh"
`include "test_utils.svh"

import types::*;

module tb_packet_buffer;

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
