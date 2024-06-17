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
`define NUM_ENTRIES 8

module tb_next_free_index_comb;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    logic [7:0] free_index_bitmap;

    // output
    logic next_free_index_valid;
    logic [$clog2(`NUM_ENTRIES)-1:0] next_free_index;

    next_free_index_comb #(
        .NUM_ENTRIES(`NUM_ENTRIES)
    ) next_free_index_comb (
        .free_index_bitmap(free_index_bitmap),
        .next_free_index_valid(next_free_index_valid),
        .next_free_index(next_free_index)
    );

    // expected
    logic expected_valid;
    logic [$clog2(`NUM_ENTRIES)-1:0] expected_index;

    int counter = 0;

    task automatic LOCAL_TEST(string file , int line);
        $display("counter = %0d", counter);
        counter++;
        @(posedge clk);
        `TEST_EXPECTED(expected_valid, next_free_index_valid, "next_free_index_valid", file, line);
        if (expected_valid) begin
            `TEST_EXPECTED(expected_index, next_free_index, "next_free_index", file, line);
        end
        #1;
    endtask

    initial begin
        `TEST_START("tb_next_free_index_comb.log")
        $dumpfile("tb_next_free_index_comb.vcd");
        $dumpvars(0, tb_next_free_index_comb);
        @(posedge clk);
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;

        free_index_bitmap = 8'b00000001;
        expected_valid = 1;
        expected_index = 0;
        LOCAL_TEST(`__FILE__, `__LINE__);

        free_index_bitmap = 8'b00000010;
        expected_valid = 1;
        expected_index = 1;
        LOCAL_TEST(`__FILE__, `__LINE__);

        free_index_bitmap = 8'b00000011;
        expected_valid = 1;
        expected_index = 1;
        LOCAL_TEST(`__FILE__, `__LINE__);

        free_index_bitmap = 8'b00000000;
        expected_valid = 0;
        LOCAL_TEST(`__FILE__, `__LINE__);

        repeat (10) @(posedge clk);

        `TEST_RESULT
        $finish(0);
    end

endmodule
