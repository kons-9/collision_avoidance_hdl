`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_make_ack_comb;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    types::flit_t flit_in;

    // output
    types::flit_t flit_out;

    make_ack_comb make_ack_comb (
        .flit_in (flit_in),
        .flit_out(flit_out)
    );

    // expected
    types::flit_t expected_flit_out;


    `define LOCAL_TEST(__unused_args) \
    @(posedge clk); \
    `TEST_EXPECTED(expected_flit_out, flit_out, "flit_out"); \
    #1

    initial begin
        `TEST_START("tb_make_ack_comb.log")
        $dumpfile("tb_make_ack_comb.vcd");
        $dumpvars(0, tb_make_ack_comb);
        @(posedge clk);
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;

        flit_in = 0;
        expected_flit_out = 0;
        expected_flit_out.header.is_ack = 1;
        `LOCAL_TEST
        flit_in.header.src_id = 1;
        expected_flit_out.header.dst_id = 1;
        `LOCAL_TEST
        flit_in.header.dst_id = 2;
        expected_flit_out.header.src_id = 2;
        `LOCAL_TEST

        repeat (10) @(posedge clk);

        `TEST_RESULT
        $finish(0);
    end

endmodule
