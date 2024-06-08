`include "types.svh"
`include "test_utils.svh"

import types::*;

module tb_flit_queue ();

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    types::flit_t pushed_flit = 0;
    logic pushed_flit_valid = 0;
    logic poped_flit_ready = 0;

    // output
    logic pushed_flit_ready;
    logic poped_flit_valid;
    types::flit_t poped_flit;

    flit_queue flit_queue (
        .clk(clk),
        .rst_n(rst_n),
        .pushed_flit(pushed_flit),
        .pushed_flit_valid(pushed_flit_valid),
        .pushed_flit_ready(pushed_flit_ready),
        .poped_flit_ready(poped_flit_ready),
        .poped_flit_valid(poped_flit_valid),
        .poped_flit(poped_flit)
    );

    // expected
    logic null_flit = 0;
    types::flit_t expected_flit = 0;
    logic expected_pushed_flit_ready;
    logic expected_poped_flit_valid;


    task automatic __local_test(int line, string file);
        `TEST_EXPECTED(expected_pushed_flit_ready, pushed_flit_ready, "pushed_flit_ready", file,
                       line);
        `TEST_EXPECTED(expected_poped_flit_valid, poped_flit_valid, "poped_flit_valid", file, line);
        if (poped_flit_valid) begin
            `TEST_EXPECTED(expected_flit, poped_flit, "poped_flit", file, line);
        end
    endtask

    `define LOCAL_TEST(line=`__LINE__, file=`__FILE__) \
        __local_test(line, file);

    initial begin
        `TEST_START("tb_flit_queue.log")
        $dumpfile("tb_flit_queue.vcd");
        $dumpvars(0, tb_flit_queue);
        // flit_in is complete flit(is_valid == true)
        @(posedge clk);
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;

        // push flit
        pushed_flit.header.src_id = 8'h01;
        pushed_flit_valid = 1;

        @(posedge clk);
        expected_flit = pushed_flit;
        expected_pushed_flit_ready = 1;
        expected_poped_flit_valid = 1;
        `LOCAL_TEST();

        // pop flit
        poped_flit_ready  = 1;
        pushed_flit_valid = 0;
        @(posedge clk);
        expected_pushed_flit_ready = 1;
        expected_poped_flit_valid = 0;
        expected_flit = null_flit;
        `LOCAL_TEST();

        // nothing
        poped_flit_ready  = 0;
        pushed_flit_valid = 0;
        @(posedge clk);
        expected_pushed_flit_ready = 1;
        expected_poped_flit_valid = 0;
        expected_flit = null_flit;
        `LOCAL_TEST();

        // multiple push
        pushed_flit.header.src_id = 8'h02;
        pushed_flit_valid = 1;
        poped_flit_ready = 0;
        @(posedge clk);
        expected_flit = pushed_flit;
        expected_pushed_flit_ready = 1;
        expected_poped_flit_valid = 1;
        `LOCAL_TEST();

        pushed_flit.header.src_id = 8'h03;
        @(posedge clk);
        `LOCAL_TEST();

        pushed_flit.header.src_id = 8'h04;
        @(posedge clk);
        `LOCAL_TEST();

        pushed_flit_valid = 0;
        @(posedge clk);
        `LOCAL_TEST();

        // multiple pop
        poped_flit_ready  = 1;
        pushed_flit_valid = 0;
        @(posedge clk);
        expected_flit.header.src_id = 8'h03;
        `LOCAL_TEST();

        @(posedge clk);
        expected_flit.header.src_id = 8'h04;
        `LOCAL_TEST();

        // push and pop
        poped_flit_ready = 1;
        pushed_flit_valid = 1;
        pushed_flit.header.src_id = 8'h05;
        @(posedge clk);
        expected_flit.header.src_id = 8'h05;
        `LOCAL_TEST();

        // pop last flit
        pushed_flit_valid = 0;
        poped_flit_ready  = 1;
        @(posedge clk);
        expected_pushed_flit_ready = 1;
        expected_poped_flit_valid = 0;
        expected_flit = null_flit;
        `LOCAL_TEST();

        repeat (10) @(posedge clk);

        `TEST_RESULT

        $finish(0);
    end

endmodule
