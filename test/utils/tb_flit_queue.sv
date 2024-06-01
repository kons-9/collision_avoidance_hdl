`include "types.svh"
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
  function automatic void test_expected(logic expected_pushed_flit_ready,
                                        logic expected_poped_flit_valid,
                                        types::flit_t expected_flit, int line, string file);
    assert (pushed_flit_ready == expected_pushed_flit_ready)
    else
      $display("Error: pushed_flit_ready = %0d(file:%0s line:%0d)", pushed_flit_ready, file, line);
    assert (poped_flit_valid == expected_poped_flit_valid)
    else $display("Error: poped_flit_valid = %0d(file:%0s line:%0d)", poped_flit_valid, file, line);
    if (poped_flit_valid) begin
      assert (poped_flit == expected_flit)
      else $display("Error: poped_flit = %0h(file:%0s line:%0d)", poped_flit, file, line);
    end
  endfunction

  logic null_flit = 0;
  types::flit_t expected_flit = 0;
  logic expected_pushed_flit_ready;
  logic expected_poped_flit_valid;

  initial begin
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
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // pop flit
    poped_flit_ready = 1;
    pushed_flit_valid = 0;
    @(posedge clk);
    expected_pushed_flit_ready = 1;
    expected_poped_flit_valid = 0;
    expected_flit = null_flit;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // nothing
    poped_flit_ready  = 0;
    pushed_flit_valid = 0;
    @(posedge clk);
    expected_pushed_flit_ready = 1;
    expected_poped_flit_valid = 0;
    expected_flit = null_flit;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // multiple push
    pushed_flit.header.src_id = 8'h02;
    pushed_flit_valid = 1;
    poped_flit_ready = 0;
    @(posedge clk);
    expected_flit = pushed_flit;
    expected_pushed_flit_ready = 1;
    expected_poped_flit_valid = 1;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    pushed_flit.header.src_id = 8'h03;
    @(posedge clk);
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    pushed_flit.header.src_id = 8'h04;
    @(posedge clk);
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);
    test_expected(1, 1, expected_flit, `__LINE__, `__FILE__);

    pushed_flit_valid = 0;
    @(posedge clk);
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // multiple pop
    poped_flit_ready = 1;
    pushed_flit_valid = 0;
    @(posedge clk);
    expected_flit.header.src_id = 8'h03;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    @(posedge clk);
    expected_flit.header.src_id = 8'h04;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // push and pop
    poped_flit_ready = 1;
    pushed_flit_valid = 1;
    pushed_flit.header.src_id = 8'h05;
    @(posedge clk);
    expected_flit.header.src_id = 8'h05;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    // pop last flit
    pushed_flit_valid = 0;
    poped_flit_ready  = 1;
    @(posedge clk);
    expected_pushed_flit_ready = 1;
    expected_poped_flit_valid = 0;
    expected_flit = null_flit;
    test_expected(expected_pushed_flit_ready, expected_poped_flit_valid, expected_flit, `__LINE__,
                  `__FILE__);

    repeat (10) @(posedge clk);

    $finish;
  end

endmodule
