`include "types.svh"
`include "test_utils.svh"

import types::*;

module tb_receive_controller_comb ();

  timeunit 10ps; timeprecision 10ps;

  // generate clk
  bit clk = 0;
  bit rst_n = 1;
  always begin
    #5 clk = ~clk;
  end

  // input
  types::flit_t in_flit;
  logic in_flit_valid;
  logic ack_buffer_ready;
  logic packet_buffer_ready;

  // output
  logic received_flit_ready;
  logic ack_buffer_valid;
  logic packet_buffer_valid;
  logic waiting_ack_buffer_valid;

  receive_controller_comb receive_controller_comb1 (
      .received_flit(in_flit),
      .received_flit_valid(in_flit_valid),
      .received_flit_ready(received_flit_ready),
      .ack_buffer_ready(ack_buffer_ready),
      .ack_buffer_valid(ack_buffer_valid),
      .packet_buffer_ready(packet_buffer_ready),
      .packet_buffer_valid(packet_buffer_valid),
      .waiting_ack_buffer_valid(waiting_ack_buffer_valid)
  );

  // expected
  logic expected_received_flit_ready;
  logic expected_ack_buffer_valid;
  logic expected_packet_buffer_valid;
  logic expected_waiting_ack_buffer_valid;

  `define ASSERT_EXPECTED(__unused_args) \
    @(posedge clk); \
    `TEST_EXPECTED(expected_received_flit_ready, received_flit_ready, "received_flit_ready"); \
    `TEST_EXPECTED(expected_ack_buffer_valid, ack_buffer_valid, "ack_buffer_valid"); \
    `TEST_EXPECTED(expected_packet_buffer_valid, packet_buffer_valid, "packet_buffer_valid"); \
    `TEST_EXPECTED(expected_waiting_ack_buffer_valid, waiting_ack_buffer_valid, "waiting_ack_buffer_valid"); \
    #1;


  initial begin
    `TEST_START("tb_receive_controller_comb.log")
    $dumpfile("tb_receive_controller_comb.vcd");
    $dumpvars(0, tb_receive_controller_comb);
    @(posedge clk);
    rst_n = 0;
    @(posedge clk);
    rst_n = 1;

    // begin
    in_flit = 0;
    in_flit.header.is_ack = 0;
    in_flit_valid = 1;
    ack_buffer_ready = 1;
    packet_buffer_ready = 1;

    expected_received_flit_ready = 1;
    expected_ack_buffer_valid = 1;
    expected_packet_buffer_valid = 1;
    expected_waiting_ack_buffer_valid = 0;
    `ASSERT_EXPECTED;
    // end


    // begin
    in_flit.header.is_ack = 1;
    in_flit_valid = 1;
    ack_buffer_ready = 1;
    packet_buffer_ready = 0;

    expected_received_flit_ready = 1;
    expected_ack_buffer_valid = 0;
    expected_packet_buffer_valid = 0;
    expected_waiting_ack_buffer_valid = 1;

    `ASSERT_EXPECTED;
    // end

    // begin
    in_flit.header.is_ack = 0;
    in_flit_valid = 1;
    ack_buffer_ready = 0;
    packet_buffer_ready = 1;

    expected_received_flit_ready = 0;
    expected_ack_buffer_valid = 0;
    expected_packet_buffer_valid = 0;
    expected_waiting_ack_buffer_valid = 0;

    `ASSERT_EXPECTED;
    // end

    // begin
    in_flit.header.is_ack = 0;
    in_flit_valid = 1;
    ack_buffer_ready = 1;
    packet_buffer_ready = 0;

    expected_received_flit_ready = 0;
    expected_ack_buffer_valid = 0;
    expected_packet_buffer_valid = 0;
    expected_waiting_ack_buffer_valid = 0;

    `ASSERT_EXPECTED;
    // end

    // begin
    in_flit.header.is_ack = 1;
    in_flit_valid = 0;

    expected_received_flit_ready = 0;
    expected_ack_buffer_valid = 0;
    expected_packet_buffer_valid = 0;
    expected_waiting_ack_buffer_valid = 0;

    `ASSERT_EXPECTED;
    // end

    repeat (10) @(posedge clk);

    `TEST_RESULT
    $finish(0);
  end

endmodule
