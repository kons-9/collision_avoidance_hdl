`include "types.svh"
module tb_flit_queue ();

  timeunit 10ps; timeprecision 10ps;
  import types::flit_t;

  // generate clk
  bit clk = 0;
  always begin
    #5 clk = ~clk;
  end

  // input
  types::flit_t flit_in;

  // output
  types::checksum_t checksum;
  logic is_valid;
  types::flit_t flit_out;
  // instantiate DUT
  calculate_checksum_comb calculate_checksum_comb (
      .flit_in (flit_in),
      .checksum(checksum),
      .is_valid(is_valid),
      .flit_out(flit_out)
  );

  // expected
  types::checksum_t expected_checksum;
  bit expected_is_valid;

  initial begin
    // flit_in is complete flit(is_valid == true)
    @(posedge clk);
    flit_in.header.version = 0;
    flit_in.header.flittype = types::NOPE;
    flit_in.header.src_id = 0;
    flit_in.header.dst_id = 0;
    flit_in.header.flit_id.packet_id = 0;
    flit_in.header.flit_id.flit_num = 0;
    flit_in.payload.nope = 0;
    flit_in.checksum = 8'h00;

    expected_checksum = 8'h00;
    expected_is_valid = 1;


    // flit_in is not complete flit
    // @(posedge clk);
    // flit_in = '{2'h0, 4'h0, 4'h0, 8'h02};
    // expected_checksum = 8'h0;
    // expected_is_valid = 0;
    repeat (10) @(posedge clk);

    $finish;
  end

  // assertion
  // always@(*) begin
  //   assert (flit_out.checksum == checksum)
  //   else $display("flit_out.checksum != checksum");
  //
  //   assert (flit_out.header == flit_in.header)
  //   else $display("flit_out.header != flit_in.header");
  //
  //   assert (flit_out.payload == flit_in.payload)
  //   else $display("flit_out.payload != flit_in.payload");
  //
  //   assert (checksum == expected_checksum)
  //   else $display("checksum != expected_checksum");
  //
  //   assert (is_valid == expected_is_valid)
  //   else $display("is_valid != expected_is_valid");
  // end

endmodule
