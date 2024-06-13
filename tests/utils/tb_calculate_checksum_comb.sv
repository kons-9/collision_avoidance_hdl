`include "types.svh"
`include "test_utils.svh"

module tb_calculate_checksum_comb ();

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
        `TEST_START("tb_calculate_checksum_comb.log")
        $dumpfile("tb_calculate_checksum_comb.vcd");
        $dumpvars(0, tb_calculate_checksum_comb);
        // flit_in is complete flit(is_valid == true)
        @(posedge clk);
        flit_in.header.version = 0;
        flit_in.header.is_ack = 0;
        flit_in.header.flittype = types::HEAD;
        flit_in.header.src_id = 0;
        flit_in.header.dst_id = 0;
        flit_in.header.flit_id.packet_id = 0;
        flit_in.header.flit_id.flit_num = 0;
        flit_in.payload.head = 0;
        flit_in.checksum = 8'h00;
        expected_checksum = 8'h00;
        expected_is_valid = 1;
        #1;
        `TEST_EXPECTED(expected_checksum, checksum, "checksum");
        `TEST_EXPECTED(expected_is_valid, is_valid, "is_valid");
        `TEST_EXPECTED(flit_in.header, flit_out.header, "flit_out");
        `TEST_EXPECTED(flit_in.payload, flit_out.payload, "flit_out");
        `TEST_EXPECTED(flit_in.checksum, flit_out.checksum, "flit_out");

        repeat (10) @(posedge clk);

        `TEST_RESULT
        $finish;
    end


endmodule
