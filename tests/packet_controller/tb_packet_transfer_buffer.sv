`include "types.svh"
`include "packet_types.svh"

// 完了したパケットの送信を担当する
// module packet_transfer_buffer (
//     input logic nocclk,
//     input logic rst_n,
//
//     input packet_types::packet_element_t transfered_packet,
//     input logic transfered_packet_valid,
//     // 転送が完了したら、indexをfreeするために使う
//     // 1clkで消費される
//     output logic transfered_packet_completed,
//
//     input logic transfered_flit_ready,
//     output logic transfered_flit_valid,
//     output types::flit_t transfered_flit,
//     output types::flit_t transfered_head_flit
//
// );
module tb_packet_transfer_buffer;

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
