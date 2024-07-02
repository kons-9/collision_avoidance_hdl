`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_router;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    types::node_id_t incomin_flit_node_id;
    logic incoming_flit_valid;
    types::flit_t transfered_flit;
    logic transfered_flit_valid;
    types::flit_t transfered_head_flit;
    logic is_from_cpu;
    logic noc_to_cpu_pushed_flit_ready;
    logic forwarded_flit_ready;

    // output
    logic transfered_flit_ready;
    types::flit_t noc_to_cpu_pushed_flit;
    logic noc_to_cpu_pushed_flit_valid;
    types::flit_t forwarded_flit;
    logic forwarded_flit_valid;
    types::node_id_t this_node_id;

    router #(
        .IS_ROOT(0),
        .MAX_INTERNAL_TIMER(100)
    ) router_inst (
        .nocclk(clk),
        .rst_n(rst_n),
        .incoming_flit_node_id(incomin_flit_node_id),
        .incoming_flit_valid(incoming_flit_valid),
        .transfered_flit(transfered_flit),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_head_flit(transfered_head_flit),
        .is_from_cpu(is_from_cpu),
        .noc_to_cpu_pushed_flit_ready(noc_to_cpu_pushed_flit_ready),
        .forwarded_flit_ready(forwarded_flit_ready),
        .transfered_flit_ready(transfered_flit_ready),
        .noc_to_cpu_pushed_flit(noc_to_cpu_pushed_flit),
        .noc_to_cpu_pushed_flit_valid(noc_to_cpu_pushed_flit_valid),
        .forwarded_flit(forwarded_flit),
        .forwarded_flit_valid(forwarded_flit_valid),
        .this_node_id(this_node_id)
    );

    // expected
    logic expected_transfered_flit_ready;
    types::flit_t expected_noc_to_cpu_pushed_flit;
    logic expected_noc_to_cpu_pushed_flit_valid;
    types::flit_t expected_forwarded_flit;
    logic expected_forwarded_flit_valid;
    types::node_id_t expected_this_node_id;

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        #1;
        `TEST_EXPECTED(expected_transfered_flit_ready, transfered_flit_ready, "transfered_flit_ready", file, line);

        `TEST_EXPECTED(expected_noc_to_cpu_pushed_flit_valid, noc_to_cpu_pushed_flit_valid, "noc_to_cpu_pushed_flit_valid", file, line);
        if (expected_noc_to_cpu_pushed_flit_valid & noc_to_cpu_pushed_flit_valid) begin
            `TEST_EXPECTED(expected_noc_to_cpu_pushed_flit, noc_to_cpu_pushed_flit, "noc_to_cpu_pushed_flit", file, line);
        end
        `TEST_EXPECTED(expected_forwarded_flit_valid, forwarded_flit_valid, "forwarded_flit_valid", file, line);
        if (expected_forwarded_flit_valid & forwarded_flit_valid) begin
            `TEST_EXPECTED(expected_forwarded_flit, forwarded_flit, "forwarded_flit", file, line);
        end
        `TEST_EXPECTED(expected_this_node_id, this_node_id, "this_node_id", file, line);
    endtask

    initial begin
        `TEST_START("tb_router.log")
        $dumpfile("tb_router.vcd");
        $dumpvars(0, tb_router);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        repeat (10) wait_1clk();


        `TEST_RESULT();
        $finish(0);
    end

endmodule
