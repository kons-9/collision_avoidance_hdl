`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_system_flit_comb;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    packet_types::routing_table_t routing_table;
    types::node_id_t random_id;
    types::node_id_t temporal_id;
    logic is_flit_from_cpu;
    types::flit_t flit_in;
    logic is_root;
    node_id_t routing_id_counter;

    // output
    logic system_flit_valid;
    types::flit_t flit_out;
    logic is_system_flit_self;
    logic update_parent_valid;
    types::node_id_t update_parent_node_id;
    logic update_this_node_valid;
    types::node_id_t update_this_node_id;
    logic update_routing_table_valid;
    types::node_id_t update_routing_table_key;
    types::node_id_t update_routing_table_value;
    logic update_routing_id_counter_valid;

    system_flit_comb system_flit_comb (.*);

    // expected
    logic expected_system_flit_valid;
    types::flit_t expected_flit_out;
    logic expected_is_system_flit_self;
    logic expected_update_parent_valid;
    types::node_id_t expected_update_parent_node_id;
    logic expected_update_this_node_valid;
    types::node_id_t expected_update_this_node_id;
    logic expected_update_routing_table_valid;
    types::node_id_t expected_update_routing_table_key;
    types::node_id_t expected_update_routing_table_value;
    logic expected_update_routing_id_counter_valid;

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        #1;
        `TEST_EXPECTED(expected_system_flit_valid, system_flit_valid, "system_flit_valid", file, line);
        if (expected_system_flit_valid & system_flit_valid) begin
            `TEST_EXPECTED(expected_flit_out, flit_out, "flit_out", file, line);
            `TEST_EXPECTED(expected_is_system_flit_self, is_system_flit_self, "is_system_flit_self", file, line);
            `TEST_EXPECTED(expected_update_parent_valid, update_parent_valid, "update_parent_valid", file, line);
            if (expected_update_parent_valid & update_parent_valid) begin
                `TEST_EXPECTED(expected_update_parent_node_id, update_parent_node_id, "update_parent_node_id", file, line);
            end
            `TEST_EXPECTED(expected_update_this_node_valid, update_this_node_valid, "update_this_node_valid", file, line);
            if (expected_update_this_node_valid & update_this_node_valid) begin
                `TEST_EXPECTED(expected_update_this_node_id, update_this_node_id, "update_this_node_id", file, line);
            end
            `TEST_EXPECTED(expected_update_routing_table_valid, update_routing_table_valid, "update_routing_table_valid", file, line);
            if (expected_update_routing_table_valid & update_routing_table_valid) begin
                `TEST_EXPECTED(expected_update_routing_table_key, update_routing_table_key, "update_routing_table_key", file, line);
                `TEST_EXPECTED(expected_update_routing_table_value, update_routing_table_value, "update_routing_table_value", file, line);
            end
            `TEST_EXPECTED(expected_update_routing_id_counter_valid, update_routing_id_counter_valid, "update_routing_id_counter_valid", file, line);
        end
    endtask

    initial begin
        `TEST_START("tb_system_flit_comb.log")
        $dumpfile("tb_system_flit_comb.vcd");
        $dumpvars(0, tb_system_flit_comb);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        `LOCAL_TEST();

        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
