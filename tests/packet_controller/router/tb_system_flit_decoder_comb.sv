`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_system_flit_decoder_comb;

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
    system_types::routing_state_t in_routing_state;
    types::node_id_t in_this_node_id;
    parameter int MAX_INTERNAL_TIMER = 1000;
    logic [$clog2(MAX_INTERNAL_TIMER):0] internal_timer;

    // output
    logic timer_rst;
    logic out_is_system_flit;
    logic out_is_init;
    logic out_is_join_ack_parent;
    system_types::system_header_t out_system_header;
    system_types::system_payload_t out_system_payload;
    logic out_update_parent_valid;
    types::node_id_t out_update_parent_node_id;
    logic out_update_this_node_valid;
    types::node_id_t out_update_this_node_id;
    logic out_update_neighbor_id_valid;
    types::node_id_t out_update_neighbor_id;
    logic out_update_routing_table_valid;
    types::node_id_t out_update_routing_table_key;
    logic out_is_raw_global_destination_used_to_update_routing_table;
    logic out_update_next_state;
    system_types::routing_state_t out_next_routing_state;

    system_flit_decoder_comb #(
        .MAX_INTERNAL_TIMER(MAX_INTERNAL_TIMER),
        .IS_ROOT(0)
    ) system_flit_decoder_comb_inst (
        .nocclk(clk),
        .rst_n (rst_n),

        .flit_in(in_flit),
        .flit_valid(in_flit_valid),
        .routing_state(in_routing_state),
        .this_node_id(in_this_node_id),
        .internal_timer(internal_timer),

        .timer_rst(timer_rst),
        .is_system_flit(out_is_system_flit),
        .is_init(out_is_init),
        .is_join_ack_parent(out_is_join_ack_parent),
        .system_header(out_system_header),
        .system_payload(out_system_payload),
        .update_parent_valid(out_update_parent_valid),
        .update_parent_node_id(out_update_parent_node_id),
        .update_this_node_valid(out_update_this_node_valid),
        .update_this_node_id(out_update_this_node_id),
        .update_neighbor_id_valid(out_update_neighbor_id_valid),
        .update_neighbor_id(out_update_neighbor_id),
        .update_routing_table_valid(out_update_routing_table_valid),
        .update_routing_table_key(out_update_routing_table_key),
        .is_raw_global_destination_used_to_update_routing_table(out_is_raw_global_destination_used_to_update_routing_table),
        .update_next_state(out_update_next_state),
        .next_routing_state(out_next_routing_state),
        .global_destination_id(system_global_destination)
    );

    // expected
    logic expected_timer_rst;
    logic expected_out_is_system_flit;
    logic expected_out_is_init;
    logic expected_out_is_join_ack_parent;
    system_types::system_header_t expected_out_system_header;
    system_types::system_payload_t expected_out_system_payload;
    logic expected_out_update_parent_valid;
    types::node_id_t expected_out_update_parent_node_id;
    logic expected_out_update_this_node_valid;
    types::node_id_t expected_out_update_this_node_id;
    logic expected_out_update_neighbor_id_valid;
    types::node_id_t expected_out_update_neighbor_id;
    logic expected_out_update_routing_table_valid;
    types::node_id_t expected_out_update_routing_table_key;
    logic expected_out_is_raw_global_destination_used_to_update_routing_table;
    logic expected_out_update_next_state;
    system_types::routing_state_t expected_out_next_routing_state;
    types::node_id_t expected_global_destination_id;

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        #1;
        `TEST_EXPECTED(expected_out_is_system_flit, out_is_system_flit, "out_is_system_flit", file, line);
        if (expected_out_is_system_flit && out_is_system_flit) begin
            `TEST_EXPECTED(expected_timer_rst, timer_rst, "timer_rst", file, line);
            `TEST_EXPECTED(expected_out_is_init, out_is_init, "out_is_init", file, line);
            `TEST_EXPECTED(expected_out_is_join_ack_parent, out_is_join_ack_parent, "out_is_join_ack_parent", file, line);
            `TEST_EXPECTED(expected_out_system_header, out_system_header, "out_system_header", file, line);
            `TEST_EXPECTED(expected_out_system_payload, out_system_payload, "out_system_payload", file, line);

            `TEST_EXPECTED(expected_out_update_parent_valid, out_update_parent_valid, "out_update_parent_valid", file, line);
            if (expected_out_update_parent_valid && out_update_parent_valid) begin
                `TEST_EXPECTED(expected_out_update_parent_node_id, out_update_parent_node_id, "out_update_parent_node_id", file, line);
            end
            `TEST_EXPECTED(expected_out_update_this_node_valid, out_update_this_node_valid, "out_update_this_node_valid", file, line);
            if (expected_out_update_this_node_valid && out_update_this_node_valid) begin
                `TEST_EXPECTED(expected_out_update_this_node_id, out_update_this_node_id, "out_update_this_node_id", file, line);
            end
            `TEST_EXPECTED(expected_out_update_neighbor_id_valid, out_update_neighbor_id_valid, "out_update_neighbor_id_valid", file, line);
            if (expected_out_update_neighbor_id_valid && out_update_neighbor_id_valid) begin
                `TEST_EXPECTED(expected_out_update_neighbor_id, out_update_neighbor_id, "out_update_neighbor_id", file, line);
            end
            `TEST_EXPECTED(expected_out_update_routing_table_valid, out_update_routing_table_valid, "out_update_routing_table_valid", file, line);
            if (expected_out_update_routing_table_valid && out_update_routing_table_valid) begin
                `TEST_EXPECTED(expected_out_update_routing_table_key, out_update_routing_table_key, "out_update_routing_table_key", file, line);
                `TEST_EXPECTED(expected_out_is_raw_global_destination_used_to_update_routing_table, out_is_raw_global_destination_used_to_update_routing_table,
                               "out_is_raw_global_destination_used_to_update_routing_table", file, line);
            end
            `TEST_EXPECTED(expected_out_update_next_state, out_update_next_state, "out_update_next_state", file, line);
            if (expected_out_update_next_state && out_update_next_state) begin
                `TEST_EXPECTED(expected_out_next_routing_state, out_next_routing_state, "out_next_routing_state", file, line);
            end
            `TEST_EXPECTED(expected_global_destination_id, system_global_destination, "system_global_destination", file, line);
        end
    endtask

    task automatic default_expected();
        expected_out_is_system_flit = 0;
        expected_timer_rst = 0;
        expected_out_is_init = 0;
        expected_out_is_join_ack_parent = 0;
        expected_out_system_header = system_types::S_NOPE;
        expected_out_system_payload = 0;
        expected_out_update_parent_valid = 0;
        expected_out_update_parent_node_id = 0;
        expected_out_update_this_node_valid = 0;
        expected_out_update_this_node_id = 0;
        expected_out_update_neighbor_id_valid = 0;
        expected_out_update_neighbor_id = 0;
        expected_out_update_routing_table_valid = 0;
        expected_out_update_routing_table_key = 0;
        expected_out_is_raw_global_destination_used_to_update_routing_table = 0;
        expected_out_update_next_state = 0;
        expected_out_next_routing_state = system_types::FATAL_ERROR;
        expected_global_destination_id = 0;
    endtask

    initial begin
        `TEST_START("tb_system_flit_decoder_comb.log")
        $dumpfile("tb_system_flit_decoder_comb.vcd");
        $dumpvars(0, tb_system_flit_decoder_comb);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        in_flit = 0;
        in_flit_valid = 0;
        in_routing_state = system_types::INIT;
        in_this_node_id = 1;
        internal_timer = 100;

        expected_out_is_system_flit = 0;
        `LOCAL_TEST();

        // parent_request
        in_flit.header.flittype = types::SYSTEM;
        in_flit.header.src_id = 0;
        in_flit.header.dst_id = in_this_node_id;
        in_flit.payload.system.header = system_types::S_PARENT_REQUEST;
        in_flit.payload.system.payload.parent_request.is_init = 1;
        in_flit_valid = 1;
        in_routing_state = system_types::NORMAL;

        default_expected();
        expected_out_is_system_flit = 1;
        expected_out_system_header = system_types::S_PARENT_REQUEST;
        expected_out_system_payload = in_flit.payload.system.payload;
        expected_global_destination_id = in_flit.header.src_id;
        expected_timer_rst = 0;
        expected_out_is_init = 1;
        expected_out_update_next_state = 0;
        `LOCAL_TEST();

        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
