`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_stage10;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    logic g_routing_state;
    logic g_this_node_id;
    logic g_incoming_flit_node_id;
    types::flit_t stage1_head_flit;
    logic stage1_is_from_cpu;
    logic stage1_flit_valid;
    types::flit_t stage1_flit;
    logic stage1_stall;

    // output
    types::node_id_t stage1_global_destination;
    logic stage1_is_heartbeat_request;
    logic stage1_is_destination_self;
    logic stage1_is_source_self;
    logic stage1_is_system_flit;
    logic stage1_is_init;
    logic stage1_is_join_ack_parent;
    system_types::system_header_t stage1_system_header;
    system_types::system_payload_t stage1_system_payload;
    logic stage1_update_parent_valid;  // used controller
    types::node_id_t stage1_update_parent_node_id;  // used controller
    logic stage1_update_this_node_valid;  // used controller
    types::node_id_t stage1_update_this_node_id;  // used controller
    logic stage1_update_neighbor_id_valid;  // used controller
    types::node_id_t stage1_update_neighbor_id;  // used controller
    logic stage1_update_routing_table_valid;
    types::node_id_t stage1_update_routing_table_key;
    logic stage1_is_raw_global_destination_used_to_update_routing_table;
    logic stage1_update_next_state;
    system_types::routing_state_t stage1_next_routing_state;

    stage10 #(
        .MAX_HEARTBEAT_REQUEST_TIMER(MAX_HEARTBEAT_REQUEST_TIMER),
        .MAX_INTERNAL_TIMER(MAX_INTERNAL_TIMER),
        .IS_ROOT(IS_ROOT)
    ) stage1_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .in_routing_state(g_routing_state),
        .in_stage1_stall(stage1_stall),
        .stage1_ready(stage1_ready),

        .in_this_node_id(g_this_node_id),
        .out_global_destination(stage1_global_destination),

        // heartbeat_requester
        .in_parent_valid(g_routing_table.parent_valid),
        .in_parent_node_id(g_routing_table.parent_node_id),
        .in_incoming_flit_node_id(g_incoming_flit_node_id),
        .out_is_heartbeat_request(stage1_is_heartbeat_request),

        // decode_head_flit_comb
        .in_head_flit(stage1_head_flit),
        .in_is_from_cpu(stage1_is_from_cpu),
        .out_is_destination_self(stage1_is_destination_self),
        .out_is_source_self(stage1_is_source_self),

        // system_flit_decoder_comb
        .in_flit_valid(stage1_flit_valid),
        .in_flit(stage1_flit),
        .out_is_system_flit(stage1_is_system_flit),
        .out_is_init(stage1_is_init),
        .out_is_join_ack_parent(stage1_is_join_ack_parent),
        .out_system_header(stage1_system_header),
        .out_system_payload(stage1_system_payload),
        .out_update_parent_valid(stage1_update_parent_valid),
        .out_update_parent_node_id(stage1_update_parent_node_id),
        .out_update_this_node_valid(stage1_update_this_node_valid),
        .out_update_this_node_id(stage1_update_this_node_id),
        .out_update_neighbor_id_valid(stage1_update_neighbor_id_valid),
        .out_update_neighbor_id(stage1_update_neighbor_id),
        .out_update_routing_table_valid(stage1_update_routing_table_valid),
        .out_update_routing_table_key(stage1_update_routing_table_key),
        .out_is_raw_global_destination_used_to_update_routing_table(stage1_is_raw_global_destination_used_to_update_routing_table),
        .out_update_next_state(stage1_update_next_state),
        .out_next_routing_state(stage1_next_routing_state)
    );

    // expected
    logic expected_global_destination;
    logic expected_is_heartbeat_request;
    logic expected_is_destination_self;
    logic expected_is_source_self;
    logic expected_is_system_flit;
    logic expected_is_init;
    logic expected_is_join_ack_parent;
    system_types::system_header_t expected_system_header;
    system_types::system_payload_t expected_system_payload;
    logic expected_update_parent_valid;  // used controller
    types::node_id_t expected_update_parent_node_id;  // used controller
    logic expected_update_this_node_valid;  // used controller
    types::node_id_t expected_update_this_node_id;  // used controller
    logic expected_update_neighbor_id_valid;  // used controller
    types::node_id_t expected_update_neighbor_id;  // used controller
    logic expected_update_routing_table_valid;
    types::node_id_t expected_update_routing_table_key;
    logic expected_is_raw_global_destination_used_to_update_routing_table;
    logic expected_update_next_state;
    system_types::routing_state_t expected_next_routing_state;

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        #1;
        // `TEST_EXPECTED(expected_template, output_template, "output_template", file, line);
        `TEST_EXPECTED(expected_global_destination, stage1_global_destination, "stage1_global_destination", file, line);
        `TEST_EXPECTED(expected_is_heartbeat_request, stage1_is_heartbeat_request, "stage1_is_heartbeat_request", file, line);
        `TEST_EXPECTED(expected_is_destination_self, stage1_is_destination_self, "stage1_is_destination_self", file, line);
        `TEST_EXPECTED(expected_is_source_self, stage1_is_source_self, "stage1_is_source_self", file, line);
        `TEST_EXPECTED(expected_is_system_flit, stage1_is_system_flit, "stage1_is_system_flit", file, line);
        `TEST_EXPECTED(expected_is_init, stage1_is_init, "stage1_is_init", file, line);
        `TEST_EXPECTED(expected_is_join_ack_parent, stage1_is_join_ack_parent, "stage1_is_join_ack_parent", file, line);
        `TEST_EXPECTED(expected_system_header, stage1_system_header, "stage1_system_header", file, line);
        `TEST_EXPECTED(expected_system_payload, stage1_system_payload, "stage1_system_payload", file, line);
        `TEST_EXPECTED(expected_update_parent_valid, stage1_update_parent_valid, "stage1_update_parent_valid", file, line);
        `TEST_EXPECTED(expected_update_parent_node_id, stage1_update_parent_node_id, "stage1_update_parent_node_id", file, line);
        `TEST_EXPECTED(expected_update_this_node_valid, stage1_update_this_node_valid, "stage1_update_this_node_valid", file, line);
        `TEST_EXPECTED(expected_update_this_node_id, stage1_update_this_node_id, "stage1_update_this_node_id", file, line);
        `TEST_EXPECTED(expected_update_neighbor_id_valid, stage1_update_neighbor_id_valid, "stage1_update_neighbor_id_valid", file, line);
        `TEST_EXPECTED(expected_update_neighbor_id, stage1_update_neighbor_id, "stage1_update_neighbor_id", file, line);
        `TEST_EXPECTED(expected_update_routing_table_valid, stage1_update_routing_table_valid, "stage1_update_routing_table_valid", file, line);
        `TEST_EXPECTED(expected_update_routing_table_key, stage1_update_routing_table_key, "stage1_update_routing_table_key", file, line);
        `TEST_EXPECTED(expected_is_raw_global_destination_used_to_update_routing_table, stage1_is_raw_global_destination_used_to_update_routing_table, "stage1_is_raw_global_destination_used_to_update_routing_table", file, line);
        `TEST_EXPECTED(expected_update_next_state, stage1_update_next_state, "stage1_update_next_state", file, line);
        `TEST_EXPECTED(expected_next_routing_state, stage1_next_routing_state, "stage1_next_routing_state", file, line);
    endtask

    initial begin
        `TEST_START("tb_stage10.log")
        $dumpfile("tb_stage10.vcd");
        $dumpvars(0, tb_stage10);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        input_template = 1;
        expected_template = 1;
        `LOCAL_TEST();

        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
