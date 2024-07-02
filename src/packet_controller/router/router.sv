`include "types.svh"
`include "packet_types.svh"

module router #(
    parameter logic IS_ROOT = 0,  // TODO: use ifdef?
    parameter int MAX_HEARTBEAT_REQUEST_TIMER = 100,
    parameter int MAX_EXPIRE_TIME = 500,
    parameter int MAX_NUM_OF_NEIGHBOR = 8
) (
    input logic nocclk,
    input logic rst_n,

    input types::node_id_t incoming_flit_node_id,
    input logic incoming_flit_valid,

    input types::flit_t transfered_flit,
    input logic transfered_flit_valid,
    input types::flit_t transfered_head_flit,
    input logic is_from_cpu,
    output logic transfered_flit_ready,

    input logic noc_to_cpu_pushed_flit_ready,
    output types::flit_t noc_to_cpu_pushed_flit,
    output logic noc_to_cpu_pushed_flit_valid,
    input logic forwarded_flit_ready,
    output types::flit_t forwarded_flit,
    output logic forwarded_flit_valid,
    output types::node_id_t this_node_id
);

    logic stage1_stall;
    logic stage2_stall;
    logic stage3_stall;
    logic stage4_stall;
    logic stage5_stall;

    /// global variables
    logic g_update_temporal_id;
    types::node_id_t g_next_temporal_id;
    types::node_id_t g_temporal_id;
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            g_temporal_id <= 0;
        end else begin
            if (g_update_temporal_id) begin
                g_temporal_id <= g_next_temporal_id;
            end
        end
    end
    logic g_is_root;
    logic g_incoming_flit_valid;
    types::node_id_t g_incoming_flit_node_id;
    types::node_id_t g_this_node_id;
    packet_types::routing_state_t g_routing_state;
    packet_types::routing_table_t g_routing_table;
    always_comb begin
        g_is_root = IS_ROOT;
        g_incoming_flit_node_id = incoming_flit_node_id;
        g_incoming_flit_valid = incoming_flit_valid;
        if (g_routing_table.this_node_valid) begin
            g_this_node_id = g_routing_table.this_node_id;
        end else begin
            g_this_node_id = g_temporal_id;
        end
    end

    always_comb begin
        transfered_flit_ready = stage1_ready;
        this_node_id = g_this_node_id;
    end

    //////////////////////////////////////////
    /// stage 1
    /// decode head flit
    logic stage1_valid;
    logic stage1_ready;
    logic stage2_ready;
    always_comb begin
        stage1_valid = transfered_flit_valid;
    end

    // forward
    types::flit_t stage1_flit;
    logic stage1_flit_valid;
    types::flit_t stage1_head_flit;
    logic stage1_is_from_cpu;
    always_comb begin
        stage1_flit = transfered_flit;
        stage1_flit_valid = transfered_flit_valid;
        stage1_head_flit = transfered_head_flit;
        stage1_is_from_cpu = is_from_cpu;
    end

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
    packet_types::routing_state_t stage1_next_routing_state;

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

    //////////////////////////////////////////
    /// stage 2
    /// routing

    logic stage2_valid;
    logic stage3_ready;
    // always_ff @(posedge nocclk) begin // if pipeline
    always_comb begin
        stage2_ready = stage3_ready & !stage2_stall;
        stage2_valid = stage1_valid;
    end

    // just forward
    types::flit_t stage2_flit;
    logic stage2_flit_valid;

    types::node_id_t stage2_global_destination;
    logic stage2_is_heartbeat_request;
    logic stage2_is_destination_self;
    logic stage2_is_source_self;
    logic stage2_is_system_flit;
    logic stage2_is_init;
    logic stage2_is_join_ack_parent;
    system_types::system_header_t stage2_system_header;
    system_types::system_payload_t stage2_system_payload;
    logic stage2_update_routing_table_valid;
    types::node_id_t stage2_update_routing_table_key;
    logic stage2_is_raw_global_destination_used_to_update_routing_table;
    logic stage2_update_next_state;
    packet_types::routing_state_t stage2_next_routing_state;
    // always_ff @(posedge nocclk) begin // if pipeline
    always_comb begin
        stage2_flit = stage1_flit;
        stage2_flit_valid = stage1_flit_valid;
        stage2_global_destination = stage1_global_destination;
        stage2_is_heartbeat_request = stage1_is_heartbeat_request;
        stage2_is_destination_self = stage1_is_destination_self;
        stage2_is_source_self = stage1_is_source_self;
        stage2_is_system_flit = stage1_is_system_flit;
        stage2_is_init = stage1_is_init;
        stage2_is_join_ack_parent = stage1_is_join_ack_parent;
        stage2_system_header = stage1_system_header;
        stage2_system_payload = stage1_system_payload;
        stage2_update_routing_table_valid = stage1_update_routing_table_valid;
        stage2_update_routing_table_key = stage1_update_routing_table_key;
        stage2_is_raw_global_destination_used_to_update_routing_table = stage1_is_raw_global_destination_used_to_update_routing_table;
        stage2_update_next_state = stage1_update_next_state;
        stage2_next_routing_state = stage1_next_routing_state;
    end

    // output
    types::node_id_t stage2_next_node;
    logic stage2_next_node_valid;

    // routing
    always_comb begin
        stage2_next_node_valid = g_routing_table.valid[stage2_global_destination];
        stage2_next_node = g_routing_table.routing_table[stage2_global_destination];
    end

    //////////////////////////////////////////
    /// stage 3
    /// check neighbor and generate system flit
    logic stage3_valid;
    logic stage4_ready;
    always_comb begin
        stage3_ready = stage4_ready & !stage3_stall & !r_invalid_id_valid;
        stage3_valid = stage2_valid;
    end

    // forward
    types::flit_t stage3_flit;
    logic stage3_flit_valid;
    types::node_id_t stage3_global_destination;
    logic stage3_is_heartbeat_request;
    logic stage3_is_destination_self;
    logic stage3_is_source_self;
    logic stage3_is_system_flit;
    logic stage3_is_init;
    logic stage3_is_join_ack_parent;
    system_types::system_header_t stage3_system_header;
    system_types::system_payload_t stage3_system_payload;
    logic stage3_update_routing_table_valid;
    types::node_id_t stage3_update_routing_table_key;
    logic stage3_is_raw_global_destination_used_to_update_routing_table;
    types::node_id_t stage3_next_node;  // evaluated in neighbor_controller
    logic stage3_next_node_valid;
    // always_ff @(posedge nocclk) begin // if pipeline
    always_comb begin
        stage3_flit = stage2_flit;
        stage3_flit_valid = stage2_flit_valid;
        stage3_global_destination = stage2_global_destination;
        stage3_is_heartbeat_request = stage2_is_heartbeat_request;
        stage3_is_destination_self = stage2_is_destination_self;
        stage3_is_source_self = stage2_is_source_self;
        stage3_is_system_flit = stage2_is_system_flit;
        stage3_is_init = stage2_is_init;
        stage3_is_join_ack_parent = stage2_is_join_ack_parent;
        stage3_system_header = stage2_system_header;
        stage3_system_payload = stage2_system_payload;

        stage3_update_routing_table_valid = stage2_update_routing_table_valid;
        stage3_update_routing_table_key = stage2_update_routing_table_key;
        stage3_is_raw_global_destination_used_to_update_routing_table = stage2_is_raw_global_destination_used_to_update_routing_table;
        stage3_next_node = stage2_next_node;
        stage3_next_node_valid = stage2_next_node_valid;
    end

    // output
    logic stage3_system_flit_out_valid;
    types::flit_t stage3_system_flit_out;
    logic stage3_normal_flit_valid_out;
    types::flit_t stage3_normal_flit_out;
    logic stage3_update_next_state;
    packet_types::routing_state_t stage3_next_routing_state;
    logic stage3_neighbor_id_valid;  // evaluated in neighbor_controller

    // only for root
    types::node_id_t stage3_node_id_counter;
    logic stage3_update_node_id_counter;
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            stage3_node_id_counter <= 1;
        end else begin
            if (stage3_update_node_id_counter) begin
                stage3_node_id_counter <= stage3_node_id_counter + 1;
            end
        end
    end

    stage30 #() stage3_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .in_flit(stage3_flit),
        .in_flit_valid(stage3_flit_valid),
        .in_next_destination(stage3_next_node),
        .in_next_destination_valid(stage3_next_node_valid),
        .in_this_node_id(g_this_node_id),
        .in_parent_id(g_routing_table.parent_node_id),

        // for system flit generator
        .in_is_system_flit(stage3_is_system_flit),
        .in_routing_state(g_routing_state),
        .in_global_destination_id(stage3_global_destination),
        .in_temporal_id(g_temporal_id),
        .in_is_heartbeat_request(stage3_is_heartbeat_request),
        .in_is_root(g_is_root),
        .in_is_init(stage3_is_init),
        .in_is_join_ack_parent(stage3_is_join_ack_parent),
        .in_system_header(stage3_system_header),
        .in_payload(stage3_system_payload),
        .in_node_id_counter(stage3_node_id_counter),  // only for root
        .out_update_node_id_counter(stage3_update_node_id_counter),  // only for root
        .out_next_routing_state_valid(stage3_update_next_state),
        .out_next_routing_state(stage3_next_routing_state),
        .out_sys_flit_out_valid(stage3_system_flit_out_valid),
        .out_sys_flit_out(stage3_system_flit_out),

        // for normal flit generator
        .in_is_destination_self(stage3_is_destination_self),
        .out_normal_flit_out_valid(stage3_normal_flit_valid_out),
        .out_normal_flit_out(stage3_normal_flit_out)
    );

    //////////////////////////////////////////
    /// stage 4
    /// flit selection and checksum
    logic stage4_valid;
    logic stage5_ready;
    always_comb begin
        stage4_ready = stage5_ready & !stage4_stall;
        stage4_valid = stage3_valid;
    end

    // forward
    logic stage4_system_flit_valid;
    types::flit_t stage4_system_flit;
    logic stage4_normal_flit_valid;
    types::flit_t stage4_normal_flit;
    logic stage4_is_destination_self;
    // always_ff @(posedge nocclk) begin // if pipeline
    always_comb begin
        stage4_system_flit_valid = stage3_flit_valid;
        stage4_system_flit = stage3_system_flit_out;
        stage4_normal_flit_valid = stage3_normal_flit_valid_out;
        stage4_normal_flit = stage3_normal_flit_out;
        stage4_is_destination_self = stage3_is_destination_self;
    end

    // output
    logic stage4_valid_flit_out;
    types::flit_t stage4_flit_out;

    stage40 #() stage4_inst (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .in_system_flit(stage4_system_flit),
        .in_system_flit_valid(stage4_system_flit_valid),
        .in_normal_flit(stage4_normal_flit),
        .in_normal_flit_valid(stage4_normal_flit_valid),

        .out_flit_valid(stage4_valid_flit_out),
        .out_flit(stage4_flit_out)
    );

    //////////////////////////////////////////
    /// stage 5
    logic stage5_valid;
    logic stage5_ready;

    always_comb begin
        stage5_ready = !stage5_stall;
        stage5_valid = stage4_valid;
    end

    // forward
    types::flit_t stage5_flit;
    logic stage5_flit_valid;
    logic stage5_is_destination_self;
    // always_ff @(posedge nocclk) begin // if pipeline
    always_comb begin
        stage5_flit = stage4_flit;
        stage5_flit_valid = stage4_flit_valid;
        stage5_is_destination_self = stage4_is_destination_self;
    end

    // output
    types::flit_t stage5_flit_out;

    always_comb begin
        noc_to_cpu_pushed_flit_valid = 0;
        forwarded_flit_valid = 0;
        noc_to_cpu_pushed_flit = stage5_flit_out;
        forwarded_flit = stage5_flit_out;
        if (stage5_is_destination_self) begin
            noc_to_cpu_pushed_flit_valid = stage5_flit_valid;
        end else begin
            forwarded_flit_valid = stage5_flit_valid;
        end
    end

    //////////////////////////////////////////
    // system controller
    //////////////////////////////////////////

    /// neighbor controller
    logic sys_invalid_id_valid;
    types::node_id_t sys_invalid_id;
    logic sys_is_parent_id_invalid;
    neighbor_controller #(
        .MAX_EXPIRE_TIME(MAX_EXPIRE_TIME),
        .MAX_NUM_OF_NEIGHBOR(MAX_NUM_OF_NEIGHBOR)
    ) neighbor_controller0 (
        .nocclk(nocclk),
        .rst_n (rst_n),

        .in_register_valid(stage1_update_neighbor_id_valid),
        .in_register_id(stage1_update_neighbor_id),
        .out_register_ready(),  // ignore...もしここが立たないとしたら、何か問題がある

        .in_search_id(stage3_next_node),
        .out_search_id_valid(stage3_neighbor_id_valid),
        .in_incoming_id_valid(g_incoming_flit_valid),
        .in_incoming_id(g_incoming_flit_node_id),
        .out_invalid_id_valid(sys_invalid_id_valid),
        .out_invalid_id(sys_invalid_id),
        .out_is_parent_id_invalid(sys_is_parent_id_invalid)
    );

    /// routing table update
    /// this node and parent node
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            if (g_is_root) begin
                g_routing_table.this_node_valid <= 1;
                g_routing_table.this_node_id <= 0;
            end else begin
                g_routing_table.this_node_valid <= 0;
            end
            g_routing_table.parent_valid <= 0;
            for (int i = 0; i < $bits(types::node_id_t); i++) begin
                g_routing_table.valid[i] <= 0;
            end
        end else begin
            // update parent
            if (stage1_update_parent_valid) begin
                g_routing_table.parent_valid   <= 1;
                g_routing_table.parent_node_id <= stage1_update_parent_node_id;
            end else if (stage3_is_invalid_parent) begin
                g_routing_table.parent_valid <= 0;
            end
            // update this node
            if (stage1_update_this_node_valid) begin
                g_routing_table.this_node_valid <= 1;
                g_routing_table.this_node_id <= stage1_update_this_node_id;
            end
            if (sys_invalid_id_valid) begin
                // 他のステージは全部止める
                // 能動的な切断はしない
                for (int i = 0; i < $bits(types::node_id_t); i++) begin
                    // TODO: ここが非常に重たくなることが予想されるので、
                    // クロックを分ける必要がある気がする
                    if (g_routing_table.valid[i] && g_routing_table.routing_table[i] == sys_invalid_id) begin
                        g_routing_table.valid[i] <= 0;
                    end
                end
            end else if (stage3_update_routing_table_valid) begin
                g_routing_table.valid[stage3_update_routing_table_key] <= 1;
                if (stage3_is_raw_global_destination_used_to_update_routing_table) begin
                    g_routing_table.routing_table[stage3_update_routing_table_key] <= stage3_global_destination;
                end else begin
                    g_routing_table.routing_table[stage3_update_routing_table_key] <= stage3_next_node;
                end
            end
        end
    end

    /// controller
    /// routing state machine
    logic all_stage_stall;
    always_comb begin
        all_stage_stall = sys_invalid_id_valid;
        stage1_stall = all_stage_stall;
        stage2_stall = all_stage_stall;
        stage3_stall = all_stage_stall;
        stage4_stall = all_stage_stall;
        stage5_stall = all_stage_stall;
        case (g_routing_state)
            INIT,
            I_GENERATE_PARENT_REQUEST,
            I_WAIT_PARENT_ACK,
            I_GENERATE_JOIN_REQUEST,
            I_WAIT_JOIN_ACK,
            S_GENERATE_PARENT_REQUEST,
            S_WAIT_PARENT_ACK,
            S_GENERATE_JOIN_REQUEST,
            S_WAIT_JOIN_ACK,
            FATAL_ERROR: begin
                stage1_stall = 1;
                stage2_stall = 1;
                stage3_stall = 1;
                stage4_stall = 1;
                stage5_stall = 1;
            end
            NORMAL: begin
            end
            default: begin
            end
        endcase
    end

    // update routing state
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            if (g_is_root) begin
                g_routing_state <= NORMAL;
            end else begin
                g_routing_state <= INIT;
            end
        end else begin
            case (g_routing_state)
                INIT: begin
                    if (stage1_update_next_state) begin
                        g_routing_state <= stage1_next_routing_state;
                    end
                end
                I_GENERATE_PARENT_REQUEST: begin
                    if (stage3_update_next_state) begin
                        g_routing_state <= stage3_next_routing_state;
                    end
                end
                I_WAIT_PARENT_ACK: begin
                    if (stage1_update_next_state) begin
                        g_routing_state <= stage1_next_routing_state;
                    end
                end
                I_GENERATE_JOIN_REQUEST: begin
                    if (stage3_update_next_state) begin
                        g_routing_state <= stage3_next_routing_state;
                    end
                end
                I_WAIT_JOIN_ACK: begin
                    if (stage1_update_next_state) begin
                        g_routing_state <= stage1_next_routing_state;
                    end
                end
                S_GENERATE_PARENT_REQUEST: begin
                    if (stage3_update_next_state) begin
                        g_routing_state <= stage3_next_routing_state;
                    end
                end
                S_WAIT_PARENT_ACK: begin
                    if (stage1_update_next_state) begin
                        g_routing_state <= stage1_next_routing_state;
                    end
                end
                S_GENERATE_JOIN_REQUEST: begin
                    if (stage3_update_next_state) begin
                        g_routing_state <= stage3_next_routing_state;
                    end
                end
                S_WAIT_JOIN_ACK: begin
                    if (stage1_update_next_state) begin
                        g_routing_state <= stage1_next_routing_state;
                    end
                end
                NORMAL: begin
                end
                FATAL_ERROR: begin
                    g_routing_state <= FATAL_ERROR;
                end
                default: begin
                    g_routing_state <= FATAL_ERROR;
                end
            endcase
        end
    end
endmodule
