`include "types.svh"
`include "packet_types.svh"

module router (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t transfered_flit,
    input logic transfered_flit_valid,
    input types::flit_t transfered_head_flit,
    input logic is_flit_from_cpu,
    output logic transfered_flit_ready,

    input logic noc_to_cpu_pushed_flit_ready,
    output types::flit_t noc_to_cpu_pushed_flit,
    output logic noc_to_cpu_pushed_flit_valid,
    input logic forwarded_flit_ready,
    output types::flit_t forwarded_flit,
    output logic forwarded_flit_valid,
    output types::node_id_t this_node_id
);
    packet_types::routing_table_t routing_table;

    // MUST TODO
    // 送られてきたflitをデコードして、システムフリットかどうか確認する
    // システムフリットの場合、システムフリットの処理を行う
    logic is_system_flit;
    types::node_id_t global_destination;
    logic is_destination_self;
    logic is_source_self;
    types::node_id_t next_node;
    logic next_node_valid;
    // decode head flit
    always_comb begin
        is_system_flit = transfered_head_flit.header.flittype == types::SYSTEM;
        global_destination = transfered_head_flit.payload.head.global_dst_id;
        is_destination_self = (routing_table.this_node_id == transfered_head_flit.payload.head.global_dst_id);
        is_source_self = (routing_table.this_node_id == transfered_head_flit.payload.head.global_src_id);
        next_node_valid = routing_table.valid[global_destination];
        next_node = routing_table.routing_table[global_destination];
    end

    // used for sending flit
    node_id_t random_id;
    always_ff @(posedge nocclk) begin
        if (rst_n == 0) begin
            random_id <= 0;
        end else begin
            random_id <= random_id + 1;
        end
    end

    types::node_id_t temporal_id;
    always_comb begin
        if (routing_table.this_node_id_valid) begin
            this_node_id = routing_table.this_node_id;
        end else begin
            this_node_id = temporal_id;
        end
    end
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            temporal_id <= 0;
        end else if (transfered_flit_valid & transfered_flit_ready & is_system_flit) begin
            if (transfered_flit.payload.system.header == types::S_PARENT_REQUEST_FROM_NEIGHBOR) begin
                if (is_flit_from_cpu) begin
                    temporal_id <= random_id;
                end
            end
        end
    end

    types::flit_t system_flit;
    logic system_flit_valid;
    logic is_system_flit_self;
    logic update_parent_valid;
    logic update_parent_node_id;
    logic update_this_node_valid;
    logic update_this_node_id;
    logic update_routing_table_valid;
    types::node_id_t update_routing_table_key;
    types::node_id_t update_routing_table_value;

    system_flit_comb system_flit_comb (
        .flit_in(transfered_flit),
        .routing_table(routing_table),
        .random_id(random_id),
        .temporal_id(temporal_id),
        .is_flit_from_cpu(is_flit_from_cpu),
        .is_root(),

        .flit_out(system_flit),
        .system_flit_valid(system_flit_valid),
        .is_system_flit_self(is_system_flit_self),
        .update_parent_valid(update_parent_valid),
        .update_parent_node_id(update_parent_node_id),
        .update_this_node_valid(update_this_node_valid),
        .update_this_node_id(update_this_node_id),
        .update_routing_table_valid(update_routing_table_valid),
        .update_routing_table_key(update_routing_table_key),
        .update_routing_table_value(update_routing_table_value)
    );

    // update routing table
    always_ff @(posedge nocclk) begin
        if (rst_n == 0) begin
            routing_table.this_node_valid <= 0;
            routing_table.parent_valid <= 0;
            foreach (routing_table.valid[i]) begin
                routing_table.valid[i] <= 0;
            end
        end else begin
            if (transfered_flit_valid & transfered_flit_ready) begin
                if (is_system_flit) begin
                    if (update_parent_valid) begin
                        routing_table.parent_valid   <= 1;
                        routing_table.parent_node_id <= update_parent_node_id;
                    end
                    if (update_this_node_valid) begin
                        routing_table.this_node_valid <= 1;
                        routing_table.this_node_id <= update_this_node_id;
                    end
                    if (update_routing_table_valid) begin
                        routing_table.valid[update_routing_table_key] <= 1;
                        routing_table.routing_table[update_routing_table_key] <= update_routing_table_value;
                    end
                end
            end
        end
    end

    // used for sending flit
    // TODO: rename
    types::flit_t transfered_flit2;
    logic transfered_flit_valid2;
    logic is_destination_self2;

    // processing flit
    always_ff @(posedge nocclk) begin
        if (rst_n == 0) begin
            transfered_flit_valid2 <= 0;
        end else begin
            if (transfered_flit_valid & transfered_flit_ready) begin
                if (is_system_flit) begin
                    // system
                    // NOTE: system flit doesnot have head flit
                    transfered_flit2 <= system_flit;
                    transfered_flit_valid2 <= system_flit_valid;
                    is_destination_self2 <= is_system_flit_self;

                end else begin
                    // not system flit
                    // 送られてきたflitがシステムフリットでない場合、
                    // change destination node id by routing table
                    // TODO: error handling if destination node id is not valid
                    transfered_flit2.header.version <= transfered_flit.header.version;
                    transfered_flit2.header.flittype <= transfered_flit.header.flittype;
                    transfered_flit2.header.src_id <= routing_table.this_node_id;
                    transfered_flit2.header.dst_id <= next_node;
                    transfered_flit2.header.flit_id <= transfered_flit.header.flit_id;
                    transfered_flit2.payload <= transfered_flit.payload;
                    transfered_flit_valid2 <= next_node_valid;
                    is_destination_self2 <= is_destination_self;
                end
            end
        end
    end

    flit_t transfered_flit3;
    calculate_checksum_comb calculate_checksum_comb (
        .flit_in (transfered_flit2),
        .flit_out(transfered_flit3)
    );

    always_comb begin
        transfered_flit_ready = 1;
        noc_to_cpu_pushed_flit_valid = 0;
        noc_to_cpu_pushed_flit = 0;
        forwarded_flit_valid = 0;
        forwarded_flit = 0;
        if (is_destination_self2) begin
            noc_to_cpu_pushed_flit = transfered_flit3;
            noc_to_cpu_pushed_flit_valid = transfered_flit_valid2;
        end else begin
            forwarded_flit = transfered_flit3;
            forwarded_flit_valid = transfered_flit_valid2;
        end
    end
endmodule
