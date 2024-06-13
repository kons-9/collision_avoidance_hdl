`include "types.svh"
`include "packet_types.svh"

module system_flit_comb (
    input types::flit_t flit_in,

    input packet_types::routing_table_t routing_table,
    input types::node_id_t random_id,
    input types::node_id_t temporal_id,
    input logic is_flit_from_cpu,
    input logic is_root,
    input node_id_t routing_id_counter,

    output logic system_flit_valid,
    output types::flit_t flit_out,
    output logic is_system_flit_self,

    output logic update_parent_valid,
    output types::node_id_t update_parent_node_id,
    output logic update_this_node_valid,
    output types::node_id_t update_this_node_id,
    output logic update_routing_table_valid,
    output types::node_id_t update_routing_table_key,
    output types::node_id_t update_routing_table_value,
    // for root
    output logic update_routing_id_counter_valid

);
    logic is_broadcast;

    system_types::system_payload_t payload;
    always_comb begin
        payload = flit_in.payload.system.payload;
    end

    always_comb begin
        is_broadcast = (flit_in.header.dst_id == types::BROADCAST_ID);
        flit_out = flit_in;
        update_parent_valid = 0;
        update_parent_node_id = 0;
        update_this_node_valid = 0;
        update_routing_table_valid = 0;
        system_flit_valid = 0;
        is_system_flit_self = 0;
        case (flit_in.payload.system.header)
            system_types::S_PARENT_REQUEST_FROM_NEIGHBOR: begin
                if (is_flit_from_cpu) begin
                    // 親リクエストを送信
                    // ブロードキャスト
                    // 一時的なrandom idを生成
                    system_flit_valid = 1;
                    is_system_flit_self = 0;
                    flit_out.header.src_id = random_id;
                    flit_out.header.dst_id = types::BROADCAST_ID;
                end else if (is_broadcast) begin
                    // 親リクエストを受信
                    // 親アックを返す
                    if (routing_table.this_node_valid) begin
                        // joinしている場合のみ
                        system_flit_valid = 1;
                        is_system_flit_self = 0;
                        flit_out.header.src_id = routing_table.this_node_id;
                        flit_out.header.dst_id = flit_in.header.src_id;
                        flit_out.payload.system.header = system_types::S_PARENT_ACK_FROM_NEIGHBOR;
                    end
                end else begin
                    // error
                    assert (0);
                end
            end
            system_types::S_PARENT_ACK_FROM_NEIGHBOR: begin
                if (temporal_id == flit_in.header.dst_id) begin
                    // 親アックを受信
                    // 親を決める。
                    // 最初に来たものを親にする
                    if (routing_table.parent_valid) begin
                        // 親が決まっている場合、最初に来たflitではないので何もしない
                    end else begin
                        // 親が決まっていない場合
                        routing_table.parent_valid   = 1;
                        routing_table.parent_node_id = flit_in.header.src_id;
                        system_flit_valid = 1;
                        flit_out.header.src_id = temporal_id;
                        flit_out.header.dst_id = flit_in.header.src_id;
                        flit_out.header.flittype = types::SYSTEM;
                        flit_out.payload.system.header = system_types::S_JOIN_REQUEST;
                        flit_out.payload.system.payload.join_request.parent_id = flit_in.header.src_id;
                        flit_out.payload.system.payload.join_request.random_child_id = temporal_id;
                    end
                end else begin
                    // error
                    // this flit is made automatically
                    assert (0);
                end
            end
            system_types::S_JOIN_REQUEST: begin
                if (is_flit_from_cpu) begin
                    // error
                    // this flit is made automatically
                    assert (0);
                end else begin
                    // rootでないときはひたすら親に送る
                    if (is_root) begin
                        // TODO S_JOIN_ACK に変更
                        // routing tableを更新
                        // routing counterを更新
                        update_routing_table_valid = 1;
                        update_routing_table_key = routing_id_counter;
                        update_routing_table_value = flit_in.header.src_id;

                        update_routing_id_counter_valid = 1;

                        system_flit_valid = 1;
                        flit_out.header.src_id = 0; // root
                        flit_out.header.dst_id = flit_in.header.src_id;
                        flit_out.header.flittype = types::SYSTEM;
                        flit_out.payload.system.header = system_types::S_JOIN_ACK;
                        flit_out.payload.system.payload.join_ack.parent_id = flit_in.payload.system.payload.join_request.parent_id;
                        flit_out.payload.system.payload.join_ack.random_child_id = flit_in.payload.system.payload.join_request.random_child_id;
                        flit_out.payload.system.payload.join_ack.child_id = routing_id_counter;
                    end else begin
                        assert (routing_table.parent_valid);
                        assert (routing_table.this_node_valid);
                        system_flit_valid = 1;
                        flit_out.header.src_id = routing_table.this_node_id;
                        flit_out.header.dst_id = routing_table.parent_node_id;
                    end
                end
            end
            system_types::S_JOIN_ACK: begin
                if (is_flit_from_cpu) begin
                    // error
                    // this flit is made automatically
                end else if (payload.join_ack.parent_id == routing_table.this_node_id) begin
                    // ジョインアックを受信
                    system_flit_valid = 1;
                    flit_out.header.src_id = routing_table.this_node_id;
                    // 直接の親の場合、子はまだ自分のidを知らないので、random idをdstにする
                    flit_out.header.dst_id = payload.join_ack.random_child_id;

                    update_routing_table_valid = 1;
                    update_routing_table_key = payload.join_ack.child_id;
                    update_routing_table_value = routing_table.routing_table[payload.join_ack.parent_id];
                    assert (routing_table.valid[payload.join_ack.parent_id] == 1);
                end else if (payload.join_ack.random_child_id == temporal_id) begin
                    // this_node_idを更新
                    update_this_node_valid = 1;
                    update_this_node_id = payload.join_ack.child_id;
                    // TODO: 完了通知を送る？
                end else begin
                    system_flit_valid = 1;
                    flit_out.header.src_id = routing_table.this_node_id;
                    flit_out.header.dst_id = routing_table.routing_table[payload.join_ack.parent_id];

                    update_routing_table_valid = 1;
                    update_routing_table_key = payload.join_ack.child_id;
                    update_routing_table_value = routing_table.routing_table[payload.join_ack.parent_id];
                    assert (routing_table.valid[payload.join_ack.parent_id] == 1);
                end
            end
            default: begin
            end
        endcase
    end
endmodule
