`include "types.svh"
`include "packet_types.svh"

module packet_buffer #(
    parameter int PACKET_BUFFER_NUM_ENTRIES = 8
) (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t next_flit,
    input logic next_flit_valid,
    output logic next_flit_ready,

    input logic transfered_packet_completed,
    output packet_types::packet_element_t transfered_packet,
    output logic transfered_packet_valid
);
    import packet_types::EXPIRE_TIME;
    parameter int PACKET_BUFFER_INDEX_WIDTH = $clog2(PACKET_BUFFER_NUM_ENTRIES);

    packet_types::packet_element_t packet_buffer[PACKET_BUFFER_NUM_ENTRIES];
    logic [PACKET_BUFFER_INDEX_WIDTH-1:0] next_packet_buffer_index;
    logic next_packet_index_valid;

    logic is_next_flit_head;
    logic is_next_flit_body;
    logic is_next_flit_tail;
    always_comb begin
        is_next_flit_head = next_flit.header.flittype === types::HEAD;
        is_next_flit_body = next_flit.header.flittype === types::BODY;
        is_next_flit_tail = next_flit.header.flittype === types::TAIL;
    end
    types::flit_num_t  next_flit_num;
    types::packet_id_t next_packet_id;
    always_comb begin
        next_flit_num  = next_flit.header.flit_id.flit_num;
        next_packet_id = next_flit.header.flit_id.packet_id;
    end


    // head かつpacket bufferに入っていないとき、新しいentryを作る
    logic free_index_ready;
    logic [PACKET_BUFFER_NUM_ENTRIES-1:0] free_index_bitmap;
    logic [PACKET_BUFFER_INDEX_WIDTH-1:0] free_index;
    logic free_index_valid;
    always_comb begin
        free_index_ready = is_next_flit_head & !next_packet_index_valid & next_flit_valid;
        next_flit_ready  = free_index_valid;
    end

    next_free_index_comb #(
        .NUM_ENTRIES(PACKET_BUFFER_NUM_ENTRIES)
    ) next_free_index (
        // 転送が完了したら、indexをfreeする
        .free_index_bitmap(free_index_bitmap),

        .next_free_index_valid(free_index_valid),
        .next_free_index(free_index)
    );

    logic [PACKET_BUFFER_INDEX_WIDTH-1:0] transfered_packet_index;
    always_comb begin
        transfered_packet = packet_buffer[transfered_packet_index];
    end

    logic pushed_ready;
    queue #(
        .NUM_ENTRIES(PACKET_BUFFER_NUM_ENTRIES),
        .DATA_WIDTH (PACKET_BUFFER_INDEX_WIDTH)
    ) completed_index_queue (
        .clk(nocclk),
        .rst_n(rst_n),
        .pushed_element(next_packet_buffer_index),
        .pushed_valid(next_packet_index_valid & is_next_flit_tail),
        .pushed_ready(pushed_ready),  // theoretically, always 1

        // 転送が完了したら、completed indexから取り出す
        .poped_element(transfered_packet_index),
        .poped_valid  (transfered_packet_valid),
        .poped_ready  (transfered_packet_completed)
    );

    // 現在のflitが入るバッファの検索
    always_comb begin
        next_packet_buffer_index = 0;
        next_packet_index_valid  = 0;
        foreach (packet_buffer[i]) begin
            // 検索して、完成パケットの取り出し
            if (free_index_bitmap[i] == 0 && packet_buffer[i].packet_id == next_packet_id) begin
                next_packet_buffer_index = i;
                next_packet_index_valid  = 1;
            end
        end
    end

    // free_indexの更新
    // 1. timerがEXPIRE_TIMEに達したパケットの削除
    // 2. headflit が来たとき、新しいentryを作る
    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            free_index_bitmap <= '1;
        end else begin
            foreach (packet_buffer[i]) begin
                if (free_index_bitmap[i] == 0) begin
                    // entryが使われている == body or tail flit
                    if (packet_buffer[i].packet_id == next_packet_id) begin
                        // comming body or tail flit
                        assert (free_index_bitmap[i] == 0);
                        assert (i == next_packet_buffer_index);
                        // 現在のflitに該当するtimerはreset
                        packet_buffer[i].timer <= 0;
                    end else if (i == transfered_packet_index & transfered_packet_completed & transfered_packet_valid) begin
                        // transfered packet completed
                        free_index_bitmap[i] <= 1;
                    end else if (packet_buffer[i].is_complete) begin
                        // wait for transfer
                        // nothing to do
                        // TODO: this index should have been pushed to completed_index_queue. so check it
                    end else if (packet_buffer[i].timer == EXPIRE_TIME) begin
                        // timer out
                        free_index_bitmap[i] <= 1;
                    end else begin
                        // timerの更新
                        packet_buffer[i].timer <= packet_buffer[i].timer + 1;
                    end
                end else if (i == free_index && free_index_ready && free_index_valid) begin
                    // comming head flit
                    assert (free_index_bitmap[i] == 1);
                    assert (is_next_flit_head | !next_flit_valid);
                    // new entry
                    packet_buffer[i].timer <= 0;
                    free_index_bitmap[i]   <= 0;
                end
            end
        end
    end

    // flit 挿入
    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
        end else begin
            if (is_next_flit_head) begin
                // head
                // new entry
                if (free_index_valid && free_index_ready) begin
                    assert (free_index_bitmap[free_index] == 1);
                    packet_buffer[free_index].is_complete <= 0;
                    packet_buffer[free_index].packet_id <= next_flit.header.flit_id.packet_id;
                    packet_buffer[free_index].counter <= 1;
                    packet_buffer[free_index].tail_index <= 1;
                    packet_buffer[free_index].buffer[0] <= next_flit;
                end else begin
                    // error: no free buffer
                end
            end else if (is_next_flit_body) begin
                // body
                if (next_flit_valid && next_flit_ready && next_packet_index_valid) begin
                    if (packet_buffer[next_packet_buffer_index].counter == next_flit_num) begin
                        packet_buffer[next_packet_buffer_index].counter <= packet_buffer[next_packet_buffer_index].counter + 1;
                        packet_buffer[next_packet_buffer_index].tail_index <= packet_buffer[next_packet_buffer_index].tail_index + 1;
                        packet_buffer[next_packet_buffer_index].buffer[packet_buffer[next_packet_buffer_index].tail_index] <= next_flit;
                    end else begin
                        // TODO: error, just ignore
                    end
                end
            end else if (is_next_flit_tail) begin
                // tail
                if (next_flit_valid && next_flit_ready && next_packet_index_valid) begin
                    if (packet_buffer[next_packet_buffer_index].counter == next_flit_num) begin
                        packet_buffer[next_packet_buffer_index].counter <= packet_buffer[next_packet_buffer_index].counter + 1;
                        packet_buffer[next_packet_buffer_index].tail_index <= packet_buffer[next_packet_buffer_index].tail_index + 1;
                        packet_buffer[next_packet_buffer_index].buffer[packet_buffer[next_packet_buffer_index].tail_index] <= next_flit;
                        packet_buffer[next_packet_buffer_index].is_complete <= 1;
                    end else begin
                        // TODO: error, just ignore
                    end
                end else begin
                    // error: no packet index
                end
            end else begin
                // nope flit
                // system flitとして来ることが想定される
                // 今のところ、何もしない
            end
        end
    end

endmodule
