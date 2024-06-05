`include "types.svh"

module packet_buffer #(
    parameter int PACKET_BUFFER_NUM_ENTRIES = 8,
    parameter int MAX_NUM_OF_FLIT = 8,
    parameter int EXPIRE_TIME = 100
) (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t next_flit,
    input logic next_flit_valid,
    output logic next_flit_ready,

    output logic is_next_flit_self,
    output types::flit_t poped_flit,
    output logic poped_flit_valid
);
    typedef struct {
        logic valid_state;
        logic is_complete;
        packet_id_t packet_id;
        logic [$clog2(EXPIRE_TIME)-1:0] timer;

        types::flit_num_t counter;
        logic [$clog2(MAX_NUM_OF_FLIT)-1:0] head_index;
        logic [$clog2(MAX_NUM_OF_FLIT)-1:0] tail_index;
        types::flit_t buffer[MAX_NUM_OF_FLIT];
    } packet_element_t;

    packet_element_t packet_buffer[PACKET_BUFFER_NUM_ENTRIES];
    logic [$clog2(PACKET_BUFFER_NUM_ENTRIES)-1:0] num_of_packet_buffer;

    logic next_flit_counter;
    logic is_next_flit_head = next_flit.header.flittype === types::HEAD;
    logic is_next_flit_tail = next_flit.header.flittype === types::TAIL;
    logic is_next_flit_self = next_flit_head && next_flit.payload.global_dst_id == this_node_id;
    logic is_next_flit_complete = next_flit_tail &&
      next_flit_counter == next_flit.header.flit_id.flit_num;

    logic is_transfer_completed;
    types::flit_t transfered_tail_flit;
    logic transfered_tail_flit_valid;
    packet_id_t transfered_packet_id = transfered_tail_flit.header.flit_id.packet_id;

    flit_queue #(
        .NUM_ENTRIES(PACKET_BUFFER_NUM_ENTRIES)
    ) complete_tail_queue (
        .clk(nocclk),
        .rst_n(rst_n),
        .pushed_flit_valid(is_next_flit_complete),
        .pushed_flit(next_flit),
        .pushed_flit_ready(next_flit_ready),

        .poped_flit_ready(is_transfer_completed),
        .poped_flit_valid(transfered_tail_flit_valid),
        .poped_flit(transferred_tail_flit)
    );

    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            foreach (packet_buffer[i]) begin
                packet_buffer[i].valid_state <= 0;
            end
            next_flit_counter <= 0;
            num_of_packet_buffer <= 0;
        end else begin
            if (next_flit_valid && next_flit_ready) begin
                // 検索して、パケットバッファに格納
                // 検索して、完成パケットのの取り出し
                // timerの更新
                foreach (packet_buffer[i]) begin
                    if (packet_buffer[i].valid_state) begin
                        packet_buffer[i].timer <= packet_buffer[i].timer + 1;
                        if (packet_buffer[i].timer == EXPIRE_TIME) begin
                            packet_buffer[i].valid_state <= 0;
                        end
                        if (packet_buffer[i].packet_id == next_flit.header.flit_id.packet_id) begin
                            if (is_next_flit_head) begin
                                packet_buffer[i].head_index <= packet_buffer[i].head_index + 1;
                                packet_buffer[i].buffer[packet_buffer[i].head_index] <= next_flit;
                            end else if (is_next_flit_tail) begin
                                packet_buffer[i].tail_index <= packet_buffer[i].tail_index + 1;
                                packet_buffer[i].buffer[packet_buffer[i].tail_index] <= next_flit;
                            end
                        end
                    end
                end
            end else begin
                // 検索して、完成パケットのの取り出し
                // timerの更新
                foreach (packet_buffer[i]) begin
                end
            end

        end
    end

endmodule
