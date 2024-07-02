`include "types.svh"

module waiting_ack_controller #(
    parameter int ACK_BUFFER_NUM_ENTRIES = 8,
    parameter int MAX_RESEND_NUM = 3,
    parameter int MAX_TIMEOUT = 100
) (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t interdevice_tx_flit,
    input logic interdevice_tx_ready,
    input logic interdevice_tx_valid,

    input types::flit_t waiting_ack_flit,
    input logic waiting_ack_flit_valid,

    input logic poped_waiting_ack_flit_ready,
    output logic poped_waiting_ack_flit_valid,
    output types::flit_t poped_waiting_ack_flit
);
    typedef struct {
        logic is_valid;  // TODO: actually, this is not necessary but for debug
        types::flit_id_t flit_id;
        types::node_id_t node_id;

        logic [$clog2(MAX_RESEND_NUM+1)-1:0] resend_num;
        logic [$clog2(MAX_TIMEOUT)-1:0] timer;
        logic resending;

        types::flit_t ack_flit;
    } ack_field_t;

    ack_field_t ack_buffer[ACK_BUFFER_NUM_ENTRIES];

    logic [ACK_BUFFER_NUM_ENTRIES-1:0] free_index_bitmap;
    logic [$clog2(ACK_BUFFER_NUM_ENTRIES)-1:0] free_index;
    logic free_index_valid;

    next_free_index_comb #(
        .NUM_ENTRIES(ACK_BUFFER_NUM_ENTRIES)
    ) next_free_index (
        .free_index_bitmap(free_index_bitmap),
        .free_index(free_index),
        .free_index_valid(free_index_valid)
    );

    logic [$clog2(ACK_BUFFER_NUM_ENTRIES)-1:0] tx_index;
    logic tx_index_valid;

    logic [$clog2(ACK_BUFFER_NUM_ENTRIES)-1:0] waiting_ack_index;
    logic waiting_ack_index_valid;

    always_comb begin
        tx_index_valid = 0;
        waiting_ack_index_valid = 0;
        for (int i = 0; i < ACK_BUFFER_NUM_ENTRIES; i++) begin
            if (ack_buffer[i].is_valid) begin
                if (ack_buffer[i].ack_flit.header.node_id === waiting_ack_flit.header.node_id) begin
                    waiting_ack_index = i;
                    waiting_ack_index_valid = 1;
                end
                if (ack_buffer[i].ack_flit.header.node_id === interdevice_tx_flit.header.node_id) begin
                    tx_index = i;
                    tx_index_valid = 1;
                end
            end
        end
    end

    logic [$clog2(ACK_BUFFER_NUM_ENTRIES)-1:0] resend_index;
    logic resend_flit_valid;
    logic resend_ready;

    always_comb begin
        resend_flit_valid = 0;
        resend_ready = 0;
        for (int i = 0; i < ACK_BUFFER_NUM_ENTRIES; i++) begin
            if (ack_buffer[i].is_valid && !ack_buffer[i].resending) begin
                if (ack_buffer[i].timer == MAX_TIMEOUT && ack_buffer[i].resend_num < MAX_RESEND_NUM) begin
                    resend_index = i;
                    resend_flit_valid = resend_ready;
                end
            end
        end
    end

    logic [$clog2(ACK_BUFFER_NUM_ENTRIES)-1:0] poped_ack_flit_index;
    logic poped_ack_flit_index_valid;

    queue #(
        .NUM_ENTRIES(ACK_BUFFER_NUM_ENTRIES)
    ) resend_queue (
        .clk(nocclk),
        .rst_n(rst_n),
        .pushed_element(resend_index),
        .pushed_valid(resend_flit_valid),
        .pushed_ready(resend_ready),

        .poped_element(poped_ack_flit_index),
        .poped_valid  (poped_ack_flit_index_valid),
        .poped_ready  (poped_waiting_ack_flit_ready)
    );

    always_comb begin
        poped_waiting_ack_flit = ack_buffer[poped_ack_flit_index].ack_flit;
        poped_waiting_ack_flit_valid = poped_ack_flit_index_valid;
    end

    logic resend_complete;
    always_comb begin
        resend_complete = poped_ack_flit_index_valid & poped_waiting_ack_flit_ready;
    end



    generate
        for (genvar i = 0; i < ACK_BUFFER_NUM_ENTRIES; i++) begin : ACK_BUFFER_GENERATE
            // resend
            always_ff @(posedge nocclk) begin
                if (!rst_n) begin
                    ack_buffer[i].resending  <= 0;
                    ack_buffer[i].resend_num <= 0;
                end else begin
                    if (ack_buffer[i].is_valid) begin
                        if (ack_buffer[i].resending) begin
                            if (resend_complete) begin
                                // when flit is poped, reset resending flag
                                ack_buffer[i].resending  <= 0;
                                ack_buffer[i].resend_num <= ack_buffer[i].resend_num + 1;
                            end
                        end else if (ack_buffer[i].timer == MAX_TIMEOUT && ack_buffer[i].resend_num < MAX_RESEND_NUM) begin
                            // while flit is not poped, set resending flag
                            ack_buffer[i].resending <= 1;
                        end
                    end
                end
            end
            // timer
            always_ff @(posedge nocclk) begin
                if (!rst_n) begin
                    ack_buffer[i].timer <= 0;
                end else begin
                    if (ack_buffer[i].is_valid) begin
                        if (ack_buffer[i].resending) begin
                            // resenging flag is set when timer reaches TIMEOUT and resend_num is less than MAX_RESEND_NUM
                            // nothing to do
                        end else if (ack_buffer[i].timer < MAX_TIMEOUT) begin
                            ack_buffer[i].timer <= ack_buffer[i].timer + 1;
                        end else if (resend_flit_valid && i == resend_index) begin
                            // MAX_TIMEOUT && resend_num < MAX_RESEND_NUM
                            // if multiple flits are ready to resend, only the first flit is selected
                            ack_buffer[i].timer <= 0;
                        end
                    end else begin
                        ack_buffer[i].timer <= 0;
                    end
                end
            end
            // valid
            always_comb begin
                ack_buffer[i].is_valid = !free_index_bitmap[i];
            end
            always_ff @(posedge nocclk) begin
                if (!rst_n) begin
                    free_index_bitmap[i] <= 1;  // all free
                end else begin
                    if (ack_buffer[i].is_valid) begin
                        if (waiting_ack_index_valid && i == waiting_ack_index && waiting_ack_flit_valid) begin
                            // ack is received
                            free_index_bitmap[i] <= 1;
                        end else if (ack_buffer[i].timer == MAX_TIMEOUT && ack_buffer[i].resend_num == MAX_RESEND_NUM) begin
                            // TODO: error handling
                            // maybe, delete this flit node from routing table
                            free_index_bitmap[i] <= 1;
                        end
                    end else if (free_index_valid && free_index == i) begin
                        if (interdevice_tx_valid && interdevice_tx_ready) begin
                            if (!interdevice_tx_flit.header.is_ack) begin
                                // if this flit is not made in this module
                                free_index_bitmap[i] <= 0;
                            end
                        end
                    end
                end
            end
        end
    endgenerate

    // insert tx flit to ack buffer if tx flit is not ack flit
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
        end else begin
            if (interdevice_tx_valid && interdevice_tx_ready && free_index_valid) begin
                if (!interdevice_tx_flit.header.is_ack) begin
                    // if this flit is not made in this module
                    ack_buffer[free_index].flit_id  <= interdevice_tx_flit.header.flit_id;
                    ack_buffer[free_index].node_id  <= interdevice_tx_flit.header.node_id;
                    ack_buffer[free_index].ack_flit <= interdevice_tx_flit;
                end
            end
        end
    end

endmodule
