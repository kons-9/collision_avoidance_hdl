module next_free_index_buffer #(
    parameter int NUM_ENTRIES = 8
) (
    input logic nocclk,
    input logic rst_n,

    input logic return_index_valid,
    input logic [$clog2(NUM_ENTRIES)-1:0] return_index,

    input logic next_free_index_ready,
    output logic next_free_index_valid,
    output logic [$clog2(NUM_ENTRIES)-1:0] next_free_index
);
    // TODO: utils/queueの実装でもいいかもしれない。
    // ただ、こちらはきちんと実装ができていればfullになることはないので、
    // 効率的な実装が可能。

    typedef struct {
        // head == tail is used when the buffer is empty and full.
        // so we need to use another flag to check if the buffer is empty.
        logic is_empty;
        logic [$clog2(NUM_ENTRIES)-1:0] head_index;
        logic [$clog2(NUM_ENTRIES)-1:0] tail_index;
        logic [$clog2(NUM_ENTRIES)-1:0] free_index_buffer[NUM_ENTRIES];
    } free_index_buffer_t;

    free_index_buffer_t free_index_buffer;

    always_comb begin
        next_free_index_valid = !free_index_buffer.is_empty;
        next_free_index = free_index_buffer.free_index_buffer[free_index_buffer.head_index];
    end

    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            is_empty <= 1;
            free_index_buffer.head_index <= 0;
            free_index_buffer.tail_index <= 0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                free_index_buffer.free_index_buffer[i] <= i;
            end
        end else begin
            if (return_index_valid) begin
                free_index_buffer.free_index_buffer[free_index_buffer.tail_index] <= return_index;
                free_index_buffer.tail_index <= free_index_buffer.tail_index + 1;
            end
        end
    end


endmodule
