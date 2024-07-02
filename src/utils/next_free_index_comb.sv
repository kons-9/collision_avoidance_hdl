module next_free_index_comb #(
    parameter int NUM_ENTRIES = 8
) (
    input logic [NUM_ENTRIES-1:0] free_index_bitmap,

    output logic next_free_index_valid,
    output logic [$clog2(NUM_ENTRIES)-1:0] next_free_index
);
    always_comb begin
        next_free_index = 0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            if (free_index_bitmap[i]) begin
                next_free_index = i;
            end
        end
        next_free_index_valid = free_index_bitmap[next_free_index];
    end

endmodule
