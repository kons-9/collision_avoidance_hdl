module random_id_generator #(
    parameter int RANDOM_SEED = 0
) (
    input logic nocclk,
    input logic rst_n,
    output node_id_t random_id
);
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            random_id <= RANDOM_SEED;
        end else begin
            random_id <= random_id + 1;
        end
    end
endmodule
