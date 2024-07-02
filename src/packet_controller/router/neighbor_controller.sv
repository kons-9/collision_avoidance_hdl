`include "types.svh"
`include "packet_types.svh"

module neighbor_controller #(
    parameter int MAX_EXPIRE_TIME = 500,
    parameter int MAX_NUM_OF_NEIGHBOR = 8
) (
    input logic nocclk,
    input logic rst_n,

    /// parent id is special
    input types::node_id_t in_parent_id,
    input logic in_parent_valid,

    input types::node_id_t in_register_id,
    input logic in_register_valid,
    output logic out_register_ready,

    input types::node_id_t in_search_id,
    output logic out_search_id_valid,

    input types::node_id_t in_incoming_id,
    input logic in_incoming_id_valid,

    output types::node_id_t out_invalid_id,
    output logic out_invalid_id_valid,
    output logic out_is_parent_id_invalid
);

    typedef struct {
        logic valid;
        types::node_id_t id;
        logic [$clog2(MAX_EXPIRE_TIME)-1:0] timer;
    } neighbor_t;
    neighbor_t neighbors[MAX_NUM_OF_NEIGHBOR];

    logic [$clog2(MAX_NUM_OF_NEIGHBOR)-1:0] register_index;
    logic [$clog2(MAX_NUM_OF_NEIGHBOR)-1:0] invalid_id_index;
    logic register_invalid; // TODO: output

    always_comb begin
        out_search_id_valid  = 0;
        out_register_ready   = 0;
        register_index   = 0;
        out_invalid_id_valid = 0;
        invalid_id_index = 0;
        register_invalid = 0;
        foreach (neighbors[i]) begin
            if (neighbors[i].valid == 1) begin
                if (neighbors[i].id == in_search_id) begin
                    out_search_id_valid = 1;
                end
                if (neighbors[i].id == in_register_id) begin
                    // already registered
                    register_invalid = 1;
                end
                if (neighbors[i].timer == MAX_EXPIRE_TIME) begin
                    out_invalid_id_valid = 1;
                    invalid_id_index = i;
                    out_invalid_id = neighbors[i].id;
                end
            end else begin
                // empty slot
                out_register_ready = 1;
                register_index = i;
            end
        end
        out_is_parent_id_invalid = in_parent_valid && in_parent_id == out_invalid_id;
    end

    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            foreach (neighbors[i]) begin
                neighbors[i].valid <= 0;
            end
        end else begin
            foreach (neighbors[i]) begin
                if (neighbors[i].valid == 1) begin
                    if (out_invalid_id_valid && i == invalid_id_index) begin
                        neighbors[i].valid <= 0;
                    end else if (in_incoming_id_valid && neighbors[i].id == in_incoming_id) begin
                        // if the incoming id is the same as the neighbor id, reset the timer
                        neighbors[i].timer <= 0;
                    end else begin
                        neighbors[i].timer <= neighbors[i].timer + 1;
                    end
                end else if (!register_invalid && i == register_index && in_register_valid == 1 && out_register_ready == 1) begin
                    // register the new neighbor
                    neighbors[i].valid <= 1;
                    neighbors[i].id <= in_register_id;
                    neighbors[i].timer <= 0;
                end
            end
        end
    end


endmodule
