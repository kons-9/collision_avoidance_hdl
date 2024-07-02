`include "types.svh"
`include "packet_types.svh"

module normal_flit_generator_comb #(
    parameter logic IS_ROOT = 0
) (
    input logic nocclk,
    input logic rst_n,

    input packet_types::routing_state_t routing_state,  // TODO
    input types::flit_t flit,
    input logic flit_valid,
    input types::node_id_t next_destination,
    input logic next_destination_valid,
    input types::node_id_t this_node_id,
    input logic is_destination_self,

    output logic flit_out_valid,
    output types::flit_t flit_out
);
    logic is_root;
    always_comb begin
        is_root = IS_ROOT;
    end

    always_comb begin
        flit_out = flit;
        flit_out.header.src_id = this_node_id;
        if (is_destination_self) begin
            flit_out_valid = flit_valid;
        end else begin
            if (next_destination_valid) begin
                flit_out_valid = flit_valid;
                flit_out.header.dst_id = next_destination;
            end else begin
                if (is_root) begin
                    flit_out_valid = 0;
                end else begin
                    flit_out_valid = flit_valid;
                    flit_out.header.dst_id = parent_id;
                end
            end
        end
    end
endmodule

