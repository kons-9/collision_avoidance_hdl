module router (
    input logic clk,
    input logic rst_n,
    input types::flit_t flit_in,

    output types::flit_t flit_out,
    output logic is_global_destination_self
);
    // MUST TODO

    types::node_id_t global_destination;
    types::node_id_t routing_table[$bits(types::node_id_t)];
    types::node_id_t next_node;
endmodule
