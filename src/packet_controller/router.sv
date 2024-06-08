module router (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t transfered_flit,
    input logic transfered_flit_valid,
    output logic transfered_flit_ready,
    input types::flit_t transfered_head_flit,

    input logic noc_to_cpu_pushed_flit_ready,
    output types::flit_t noc_to_cpu_pushed_flit,
    output logic noc_to_cpu_pushed_flit_valid,
    input logic forwarded_flit_ready,
    output types::flit_t forwarded_flit,
    output logic forwarded_flit_valid
);
    // MUST TODO

    types::node_id_t global_destination;
    types::node_id_t routing_table[$bits(types::node_id_t)];
    types::node_id_t next_node;
endmodule
