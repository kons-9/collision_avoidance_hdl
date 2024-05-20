module router (
    input logic clk,
    input logic rst_n,
    input types::flit_t flit_in,

    output types::flit_t flit_out,
    output logic is_global_destination_self
);

  types::node_id_t global_destination;
  types::node_id_t routing_table[$bits(types::node_id_t)];
  types::node_id_t next_node;

  // TODO
  // TODO: packet id to global destination
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < $bits(types::node_id_t); i++) begin
        routing_table[i] <= 0;
      end
    end else begin
      next_node <= routing_table[global_destination];
    end
  end

  types::flit_header_t flit_out_header = {
    flit_in.header.version, this_node_id, next_node, flit_in.header.flit_id, flit_in.header.flittype
  };

  assign flit_out = {flit_out_header, flit_in.payload, flit_in.checksum};
endmodule
