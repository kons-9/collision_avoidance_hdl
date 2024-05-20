`include "types.sv"
module calculate_checksum_comb (
    input types::flit_t flit,
    output types::checksum_t checksum,
    output logic is_valid,
    output types::flit_t flit_out
);

  types::checksum_t flit_checksum = flit.checksum;

  // TODO
  always_comb begin
    // TODO チェックサムを計算する
    checksum = 0;
  end

  assign is_valid = flit_checksum == checksum;
  assign flit_out = {
    flit.header,
    flit.payload,
    checksum
  };
endmodule
