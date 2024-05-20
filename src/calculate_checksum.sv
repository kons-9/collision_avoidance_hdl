`include "types.sv"
module calculate_checksum (
    input types::flit_t flit,
    output types::checksum_t checksum,
    output logic is_valid
);

  types::checksum_t flit_checksum = flit.checksum;

  always_comb begin
    // TODO チェックサムを計算する
    checksum = 0;
    is_valid = flit_checksum == checksum;
  end
endmodule
