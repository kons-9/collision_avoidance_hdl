`include "types.svh"
module calculate_checksum_comb (
    input types::flit_t flit_in,
    output types::checksum_t checksum,
    output logic is_valid,
    output types::flit_t flit_out
);

    types::checksum_t flit_checksum;
    assign flit_checksum = flit_in.checksum;

    // MUST TODO
    always_comb begin
        // TODO チェックサムを計算する
        checksum = 0;
    end

    assign is_valid = flit_checksum === checksum;
    assign flit_out = {flit_in.header, flit_in.payload, checksum};
endmodule
