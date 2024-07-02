module stage40 (
    input logic nocclk,
    input logic rst_n,

    input types::flit_t in_system_flit,
    input logic in_system_flit_valid,
    input types::flit_t in_normal_flit,
    input logic in_normal_flit_valid,

    output logic out_flit_valid,
    output types::flit_t out_flit

);
    types::flit_t _flit_pre_chechsum;
    always_comb begin
        out_flit_valid = 0;
        _flit_pre_chechsum = 0;
        if (in_system_flit_valid) begin
            out_flit_valid = 1;
            _flit_pre_chechsum = in_system_flit;
        end else if (in_normal_flit_valid) begin
            out_flit_valid = 1;
            _flit_pre_chechsum = in_normal_flit;
        end
    end

    calculate_checksum_comb calculate_checksum_comb (
        .flit_in (_flit_pre_chechsum),
        .flit_out(out_flit),
    );
endmodule
