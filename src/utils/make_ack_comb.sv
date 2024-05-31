`include "types.svh"
/// 通常のフリットの場合、ACKを生成するモジュール
module make_ack_comb(
    input types::flit_t flit_in,

    output types::flit_t flit_out
);
types::flit_t tmp_flit_out;
// 現在ackの確認はflit_id, src_idのみで行うためそれ以外はコピー
always_comb begin
    tmp_flit_out = flit_in;
    tmp_flit_out.header.src_id = flit_in.header.dst_id;
    tmp_flit_out.header.dst_id = flit_in.header.src_id;
end

calculate_checksum_comb calculate_checksum_comb(
    .flit_in(tmp_flit_out),
    .flit_out(flit_out)
);


endmodule
