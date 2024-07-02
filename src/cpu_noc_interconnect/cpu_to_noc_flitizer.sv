`include "types.svh"
/// @brief CPUとの直接的なやり取りを行うモジュール
/// @NOTE 現実装ではcpuとの通信は32bit単位で、関係のないデータを空にした128bitを分割する形で行う
//の
module cpu_to_noc_flitizer (
    input logic nocclk,
    input logic rst_n,
    // cpuとの通信(cpu -> noc)
    // vld, rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを受け取る
    input logic [31:0] data_in,
    input logic data_in_vld,
    output logic data_in_rdy,
    // for noc internal
    input logic pushed_flit_ready,
    output types::flit_t pushed_flit,
    output logic pushed_flit_valid,
    // cpuから送られたflitのchecksumが誤っていた場合、このフラグが立つ
    output logic sys_invalid_flit
);
    assign data_in_rdy = pushed_flit_ready;
    // incoming flit
    // 4分割されたflitを合成し、checksumを計算したあと、bufferに入れる。
    // TODO このバッファに入れられたflitは現在の実装だと必ず送信されるが、
    // 今後system dataを入れることも考えられ、そのときはnocの設定などをおこなう
    logic [127:0] raw_flit;
    logic [1:0] raw_flit_position;
    logic raw_flit_completed;

    logic is_checksum_valid;

    // clkの立ち上がりでdata_inがready & validの場合、データを受け取る
    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            sys_invalid_flit <= 0;
            raw_flit_position <= 0;
            raw_flit_completed <= 0;
        end else begin
            sys_invalid_flit <= sys_invalid_flit | (!is_checksum_valid & raw_flit_completed);
            if (data_in_vld & data_in_rdy & !sys_invalid_flit) begin
                raw_flit[raw_flit_position*32+:32] <= data_in;
                raw_flit_position <= raw_flit_position + 1;
                raw_flit_completed <= (raw_flit_position === 3);
            end else begin
                raw_flit_position  <= 0;
                raw_flit_completed <= 0;
            end
        end
    end

    calculate_checksum_comb check_checksum1 (
        .flit_in(raw_flit),
        .is_valid(is_checksum_valid),

        .flit_out(pushed_flit)
    );

    assign pushed_flit_valid = raw_flit_completed;

endmodule
