`include "types.svh"
/// @brief CPUとの直接的なやり取りを行うモジュール
/// @NOTE 現実装ではcpuとの通信は32bit単位で、関係のないデータを空にした128bitを分割する形で行う
// @NOTE このモジュールではチェックサムの計算を行わない
module noc_to_cpu_deflitizer (
    input logic nocclk,
    input logic rst_n,
    // for noc internal
    input types::flit_t poped_flit,
    input logic poped_flit_valid,
    output logic poped_flit_ready,
    // cpuとの通信(noc -> cpu)
    // vld, rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを送信する
    input logic data_out_ready,
    output logic [31:0] data_out,
    output logic data_out_valid
);

    logic [127:0] raw_flit_to_cpu;
    logic [  1:0] flit_to_cpu_position;
    assign data_out = raw_flit_to_cpu[flit_to_cpu_position*32+:32];

    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            raw_flit_to_cpu <= 0;
            poped_flit_ready <= 1;
            data_out_valid <= 0;
            flit_to_cpu_position <= 0;
        end else begin
            if (poped_flit_valid & poped_flit_ready) begin
                // wait for poped_flit
                raw_flit_to_cpu <= poped_flit;
                poped_flit_ready <= 0;
                data_out_valid <= 1;
                flit_to_cpu_position <= 0;
            end else if (flit_to_cpu_position === 3) begin
                // end of sending flit
                poped_flit_ready <= 1;
                data_out_valid <= 0;
                flit_to_cpu_position <= 0;
            end else if (data_out_ready & data_out_valid) begin
                flit_to_cpu_position <= flit_to_cpu_position + 1;
            end
        end
    end

endmodule

