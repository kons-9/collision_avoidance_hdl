`include "types.svh"
import types::flit_t;

module noc #(
    parameter int RANDOM_SEED = 0,
    parameter logic IS_ROOT = 0
) (
    // uartのクロックを作成するためのクロック(gclk)
    input logic cpuclk,
    // nocとの通信を行うためのクロック(sclk)
    input logic nocclk,
    // rst_nが立った場合、全てのsendバッファをクリアする
    input logic rst_n,

    // cpuとの通信(cpu -> noc)
    // vld, rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを受け取る
    input logic [31:0] data_in,
    input logic data_in_vld,
    output logic data_in_rdy,

    // cpuとの通信(noc -> cpu)
    // vld, rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを送信する
    input logic data_out_rdy,
    output logic [31:0] data_out,
    output logic data_out_vld,

    // 外部機器との接続用
    // 形状自在の通信では1bitなので、uartモジュールを使うことになるが、FPGAな
    // どの実験では128bitsそのまま送信することができる。
`ifdef UART
    // uartの入力と出力
    // 通常のuartで128ビットのデータを出力する
    input logic uart_rx,
    output logic uart_tx
`else
    // flitの入力と出力 for direct connection
    // flit_rx_vld, flit_tx_rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを受け取る
    input types::flit_t flit_rx,
    input types::flit_t flit_rx_vld,
    output types::flit_t flit_tx,
    output types::flit_t flit_tx_vld
`endif
);

    types::node_id_t this_node_id;
    types::noc_state_t noc_state;

    types::flit_t interdevice_tx_flit;

    logic interdevice_rx_rdy;
    types::flit_t interdevice_rx_flit;
    logic interdevice_rx_valid;

    // TODO: LOCKをどうするか。
    // 今回は簡単のため、bufferを共有しないようにする。

    //////////////////////////////
    // cpu to noc
    //////////////////////////////

    wire cpu_to_noc_pushed_flit_ready;
    wire cpu_to_noc_pushed_flit_valid;
    types::flit_t cpu_to_noc_pushed_flit;
    cpu_to_noc_flitizer cpu_to_noc_flitizer0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_in_vld(data_in_vld),
        .data_in_rdy(data_in_rdy),
        .pushed_flit_ready(cpu_to_noc_pushed_flit_ready),
        .pushed_flit(cpu_to_noc_pushed_flit),
        .pushed_flit_valid(cpu_to_noc_pushed_flit_valid),
        .sys_invalid_flit()
    );

    types::flit_t cpu_to_noc_poped_flit;
    wire cpu_to_noc_poped_flit_ready;
    wire cpu_to_noc_poped_flit_ready;

    flit_queue cpu_to_noc_buffer (
        .clk(nocclk),
        .rst_n(rst_n),
        // push
        .pushed_flit(cpu_to_noc_pushed_flit),
        .pushed_flit_valid(cpu_to_noc_pushed_flit_valid),
        .pushed_flit_ready(cpu_to_noc_pushed_flit_ready),
        // pop
        .poped_flit(cpu_to_noc_poped_flit),
        .poped_flit_valid(cpu_to_noc_poped_flit_valid),
        .poped_flit_ready(cpu_to_noc_poped_flit_ready)
    );

    //////////////////////////////
    // noc to cpu
    //////////////////////////////
    logic noc_to_cpu_pushed_flit_ready;
    logic noc_to_cpu_pushed_flit_valid;
    types::flit_t noc_to_cpu_pushed_flit;

    logic noc_to_cpu_poped_flit_ready;
    logic noc_to_cpu_poped_flit_valid;
    types::flit_t noc_to_cpu_poped_flit;
    flit_queue noc_to_cpu_buffer (
        .clk(nocclk),
        .rst_n(rst_n),
        // push
        .pushed_flit(noc_to_cpu_pushed_flit),
        .pushed_flit_valid(noc_to_cpu_pushed_flit_valid),
        .pushed_flit_ready(noc_to_cpu_pushed_flit_ready),
        // pop
        .poped_flit(noc_to_cpu_poped_flit),
        .poped_flit_valid(noc_to_cpu_poped_flit_valid),
        .poped_flit_ready(noc_to_cpu_poped_flit_ready)
    );

    noc_to_cpu_deflitizer noc_to_cpu_deflitizer0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .poped_flit(noc_to_cpu_poped_flit),
        .poped_flit_valid(noc_to_cpu_poped_flit_valid),
        .poped_flit_ready(noc_to_cpu_poped_flit_ready),
        .data_out_ready(data_out_rdy),
        .data_out(data_out),
        .data_out_valid(data_out_vld)
    );

    //////////////////////////////
    // receive flit
    //////////////////////////////

    // -------------------------
    // 1. make control signal
    // 受信したデータのヘッダーを見て、適切な信号処理を行う
    // 自分への宛先でない場合、flitを破棄する
    types::flit_t interdevice_rx_flit;
    logic interdevice_rx_valid;
    logic interdevice_rx_ready;
    logic ack_flit_valid;
    logic ack_flit_ready;
    logic packet_buffer_ready;
    logic packet_buffer_valid;
    logic waiting_ack_buffer_valid;
    receive_controller_comb receive_controller_comb1 (
        .received_flit(interdevice_rx_flit),
        .received_flit_valid(interdevice_rx_valid),
        .received_flit_ready(interdevice_rx_ready),
        .ack_buffer_ready(ack_flit_ready),
        .ack_buffer_valid(ack_flit_valid),
        .packet_buffer_ready(packet_buffer_ready),
        .packet_buffer_valid(packet_buffer_valid),
        .waiting_ack_buffer_valid(waiting_ack_buffer_valid)
    );

    // -------------------------
    // 2. put ack flit into buffer
    // ack flitをバッファに入れる
    // ack flitは受信したflitに対して返す
    //
    types::flit_t ack_flit;
    make_ack_comb make_ack_comb1 (
        .flit_in (interdevice_rx_flit),
        .flit_out(ack_flit)
    );

    wire ack_poped_flit_ready;
    types::flit_t ack_poped_flit;
    wire ack_poped_flit_valid;
    flit_queue ack_flit_queue (
        .clk(nocclk),
        .rst_n(rst_n),
        .pushed_flit(ack_flit),
        .pushed_flit_valid(ack_flit_valid),
        .pushed_flit_ready(ack_flit_ready),
        .poped_flit_ready(ack_poped_flit_ready),
        .poped_flit(ack_poped_flit),
        .poped_flit_valid(ack_poped_flit_valid)
    );

    // -------------------------
    // 2. packet controller
    // パケット単位で処理を行う
    logic forwarded_flit_ready;
    logic forwarded_flit_valid;
    types::flit_t forwarded_flit;

    packet_controller #(
        .IS_ROOT(IS_ROOT),
        .RANDOM_SEED(RANDOM_SEED)
    ) packet_controller0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .next_flit(interdevice_rx_flit),
        .next_flit_valid(interdevice_rx_valid),
        .next_flit_ready(interdevice_rx_ready),
        .cpu_to_noc_pushed_flit_valid(cpu_to_noc_pushed_flit_valid),
        .cpu_to_noc_pushed_flit(cpu_to_noc_pushed_flit),
        .cpu_to_noc_pushed_flit_ready(cpu_to_noc_pushed_flit_ready),

        .noc_to_cpu_pushed_flit_ready(noc_to_cpu_pushed_flit_ready),
        .noc_to_cpu_pushed_flit_valid(noc_to_cpu_pushed_flit_valid),
        .noc_to_cpu_pushed_flit(noc_to_cpu_pushed_flit),
        .forwarded_flit_ready(forwarded_flit_ready),
        .forwarded_flit_valid(forwarded_flit_valid),
        .forwarded_flit(forwarded_flit),

        .this_node_id(this_node_id)
    );

    wire forwarded_poped_flit_ready;
    wire forwarded_poped_flit_valid;
    types::flit_t forwarded_poped_flit;

    flit_queue forwarded_flit_queue (
        .clk(nocclk),
        .rst_n(rst_n),
        .pushed_flit(forwarded_flit),
        .pushed_flit_valid(forwarded_flit_valid),
        .pushed_flit_ready(forwarded_flit_ready),
        .poped_flit_ready(forwarded_poped_flit_ready),
        .poped_flit(forwarded_poped_flit),
        .poped_flit_valid(forwarded_poped_flit_valid)
    );

    //////////////////////////////
    // waiting ack controller
    //////////////////////////////

    wire waiting_ack_poped_flit_ready;
    wire waiting_ack_poped_flit_valid;
    types::flit_t waiting_ack_poped_flit;
    waiting_ack_controller waiting_ack_controller0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .interdevice_tx_flit(interdevice_tx_flit),
        .interdevice_tx_ready(interdevice_tx_ready),
        .interdevice_tx_valid(interdevice_tx_valid),
        .waiting_ack_flit(interdevice_rx_flit),
        .waiting_ack_flit_valid(waiting_ack_buffer_valid),

        .poped_waiting_ack_flit_ready(waiting_ack_poped_flit_ready),
        .poped_waiting_ack_flit(waiting_ack_poped_flit),
        .poped_waiting_ack_flit_valid(waiting_ack_poped_flit_valid)
    );

    //////////////////////////////
    // buffer selector
    //////////////////////////////

    logic interdevice_tx_valid;
    logic interdevice_tx_ready;
    types::flit_t interdevice_tx_flit;

    tx_buffer_selector_comb tx_buffer_selector_comb0 (
        .nocclk(nocclk),
        .rst_n(rst_n),
        .ack_flit(ack_poped_flit),
        .ack_flit_valid(ack_poped_flit_valid),
        .ack_flit_ready(ack_poped_flit_ready),
        .waiting_ack_buffer(waiting_ack_poped_flit),
        .waiting_ack_buffer_valid(waiting_ack_poped_flit_valid),
        .waiting_ack_buffer_ready(waiting_ack_poped_flit_ready),
        .forwarded_flit(forwarded_poped_flit),
        .forwarded_flit_valid(forwarded_poped_flit_valid),
        .forwarded_flit_ready(forwarded_poped_flit_ready),

        .flit_out_ready(interdevice_tx_ready),
        .flit_out(interdevice_tx_flit),
        .flit_out_valid(interdevice_tx_valid)
    );


    //////////////////////////////
    // inter device comunication
    //////////////////////////////
    interdevice_controller interdevice_controller0 (
        .cpuclk(cpuclk),
        .rst_n(rst_n),
        .this_node_id(this_node_id),
        .interdevice_tx_flit(interdevice_tx_flit),
        .interdevice_tx_valid(interdevice_tx_valid),
        .interdevice_tx_ready(interdevice_tx_ready),

        .interdevice_rx_ready(interdevice_rx_rdy),
        .interdevice_rx_flit (interdevice_rx_flit),
        .interdevice_rx_valid(interdevice_rx_valid),

`ifdef UART
        .uart_rx(uart_rx),
        .uart_tx(uart_tx)
`else
        .flit_rx(flit_rx),
        .flit_rx_valid(flit_rx_vld),
        .flit_rx_ready(),
        .flit_tx(flit_tx),
        .flit_tx_valid(flit_tx_vld),
        .flit_tx_ready()
`endif
    );

endmodule
