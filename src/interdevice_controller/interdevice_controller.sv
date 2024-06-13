///@brief: デバイス間での通信を規定するモジュール
///@NOTE: 実際の通信ではuartを用いるが、FPGA上のシミュレーションでは直接的な通信を行う
module interdevice_controller (
    input logic cpuclk,
    // rst_nが立った場合、全てのsendバッファをクリアする
    input logic rst_n,
    input types::node_id_t this_node_id,
    input types::flit_t interdevice_tx_flit,
    input logic interdevice_tx_valid,
    output logic interdevice_tx_ready,
    input types::flit_t interdevice_rx_ready,
    output types::flit_t interdevice_rx_flit,
    output logic interdevice_rx_valid,

`ifdef UART
    // uartの入力と出力
    // 通常のuartで128ビットのデータを出力する
    input logic uart_rx,
    output logic uart_tx
`else
    // flitの入力と出力 for direct connection
    // flit_rx_vld, flit_tx_rdy両方のフラグがnocclkの立ち上がり時に立っていた場合、データを受け取る
    input types::flit_t flit_rx,
    input types::flit_t flit_rx_valid,
    output types::flit_t flit_rx_ready,

    input  types::flit_t flit_tx_ready,
    output types::flit_t flit_tx,
    output types::flit_t flit_tx_valid
`endif
);
    logic is_destination_this_node = interdevice_rx_flit.header.dst_id === this_node_id;
    logic is_rx_flit_checksum_valid;
    // rx flitのチェックサムを計算する
    calculate_checksum_comb check_checksum1 (
        .flit_in (interdevice_rx_flit),
        .is_valid(is_rx_flit_checksum_valid)
    );
    assign interdevice_tx_ready = flit_tx_rdy;

    assign interdevice_rx_flit = flit_rx;
    assign interdevice_rx_valid = flit_rx_vld & is_rx_flit_checksum_valid & is_destination_this_node;

`ifdef UART
    // 現在はuartの実装未サポート
    // logic uart_clk;
    //
    // uart_clk uart_clk1 (
    //     .clk(cpuclk),
    //     .rst_n(rst_n),
    //     .uart_clk_out(uart_clk)
    // );
    //
    // uart_rx uart_rx1 (
    //     .uart_clk(uart_clk),
    //     .rst_n(rst_n),
    //     .uart_rx(uart_rx),
    //
    //     .flit_out(interdevice_rx_flit),
    //     .flit_out_vld(interdevice_rx_valid),
    // );
    //
    // uart_tx uart_tx1 (
    //     .uart_clk(uart_clk),
    //     .rst_n(rst_n),
    //     .flit_in_vld(interdevice_tx_valid),
    //     .flit_in(interdevice_tx_flit),
    //
    //     .flit_in_rdy(interdevice_tx_rdy),
    //     .uart_tx(uart_tx)
    // );
`else
    assign flit_rx_rdy = interdevice_rx_ready;
    assign flit_tx = interdevice_tx_flit;
    assign flit_tx_vld = interdevice_tx_valid;
`endif

endmodule
