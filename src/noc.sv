module noc (
    // uartのクロックを作成するためのクロック
    input  logic cpuclk,
    // rst_nが立った場合、全てのsendバッファをクリアする
    input  logic rst_n,
    // nocとの通信を行うためのクロック
    input  logic nocclk,
`ifdef UART
    // uartの入力と出力
    input  logic uart_rx,
    output logic uart_tx,
`else
    // flitの入力と出力 for direct connection
    input flit_t flit_rx,
    input flit_t flit_rx_vld,
    output flit_t flit_tx,
    output flit_t flit_tx_rdy,
`endif

    // for input
    input logic [31:0] data_in,
    input logic data_in_vld,
    output logic data_in_rdy,
    // todo: add channel

    // for output
    input logic data_out_rdy,
    output logic [31:0] data_out,
    output logic data_out_vld,
    // todo: add channel

    // for error
    // errorが発生した場合、signalにエラーを出力する
    // rst_nが立つまで、send以外の処理を行わない
    output logic signal,
    output types::signal_t error

    // for conficuration
);

  types::node_id_t this_node_id;
  types::noc_state_t noc_state;

  // TODO: LOCKをどうするか。
  // バッファ挿入に関して、receive bufferとsend bufferが同じ場合、コンフリクトが発生する。
  // 今回は簡単のため、bufferを共有しないようにする。

  //////////////////////////////
  // send flit
  //////////////////////////////

  // -------------------------
  // 1. make flit
  // flitは４分割されてやってくる。
  // そのためデータを結合してflitを作る
  logic [127:0] raw_send_flit;
  logic [1:0] send_position;
  logic raw_send_flit_completed;

  always_ff @(posedge cpuclk or negedge rst_n) begin
    if (!rst_n) begin
      send_position <= 0;
    end else begin
      if (data_in_vld) begin
        raw_send_flit[send_position*32+:32] <= data_in;
        send_position <= send_position + 1;
        raw_send_flit_completed <= (send_position == 3);
      end
    end
  end

  // -------------------------
  // 2. calculate checksum
  // 整合性が何らかの影響で失われた場合、signalにエラーを出力する
  types::flit_t send_flit = raw_send_flit;
  types::checksum_t send_flit_checksum;
  logic send_flit_valid;

  calculate_checksum_comb check_checksum1 (
      .flit(send_flit),
      .checksum(send_flit_checksum),
      .is_valid(send_flit_valid)
  );

  // -------------------------
  // 2. put flit into buffer
  // flitをバッファに入れる
  types::flit_buffer_t send_buffer;
  types::buffer_state_t send_buffer_state;
  types::flit_t send_buffer_flit;

  flit_buffer send_buffer (
      .clk(nocclk),
      .rst_n(rst_n),
      .buffer(send_buffer),
      .insert_flit(send_flit),
      .insert_flit_valid(send_flit_valid & raw_send_flit_completed),

      .next_flit (send_buffer_flit),
      .next_state(send_buffer_state)
  );

  //////////////////////////////
  // receive flit
  //////////////////////////////

  // -------------------------
  // 1. receive flit
  // uartを通じてflitを受信する
  types::flit_t uart_rx_flit;
  logic uart_rx_valid;

  // -------------------------
  // 2. calculate checksum
  // チェックサムを計算する
  logic uart_rx_checksum;
  logic uart_rx_checksum_valid;

  check_checksum_comb check_checksum2 (
      .flit(uart_rx_flit),
      .checksum(uart_rx_checksum),
      .is_valid(uart_rx_checksum_valid)
  );

  // -------------------------
  // 3. make control signal
  // 受信したデータのヘッダーを見て、適切な信号処理を行う
  // 自分への宛先でない場合、flitを破棄する
  logic is_ack;
  logic is_self;
  control_received_flit control_received_flit1 ();

  // -------------------------
  // 3. make ack flit
  // receive flitがackではない場合、ack flitを作る
  types::flit_t ack_flit;
  logic ack_flit_valid;
  make_ack_comb make_ack_comb1 (
      .flit_in(uart_rx_flit),
      .flit_in_vld(is_ack),
      .flit_out(ack_flit),
      .flit_out_vld(ack_flit_valid)
  );

  // -------------------------
  // 4. put ack flit into buffer
  // ack flitをバッファに入れる
  // ack flitは受信したflitに対して返す

  types::flit_buffer_t ack_flit_buffer;
  types::flit_t ack_flit_buffer_state;
  types::buffer_state_t ack_flit_buffer_state;

  flit_buffer ack_flit_buffer (
      .clk(nocclk),
      .rst_n(rst_n),
      .buffer(ack_flit_buffer),
      .insert_flit(ack_flit),
      .insert_flit_valid(ack_flit_valid),

      .next_flit (ack_flit_buffer_state),
      .next_state(ack_flit_buffer_state)
  )

  // -------------------------
  // 5. send data_out
  // 自身の宛先の場合、データを保持する
  types::flit_buffer_t receive_buffer;
  types::flit_t receive_buffer_flit;
  types::buffer_state_t receive_buffer_state;

  flit_buffer receive_buffer (
      .clk(nocclk),
      .rst_n(rst_n),
      .buffer(receive_buffer),
      .insert_flit(receive_flit),
      .insert_flit_valid(receive_flit_valid),
      .is_pop(data_out_rdy),

      .next_flit (receive_buffer_flit),
      .next_state(receive_buffer_state)
  );

  //////////////////////////////
  // send & routing
  //////////////////////////////

  // -------------------------
  // 1. get flit from buffer
  // flitをバッファから取り出す
  // 現在は単純に先頭のflitを取り出す

  types::flit_t poped_uart_tx_flit;
  logic uart_tx_flit_valid;
  logic uart_tx_rdy;
  pop_flit pop_flit1 ();

  // -------------------------
  // 2. calculate routing
  // ルーティングを計算する
  // グローバルな宛先から次のノードを決定する
  types::flit_t uart_tx_flit_without_checksum;
  types::node_id_t global_destination;
  logic is_destination_self;

  router router1 (
      .global_destination(global_destination),
      .flit_in(poped_uart_tx_flit),

      .flit_out(uart_tx_flit_without_checksum),
      .is_global_destination_self(is_destination_self)
  );

  // -------------------------
  // 3. calculate checksum
  // チェックサムを計算する
  // NOTE: 以前のチェックサムはroutingがない状態で計算されているため、再計算が必要。
  types::flit_t uart_tx_flit;

  calculate_checksum_comb checksum (
      .flit(uart_tx_flit_without_checksum),
      .flit_out(uart_tx_flit)
  );

  // -------------------------
  // 4. data out
  // is_destination_selfが立っている場合、データを出力する

  logic [127:0] raw_receive_flit;
  logic [1:0] receive_position;
  logic raw_receive_flit_completed;

  always_ff @(posedge cpuclk or negedge rst_n) begin
    if (!rst_n) begin
      receive_position <= 0;
    end else begin
      if (data_out_rdy) begin
        data_out <= raw_receive_flit[receive_position*32+:32];
        receive_position <= receive_position + 1;
        raw_receive_flit_completed <= (receive_position == 3);
      end
    end
  end


  //////////////////////////////
  // output device
  //////////////////////////////
`ifdef UART
  logic uart_clk;

  uart_clk uart_clk1 (
      .clk(cpuclk),
      .rst_n(rst_n),
      .uart_clk_out(uart_clk)
  );

  uart_rx uart_rx1 (
      .uart_clk(uart_clk),
      .rst_n(rst_n),
      .uart_rx(uart_rx),

      .flit_out(uart_rx_flit),
      .flit_out_vld(uart_tx_flit_valid)
  );

  uart_tx uart_tx1 (
      .uart_clk(uart_clk),
      .rst_n(rst_n),
      .flit_in_vld(uart_tx_flit_valid),
      .flit_in(uart_tx_flit_without_next_node),

      .flit_in_rdy(uart_tx_rdy)
  );
`else
    assign flit_rx = uart_tx_flit;
    assign flit_rx_vld = uart_tx_flit_valid;
    assign flit_tx = uart_tx_flit;
    assign flit_tx_rdy = uart_tx_rdy;
`endif

endmodule
