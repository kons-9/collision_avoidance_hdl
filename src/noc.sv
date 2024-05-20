module noc (
    // uartのクロックを作成するためのクロック
    input  logic cpuclk,
    // rst_nが立った場合、全てのsendバッファをクリアする
    input  logic rst_n,
    // nocとの通信を行うためのクロック
    input  logic nocclk,
    // uartの入力と出力
    input  logic uart_rx,
    output logic uart_tx,

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
  logic tmp_flit[127:0];
  logic [1:0] position;

  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      position <= 0;
    end else begin
      if (data_in_vld) begin
        tmp_flit[position*32] <= data_in;
        position <= position + 1;
      end
    end
  end

  // -------------------------
  // 2. calculate checksum
  // 整合性が何らかの影響で失われた場合、signalにエラーを出力する
  logic send_flit_checksum_error;
  logic send_flit_valid;
  types::flit_t send_flit;

  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      send_flit_checksum_error <= 0;
      send_flit_valid <= 0;
    end else begin
      if (position == 3) begin
        // calculate checksum
        // TODO チェックサムを計算する
        send_flit <= tmp_flit;
        send_flit_checksum_error <= 0;
        send_flit_valid <= 1;
      end else begin
        send_flit_checksum_error <= 0;
        send_flit_valid <= 0;
      end
    end
  end

  // -------------------------
  // 2. put flit into buffer
  // flitをバッファに入れる
  flit_t send_buffer[8];
  logic [2:0] send_buffer_head;
  logic [2:0] send_buffer_tail;

  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      send_buffer_head <= 0;
    end else begin
      if (send_flit_valid) begin
        // TODO: バッファがfullの場合、エラーを出力する
        send_buffer[send_buffer_head] <= send_flit;
        send_buffer_head <= send_buffer_head + 1;
      end
    end
  end

  //////////////////////////////
  // receive flit
  //////////////////////////////

  // -------------------------
  // 1. receive flit
  // uartを通じてflitを受信する
  flit_t receive_flit;
  logic  receive_flit_valid;
  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      receive_flit <= 0;
      receive_flit_valid <= 0;
    end else begin
      // TODO: uartからflitを受信する
      receive_flit <= 0;
      receive_flit_valid <= 1;
    end
  end

  // -------------------------
  // 2. calculate checksum
  // チェックサムを計算する
  logic receive_flit_checksum_error;
  logic receive_flit_checksum_valid;
  always_comb begin
    if (!rst_n) begin
      receive_flit_checksum_error = 0;
      receive_flit_checksum_valid = 0;
    end else begin
      // TODO: チェックサムを計算する
      if (receive_flit_valid) begin
        receive_flit_checksum_error = 0;
        receive_flit_checksum_valid = 1;
      end else begin
        receive_flit_checksum_error = 0;
        receive_flit_checksum_valid = 0;
      end
    end
  end

  // -------------------------
  // 3. make ack flit
  // receive flitがackではない場合、ack flitを作る
  flit_t ack_flit;
  logic  ack_flit_valid;
  always_comb begin
    // TODO: ack flitを作る
    ack_flit = 0;
    ack_flit_valid = 0;
  end

  // -------------------------
  // 4. put ack flit into buffer
  // ack flitをバッファに入れる
  // ack flitは受信したflitに対して返す
  flit_t ack_flit_buffer[8];
  logic [2:0] ack_flit_head;
  logic [2:0] ack_flit_tail;
  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      ack_flit_head <= 0;
    end else begin
      if (receive_flit_checksum_valid & ack_flit_valid) begin
        // TODO: バッファがfullの場合、エラーを出力する
        ack_flit_buffer[ack_flit_head] <= ack_flit;
        ack_flit_head <= ack_flit_head + 1;
      end
    end
  end
  // -------------------------
  // 4. make flit
  // 自分への宛先でない場合、flitを作成する
  flit_t forward_flit;
  logic  forward_flit_valid;

  always_comb begin
    // TODO: 自分への宛先かどうかを判定する
    forward_flit = 0;
    forward_flit_valid = 0;
  end

  // -------------------------
  // 4. put flit into buffer
  // forward_flit_validな場合、flitをバッファに入れる
  flit_t forward_flit_buffer[8];
  logic [2:0] forward_flit_head;
  logic [2:0] forward_flit_tail;

  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      forward_flit_head <= 0;
    end else begin
      if (receive_flit_checksum_valid && !forward_flit_valid) begin
        // TODO: バッファがfullの場合、エラーを出力する
        forward_flit_buffer[forward_flit_head] <= forward_flit;
        forward_flit_head <= forward_flit_head + 1;
      end
    end
  end

  //////////////////////////////
  // routing & uart
  //////////////////////////////

  // -------------------------
  // 1. get flit from buffer
  // flitをバッファから取り出す
  // 現在は単純に先頭のflitを取り出す

  flit_t uart_flit;
  logic  uart_flit_valid;
  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      uart_flit_valid <= 0;
      ack_flit_tail <= 0;
      forward_flit_tail <= 0;
      send_buffer_tail <= 0;
    end else begin
      if (ack_flit_tail != ack_flit_head) begin
        uart_flit <= ack_flit_buffer[ack_flit_tail];
        ack_flit_tail <= ack_flit_tail + 1;
        uart_flit_valid <= 1;
      end else if (forward_flit_tail != forward_flit_head) begin
        uart_flit <= forward_flit_buffer[forward_flit_tail];
        forward_flit_tail <= forward_flit_tail + 1;
        uart_flit_valid <= 1;
      end else if (send_buffer_tail != send_buffer_head) begin
        uart_flit <= send_buffer[send_buffer_tail];
        send_buffer_tail <= send_buffer_tail + 1;
        uart_flit_valid <= 1;
      end else begin
        uart_flit_valid <= 0;
      end
    end
  end


  // -------------------------
  // 2. calculate routing
  // ルーティングを計算する
  // グローバルな宛先から次のノードを決定する
  logic [15:0] next_node;
  logic [15:0] routing_table[16];
  logic [15:0] global_destination;

  always_comb begin
    next_node = routing_table[global_destination];
  end

  // -------------------------
  // 3. calculate checksum
  // チェックサムを計算する
  // NOTE: 以前のチェックサムはroutingがない状態で計算されているため、再計算が必要。
  types::checksum_t uart_checksum;
  always_comb begin
      // TODO: チェックサムを計算する
      uart_checksum = 0;
  end

  // -------------------------
  // 4. send flit by uart
  // flitをuartを通じて送信する
  always_ff @(posedge nocclk or negedge rst_n) begin
    if (!rst_n) begin
      uart_tx <= 0;
    end else begin
      if (uart_flit_valid) begin
          // TODO: uartにflitを送信する
      end
    end
  end

endmodule
