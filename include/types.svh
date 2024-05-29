`ifndef TYPES_SVH
`define TYPES_SVH
package types;
  //////////////////////////////////////////////////////////////////////
  // uart clk definition
  //////////////////////////////////////////////////////////////////////
  typedef logic [7:0] uart_clk_precision_t;
  parameter int UART_CLK_HZ = 115200;
  parameter int CPU_CLK_HZ = 100000000;
  parameter uart_clk_precision_t CPU_CLK_DIV = CPU_CLK_HZ / UART_CLK_HZ;


  //////////////////////////////////////////////////////////////////////
  // state definition
  //////////////////////////////////////////////////////////////////////
  typedef enum logic [3:0] {
    INITIALIZING,
    NORMAL,
    WAIT_ACK,
    ERROR
  } noc_state_t;

  typedef enum logic [1:0] {
    TX_IDLE,
    TX_START_BIT,
    TX_DATA,
    TX_END_BIT
  } uart_tx_state_t;

  typedef enum logic [1:0] {
    RX_IDLE,
    RX_NOT_RECEIVING,
    RX_DATA,
    RX_END_BIT
  } uart_rx_state_t;

  //////////////////////////////////////////////////////////////////////
  // signal definition
  //////////////////////////////////////////////////////////////////////
  typedef enum logic [31:0] {
    NO_ERROR = 0,
    RX_BUFFER_OVERFLOW = 1 << 0,
    TX_NOT_REACHABLE = 1 << 1,

    // fatal error
    GENERAL_FATAL_ERROR = 1 << 31
  } signal_t;


  //////////////////////////////////////////////////////////////////////
  // flit definition
  //////////////////////////////////////////////////////////////////////

  parameter int FLIT_WIDTH = 128;
  typedef enum logic [3:0] {
    HEAD,
    BODY,
    TAIL,
    NOPE
  } flit_type_t;
  typedef logic [7:0] node_id_t;
  typedef struct packed {
    logic [7:0] packet_id;
    logic [7:0] flit_num;
  } flit_id_t;
  typedef struct packed {
    logic [3:0] version;   // 4 bits
    flit_type_t flittype;  // 4 bits
    node_id_t   src_id;    // 8 bits
    node_id_t   dst_id;    // 8 bits
    flit_id_t   flit_id;   // 16 bits
  } flit_header_t;
  // flit_header_t == 40

  // flit payload 72 bits
  typedef enum logic [11:0] {
    H_ACK = 0,
    H_NORMAL = 1
  } message_header_t;
  typedef struct packed {
    node_id_t global_src_id;  // 8 bits
    node_id_t global_dst_id;  // 8 bits
    logic [7:0] length;  // 8 bits
    logic [7:0] vc;  // 8 bits
    message_header_t header;  // 12 bits
    logic [3:0] option_flag;  // 4 bits
    logic [23:0] options;  // 24 bits
  } head_t;
  typedef struct packed {
    logic [71:0] data;  // 72 bits
  } body_t;
  typedef struct packed {
    logic [71:0] data;  // 72 bits
  } tail_t;
  typedef struct packed {
    logic [71:0] undefined;  // 72 bits
  } nope_t;
  typedef union packed {
    head_t head;
    body_t body;
    tail_t tail;
    nope_t nope;
  } flit_payload_t;

  // checksum 16 bits
  typedef logic [15:0] checksum_t;

  // flit 128 bits = 40 + 72 + 16
  typedef struct packed {
    // header = 40 bits
    flit_header_t header;

    // body = 72 bits
    flit_payload_t payload;

    // チェックサムが大きいのは衝突が頻繁に起こるため
    checksum_t checksum;  // 16 bits
  } flit_t;

  //////////////////////////////////////////////////////////////////////
  // buffer definition
  //////////////////////////////////////////////////////////////////////
  parameter int NUM_ENTRIES = 8;
  typedef enum logic [1:0] {
    EMPTY,  // head == tail
    VACANT,  // head != tail && tail != head + 1
    ALMOST_FULL,  // tail == head + 1
    FULL  // head == tail
  } buffer_state_t;
  typedef struct packed {
    logic [$clog2(NUM_ENTRIES)-1:0] head_index;
    logic [$clog2(NUM_ENTRIES)-1:0] tail_index;
    flit_t [NUM_ENTRIES-1:0] flit_buffer;
    buffer_state_t state;
  } flit_buffer_t;
endpackage
`endif
