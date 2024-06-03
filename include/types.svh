`ifndef TYPES_SVH
`define TYPES_SVH
package types;
  //////////////////////////////////////////////////////////////////////
  // noc configuration
  //////////////////////////////////////////////////////////////////////

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
  typedef logic [7:0] packet_id_t;
  typedef struct packed {
    packet_id_t packet_id;
    logic [7:0] flit_num;
  } flit_id_t;
  typedef struct packed {
    logic [2:0] version;   // 3 bits
    logic is_ack;  // 1 bit
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
  // packet buffer
  //////////////////////////////////////////////////////////////////////
  parameter int PACKET_BUFFER_NUM_ENTRIES = 8;
  parameter int NUM_ENTRIES = 8;

  typedef struct packed {
    logic valid_state;
    packet_id_t packet_id;
    logic [$clog2(PACKET_BUFFER_NUM_ENTRIES)-1:0] index;
  } packet_key_t;

  typedef struct packed {
    logic is_completed;
    flit_t [NUM_ENTRIES-1:0] buffer;
  } packet_element_t;

  typedef struct packed {
    packet_key_t [PACKET_BUFFER_NUM_ENTRIES-1:0] packet_key;
    packet_element_t [PACKET_BUFFER_NUM_ENTRIES-1:0] packet_element;
  } packet_buffer_t;

endpackage
`endif
