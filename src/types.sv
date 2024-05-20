package types;

  typedef enum logic [31:0] {
    NO_ERROR = 0,
    RX_BUFFER_OVERFLOW = 1 << 0,
    TX_NOT_REACHABLE = 1 << 1,

    // fatal error
    GENERAL_FATAL_ERROR = 1 << 32
  } signal_t;

  // buffer.next_push_index == buffer.next_pop_indexのとき、実際にはfullまたはemptyのどちらかである
  // そこで、empty を buffer.next_push_index == buffer.next_pop_index と定義する
  // full を buffer.next_push_index == buffer.next_pop_index + 1 と定義する.
  // これは一見無駄のように見えるが、fullとtriggerが同時に立ったとき、overflowを防ぐために必要である
  typedef enum logic [1:0] {
    EMPTY,
    VACANT,
    FULL,
    OVERFULL
  } state_t;

  typedef struct packed {
    logic [$clog2(NUM_ENTRIES)-1:0] push_index;  // max index is next_pop_index-1
    logic [$clog2(NUM_ENTRIES)-1:0] pop_index;
    // data buffer queue
    logic [FLIT_WIDTH-1:0] data_buffer[NUM_ENTRIES];
    state_t state;
  } buffer_t;

  typedef enum logic [3:0] {
    HEAD,
    BODY,
    TAIL
  } flit_type_t;

  // checksum 16 bits// che
  typedef logic [15:0] checksum_t;

  // flit 128 bits = 4 + 4 + 8 + 96 + 16
  typedef struct packed {
    logic [3:0] version;   // 4 bits
    flit_type_t flittype;  // 4 bits
    logic [7:0] flit_id;   // 8 bits

    union packed {
      struct packed {
        logic [15:0] src;
        logic [15:0] dst;
        logic [15:0] length;
        logic [15:0] header;
        logic [15:0] vc;
        logic [15:0] options;
      } head;
      struct packed {logic [95:0] data;} body;
      struct packed {logic [95:0] data;} tail;
      struct packed {logic [95:0] undefined;} nope;
    } data;  // 96 bits
    // チェックサムが大きいのは衝突が頻繁に起こるため
    checksum_t checksum;  // 16 bits
  } flit_t;

  // packet

  typedef struct packed {
    logic [7:0]  version;
    logic [7:0]  headlength;    // fixed 20
    logic [7:0]  p_priority;    // packet priority, now ignore
    logic [15:0] packetid;
    logic [15:0] src;
    logic [15:0] dst;
    logic [7:0]  flag;
    logic [7:0]  fragment;
    logic [15:0] headchecksum;
    logic [7:0]  protocol;
    logic [15:0] option;
  } packet_header_t;  // 16 * 8 = 128 bits

  parameter logic [2:0] UART_DATA_IND_MAX = 7;
  typedef logic [UART_DATA_IND_MAX:0] uart_data_t;
endpackage
