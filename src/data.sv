typedef enum logic [3:0] {
  HEAD,
  BODY,
  TAIL
} flit_type_t;

// flit 128 bits = 4 + 4 + 8 + 96 + 16
typedef struct packed {
  logic [3:0] version;  // 4 bits
  flit_type_t flittype;   // 4 bits
  logic[7:0] flit_id;     // 8 bits

  union packed {
    struct packed {
      logic[15:0] src;
      logic[15:0] dst;
      logic[15:0] length;
      logic[15:0] header;
      logic[15:0] vc;
      logic[15:0] options;
    } head;
    struct packed {
        logic[95:0] data;
    } body;
    struct packed {
        logic[95:0] data;
    } tail;
    struct packed {
        logic [95:0] undefined;
    } nope;
  } data; // 96 bits
  // チェックサムが大きいのは衝突が頻繁に起こるため
  logic [15:0] checksum;  // 16 bits
} flit_t;

// packet

typedef struct packed {
    logic [7:0] version;
    logic [7:0] headlength;// fixed 20
    logic [7:0] p_priority;// packet priority, now ignore
    logic [15:0] packetid;
    logic [15:0] src;
    logic [15:0] dst;
    logic [7:0] flag;
    logic [7:0] fragment;
    logic [15:0] headchecksum;
    logic [7:0] protocol;
    logic [15:0] option;
} packet_header_t; // 16 * 8 = 128 bits

parameter logic [2:0] UART_DATA_IND_MAX = 7;
typedef logic [UART_DATA_IND_MAX:0] uart_data_t;

