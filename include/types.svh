`ifndef TYPES_SVH
`define TYPES_SVH
`include "system_types.svh"
`include "primitive_types.svh"
package types;
    typedef primitive_types::node_id_t node_id_t;
    typedef primitive_types::packet_id_t packet_id_t;
    typedef primitive_types::flit_num_t flit_num_t;
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
        SYSTEM
    } flit_type_t;
    typedef struct packed {
        packet_id_t packet_id;
        flit_num_t  flit_num;
    } flit_id_t;
    typedef struct packed {
        logic [2:0] version;  // 3 bits
        logic is_ack;  // 1 bit
        flit_type_t flittype;  // 4 bits
        node_id_t src_id;  // 8 bits
        node_id_t dst_id;  // 8 bits
        flit_id_t flit_id;  // 16 bits
    } flit_header_t;
    // flit_header_t == 40

    // flit payload 72 bits
    typedef enum logic [11:0] {
        H_NORMAL = 0,
        H_SYSTEM = 1
        // user defined
    } message_header_t;
    typedef struct packed {
        node_id_t global_src_id;  // 8 bits
        node_id_t global_dst_id;  // 8 bits
        flit_num_t length;  // 8 bits
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
        system_types::system_header_t header;  // 16 bits
        system_types::system_payload_t payload;  // 56 bits
    } system_t;
    typedef union packed {
        head_t head;
        body_t body;
        tail_t tail;
        system_t system;
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

    parameter int FLIT_NUM_WIDTH = 8;
    parameter node_id_t BROADCAST_ID = ((1 << $bits(node_id_t)) - 1);
endpackage
`endif
