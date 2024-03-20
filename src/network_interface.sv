// ホストからデータをmessage_bufferを通じて受取る。
// message_bufferはパケットの配列である
//

module network_interface(
    input logic clk,
    input logic reset,
    input packet_t message_buffer_top,
    input logic packet_valid,

    output bit busy,
    output flit_t flit
);

endmodule
