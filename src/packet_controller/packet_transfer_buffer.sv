`include "types.svh"
`include "packet_types.svh"

// 完了したパケットの送信を担当する
module packet_transfer_buffer (
    input logic nocclk,
    input logic rst_n,

    input packet_types::packet_element_t transfered_packet,
    input logic transfered_packet_valid,
    // 転送が完了したら、indexをfreeするために使う
    // 1clkで消費される
    output logic transfered_packet_completed,

    input packet_types::packet_element_t cpu_transfered_packet,
    input logic cpu_transfered_packet_valid,
    output logic cpu_transfered_packet_completed,

    input logic transfered_flit_ready,
    output logic transfered_flit_valid,
    output types::flit_t transfered_flit,
    output types::flit_t transfered_head_flit,
    output is_flit_from_cpu
);
    // TODO: timeout制御必要かな？
    //
    typedef enum logic [1:0] {
        IDLE,
        SENDING_PACKET,
        SENDING_CPU_TRANSFERED_PACKET
    } state_t;
    state_t state;

    types::flit_num_t current_flit_num;
    types::flit_num_t next_flit_num;
    logic is_end_of_packet;
    always_comb begin
        next_flit_num = current_flit_num + 1;
        is_end_of_packet = 0;
        cpu_transfered_packet_completed = 0;
        transfered_packet_completed = 0;
        transfered_flit_valid = 0;
        transfered_flit = 0;
        transfered_head_flit = 0;
        is_flit_from_cpu = 0;
        case (state)
            SENDING_PACKET: begin
                is_end_of_packet = transfered_packet.tail_index == next_flit_num;
                cpu_transfered_packet_completed = 0;
                transfered_packet_completed = is_end_of_packet & transfered_packet_valid;
                transfered_flit_valid = transfered_packet_valid && (transfered_packet.tail_index > current_flit_num);
                transfered_flit = transfered_packet.buffer[current_flit_num];
                transfered_head_flit = transfered_packet.buffer[0];
            end
            SENDING_CPU_TRANSFERED_PACKET: begin
                is_end_of_packet = cpu_transfered_packet.tail_index == next_flit_num;
                cpu_transfered_packet_completed = is_end_of_packet & cpu_transfered_packet_valid;
                transfered_packet_completed = 0;
                transfered_flit_valid = cpu_transfered_packet_valid && (cpu_transfered_packet.tail_index > current_flit_num);
                transfered_flit = cpu_transfered_packet.buffer[current_flit_num];
                transfered_head_flit = cpu_transfered_packet.buffer[0];
                is_flit_from_cpu = 1;
            end
            default: begin
            end
        endcase
    end
    // update counter
    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            current_flit_num <= 0;
        end else begin
            case (state)
                IDLE: begin
                    current_flit_num <= 0;
                end
                SENDING_PACKET: begin
                    if (transfered_flit_ready & transfered_flit_valid) begin
                        if (is_end_of_packet) begin
                            current_flit_num <= 0;
                        end else begin
                            current_flit_num <= next_flit_num;
                        end
                    end
                end
                SENDING_CPU_TRANSFERED_PACKET: begin
                    if (transfered_flit_ready & transfered_flit_valid) begin
                        current_flit_num <= next_flit_num;
                        if (is_end_of_packet) begin
                            current_flit_num <= 0;
                        end else begin
                            current_flit_num <= next_flit_num;
                        end
                    end
                end
                default: begin
                end
            endcase
        end
    end

    // update state
    always_ff @(posedge nocclk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            case (state)
                IDLE: begin
                    // 優先度はtransfered_packet
                    if (transfered_packet_valid) begin
                        state <= SENDING_PACKET;
                    end else if (cpu_transfered_packet_valid) begin
                        state <= SENDING_CPU_TRANSFERED_PACKET;
                    end
                end
                SENDING_PACKET: begin
                    if (is_end_of_packet) begin
                        state <= IDLE;
                    end
                end
                SENDING_CPU_TRANSFERED_PACKET: begin
                    if (is_end_of_packet) begin
                        state <= IDLE;
                    end
                end
                default: begin
                    state <= IDLE;
                end
            endcase
        end
    end


endmodule
