`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_packet_buffer;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    // input
    types::flit_t next_flit;
    logic next_flit_valid;

    logic transfered_packet_completed;

    // output
    logic next_flit_ready;
    packet_types::packet_element_t transfered_packet;
    logic transfered_packet_valid;

    packet_buffer #(
        .PACKET_BUFFER_NUM_ENTRIES(8)
    ) tb_packet_buffer (
        .nocclk(clk),
        .rst_n(rst_n),

        .next_flit(next_flit),
        .next_flit_valid(next_flit_valid),
        .next_flit_ready(next_flit_ready),

        .transfered_packet_completed(transfered_packet_completed),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid)
    );

    // expected
    logic expected_next_flit_ready;
    packet_types::packet_element_t expected_transfered_packet;
    logic expected_transfered_packet_valid;

    task automatic __packet_element_t_compare(packet_types::packet_element_t a, packet_types::packet_element_t b, string file = `__FILE__, int line = `__LINE__);
        `TEST_EXPECTED(a.is_complete, b.is_complete, "is_complete", file, line);
        `TEST_EXPECTED(a.packet_id, b.packet_id, "packet_id", file, line);
        `TEST_EXPECTED(a.timer, b.timer, "timer", file, line);
        `TEST_EXPECTED(a.tail_index, b.tail_index, "tail_index", file, line);
        for (int i = 0; i < 8; i++) begin
            `TEST_EXPECTED(a.buffer[i], b.buffer[i], $sformatf("buffer[%0d]", i), file, line);
        end
    endtask

    task automatic __local_test(string file, int line);
        #1
        `TEST_EXPECTED(expected_next_flit_ready, next_flit_ready, "next_flit_ready", file, line);
        `TEST_EXPECTED(expected_transfered_packet_valid, transfered_packet_valid, "transfered_packet_valid", file, line);
        if (expected_transfered_packet_valid & transfered_packet_valid) begin
            __packet_element_t_compare(expected_transfered_packet, transfered_packet, file, line);
        end
        #1;
    endtask

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    initial begin
        `TEST_START("tb_packet_buffer.log")
        $dumpfile("tb_packet_buffer.vcd");
        $dumpvars(0, tb_packet_buffer);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        next_flit = 0;
        next_flit_valid = 0;
        transfered_packet_completed = 0;

        next_flit.header.flittype = types::HEAD;
        next_flit.header.flit_id.flit_num = 0;
        next_flit.header.flit_id.packet_id = 0;
        next_flit_valid = 1;

        wait_1clk();
        expected_next_flit_ready = 1;
        expected_transfered_packet_valid = 0;
        expected_transfered_packet.buffer[0] = next_flit;
        `LOCAL_TEST();

        next_flit.header.flittype = types::BODY;
        next_flit.header.flit_id.flit_num = 1;
        next_flit.header.flit_id.packet_id = 0;
        next_flit_valid = 1;

        wait_1clk();
        expected_next_flit_ready = 1;
        expected_transfered_packet_valid = 0;
        expected_transfered_packet.buffer[1] = next_flit;
        `LOCAL_TEST();

        next_flit.header.flittype = types::TAIL;
        next_flit.header.flit_id.flit_num = 2;
        next_flit.header.flit_id.packet_id = 0;
        next_flit_valid = 1;

        wait_1clk();
        next_flit_valid = 0;
        expected_next_flit_ready = 1;
        expected_transfered_packet_valid = 1;
        expected_transfered_packet.is_complete = 1;
        expected_transfered_packet.packet_id = 0;
        expected_transfered_packet.timer = 0;
        expected_transfered_packet.tail_index = 3;
        expected_transfered_packet.buffer[2] = next_flit;
        `LOCAL_TEST();

        repeat (10) wait_1clk();
        // 引き出さなければ、次のパケットが入っても、transfered_packetは変わらない
        `LOCAL_TEST();

        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
