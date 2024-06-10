`include "types.svh"
`include "packet_types.svh"
`include "test_utils.svh"

import types::*;

module tb_packet_transfer_buffer;

    timeunit 10ps; timeprecision 10ps;

    // generate clk
    bit clk = 0;
    bit rst_n = 1;
    always begin
        #5 clk = ~clk;
    end

    task automatic wait_1clk();
        repeat (1) @(posedge clk);
        #1;
    endtask

    // input
    packet_types::packet_element_t transfered_packet;
    logic transfered_packet_valid;
    packet_types::packet_element_t cpu_transfered_packet;
    logic cpu_transfered_packet_valid;
    logic transfered_flit_ready;

    // output
    logic transfered_packet_completed;
    logic cpu_transfered_packet_completed;
    logic transfered_flit_valid;
    types::flit_t transfered_flit;
    types::flit_t transfered_head_flit;

    packet_transfer_buffer packet_transfer_buffer (
        .nocclk(clk),
        .rst_n(rst_n),
        .transfered_packet(transfered_packet),
        .transfered_packet_valid(transfered_packet_valid),
        .transfered_packet_completed(transfered_packet_completed),
        .cpu_transfered_packet(cpu_transfered_packet),
        .cpu_transfered_packet_valid(cpu_transfered_packet_valid),
        .cpu_transfered_packet_completed(cpu_transfered_packet_completed),

        .transfered_flit_ready(transfered_flit_ready),
        .transfered_flit_valid(transfered_flit_valid),
        .transfered_flit(transfered_flit),
        .transfered_head_flit(transfered_head_flit)
    );

    // expected
    logic expected_transfered_packet_completed;
    logic expected_cpu_transfered_packet_completed;
    logic expected_transfered_flit_valid;
    types::flit_t expected_transfered_flit;
    types::flit_t expected_transfered_head_flit;

    `define LOCAL_TEST(file = `__FILE__, line = `__LINE__) __local_test(file, line);

    task automatic __local_test(string file, int line);
        `TEST_EXPECTED(expected_transfered_flit_valid, transfered_flit_valid, "transfered_flit_valid", file, line);
        if (expected_transfered_flit_valid & transfered_flit_valid) begin
            `TEST_EXPECTED(expected_transfered_flit, transfered_flit, "transfered_flit", file, line);
            `TEST_EXPECTED(expected_transfered_head_flit, transfered_head_flit, "transfered_head_flit", file, line);
        end
        `TEST_EXPECTED(expected_transfered_packet_completed, transfered_packet_completed, "transfered_packet_completed", file, line);
        `TEST_EXPECTED(expected_cpu_transfered_packet_completed, cpu_transfered_packet_completed, "cpu_transfered_packet_completed", file, line);
    endtask

    task automatic reset_packet();
        transfered_packet.is_complete = 0;
        transfered_packet.packet_id = 0;
        transfered_packet.timer = 0;
        transfered_packet.tail_index = 0;
        foreach (transfered_packet.buffer[i]) begin
            transfered_packet.buffer[i] = 0;
        end
        cpu_transfered_packet.is_complete = 0;
        cpu_transfered_packet.packet_id = 0;
        cpu_transfered_packet.timer = 0;
        cpu_transfered_packet.tail_index = 0;
        foreach (cpu_transfered_packet.buffer[i]) begin
            cpu_transfered_packet.buffer[i] = 0;
        end
    endtask

    initial begin
        `TEST_START("tb_packet_transfer_buffer.log")
        $dumpfile("tb_packet_transfer_buffer.vcd");
        $dumpvars(0, tb_packet_transfer_buffer);
        wait_1clk();
        rst_n = 0;
        wait_1clk();
        rst_n = 1;

        // nothing
        reset_packet();
        transfered_packet_valid = 0;
        cpu_transfered_packet_valid = 0;
        transfered_flit_ready = 0;

        expected_transfered_flit_valid = 0;
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        wait_1clk();
        `LOCAL_TEST();

        // transfered_packet
        reset_packet();
        transfered_packet.buffer[0].header.flittype = types::HEAD;
        transfered_packet.buffer[0].header.flit_id.packet_id = 1;
        transfered_packet.buffer[1].header.flittype = types::BODY;
        transfered_packet.buffer[1].header.flit_id.packet_id = 1;
        transfered_packet.buffer[2].header.flittype = types::TAIL;
        transfered_packet.buffer[2].header.flit_id.packet_id = 1;
        transfered_packet.tail_index = 3;
        transfered_packet.packet_id = 1;
        transfered_packet.timer = 0;
        transfered_packet.is_complete = 1;
        transfered_packet_valid = 1;
        transfered_flit_ready = 1;

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[0];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[1];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 1;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[2];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        transfered_packet_valid = 0;
        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 0;
        `LOCAL_TEST();

        // cpu_transfered_packet
        reset_packet();
        cpu_transfered_packet.buffer[0].header.flittype = types::HEAD;
        cpu_transfered_packet.buffer[0].header.flit_id.packet_id = 2;
        cpu_transfered_packet.buffer[1].header.flittype = types::BODY;
        cpu_transfered_packet.buffer[1].header.flit_id.packet_id = 2;
        cpu_transfered_packet.buffer[2].header.flittype = types::TAIL;
        cpu_transfered_packet.buffer[2].header.flit_id.packet_id = 2;
        cpu_transfered_packet.tail_index = 3;
        cpu_transfered_packet.packet_id = 2;
        cpu_transfered_packet.timer = 0;
        cpu_transfered_packet.is_complete = 1;
        cpu_transfered_packet_valid = 1;
        transfered_flit_ready = 1;

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[0];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[1];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_cpu_transfered_packet_completed = 1;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[2];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        cpu_transfered_packet_valid = 0;
        wait_1clk();
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 0;
        `LOCAL_TEST();

        // both
        reset_packet();
        transfered_packet.buffer[0].header.flittype = types::HEAD;
        transfered_packet.buffer[0].header.flit_id.packet_id = 1;
        transfered_packet.buffer[1].header.flittype = types::BODY;
        transfered_packet.buffer[1].header.flit_id.packet_id = 1;
        transfered_packet.buffer[2].header.flittype = types::TAIL;
        transfered_packet.buffer[2].header.flit_id.packet_id = 1;
        transfered_packet.tail_index = 3;
        transfered_packet.packet_id = 1;
        transfered_packet.timer = 0;
        transfered_packet.is_complete = 1;
        transfered_packet_valid = 1;
        cpu_transfered_packet.buffer[0].header.flittype = types::HEAD;
        cpu_transfered_packet.buffer[0].header.flit_id.packet_id = 2;
        cpu_transfered_packet.buffer[1].header.flittype = types::BODY;
        cpu_transfered_packet.buffer[1].header.flit_id.packet_id = 2;
        cpu_transfered_packet.buffer[2].header.flittype = types::TAIL;
        cpu_transfered_packet.buffer[2].header.flit_id.packet_id = 2;
        cpu_transfered_packet.tail_index = 3;
        cpu_transfered_packet.packet_id = 2;
        cpu_transfered_packet.timer = 0;
        cpu_transfered_packet.is_complete = 1;
        cpu_transfered_packet_valid = 1;
        transfered_flit_ready = 1;

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[0];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[1];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 1;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = transfered_packet.buffer[2];
        expected_transfered_head_flit = transfered_packet.buffer[0];
        `LOCAL_TEST();

        transfered_packet_valid = 0;

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 0;
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[0];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[1];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 1;
        expected_transfered_flit_valid = 1;
        expected_transfered_flit = cpu_transfered_packet.buffer[2];
        expected_transfered_head_flit = cpu_transfered_packet.buffer[0];
        `LOCAL_TEST();

        cpu_transfered_packet_valid = 0;
        wait_1clk();
        expected_transfered_packet_completed = 0;
        expected_cpu_transfered_packet_completed = 0;
        expected_transfered_flit_valid = 0;
        `LOCAL_TEST();


        repeat (10) wait_1clk();

        `TEST_RESULT
        $finish(0);
    end

endmodule
