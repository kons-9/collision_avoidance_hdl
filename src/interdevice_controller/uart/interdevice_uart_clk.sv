module interdevice_uart_clk (
    input logic clk,
    input logic rst_n,

    output logic uart_clk_out
);

    types::uart_clk_precisision_t _uart_clk;

    always_comb begin
        uart_clk_out = _uart_clk == 0;
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            _uart_clk <= 1;
        end
    end

    // uart_clk
    always_ff @(posedge clk) begin
        // cnt >= CPU_CLK_HZ / UART_CLK_HZ
        // 100000000 / 115200 = 868.0555555555556
        if (_uart_clk == types::CPU_CLK_DIV) begin
            _uart_clk <= 0;
        end else begin
            _uart_clk <= _uart_clk + 1;
        end
    end

endmodule
