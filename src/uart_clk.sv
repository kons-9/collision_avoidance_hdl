module uart_clk (
    input logic clk,
    input logic rst_n,

    output logic uart_clk_out
);


  parameter UART_CLK_HZ = 115200;
  parameter CPU_CLK_HZ = 100000000;
  parameter CPU_CLK_DIV = CPU_CLK_HZ / UART_CLK_HZ;

  logic [7:0] _uart_clk;

  assign uart_clk_out = _uart_clk == 0;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      _uart_clk <= 1;
    end
  end

  // uart_clk
  always_ff @(posedge clk) begin
    // cnt >= CPU_CLK_HZ / UART_CLK_HZ
    // 100000000 / 115200 = 868.0555555555556
    if (_uart_clk == CPU_CLK_DIV) begin
      _uart_clk <= 0;
    end else begin
      _uart_clk <= _uart_clk + 1;
    end
  end

endmodule
