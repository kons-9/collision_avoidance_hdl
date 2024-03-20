module tb_top ();
    logic clk, rst_n;

    always begin
        clk = 0;
        #10;
        clk = 1;
        #10;
    end

    initial begin

    end

endmodule
