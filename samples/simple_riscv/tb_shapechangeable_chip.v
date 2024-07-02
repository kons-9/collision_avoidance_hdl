module tb_shapechangeable_chip ();

    reg clk;
    reg rst_n;

    dummy_top dummy_top_inst (
        .clk(clk),
        .rst_n(rst_n)
    );

    always begin
        #5 clk = ~clk;
    end

    initial begin
        clk = 0;
        rst_n = 0;
        #10 rst_n = 1;
        repeat(1000) begin
            #10;
        end
        #1000 $finish;
    end
endmodule
