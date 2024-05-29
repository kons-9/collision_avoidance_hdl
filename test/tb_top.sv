
`include "types.svh"
module tb_top ();
    import types::flit_t;
    logic clk, rst_n;

    always begin
        clk = 0;
        #10;
        clk = 1;
        #10;
    end
    types::checksum_t flit_checksum;
    types::flit_t flit;

    initial begin
        $display("hello tb_top");
        flit_checksum = 0;
        flit = 0;
        @(posedge clk);
        $finish;
    end

endmodule
