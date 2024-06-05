module led (
    input  clk,
    output led[4]
);

    logic [26:0] counter;

    assign led[0] = counter[26];
    assign led[1] = counter[25];
    assign led[2] = counter[24];
    assign led[3] = counter[23];

    always @(posedge clk) begin
        counter <= counter + 1;
    end

endmodule
