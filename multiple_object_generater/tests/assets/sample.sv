module sample(
    input logic clk,
    input logic rst_n
);

    logic [7:0] timer;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            timer <= 0;
        end else if (timer < 200) begin
            timer <= timer + 1;
        end
    end

    logic nic0_rx, nic0_tx;
    nic nic0(
        .rx(nic0_rx),
        .tx(nic0_tx)
    );

    logic nic1_rx, nic1_tx;
    nic nic1(
        .rx(nic1_rx),
        .tx(nic1_tx)
    );

    logic nic2_rx, nic2_tx;
    nic nic2(
        .rx(nic2_rx),
        .tx(nic2_tx)
    );

    logic nic3_rx, nic3_tx;
    nic nic3(
        .rx(nic3_rx),
        .tx(nic3_tx)
    );

    always_comb begin
        if (0) begin
            // dummy
            nic0_tx = 0;
            nic1_tx = 0;
            nic2_tx = 0;
            nic3_tx = 0;
        end else if (timer < 100) begin
            nic0_rx = nic0_tx | nic1_tx | nic2_tx | nic3_tx;
            nic1_rx = nic0_tx | nic1_tx
            nic2_rx = nic0_tx | nic2_tx;
            nic3_rx = nic0_tx | nic3_tx;
        end else if(timer < 200) begin
            nic0_rx = nic0_tx | nic1_tx | nic2_tx;
            nic1_rx = nic0_tx | nic1_tx | nic3_tx;
            nic2_rx = nic0_tx | nic2_tx | nic3_tx;
            nic3_rx = nic1_tx | nic2_tx | nic3_tx;
        end else begin
            nic0_rx = 0;
            nic1_rx = 0;
            nic2_rx = 0;
            nic3_rx = 0;
        end
    end

endmodule
