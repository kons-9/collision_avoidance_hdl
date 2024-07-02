module heartbeat_requester #(
    parameter int MAX_HEARTBEAT_REQUEST_TIMER = 100
) (
    input logic nocclk,
    input logic rst_n,
    input logic stall,

    input logic parent_valid,
    input types::node_id_t parent_node_id,

    input types::node_id_t incoming_flit_node_id,

    output logic is_heartbeat_request
);
    logic [$clog2(MAX_HEARTBEAT_REQUEST_TIMER)-1:0] heartbeat_request_timer;

    always_comb begin
        is_heartbeat_request = (heartbeat_request_timer == MAX_HEARTBEAT_REQUEST_TIMER) && parent_valid;
    end

    always_ff @(posedge nocclk) begin
        if (!rst_n) begin
            heartbeat_request_timer <= 0;
        end else begin
            if (incoming_flit_node_id == parent_node_id) begin
                heartbeat_request_timer <= 0;
            end else begin
                if (!stall) begin
                    heartbeat_request_timer <= heartbeat_request_timer + 1;
                end
            end
        end
    end
endmodule
