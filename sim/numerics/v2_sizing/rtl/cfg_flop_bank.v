// cfg_flop_bank: flop-based equivalent of cfg_latch_bank (same interface, same 2-cycle write latency, same
// reset-release behaviour) for area comparison. Per-byte enable flops (dfrbpq with enable inferred normally).
module cfg_flop_bank #(parameter BYTES = 8, localparam AW = (BYTES > 2) ? $clog2(BYTES) : 1) (
    input                          clk,
    input                          rst_n,
    input                          we,
    input  [AW-1:0]                waddr,
    input  [7:0]                   wdata,
    output reg [8*BYTES-1:0]       q
);

    reg rst_m, rst_s;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rst_m <= 1'b0;
            rst_s <= 1'b0;
        end else begin
            rst_m <= 1'b1;
            rst_s <= rst_m;
        end
    end

    reg          we1;
    reg [AW-1:0] addr1;
    reg [7:0]    data1;
    always @(posedge clk or negedge rst_s) begin
        if (!rst_s) we1 <= 1'b0;
        else        we1 <= we;
    end
    always @(posedge clk) begin
        addr1 <= waddr;
        data1 <= wdata;
    end

    integer k;
    always @(posedge clk or negedge rst_s) begin
        if (!rst_s) q <= {8*BYTES{1'b0}};
        else for (k = 0; k < BYTES; k = k + 1)
            if (we1 && addr1 == k[AW-1:0]) q[8*k +: 8] <= data1;
    end
endmodule
