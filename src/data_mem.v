// Data memory: 2048 x 8 behaviour, one port, synchronous read (byte visible in the cycle after the access).
// Behavioural model by default; with `define USE_IHP_SRAM a 512 x 32 IHP macro with byte writes via the bit mask.
`timescale 1ns/1ps
`default_nettype none
module data_mem (
    input  wire        clk,
    input  wire        en,
    input  wire        we,
    input  wire [10:0] addr,
    input  wire [7:0]  wd,
    output wire [7:0]  rd
);
`ifdef USE_IHP_SRAM
    wire [31:0] dout;
    reg  [1:0]  lane_q;     // byte lane of the last read (memory-side pipeline register, not reset)
    always @(posedge clk) if (en & ~we) lane_q <= addr[1:0];
    RM_IHPSG13_1P_512x32_c2_bm_bist u_sram (
        .A_CLK(clk), .A_MEN(en), .A_WEN(we), .A_REN(en & ~we), .A_ADDR(addr[10:2]), .A_DIN({4{wd}}),
        .A_DLY(1'b1), .A_DOUT(dout), .A_BM(32'hFF << (8 * addr[1:0])),
        .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0), .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0),
        .A_BIST_ADDR(9'd0), .A_BIST_DIN(32'd0), .A_BIST_BM(32'd0)
    );
    assign rd = dout[8*lane_q +: 8];
`else
    reg [7:0] mem [0:2047];
    reg [7:0] q;
`ifndef SYNTHESIS
    integer i;
    initial begin
        for (i = 0; i < 2048; i = i + 1) mem[i] = 8'd0;
        q = 8'd0;
    end
`endif
    always @(posedge clk) begin
        if (en) begin
            if (we) mem[addr] <= wd;
            else    q <= mem[addr];
        end
    end
    assign rd = q;
`endif
endmodule
`default_nettype wire
