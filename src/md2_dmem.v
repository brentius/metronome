// Metronome v2: 512 x 32 (2 KB) data memory, one port, synchronous read (word at rd in the cycle after a read;
// rd holds until the next read). Writes use a byte mask `be` over the four lanes; a write takes priority over a read.
// USE_IHP_SRAM: the IHP macro RM_IHPSG13_1P_512x32_c2_bm_bist as instance u_sram (MACROS in src/config.json).
// Otherwise a behavioural array with the same timing.
`timescale 1ns/1ps
`default_nettype none
module md2_dmem (
    input  wire        clk,
    input  wire        ren,
    input  wire        we,
    input  wire [8:0]  addr,
    input  wire [3:0]  be,      // byte-lane enables of a write
    input  wire [31:0] wd,
    output wire [31:0] rd
);
    wire [31:0] bm = {{8{be[3]}}, {8{be[2]}}, {8{be[1]}}, {8{be[0]}}};
`ifdef USE_IHP_SRAM
    RM_IHPSG13_1P_512x32_c2_bm_bist u_sram (
        .A_CLK(clk), .A_MEN(ren | we), .A_WEN(we), .A_REN(ren & ~we), .A_ADDR(addr), .A_DIN(wd),
        .A_DLY(1'b1), .A_DOUT(rd), .A_BM(bm),
        .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0), .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0),
        .A_BIST_ADDR(9'd0), .A_BIST_DIN(32'd0), .A_BIST_BM(32'd0)
    );
`else
    reg [31:0] mem [0:511];
    reg [31:0] q;
`ifndef SYNTHESIS
    integer i;
    initial begin
        for (i = 0; i < 512; i = i + 1) mem[i] = 32'd0;
        q = 32'd0;
    end
`endif
    always @(posedge clk) begin
        if (we)       mem[addr] <= (mem[addr] & ~bm) | (wd & bm);
        else if (ren) q <= mem[addr];
    end
    assign rd = q;
`endif
endmodule
`default_nettype wire
