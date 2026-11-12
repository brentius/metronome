// Metronome v2: 256 x 64 program memory of one core, one port, synchronous read (address registered at the clock
// edge, word at rd in the next cycle; rd holds until the next read). Byte-lane writes from the host (one byte per
// write, replicated to all lanes and selected by `be`); a write cycle takes priority over a read.
// USE_IHP_SRAM: the IHP macro RM_IHPSG13_1P_256x64_c2_bm_bist as instance u_sram (MACROS in src/config.json).
// Otherwise a behavioural array with the same timing.
`timescale 1ns/1ps
`default_nettype none
module md2_pmem (
    input  wire        clk,
    input  wire        ren,
    input  wire        we,
    input  wire [7:0]  addr,
    input  wire [7:0]  be,      // byte-lane enables of a write
    input  wire [7:0]  wd,      // write byte (all lanes)
    output wire [63:0] rd
);
    wire [63:0] bm = {{8{be[7]}}, {8{be[6]}}, {8{be[5]}}, {8{be[4]}}, {8{be[3]}}, {8{be[2]}}, {8{be[1]}}, {8{be[0]}}};
`ifdef USE_IHP_SRAM
    RM_IHPSG13_1P_256x64_c2_bm_bist u_sram (
        .A_CLK(clk), .A_MEN(ren | we), .A_WEN(we), .A_REN(ren & ~we), .A_ADDR(addr), .A_DIN({8{wd}}),
        .A_DLY(1'b1), .A_DOUT(rd), .A_BM(bm),
        .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0), .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0),
        .A_BIST_ADDR(8'd0), .A_BIST_DIN(64'd0), .A_BIST_BM(64'd0)
    );
`else
    reg [63:0] mem [0:255];
    reg [63:0] q;
`ifndef SYNTHESIS
    integer i;
    initial begin
        for (i = 0; i < 256; i = i + 1) mem[i] = 64'd0;
        q = 64'd0;
    end
`endif
    always @(posedge clk) begin
        if (we)       mem[addr] <= (mem[addr] & ~bm) | ({8{wd}} & bm);
        else if (ren) q <= mem[addr];
    end
    assign rd = q;
`endif
endmodule
`default_nettype wire
