// FORMAL-ONLY replacement for src/md2_cfg_bank.v (same module name and ports; the build lists this file instead).
// PRELOAD EQUIVALENCE ASSUMPTION: after the host has written the image's configuration bytes (SPEC_V2 1: visible from
// W+2) the latch bank outputs exactly `CFG_IMG & MASK` and nothing writes it again. Here q is that constant once
// the bank's own reset chain (identical to md2_cfg_bank: rst_s = rst_n delayed 2 flops, async clear) has released.
// The host write port is ignored: the image contains no configuration write after RUN, so the latch write path
// (gate-level verified separately) is not part of this proof.
`default_nettype none
module md2_cfg_bank #(
    parameter integer      BYTES = 8,
    parameter [8*BYTES-1:0] MASK = {8*BYTES{1'b1}},
    parameter integer      AW    = 9
) (
    input  wire               clk,
    input  wire               rst_n,
    input  wire               we,
    input  wire [AW-1:0]      waddr,
    input  wire [7:0]         wdata,
    output wire [8*BYTES-1:0] q
);
    `include "fv_cfg_img.vh"
    reg rst_m, rst_s;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin rst_m <= 1'b0; rst_s <= 1'b0; end
        else        begin rst_m <= 1'b1; rst_s <= rst_m; end
    end
    assign q = rst_s ? (CFG_IMG & MASK) : {8*BYTES{1'b0}};
endmodule
`default_nettype wire
