// Metronome v2 sizing: 256 x 64 program memory, synchronous read (address registered at the clock edge, word
// visible in the next cycle). Behavioural model for simulation; black-boxed (read with -lib) for area.
// A write cycle takes priority over a read, as in src/prog_mem.v. Whole-word writes (the sizing bench only).
`timescale 1ns/1ps
`default_nettype none
module md2_core_pmem (
    input  wire        clk,
    input  wire        ren,
    input  wire        we,
    input  wire [7:0]  addr,
    input  wire [63:0] wd,
    output wire [63:0] rd
);
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
        if (we)       mem[addr] <= wd;
        else if (ren) q <= mem[addr];
    end
    assign rd = q;
endmodule
`default_nettype wire
