// Metronome v1 input synchronisers (SPEC 2): s1' = raw, s2' = s1, sp' = s2.
// PIN = s2, RISE = s2 & !sp, FALL = !s2 & sp.
`timescale 1ns/1ps
`default_nettype none
module md_sync #(
    parameter integer N = 16
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire [N-1:0] raw,
    output wire [N-1:0] lvl,
    output wire [N-1:0] rise,
    output wire [N-1:0] fall
);
    reg [N-1:0] s1, s2, sp;
    always @(posedge clk) begin
        if (!rst_n) begin
            s1 <= {N{1'b0}};
            s2 <= {N{1'b0}};
            sp <= {N{1'b0}};
        end else begin
            s1 <= raw;
            s2 <= s1;
            sp <= s2;
        end
    end
    assign lvl  = s2;
    assign rise = s2 & ~sp;
    assign fall = ~s2 & sp;
endmodule
`default_nettype wire
