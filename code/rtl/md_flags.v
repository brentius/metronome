// Flags unit (SPEC 6.1): F[15:0], FP' = F every cycle. One write group FLAGS.{SET,CLR} (sel 0 SET, 1 CLR),
// flag number = bus[3:0].
`timescale 1ns/1ps
`default_nettype none
module md_flags (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        we,
    input  wire        sel,
    input  wire [3:0]  d,
    output reg  [15:0] f,
    output wire [15:0] f_rise
);
    reg [15:0] fp;
    always @(posedge clk) begin
        if (!rst_n) begin
            f  <= 16'd0;
            fp <= 16'd0;
        end else begin
            fp <= f;
            if (we) f[d] <= ~sel;
        end
    end
    assign f_rise = f & ~fp;
endmodule
`default_nettype wire
