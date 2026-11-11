// Counter unit k (SPEC 6.1): V (16 bits). Write group CNTk.{LO,HI,DEC}. Z = (V == 0).
`timescale 1ns/1ps
`default_nettype none
module md_counter (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        we,
    input  wire [1:0]  sel,      // 0 LO, 1 HI, 2 DEC
    input  wire [7:0]  d,
    output reg  [15:0] v,
    output wire        z
);
    always @(posedge clk) begin
        if (!rst_n) begin
            v <= 16'd0;
        end else if (we) begin
            if (sel == 2'd0) v[7:0]  <= d;
            if (sel == 2'd1) v[15:8] <= d;
            if (sel[1])      v <= (v != 16'd0) ? v - 16'd1 : 16'd0;
        end
    end
    assign z = (v == 16'd0);
endmodule
`default_nettype wire
