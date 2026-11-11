// Accumulator unit (SPEC 6.1): A, Z, C, N and scratch registers R0..R(NR-1).
// Write groups: ACC.* (one group, seven ops) and each Rk.
`timescale 1ns/1ps
`default_nettype none
module md_acc #(
    parameter integer NR = 4
) (
    input  wire          clk,
    input  wire          rst_n,
    input  wire          we,
    input  wire [2:0]    sel,     // 0 LD, 1 ADD, 2 SUB, 3 AND, 4 OR, 5 XOR, 6 CMP (md_movebus)
    input  wire [7:0]    d,
    input  wire [NR-1:0] r_we,
    input  wire [8*NR-1:0] r_d,
    output reg  [7:0]    a,
    output reg           z,
    output reg           c,
    output reg           n,
    output reg  [8*NR-1:0] r
);
    reg [8:0] sum;
    reg [7:0] res;
    reg       cy;
    reg       wa;   // op writes A
    reg       wc;   // op writes C
    always @* begin
        sum = {1'b0, a} + {1'b0, d};
        res = d;
        cy  = c;
        wa  = 1'b1;
        wc  = 1'b0;
        case (sel)
            3'd0:      res = d;
            3'd1: begin res = sum[7:0]; cy = sum[8]; wc = 1'b1; end
            3'd2: begin res = a - d; cy = (a >= d); wc = 1'b1; end
            3'd3: res = a & d;
            3'd4: res = a | d;
            3'd5: res = a ^ d;
            3'd6: begin res = a - d; cy = (a >= d); wc = 1'b1; wa = 1'b0; end
            default:   wa = 1'b0;
        endcase
    end
    integer k;
    always @(posedge clk) begin
        if (!rst_n) begin
            a <= 8'd0;
            z <= 1'b0;
            c <= 1'b0;
            n <= 1'b0;
            r <= {8*NR{1'b0}};
        end else begin
            if (we) begin
                if (wa) a <= res;
                if (wc) c <= cy;
                z <= (res == 8'd0);
                n <= res[7];
            end
            for (k = 0; k < NR; k = k + 1)
                if (r_we[k]) r[8*k +: 8] <= r_d[8*k +: 8];
        end
    end
endmodule
`default_nettype wire
