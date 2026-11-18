// Metronome v2 Accumulator unit (SPEC_V2 6.1, as SPEC v1 6.1; copied from v1 md_acc.v): A, Z, C, N and scratch registers R0..R(NR-1).
// Write groups: ACC.* (one group, seven ops) and each Rk.
// Timing restructure (2026-11-15): the ALU runs once per move slot (NM of them) on that move's own op and data,
// and the one-hot write-group hit selects the result. The register update is the same as selecting the
// winner's op and data first: hit is one-hot or zero, and A/C feed every slot's ALU unchanged.
`timescale 1ns/1ps
`default_nettype none
module md2_acc #(
    parameter integer NR = 4,
    parameter integer NM = 6
) (
    input  wire          clk,
    input  wire          rst_n,
    input  wire [NM-1:0]   hit,   // one-hot or zero: the move that writes ACC this cycle
    input  wire [3*NM-1:0] sel,   // per move: 0 LD, 1 ADD, 2 SUB, 3 AND, 4 OR, 5 XOR, 6 CMP (md_movebus)
    input  wire [8*NM-1:0] d,     // per move data
    input  wire [NR-1:0] r_we,
    input  wire [8*NR-1:0] r_d,
    output reg  [7:0]    a,
    output reg           z,
    output reg           c,
    output reg           n,
    output reg  [8*NR-1:0] r
);
    // {wa, wc, cy, z, n, res[7:0]}
    function [12:0] alu;
        input [7:0] a_i;
        input       c_i;
        input [2:0] s;
        input [7:0] dv;
        reg [8:0] sum;
        reg [7:0] res;
        reg       cy, wa, wc;
        begin
            sum = {1'b0, a_i} + {1'b0, dv};
            res = dv;
            cy  = c_i;
            wa  = 1'b1;
            wc  = 1'b0;
            case (s)
                3'd0:      res = dv;
                3'd1: begin res = sum[7:0]; cy = sum[8]; wc = 1'b1; end
                3'd2: begin res = a_i - dv; cy = (a_i >= dv); wc = 1'b1; end
                3'd3: res = a_i & dv;
                3'd4: res = a_i | dv;
                3'd5: res = a_i ^ dv;
                3'd6: begin res = a_i - dv; cy = (a_i >= dv); wc = 1'b1; wa = 1'b0; end
                default:   wa = 1'b0;
            endcase
            alu = {wa, wc, cy, (res == 8'd0), res[7], res};
        end
    endfunction

    reg [12:0] o;
    integer m;
    always @* begin
        o = 13'd0;
        for (m = 0; m < NM; m = m + 1)
            o = o | ({13{hit[m]}} & alu(a, c, sel[3*m +: 3], d[8*m +: 8]));
    end
    wire we = |hit;

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
                if (o[12]) a <= o[7:0];
                if (o[11]) c <= o[10];
                z <= o[9];
                n <= o[8];
            end
            for (k = 0; k < NR; k = k + 1)
                if (r_we[k]) r[8*k +: 8] <= r_d[8*k +: 8];
        end
    end
endmodule
`default_nettype wire
