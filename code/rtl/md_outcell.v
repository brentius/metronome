// Output cell o (SPEC 8): idx = {SEG of ENG's beat generator, COMMITTED of ENG} (0 when unbound);
// OUT' = LUT[idx], OEN' = OE[idx] (cells with HAS_OE only). The pin outputs are these registers.
`timescale 1ns/1ps
`default_nettype none
module md_outcell #(
    parameter integer NE     = 6,
    parameter integer HAS_OE = 1
) (
    input  wire            clk,
    input  wire            rst_n,
    input  wire            h_we,
    input  wire [2:0]      h_off,
    input  wire [7:0]      h_wd,
    input  wire [2*NE-1:0] e_seg,
    input  wire [2*NE-1:0] e_com,
    output reg             out,
    output reg             oen
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    reg [2:0]  eng;
    reg [15:0] lut, oe;

    reg [3:0] idx;
    integer i;
    always @* begin
        idx = 4'd0;
        for (i = 0; i < NE; i = i + 1)
            if (eng == i[2:0]) idx = {e_seg[2*i +: 2], e_com[2*i +: 2]};
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            eng <= 3'd0; lut <= 16'd0; oe <= 16'd0; out <= 1'b0; oen <= 1'b0;
        end else begin
            out <= lut[idx];
            oen <= (HAS_OE != 0) ? oe[idx] : 1'b0;
            if (h_we) begin
                case (h_off)
                    HOUT_ENG[2:0]:        eng <= h_wd[2:0];
                    HOUT_LUT[2:0]:        lut[7:0]  <= h_wd;
                    HOUT_LUT[2:0] + 3'd1: lut[15:8] <= h_wd;
                    HOUT_OE[2:0]:         if (HAS_OE != 0) oe[7:0]  <= h_wd;
                    HOUT_OE[2:0] + 3'd1:  if (HAS_OE != 0) oe[15:8] <= h_wd;
                    default: ;
                endcase
            end
        end
    end

    // D14: output-cell registers are write-only (host reads return 0)
endmodule
`default_nettype wire
