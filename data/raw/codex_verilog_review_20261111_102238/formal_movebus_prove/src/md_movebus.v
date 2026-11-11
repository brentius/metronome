// Move bus (SPEC 6): decodes the destination of each enabled move of both cores once (slot j = core*3 + move,
// so the slot order is the (core, move) priority order) into a one-hot port vector, forms the write groups,
// resolves each group with md_wgroup, and raises CONFLICT when any group has two or more writers. Each unit sees
// a uniform (we, sel, data) interface, where sel is a compact port select within the group:
//   ACC  sel[2:0]: 0 LD, 1 ADD, 2 SUB, 3 AND, 4 OR, 5 XOR, 6 CMP
//   SHk  sel[0]:   0 LD, 1 SH          CNTk sel[1:0]: 0 LO, 1 HI, 2 DEC
//   LFk  sel[2:0]: 0 ST, 1..4 B0..B3   Pk   sel[1:0]: 0 AL, 1 AH, 2 W, 3 R
//   FLAGS sel[0]:  0 SET, 1 CLR
`timescale 1ns/1ps
`default_nettype none
module md_movebus #(
    parameter integer NE  = 6,  // engines
    parameter integer NB  = 4,  // beat generators
    parameter integer NSH = 4,  // shifters
    parameter integer NCN = 4,  // counters
    parameter integer NLF = 2,  // LFSRs
    parameter integer NR  = 4,  // scratch registers
    parameter integer NP  = 2   // pointers
) (
    input  wire [5:0]        en,     // 2 cores x 3 moves
    input  wire [35:0]       dst,
    input  wire [47:0]       data,
    input  wire [2:0]        xe0,    // executing engine of core 0
    input  wire [2:0]        xe1,
    output wire              acc_we,
    output wire [2:0]        acc_sel,
    output wire [7:0]        acc_d,
    output wire [NR-1:0]     r_we,
    output wire [8*NR-1:0]   r_d,
    output wire [NSH-1:0]    sh_we,
    output wire [NSH-1:0]    sh_sel,
    output wire [8*NSH-1:0]  sh_d,
    output wire [NSH-1:0]    shc_we,
    output wire [5*NSH-1:0]  shc_d,
    output wire [NCN-1:0]    cn_we,
    output wire [2*NCN-1:0]  cn_sel,
    output wire [8*NCN-1:0]  cn_d,
    output wire [NLF-1:0]    lf_we,
    output wire [3*NLF-1:0]  lf_sel,
    output wire [8*NLF-1:0]  lf_d,
    output wire [NP-1:0]     p_we,
    output wire [2*NP-1:0]   p_sel,
    output wire [8*NP-1:0]   p_d,
    output wire              fl_we,
    output wire              fl_sel,
    output wire [3:0]        fl_d,
    output wire [NB-1:0]     bg_we,
    output wire [3*NB-1:0]   bg_d,
    output wire              ho_we,
    output wire [7:0]        ho_d,
    output wire [NE-1:0]     sym_we,
    output wire [2*NE-1:0]   sym_d,
    output wire [NE-1:0]     stop_we,
    output wire              conflict
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    localparam integer NG = 3 + NR + 2 * NSH + NCN + NLF + NP + NB + 2 * NE;

    // per-slot one-hot destination (enabled moves only) and executing-engine decode
    wire [63:0] oh [0:5];
    wire [7:0]  xo [0:5];
    wire [7:0]  dt [0:5];
    genvar j, k;
    generate
        for (j = 0; j < 6; j = j + 1) begin : g_slot
            // gated with a known select so an X destination (SRAM output before its first read) stays 0 in sim
            assign oh[j] = en[j] ? (64'd1 << dst[6*j +: 6]) : 64'd0;
            assign xo[j] = 8'd1 << ((j < 3) ? xe0 : xe1);
            assign dt[j] = data[8*j +: 8];
        end
    endgenerate

    // gather helpers: column `c` of the one-hot vectors, and slot data slices, as 6-bit / packed vectors
    function [5:0] col;
        input [63:0] o0, o1, o2, o3, o4, o5;
        input [5:0]  c;
        begin
            col = {o5[c], o4[c], o3[c], o2[c], o1[c], o0[c]};
        end
    endfunction

    // header code + offset, width-clean
    /* verilator lint_off UNUSEDSIGNAL */  // t[31:6]: codes are 6 bits
    function [5:0] add6;
        input [5:0] a;
        input integer b;
        reg [31:0] t;
        begin
            t = {26'd0, a} + b;
            add6 = t[5:0];
        end
    endfunction
    /* verilator lint_on UNUSEDSIGNAL */

    wire [47:0] d8 = data;
    wire [NG-1:0] multi;

    `define MD_COL(c) col(oh[0], oh[1], oh[2], oh[3], oh[4], oh[5], (c))

    generate
        // ACC.* : one group for the seven ops
        if (1) begin : g_acc
            wire [5:0] h_ld  = `MD_COL(D_ACC_LD);
            wire [5:0] h_add = `MD_COL(D_ACC_ADD);
            wire [5:0] h_sub = `MD_COL(D_ACC_SUB);
            wire [5:0] h_and = `MD_COL(D_ACC_AND);
            wire [5:0] h_or  = `MD_COL(D_ACC_OR);
            wire [5:0] h_xor = `MD_COL(D_ACC_XOR);
            wire [5:0] h_cmp = `MD_COL(D_ACC_CMP);
            wire [5:0] hit = h_ld | h_add | h_sub | h_and | h_or | h_xor | h_cmp;
            wire [17:0] sel;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign sel[3*j +: 3] = {h_or[j] | h_xor[j] | h_cmp[j], h_sub[j] | h_and[j] | h_cmp[j],
                                        h_add[j] | h_and[j] | h_xor[j]};
            end
            md_wgroup #(.DW(8), .SW(3)) u (.hit(hit), .sel(sel), .data(d8), .we(acc_we), .wsel(acc_sel),
                                           .wdata(acc_d), .multi(multi[0]));
        end
        for (k = 0; k < NR; k = k + 1) begin : g_r
            wire wsel_unused;
            md_wgroup #(.DW(8), .SW(1)) u (.hit(`MD_COL(add6(D_R0, k))), .sel(6'd0), .data(d8), .we(r_we[k]),
                                           .wsel(wsel_unused), .wdata(r_d[8*k +: 8]), .multi(multi[1 + k]));
        end
        for (k = 0; k < NSH; k = k + 1) begin : g_sh
            wire [5:0] h_ld = `MD_COL(add6(D_SH0_LD, k));
            wire [5:0] h_sh = `MD_COL(add6(D_SH0_SH, k));
            wire [5:0] h_c  = `MD_COL(add6(D_SH0_CFG, k));
            wire [29:0] d5;
            wire wsel_unused;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign d5[5*j +: 5] = dt[j][4:0];
            end
            md_wgroup #(.DW(8), .SW(1)) u (.hit(h_ld | h_sh), .sel(h_sh), .data(d8), .we(sh_we[k]),
                                           .wsel(sh_sel[k]), .wdata(sh_d[8*k +: 8]),
                                           .multi(multi[1 + NR + k]));
            md_wgroup #(.DW(5), .SW(1)) uc (.hit(h_c), .sel(6'd0), .data(d5), .we(shc_we[k]), .wsel(wsel_unused),
                                            .wdata(shc_d[5*k +: 5]), .multi(multi[1 + NR + NSH + k]));
        end
        for (k = 0; k < NCN; k = k + 1) begin : g_cn
            wire [5:0] h_lo  = `MD_COL(add6(D_CNT0_LO, k));
            wire [5:0] h_hi  = `MD_COL(add6(D_CNT0_HI, k));
            wire [5:0] h_dec = `MD_COL(add6(D_CNT0_DEC, k));
            wire [11:0] sel;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign sel[2*j +: 2] = {h_dec[j], h_hi[j]};
            end
            md_wgroup #(.DW(8), .SW(2)) u (.hit(h_lo | h_hi | h_dec), .sel(sel), .data(d8), .we(cn_we[k]),
                                           .wsel(cn_sel[2*k +: 2]), .wdata(cn_d[8*k +: 8]),
                                           .multi(multi[1 + NR + 2*NSH + k]));
        end
        for (k = 0; k < NLF; k = k + 1) begin : g_lf
            wire [5:0] h_st = `MD_COL(add6(D_LF0_ST, k));
            wire [5:0] h_b0 = `MD_COL(add6(D_LF0_B0, 4 * k + 0));
            wire [5:0] h_b1 = `MD_COL(add6(D_LF0_B0, 4 * k + 1));
            wire [5:0] h_b2 = `MD_COL(add6(D_LF0_B0, 4 * k + 2));
            wire [5:0] h_b3 = `MD_COL(add6(D_LF0_B0, 4 * k + 3));
            wire [17:0] sel;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign sel[3*j +: 3] = {h_b3[j], h_b1[j] | h_b2[j], h_b0[j] | h_b2[j]};
            end
            md_wgroup #(.DW(8), .SW(3)) u (.hit(h_st | h_b0 | h_b1 | h_b2 | h_b3), .sel(sel), .data(d8),
                                           .we(lf_we[k]), .wsel(lf_sel[3*k +: 3]), .wdata(lf_d[8*k +: 8]),
                                           .multi(multi[1 + NR + 2*NSH + NCN + k]));
        end
        for (k = 0; k < NP; k = k + 1) begin : g_p
            wire [5:0] h_al = `MD_COL(add6(D_P0_AL, k));
            wire [5:0] h_ah = `MD_COL(add6(D_P0_AH, k));
            wire [5:0] h_w  = `MD_COL(add6(D_P0_W, k));
            wire [5:0] h_r  = `MD_COL(add6(D_P0_R, k));
            wire [11:0] sel;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign sel[2*j +: 2] = {h_w[j] | h_r[j], h_ah[j] | h_r[j]};
            end
            md_wgroup #(.DW(8), .SW(2)) u (.hit(h_al | h_ah | h_w | h_r), .sel(sel), .data(d8), .we(p_we[k]),
                                           .wsel(p_sel[2*k +: 2]), .wdata(p_d[8*k +: 8]),
                                           .multi(multi[1 + NR + 2*NSH + NCN + NLF + k]));
        end
        if (1) begin : g_fl
            wire [5:0] h_set = `MD_COL(D_FLAGS_SET);
            wire [5:0] h_clr = `MD_COL(D_FLAGS_CLR);
            wire [23:0] d4;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign d4[4*j +: 4] = dt[j][3:0];
            end
            md_wgroup #(.DW(4), .SW(1)) u (.hit(h_set | h_clr), .sel(h_clr), .data(d4), .we(fl_we), .wsel(fl_sel),
                                           .wdata(fl_d), .multi(multi[1 + NR + 2*NSH + NCN + NLF + NP]));
        end
        for (k = 0; k < NB; k = k + 1) begin : g_bg
            wire [17:0] d3;
            wire wsel_unused;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign d3[3*j +: 3] = dt[j][2:0];
            end
            md_wgroup #(.DW(3), .SW(1)) u (.hit(`MD_COL(add6(D_BG0_CTL, k))), .sel(6'd0), .data(d3),
                                           .we(bg_we[k]), .wsel(wsel_unused), .wdata(bg_d[3*k +: 3]),
                                           .multi(multi[2 + NR + 2*NSH + NCN + NLF + NP + k]));
        end
        if (1) begin : g_ho
            wire wsel_unused;
            md_wgroup #(.DW(8), .SW(1)) u (.hit(`MD_COL(D_HOST_OUT)), .sel(6'd0), .data(d8), .we(ho_we),
                                           .wsel(wsel_unused), .wdata(ho_d),
                                           .multi(multi[2 + NR + 2*NSH + NCN + NLF + NP + NB]));
        end
        // per-engine E.SYM and E.STOP: the engine is the one executing on the move's core
        if (1) begin : g_e
            wire [5:0] h_sym  = `MD_COL(D_E_SYM);
            wire [5:0] h_stop = `MD_COL(D_E_STOP);
            wire [11:0] d2;
            for (j = 0; j < 6; j = j + 1) begin : g_s
                assign d2[2*j +: 2] = dt[j][1:0];
            end
            for (k = 0; k < NE; k = k + 1) begin : g_k
                wire [5:0] me = {xo[5][k], xo[4][k], xo[3][k], xo[2][k], xo[1][k], xo[0][k]};
                wire ws_unused, wt_unused, td_unused;
                md_wgroup #(.DW(2), .SW(1)) us (.hit(h_sym & me), .sel(6'd0), .data(d2), .we(sym_we[k]),
                                                .wsel(ws_unused), .wdata(sym_d[2*k +: 2]),
                                                .multi(multi[3 + NR + 2*NSH + NCN + NLF + NP + NB + k]));
                md_wgroup #(.DW(1), .SW(1)) ut (.hit(h_stop & me), .sel(6'd0), .data(6'd0), .we(stop_we[k]),
                                                .wsel(wt_unused), .wdata(td_unused),
                                                .multi(multi[3 + NR + 2*NSH + NCN + NLF + NP + NB + NE + k]));
            end
        end
    endgenerate
    `undef MD_COL

    assign conflict = |multi;
endmodule
`default_nettype wire
