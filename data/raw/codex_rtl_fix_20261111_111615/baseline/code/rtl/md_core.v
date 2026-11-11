// Core c (SPEC 5): fetch, decode, guard evaluation, source muxes and dispatch (including the watchers of the
// engine being dispatched). The program memory sits outside; this module drives its read address (fetch_addr,
// registered by the SRAM at the end of the cycle) and receives the instruction word I in the following cycle.
`timescale 1ns/1ps
`default_nettype none
module md_core #(
    parameter integer C   = 0,      // core index
    parameter integer NE  = 6,      // engines
    parameter integer NR  = 4,
    parameter integer NSH = 4,
    parameter integer NCN = 4,
    parameter integer NLF = 2
) (
    input  wire            clk,
    input  wire            rst_n,
    input  wire [63:0]     insn,        // I: program word addressed in the previous cycle
    input  wire            run_g,       // RUN_global
    // engines
    input  wire [NE-1:0]   e_ready,
    input  wire [NE-1:0]   e_core,      // engine CORE bit
    input  wire [8*NE-1:0] e_pc,
    input  wire [6*NE-1:0] e_w0c,
    input  wire [6*NE-1:0] e_w1c,
    input  wire [8*NE-1:0] e_w0h,
    input  wire [8*NE-1:0] e_w1h,
    input  wire [2*NE-1:0] e_in,
    input  wire [4*NE-1:0] e_cap,
    input  wire [NE-1:0]   e_sync,
    input  wire [NE-1:0]   e_pina,
    input  wire [NE-1:0]   e_pinb,
    // sources (SPEC 6 source table)
    input  wire [15:0]       s_f,
    input  wire [12:0]       s_pin,
    input  wire [7:0]        s_acc,
    input  wire [8*NR-1:0]   s_r,
    input  wire [8*NSH-1:0]  s_shd,
    input  wire [NSH-1:0]    s_sho,
    input  wire [16*NCN-1:0] s_cnt,
    input  wire [32*NLF-1:0] s_lf,
    input  wire [15:0]       s_pd,
    input  wire [7:0]        s_inb,
    input  wire [63:0]       grd_g,     // global guard vector (engine-relative slots 0)
    output wire            fetch_en,
    output wire [7:0]      fetch_addr,
    output wire            pause_o,     // XV and I.pause: PC[XE]' = npc, RUNNING[XE]' = 0
    output wire [7:0]      npc_o,
    output wire            disp_o,      // dispatching engine disp_e this cycle
    output reg  [2:0]      disp_e,
    output reg  [2:0]      xe,
    output wire [2:0]      mv_en,       // per move: enabled (XV and guard)
    output wire [17:0]     mv_src,
    output wire [17:0]     mv_dst,
    output wire [23:0]     mv_data
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    reg       xv;
    reg [7:0] xpc;

    // header code + offset as a 32-bit index (width-clean)
    function integer ix;
        input [5:0] base;
        input integer off;
        begin
            ix = {26'd0, base} + off;
        end
    endfunction

    // instruction fields
    wire       i_pause = insn[F_PAUSE_LSB];
    wire [1:0] i_jmode = insn[F_JMODE_LSB +: 2];
    wire [7:0] i_imm   = insn[F_IMM_LSB +: 8];
    wire [5:0] i_cond  = insn[F_COND_LSB +: 6];
    wire [1:0] i_g [0:2];
    wire [5:0] i_s [0:2];
    wire [5:0] i_d [0:2];
    assign i_g[0] = insn[F_M0_GUARD_LSB +: 2];
    assign i_s[0] = insn[F_M0_SRC_LSB +: 6];
    assign i_d[0] = insn[F_M0_DST_LSB +: 6];
    assign i_g[1] = insn[F_M1_GUARD_LSB +: 2];
    assign i_s[1] = insn[F_M1_SRC_LSB +: 6];
    assign i_d[1] = insn[F_M1_DST_LSB +: 6];
    assign i_g[2] = insn[F_M2_GUARD_LSB +: 2];
    assign i_s[2] = insn[F_M2_SRC_LSB +: 6];
    assign i_d[2] = insn[F_M2_DST_LSB +: 6];

    // executing engine's relative signals (XE is always a valid engine once XV has been set)
    reg [1:0] x_in;
    reg [3:0] x_cap;
    reg       x_sync, x_pina, x_pinb;
    integer i, b;
    always @* begin
        x_in = 2'd0; x_cap = 4'd0; x_sync = 1'b0; x_pina = 1'b0; x_pinb = 1'b0;
        for (i = 0; i < NE; i = i + 1) begin
            if (xe == i[2:0]) begin
                x_in   = e_in[2*i +: 2];
                x_cap  = e_cap[4*i +: 4];
                x_sync = e_sync[i];
                x_pina = e_pina[i];
                x_pinb = e_pinb[i];
            end
        end
    end

    // guard mux (instruction condition)
    reg [63:0] grd;
    always @* begin
        grd = grd_g;
        grd[G_E_IN0]  = x_in[0];
        grd[G_E_IN1]  = x_in[1];
        grd[G_E_SYNC] = x_sync;
        grd[G_E_PINA] = x_pina;
        grd[G_E_PINB] = x_pinb;
    end
    wire cc = grd[i_cond];

    // source vector, indexed by the header's S_* codes (unused codes read 0)
    reg [511:0] src;
    always @* begin
        src = 512'd0;
        src[ix(S_IMM, 0) * 8 +: 8]      = i_imm;
        src[ix(S_E_IN, 0) * 8 +: 8]     = {6'd0, x_in};
        src[ix(S_E_CAP, 0) * 8 +: 8]    = {4'd0, x_cap};
        src[ix(S_FLAGS_LO, 0) * 8 +: 8] = s_f[7:0];
        src[ix(S_FLAGS_HI, 0) * 8 +: 8] = s_f[15:8];
        src[ix(S_PINS_LO, 0) * 8 +: 8]  = s_pin[7:0];
        src[ix(S_PINS_HI, 0) * 8 +: 8]  = {3'd0, s_pin[12:8]};
        src[ix(S_ACC, 0) * 8 +: 8]      = s_acc;
        for (i = 0; i < NR; i = i + 1)  src[ix(S_R0, i) * 8 +: 8]      = s_r[8*i +: 8];
        for (i = 0; i < NSH; i = i + 1) src[ix(S_SH0_D, i) * 8 +: 8]   = s_shd[8*i +: 8];
        for (i = 0; i < NSH; i = i + 1) src[ix(S_SH0_O, i) * 8 +: 8]   = {7'd0, s_sho[i]};
        for (i = 0; i < NCN; i = i + 1) src[ix(S_CNT0_LO, i) * 8 +: 8] = s_cnt[16*i +: 8];
        for (i = 0; i < NCN; i = i + 1) src[ix(S_CNT0_HI, i) * 8 +: 8] = s_cnt[16*i + 8 +: 8];
        for (i = 0; i < NLF; i = i + 1)
            for (b = 0; b < 4; b = b + 1)
                src[ix(S_LF0_B0, 4 * i + b) * 8 +: 8] = s_lf[32*i + 8*b +: 8];
        src[ix(S_P0_D, 0) * 8 +: 8]     = s_pd[7:0];
        src[ix(S_P1_D, 0) * 8 +: 8]     = s_pd[15:8];
        src[ix(S_HOST_IN, 0) * 8 +: 8]  = s_inb;
    end

    genvar m;
    generate
        for (m = 0; m < 3; m = m + 1) begin : g_mv
            wire gok = (i_g[m] == GD_ALWAYS) | ((i_g[m] == GD_IF) & cc) | ((i_g[m] == GD_IFNOT) & ~cc);
            assign mv_en[m]           = xv & gok;
            assign mv_src[6*m +: 6]   = i_s[m];
            assign mv_dst[6*m +: 6]   = i_d[m];
            // one-hot AND-OR select; bits that are constant 0 for a source drop out in synthesis
            wire [63:0] sh = 64'd1 << i_s[m];
            reg  [7:0]  sd;
            integer q;
            always @* begin
                sd = 8'd0;
                for (q = 0; q < 64; q = q + 1)
                    sd = sd | (src[8*q +: 8] & {8{sh[q]}});
            end
            assign mv_data[8*m +: 8]  = sd;
        end
    endgenerate

    wire taken = (i_jmode == JM_ALWAYS) | ((i_jmode == JM_IF) & cc) | ((i_jmode == JM_IFNOT) & ~cc);
    wire [7:0] npc = taken ? i_imm : (xpc + 8'd1);
    wire cont = xv & ~i_pause;
    assign pause_o = xv & i_pause;
    assign npc_o   = npc;

    // dispatch: lowest ready engine bound to this core (one-hot priority), then its watchers
    wire [NE-1:0] mine = (C != 0) ? e_core : ~e_core;
    wire [NE-1:0] cand = e_ready & mine & {NE{run_g}};
    wire [NE-1:0] lower;
    assign lower[0] = 1'b0;
    genvar g;
    generate
        for (g = 1; g < NE; g = g + 1) begin : g_low
            assign lower[g] = lower[g-1] | cand[g-1];
        end
    endgenerate
    wire [NE-1:0] win = cand & ~lower;

    reg [7:0] d_pc, d_w0h, d_w1h;
    reg [5:0] d_w0c, d_w1c;
    reg [1:0] d_in;
    reg       d_sync, d_pina, d_pinb;
    always @* begin
        disp_e = 3'd0; d_pc = 8'd0; d_w0h = 8'd0; d_w1h = 8'd0; d_w0c = 6'd0; d_w1c = 6'd0;
        d_in = 2'd0; d_sync = 1'b0; d_pina = 1'b0; d_pinb = 1'b0;
        for (i = 0; i < NE; i = i + 1) begin
            disp_e = disp_e | (i[2:0] & {3{win[i]}});
            d_pc   = d_pc   | (e_pc[8*i +: 8]  & {8{win[i]}});
            d_w0h  = d_w0h  | (e_w0h[8*i +: 8] & {8{win[i]}});
            d_w1h  = d_w1h  | (e_w1h[8*i +: 8] & {8{win[i]}});
            d_w0c  = d_w0c  | (e_w0c[6*i +: 6] & {6{win[i]}});
            d_w1c  = d_w1c  | (e_w1c[6*i +: 6] & {6{win[i]}});
            d_in   = d_in   | (e_in[2*i +: 2]  & {2{win[i]}});
            d_sync = d_sync | (e_sync[i] & win[i]);
            d_pina = d_pina | (e_pina[i] & win[i]);
            d_pinb = d_pinb | (e_pinb[i] & win[i]);
        end
    end
    // watchers use guards relative to the engine being dispatched
    reg [63:0] gd;
    always @* begin
        gd = grd_g;
        gd[G_E_IN0]  = d_in[0];
        gd[G_E_IN1]  = d_in[1];
        gd[G_E_SYNC] = d_sync;
        gd[G_E_PINA] = d_pina;
        gd[G_E_PINB] = d_pinb;
    end
    wire w0 = (d_w0c != 6'd0) & gd[d_w0c];
    wire w1 = (d_w1c != 6'd0) & gd[d_w1c];
    wire [7:0] dpc = w0 ? d_w0h : (w1 ? d_w1h : d_pc);

    assign disp_o     = ~cont & (|cand);
    assign fetch_en   = cont | disp_o;
    assign fetch_addr = cont ? npc : dpc;

    always @(posedge clk) begin
        if (!rst_n) begin
            xv  <= 1'b0;
            xe  <= 3'd0;
            xpc <= 8'd0;
        end else begin
            xv <= fetch_en;
            if (cont) begin
                xpc <= npc;
            end else if (disp_o) begin
                xpc <= dpc;
                xe  <= disp_e;
            end
        end
    end

    // reserved instruction bits are ignored
    wire unused_ok = &{1'b0, insn[F_RESERVED_LSB +: F_RESERVED_W]};
endmodule
`default_nettype wire
