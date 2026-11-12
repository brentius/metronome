// Metronome v2 sizing: pipelined core c (BOTS/PLANS/V2_DESIGN.md section 4.6; dispatch, watchers and moves as
// wiki/SPEC.md sections 5-7 of v1, with v2 fields from code/md2/md2_defs.vh).
//
// Three stages per word, each one cycle:
//   F  fetch_addr/fetch_en presented; the SRAM registers the address at the end of the cycle.
//   R  the word is at the SRAM output (rdata) and is captured into the instruction register IR.
//   X  IR is decoded and executed: guards, three moves, jump/pause, and dispatch when the core frees up.
// Fetch runs one word ahead on the sequential address. State:
//   xv  IR holds an instruction to execute this cycle (X valid)
//   rv  rdata holds the word at address fpc for the current burst (R valid)
//   fpc address of the word at rdata; while xv, fpc = PC(IR) + 1, so the sequential next PC is fpc itself
//   xe, xl  executing thread and its line (registered at dispatch), rr round-robin cursor (SPEC v1 5, D17)
// In X: a taken jump on a non-pausing instruction presents imm and drops the R word (rv' = 1 for the target,
// xv' = 0, so the dropped word never reaches X: one idle cycle). A pause hands npc to the thread, drops the R
// word and frees the core, which dispatches in the same cycle (READY and watchers sampled on cycle-X state as in
// v1); the dispatched word executes two cycles later. A trigger in t gives READY in t+1, dispatch (F) in t+1,
// R in t+2 and X in t+3.
`timescale 1ns/1ps
`default_nettype none
module md2_core #(
    parameter integer C  = 0,       // core index
    parameter integer NT = 6        // threads
) (
    input  wire            clk,
    input  wire            rst_n,
    input  wire            run_g,      // RUN_global
    input  wire [63:0]     rdata,      // program word at address fpc (registered by the SRAM last cycle)
    output wire            fetch_en,
    output wire [7:0]      fetch_addr,
    // threads: state and configuration
    input  wire [NT-1:0]   t_ready,
    input  wire [NT-1:0]   t_core,
    input  wire [2*NT-1:0] t_line,
    input  wire [8*NT-1:0] t_pc,
    input  wire [6*NT-1:0] t_w0c,
    input  wire [6*NT-1:0] t_w1c,
    input  wire [8*NT-1:0] t_w0h,
    input  wire [8*NT-1:0] t_w1h,
    // commons
    input  wire [63:0]     guards,     // global guard vector (line-relative slots replaced here)
    input  wire [19:0]     g_line,     // per line {PINB, PINA, SYNC, IN1, IN0}
    input  wire [511:0]    srcs,       // 64 x 8 sources (IMM, L.IN, L.CAP replaced here)
    input  wire [7:0]      l_in,       // per line 2-bit input symbol
    input  wire [19:0]     l_cap,      // per line 5-bit snapshot
    output wire            pause_o,    // X retires a pausing instruction of thread xe: PC[xe]' = npc_o
    output wire [7:0]      npc_o,
    output wire            disp_o,     // dispatching thread disp_e this cycle
    output reg  [2:0]      disp_e,
    output wire            stop_o,     // an enabled move to T.STOP (thread xe)
    output wire            xv_o,
    output wire [2:0]      xe_o,
    output wire [1:0]      xl_o,
    output wire [2:0]      mv_en,
    output wire [17:0]     mv_dst,
    output wire [23:0]     mv_data
);
/* verilator lint_off UNUSEDPARAM */
`undef MD2_DEFS_VH
`include "md2_defs.vh"
/* verilator lint_on UNUSEDPARAM */

    reg        xv, rv;
    reg [7:0]  fpc;
    reg [2:0]  xe, rr;
    reg [1:0]  xl;
    reg [63:0] ir;

    integer i;

    // ---------------------------------------------------------------- decode (from IR)
    wire       i_pause = ir[F_PAUSE_LSB];
    wire [1:0] i_jmode = ir[F_JMODE_LSB +: 2];
    wire [7:0] i_imm   = ir[F_IMM_LSB +: 8];
    wire [5:0] i_cond  = ir[F_COND_LSB +: 6];
    wire [4:0] i_jcond = ir[F_JCOND_LSB +: 5];
    wire [1:0] i_g [0:2];
    wire [5:0] i_s [0:2];
    wire [5:0] i_d [0:2];
    assign i_g[0] = ir[F_M0_GUARD_LSB +: 2];
    assign i_s[0] = ir[F_M0_SRC_LSB +: 6];
    assign i_d[0] = ir[F_M0_DST_LSB +: 6];
    assign i_g[1] = ir[F_M1_GUARD_LSB +: 2];
    assign i_s[1] = ir[F_M1_SRC_LSB +: 6];
    assign i_d[1] = ir[F_M1_DST_LSB +: 6];
    assign i_g[2] = ir[F_M2_GUARD_LSB +: 2];
    assign i_s[2] = ir[F_M2_SRC_LSB +: 6];
    assign i_d[2] = ir[F_M2_DST_LSB +: 6];

    // guard vector with the line-relative slots of line ln; TRUE is constant, codes past the table are false
    function [63:0] gvec;
        input [63:0] g;
        input [19:0] gl;
        input [1:0]  ln;
        reg   [4:0]  s;
        begin
            s = gl[5*ln +: 5];
            gvec = g;
            gvec[G_TRUE]   = 1'b1;
            gvec[G_L_IN0]  = s[0];
            gvec[G_L_IN1]  = s[1];
            gvec[G_L_SYNC] = s[2];
            gvec[G_L_PINA] = s[3];
            gvec[G_L_PINB] = s[4];
            gvec[63:62]    = 2'b00;
        end
    endfunction

    // ---------------------------------------------------------------- execute
    wire [63:0] grd = gvec(guards, g_line, xl);
    wire        cc  = grd[i_cond];
    // jump condition: jcond indexes the 32-entry subset JG_MAP of the guards
    wire [31:0] jg;
    genvar j;
    generate
        for (j = 0; j < 32; j = j + 1) begin : g_jg
            assign jg[j] = grd[JG_MAP[6*j +: 6]];
        end
    endgenerate
    wire jc    = jg[i_jcond];
    wire taken = (i_jmode == JM_ALWAYS) | ((i_jmode == JM_IF) & jc) | ((i_jmode == JM_IFNOT) & ~jc);

    // sources: IMM from IR, L.IN and L.CAP from the executing thread's line. Codes past the table read 0 and
    // single-bit or 5-bit ports keep only their width (as v1 md_core), so the stub bundle does not inflate the mux.
    localparam integer NSRC = {26'd0, S_HOST_IN} + 1;
    reg [511:0] src;
    always @* begin
        src = srcs;
        src[511:8*NSRC]         = {(512 - 8 * NSRC){1'b0}};
        src[8*S_ZERO  +: 8]     = 8'd0;
        src[8*S_IMM   +: 8]     = i_imm;
        src[8*S_L_IN  +: 8]     = {6'd0, l_in[2*xl +: 2]};
        src[8*S_L_CAP +: 8]     = {3'd0, l_cap[5*xl +: 5]};
        src[8*S_PINS_HI+5 +: 3] = 3'd0;
        src[8*S_SH0_O+1  +: 7]  = 7'd0;
        src[8*S_SH1_O+1  +: 7]  = 7'd0;
        src[8*S_LF0_O+1  +: 7]  = 7'd0;
        src[8*S_LF1_O+1  +: 7]  = 7'd0;
        src[8*S_S0_BIT+1 +: 7]  = 7'd0;
        src[8*S_S1_BIT+1 +: 7]  = 7'd0;
    end

    wire [2:0] stop_m;
    genvar m;
    generate
        for (m = 0; m < 3; m = m + 1) begin : g_mv
            wire gok = (i_g[m] == GD_ALWAYS) | ((i_g[m] == GD_IF) & cc) | ((i_g[m] == GD_IFNOT) & ~cc);
            assign mv_en[m]         = xv & gok;
            assign mv_dst[6*m +: 6] = i_d[m];
            assign stop_m[m]        = mv_en[m] & (i_d[m] == D_T_STOP);
            wire [63:0] sh = 64'd1 << i_s[m];
            reg  [7:0]  sd;
            integer q;
            always @* begin
                sd = 8'd0;
                for (q = 0; q < 64; q = q + 1)
                    sd = sd | (src[8*q +: 8] & {8{sh[q]}});
            end
            assign mv_data[8*m +: 8] = sd;
        end
    endgenerate
    assign stop_o = |stop_m;

    // ---------------------------------------------------------------- sequencing
    wire jmp  = xv & ~i_pause & taken;          // redirect: present imm, drop the R word
    wire pse  = xv & i_pause;                   // retire the burst, drop the R word
    wire load = rv & ~jmp & ~pse;               // R word goes to IR and X next cycle; fetch fpc + 1
    wire free = pse | (~xv & ~rv);
    assign pause_o = pse;
    assign npc_o   = taken ? i_imm : fpc;
    assign xv_o    = xv;
    assign xe_o    = xe;
    assign xl_o    = xl;

    // ---------------------------------------------------------------- dispatch (as v1 md_core)
    wire [NT-1:0] mine = (C != 0) ? t_core : ~t_core;
    wire [NT-1:0] cand = t_ready & mine & {NT{run_g}};
    wire [NT-1:0] after_rr, eligible, lower;
    assign eligible = (|after_rr) ? after_rr : cand;
    assign lower[0] = 1'b0;
    genvar g;
    generate
        for (g = 0; g < NT; g = g + 1) begin : g_rr
            assign after_rr[g] = cand[g] & (g[2:0] >= rr);
        end
        for (g = 1; g < NT; g = g + 1) begin : g_low
            assign lower[g] = lower[g-1] | eligible[g-1];
        end
    endgenerate
    wire [NT-1:0] win = eligible & ~lower;
    localparam integer LAST_T = NT - 1;

    reg [7:0] d_pc, d_w0h, d_w1h;
    reg [5:0] d_w0c, d_w1c;
    reg [1:0] d_line;
    always @* begin
        disp_e = 3'd0; d_pc = 8'd0; d_w0h = 8'd0; d_w1h = 8'd0; d_w0c = 6'd0; d_w1c = 6'd0; d_line = 2'd0;
        for (i = 0; i < NT; i = i + 1) begin
            disp_e = disp_e | (i[2:0] & {3{win[i]}});
            d_pc   = d_pc   | (t_pc[8*i +: 8]  & {8{win[i]}});
            d_w0h  = d_w0h  | (t_w0h[8*i +: 8] & {8{win[i]}});
            d_w1h  = d_w1h  | (t_w1h[8*i +: 8] & {8{win[i]}});
            d_w0c  = d_w0c  | (t_w0c[6*i +: 6] & {6{win[i]}});
            d_w1c  = d_w1c  | (t_w1c[6*i +: 6] & {6{win[i]}});
            d_line = d_line | (t_line[2*i +: 2] & {2{win[i]}});
        end
    end
    // watchers use guards relative to the dispatched thread's line
    wire [63:0] gd = gvec(guards, g_line, d_line);
    wire w0 = (d_w0c != 6'd0) & gd[d_w0c];
    wire w1 = (d_w1c != 6'd0) & gd[d_w1c];
    wire [7:0] dpc = w0 ? d_w0h : (w1 ? d_w1h : d_pc);

    assign disp_o     = free & (|cand);
    assign fetch_en   = jmp | load | disp_o;
    assign fetch_addr = jmp ? i_imm : (load ? fpc + 8'd1 : dpc);

    always @(posedge clk) begin
        ir <= rdata;                         // no enable: xv qualifies it
        if (!rst_n) begin
            xv  <= 1'b0;
            rv  <= 1'b0;
            fpc <= 8'd0;
            xe  <= 3'd0;
            xl  <= 2'd0;
            rr  <= 3'd0;
        end else begin
            xv <= load;
            rv <= fetch_en;
            if (fetch_en) fpc <= fetch_addr;
            if (disp_o) begin
                xe <= disp_e;
                xl <= d_line;
                rr <= (disp_e == LAST_T[2:0]) ? 3'd0 : disp_e + 3'd1;
            end
        end
    end
endmodule
`default_nettype wire
