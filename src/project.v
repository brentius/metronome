/*
 * SPDX-License-Identifier: Apache-2.0
 */
// Metronome v2 top level (wiki/SPEC_V2.md part B, normative). Tiny Tapeout wrapper: reset, pin synchronisers and
// map (SPEC 2), host link and host map (9), configuration latches, lines (3), threads (4), cores (5), write groups
// and units (6), guards and jump conditions (7), output pins (8). Numbers come from md2_defs.vh (code/md2/gen.py)
// and md2_map.vh (code/tests/rtl_v2/gen_rtl_tables.py), both generated from code/md2/machine.py.
`timescale 1ns/1ps
`default_nettype none
// The official template keeps its top level in project.v.
/* verilator lint_off DECLFILENAME */
module tt_um_brentius_metronome (
    input  wire [7:0] ui_in,    // Dedicated inputs
    output wire [7:0] uo_out,   // Dedicated outputs
    input  wire [7:0] uio_in,   // IOs: Input path
    output wire [7:0] uio_out,  // IOs: Output path
    output wire [7:0] uio_oe,   // IOs: Enable path (active high: 0=input, 1=output)
    input  wire       ena,      // always 1 when the design is powered, so you can ignore it
    input  wire       clk,      // clock
    input  wire       rst_n     // reset_n - low to reset
);
/* verilator lint_on DECLFILENAME */
/* verilator lint_off UNUSEDPARAM */
`undef MD2_DEFS_VH
`include "md2_defs.vh"
`undef MD2_MAP_VH
`include "md2_map.vh"
/* verilator lint_on UNUSEDPARAM */
    localparam integer NL  = MD_N_LINES;
    localparam integer NT  = MD_N_THREADS;
    localparam integer NO  = MD_N_OUT_PINS;
    localparam integer NOE = MD_N_OE_PINS;

    // instance-indexed constants (families listed explicitly, not assumed contiguous)
    localparam [4*5-1:0] DG_LCTL = {DG_L3_CTL, DG_L2_CTL, DG_L1_CTL, DG_L0_CTL};
    localparam [4*5-1:0] DG_RK   = {DG_R3, DG_R2, DG_R1, DG_R0};
    localparam [2*5-1:0] DG_SHK  = {DG_SH1, DG_SH0};
    localparam [2*5-1:0] DG_SHC  = {DG_SH1_CFG, DG_SH0_CFG};
    localparam [3*5-1:0] DG_CNK  = {DG_CNT2, DG_CNT1, DG_CNT0};
    localparam [2*5-1:0] DG_LFK  = {DG_LF1, DG_LF0};
    localparam [2*5-1:0] DG_SK   = {DG_S1, DG_S0};

    // ---------------------------------------------------------------- reset: async assert, synchronous release
    // rst_q = rst_n delayed by two rising edges (SPEC 1); every flop below resets synchronously on rst_q.
    reg rst_m;
    // Configuration uses the same synchronized release and requires asynchronous clear.
    /* verilator lint_off SYNCASYNCNET */
    reg rst_q;
    /* verilator lint_on SYNCASYNCNET */
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rst_m <= 1'b0; rst_q <= 1'b0;
        end else begin
            rst_m <= 1'b1; rst_q <= rst_m;
        end
    end

    // ---------------------------------------------------------------- pins (SPEC 2)
    // raw vector: bits 7:0 uio_in, bits 15:8 ui_in. s1' = raw, s2' = s1, sp' = s2.
    reg [15:0] s1, s2, sp;
    always @(posedge clk) begin
        if (!rst_q) begin
            s1 <= 16'd0; s2 <= 16'd0; sp <= 16'd0;
        end else begin
            s1 <= {ui_in, uio_in}; s2 <= s1; sp <= s2;
        end
    end
    // input pins P0..P12 = uio_in[0..7], ui_in[3..7]; selects 13..15 read 0
    reg replay;
    reg [12:0] rlv, rlv_prev, emask;
    wire [12:0] replay_mask = emask & {13{replay}};
    wire [12:0] pins_level = ({s2[15:11], s2[7:0]} & ~replay_mask) | (rlv & replay_mask);
    wire [12:0] pins_prev = ({sp[15:11], sp[7:0]} & ~replay_mask) | (rlv_prev & replay_mask);
    wire [15:0] lvl  = {3'd0, pins_level};
    wire [15:0] rise = {3'd0, pins_level & ~pins_prev};
    wire [15:0] fall = {3'd0, ~pins_level & pins_prev};

    // ---------------------------------------------------------------- host link
    wire [15:0] ha;
    wire        h_wr, h_rd, miso, h_land;
    wire [7:0]  h_wd, h_land_d;
    reg  [7:0]  rd_val;
    wire [15:0] a_dat = ha - HA_DATA_BASE;
    wire in_data = (a_dat < HSPAN_DATA);      // unsigned: addresses below the base wrap high
    md2_host u_host (
        .clk(clk), .rst_n(rst_q), .sck(s2[8]), .sck_p(sp[8]), .cs_n(s2[9]), .mosi(s2[10]),
        .addr(ha), .wr(h_wr), .wdata(h_wd), .rd(h_rd), .rd_data(in_data), .rd_val(rd_val),
        .hland(h_land), .hland_d(h_land_d), .miso(miso)
    );

    // address decode (block, instance, offset)
    localparam integer LRT_SH = $clog2(HS_LRT);
    localparam integer TRT_SH = $clog2(HS_TRT);
    localparam integer SRT_SH = $clog2(HS_SRT);
    localparam integer PRG_SH = $clog2(HS_PROG_CORE);   // 2 cores: a_prg[11] selects the core
    wire [15:0] a_ctl = ha - HA_CTRL_BASE;
    wire [15:0] a_lrt = ha - HA_LRT_BASE;
    wire [15:0] a_trt = ha - HA_TRT_BASE;
    wire [15:0] a_srt = ha - HA_SRT_BASE;
    wire [15:0] a_dbg = ha - HA_DBG_BASE;
    wire [15:0] a_cfg = ha - CFG_LO;
    wire [15:0] a_prg = ha - HA_PROG_BASE;
    wire in_ctl = (a_ctl < HSPAN_CTRL);
    wire in_lrt = (a_lrt < HSPAN_LRT);
    wire in_trt = (a_trt < HSPAN_TRT);
    wire in_srt = (a_srt < HSPAN_SRT);
    wire in_dbg = (a_dbg < HSPAN_DBG);
    wire in_cfg = (a_cfg < HSPAN_CFG);
    wire in_prg = (a_prg < HSPAN_PROG);
    wire [15:0] i_lrt = a_lrt >> LRT_SH;
    wire [15:0] i_trt = a_trt >> TRT_SH;
    wire [15:0] i_srt = a_srt >> SRT_SH;
    // offsets as 32-bit values so that they compare cleanly with the integer HO_* offsets
    wire [31:0] o_ctl = {16'd0, a_ctl};
    wire [31:0] o_lrt = {16'd0, a_lrt} & (HS_LRT - 1);
    wire [31:0] o_trt = {16'd0, a_trt} & (HS_TRT - 1);
    wire [31:0] o_srt = {16'd0, a_srt} & (HS_SRT - 1);
    wire [31:0] o_dbg = {16'd0, a_dbg};
    wire w_ctl = h_wr & in_ctl;
    wire w_lrt = h_wr & in_lrt;
    wire w_trt = h_wr & in_trt;
    wire w_srt = h_wr & in_srt;
    wire w_dbg = h_wr & in_dbg;

    // ---------------------------------------------------------------- configuration latches
    reg frz;
    // A single write stage feeds the line-local banks and the remaining host banks.
    wire [8*CFG_BYTES-1:0] cfg;
    wire cfg_we1;
    wire [8:0] cfg_addr1;
    wire [7:0] cfg_data1;
    // CW and SPI use the same stage. The previous write strobe implements the D24 spacing interlock.
    reg [15:0] cw_addr, cw_pending_addr;
    reg [7:0] cw_pending_data;
    reg cw_pending, cw_overrun;
    wire cfg_host_now = h_wr & in_cfg & cfg_address_is_live(ha);
    wire cw_is_cfg = cfg_address_is_live(cw_pending_addr);
    wire cfg_issue, cfg_core_issue;
    wire cw_drain = cw_pending & ~frz & (~cw_is_cfg | cfg_core_issue);
    wire [8:0] cfg_issue_addr;
    wire [7:0] cfg_issue_data;
    md2_cfg_arb u_cfg_arb (
        .clk(clk), .rst_s(rst_q), .previous_write(cfg_we1),
        .host_valid(cfg_host_now), .host_addr(a_cfg[8:0]), .host_data(h_wd),
        .core_valid(cw_pending & ~frz & cw_is_cfg), .core_addr(cw_pending_addr[8:0]),
        .core_data(cw_pending_data), .core_issue(cfg_core_issue),
        .bank_write(cfg_issue), .bank_addr(cfg_issue_addr), .bank_data(cfg_issue_data)
    );
    md2_cfg_stage u_cfg_stage (
        .clk(clk), .rst_s(rst_q), .we(cfg_issue), .waddr(cfg_issue_addr),
        .wdata(cfg_issue_data),
        .we1(cfg_we1), .addr1(cfg_addr1), .data1(cfg_data1)
    );
    md2_cfg_cells #(.BYTES(CFG_BYTES), .MASK(CFG_MASK)) u_cfg (
        .clk(clk), .rst_s(rst_q), .we1(cfg_we1), .addr1(cfg_addr1), .data1(cfg_data1),
        .q(cfg)
    );

    // ---------------------------------------------------------------- global state declared ahead
    reg         run_g, conflict, memhaz, irq;
    reg  [1:0]  irqen;
    reg  [NT-1:0] db;
    reg  [15:0] fl, flp;
    reg  [7:0]  inb, outb;
    reg         inv, invp, outv;
    // v3 (SPEC v2 12): freeze/step, execution digest, edge capture. All 0 after reset = v2 behaviour.
    reg         freeze, frzd, men, cen;
    reg  [NO-1:0]  o_out;      // output pin registers (SPEC 8), declared ahead for the digest
    reg  [NOE-1:0] o_oe;
    reg  [31:0] misr;
    reg  [18:0] dc;
    wire        cev = cen & ~replay & ~frz & |((rise[12:0] | fall[12:0]) & emask);
    wire [NL-1:0]   l_beat, l_run, l_sp, l_held, l_tapmiss, l_pina, l_pinb, l_parise, l_pafall;
    wire [3*NL-1:0] l_tap, l_fired;
    wire [2*NL-1:0] l_in, l_seg;
    wire [5*NL-1:0] l_cap;
    wire [4*NL-1:0] l_staged, l_comm;
    wire [16*NL-1:0] l_ph;
    wire [NL-1:0]   l_arm, l_ren;
    wire [NT-1:0]   t_en, t_ready, t_running, t_armed, t_late, t_ovr, t_core;
    wire [8*NT-1:0] t_pc, t_w0h, t_w1h;
    wire [6*NT-1:0] t_w0c, t_w1c;
    wire [2*NT-1:0] t_line;
    wire [5*NT-1:0] t_trig;

    // ---------------------------------------------------------------- cores and program memories
    wire [1:0]  pse, dsp, fen;
    wire [15:0] npc, fadr;
    wire [5:0]  disp_e, xt;
    wire [3:0]  xl;
    wire [5:0]  c_en;
    wire [1:0]  c_xv, c_rv;
    wire [15:0] c_fpc;
    wire [35:0] c_src, c_dst;
    wire [47:0] c_dat;
    wire [63:0] pm_rd [0:1];
    wire [63:0]  guards;
    wire [19:0]  g_line;
    wire [511:0] srcs;
    wire [7:0]   pm_be = 8'd1 << a_prg[2:0];

    // program memories (fixed instance names: src/config.json places the SRAM macros u_pmem0/1.u_sram)
    wire pm_we0 = h_wr & in_prg & (a_prg[PRG_SH] == 1'b0);
    wire pm_we1 = h_wr & in_prg & (a_prg[PRG_SH] == 1'b1);
    md2_pmem u_pmem0 (
        .clk(clk), .ren(fen[0]), .we(pm_we0), .addr(pm_we0 ? a_prg[10:3] : fadr[7:0]), .be(pm_be), .wd(h_wd),
        .rd(pm_rd[0])
    );
    md2_pmem u_pmem1 (
        .clk(clk), .ren(fen[1]), .we(pm_we1), .addr(pm_we1 ? a_prg[10:3] : fadr[15:8]), .be(pm_be), .wd(h_wd),
        .rd(pm_rd[1])
    );
    genvar k;
    generate
        for (k = 0; k < MD_N_CORES; k = k + 1) begin : g_core
            md2_core #(.C(k), .NT(NT)) u_core (
                .clk(clk), .rst_n(rst_q), .run_g(run_g), .frz(frz), .rdata(pm_rd[k]), .fetch_en(fen[k]),
                .fetch_addr(fadr[8*k +: 8]),
                .t_ready(t_ready), .t_core(t_core), .t_line(t_line), .t_pc(t_pc),
                .t_w0c(t_w0c), .t_w1c(t_w1c), .t_w0h(t_w0h), .t_w1h(t_w1h),
                .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap),
                .pause_o(pse[k]), .npc_o(npc[8*k +: 8]), .disp_o(dsp[k]), .disp_e(disp_e[3*k +: 3]),
                .xt_o(xt[3*k +: 3]), .xl_o(xl[2*k +: 2]),
                .mv_en(c_en[3*k +: 3]), .mv_src(c_src[18*k +: 18]), .mv_dst(c_dst[18*k +: 18]),
                .mv_data(c_dat[24*k +: 24]),
                .dbg_xv(c_xv[k]), .dbg_rv(c_rv[k]), .dbg_fpc(c_fpc[8*k +: 8])
            );
        end
    endgenerate

    // ---------------------------------------------------------------- write groups (SPEC 6)
    // moves in priority order (core, move index): i = 3*core + m
    wire [5:0] mv_en = c_en;
    wire [4:0] grp [0:5];
    wire [5:0] mv_valid, mv_win;
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_grp
            assign grp[k]      = DG_MAP[5*c_dst[6*k +: 6] +: 5];
            assign mv_valid[k] = mv_en[k] & (grp[k] != DG_NONE);
        end
    endgenerate
    // same key: same group, and for L.SYM the same line, for T.STOP the same thread
    function same_key;
        input [4:0] ga, gb;
        input [1:0] la, lb;
        input [2:0] ta, tb;
        begin
            same_key = (ga == gb) && ((ga != DG_L_SYM) || (la == lb)) && ((ga != DG_T_STOP) || (ta == tb));
        end
    endfunction
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_win
            wire [5:0] blk;
            genvar j;
            for (j = 0; j < 6; j = j + 1) begin : g_b
                if (j < k) begin : g_lo
                    assign blk[j] = mv_valid[j] & same_key(grp[j], grp[k], xl[2*(j/3) +: 2], xl[2*(k/3) +: 2],
                                                           xt[3*(j/3) +: 3], xt[3*(k/3) +: 3]);
                end else begin : g_hi
                    assign blk[j] = 1'b0;
                end
            end
            assign mv_win[k] = mv_valid[k] & ~|blk;
        end
    endgenerate
    wire conflict_ev = |(mv_valid & ~mv_win);

    // Winner of a plain group (every group except L.SYM and T.STOP, whose key also holds a line or thread): the
    // first enabled move, in priority order, whose destination is in the group. For a plain group this equals
    // mv_win & (grp == G): same_key reduces to grp equality, so a move is blocked exactly by an earlier valid
    // move of the same group. Timing (2026-11-15, slow corner): the late input is mv_en (guard evaluation), so the
    // hit is a one-level priority on mv_en and the pick is a one-hot AND-OR instead of a six-deep priority chain.
    // Behaviour is unchanged (proved equivalent to the earlier pick/hits form with Yosys equiv_*).
    function [5:0] hits;
        input [5:0]  en;
        input [29:0] g;
        input [4:0]  want;
        reg   [5:0]  v;
        integer q;
        begin
            for (q = 0; q < 6; q = q + 1) v[q] = en[q] & (g[5*q +: 5] == want);
            hits[0] = v[0];
            for (q = 1; q < 6; q = q + 1) hits[q] = v[q] & ~|(v & ((6'd1 << q) - 6'd1));
        end
    endfunction
    function [14:0] pick;           // {we, dst[5:0], data[7:0]}; hit is one-hot or zero
        input [5:0]  hit;
        input [35:0] dst;
        input [47:0] dat;
        integer q;
        begin
            pick = 15'd0;
            for (q = 0; q < 6; q = q + 1)
                pick = pick | ({15{hit[q]}} & {1'b1, dst[6*q +: 6], dat[8*q +: 8]});
        end
    endfunction
    wire [29:0] grp_v = {grp[5], grp[4], grp[3], grp[2], grp[1], grp[0]};
    // (a macro, not a function, so that simulators see every operand)
`define HITG(G) hits(mv_en, grp_v, G)
    // per move: destination == want (from IR, early); `OPG(G, D) is "the winner of group G writes D", formed
    // without decoding the late picked destination (same value as w[14] & (w[13:8] == D)).
    function [5:0] dsteq;
        input [35:0] dst;
        input [5:0]  want;
        integer q;
        begin
            for (q = 0; q < 6; q = q + 1) dsteq[q] = (dst[6*q +: 6] == want);
        end
    endfunction
`define OPG(G, D) (|(`HITG(G) & dsteq(c_dst, D)))
`define PICKG(G) pick(`HITG(G), c_dst, c_dat)

    // source side effects of enabled moves
    wire [5:0] rd_pd, rd_hin;
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_eff
            assign rd_pd[k]  = mv_en[k] & (c_src[6*k +: 6] == S_P0_D);
            assign rd_hin[k] = mv_en[k] & (c_src[6*k +: 6] == S_HOST_IN);
        end
    endgenerate

    // ---------------------------------------------------------------- units
    wire [14:0] w_flags = `PICKG(DG_FLAGS);
    wire [14:0] w_cw = `PICKG(DG_CW);
    wire cw_write_data = w_cw[14] & (w_cw[13:8] == D_CW_D);
    wire cw_accept = cw_write_data & (~cw_pending | cw_drain);
    always @(posedge clk) begin
        if (!rst_q) begin
            cw_addr <= 16'd0;
            cw_pending <= 1'b0;
            cw_pending_addr <= 16'd0;
            cw_pending_data <= 8'd0;
        end else begin
            if (cw_drain) cw_pending <= 1'b0;
            if (cw_accept) begin
                cw_pending <= 1'b1;
                cw_pending_addr <= cw_addr;
                cw_pending_data <= w_cw[7:0];
                cw_addr <= cw_addr + 16'd1;
            end else if (w_cw[14] & (w_cw[13:8] == D_CW_AL)) begin
                cw_addr[7:0] <= w_cw[7:0];
            end else if (w_cw[14] & (w_cw[13:8] == D_CW_AH)) begin
                cw_addr[15:8] <= w_cw[7:0];
            end
        end
    end
    wire [14:0] w_p0    = `PICKG(DG_P0);
    wire [14:0] w_hout  = `PICKG(DG_HOST_OUT);

    // Accumulator: the ALU result is computed per move from that move's own data and destination, before the
    // late write-group hit selects one (timing, 2026-11-15: takes the add/subtract and zero detect off the
    // guard -> hit path). acc_hit is one-hot or zero, so u_acc sees exactly the winner's op and data as before.
    wire [5:0]  acc_hit = `HITG(DG_ACC);
    reg  [17:0] acc_sel6;
    integer am;
    always @* begin
        for (am = 0; am < 6; am = am + 1)
            case (c_dst[6*am +: 6])
                D_ACC_LD:  acc_sel6[3*am +: 3] = 3'd0;
                D_ACC_ADD: acc_sel6[3*am +: 3] = 3'd1;
                D_ACC_SUB: acc_sel6[3*am +: 3] = 3'd2;
                D_ACC_AND: acc_sel6[3*am +: 3] = 3'd3;
                D_ACC_OR:  acc_sel6[3*am +: 3] = 3'd4;
                D_ACC_XOR: acc_sel6[3*am +: 3] = 3'd5;
                default:   acc_sel6[3*am +: 3] = 3'd6;     // D_ACC_CMP
            endcase
    end
    wire [7:0]  acc_a;
    wire        acc_z, acc_c, acc_n;
    wire [31:0] acc_r;
    wire [3:0]  r_we;
    wire [31:0] r_d;
    generate
        for (k = 0; k < 4; k = k + 1) begin : g_r
            wire [14:0] w = `PICKG(DG_RK[5*k +: 5]);
            wire _unused_r = &{1'b0, w[13:8]};
            assign r_we[k] = w[14];
            assign r_d[8*k +: 8] = w[7:0];
        end
    endgenerate
    md2_acc #(.NR(4)) u_acc (
        .clk(clk), .rst_n(rst_q), .hit(acc_hit), .sel(acc_sel6), .d(c_dat), .r_we(r_we), .r_d(r_d),
        .a(acc_a), .z(acc_z), .c(acc_c), .n(acc_n), .r(acc_r)
    );

    wire [15:0] sh_d;
    wire [1:0]  sh_o, sh_done;
    localparam [11:0] D_SHSH = {D_SH1_SH, D_SH0_SH};
    generate
        for (k = 0; k < MD_N_SHIFTERS; k = k + 1) begin : g_sh
            wire [14:0] w = `PICKG(DG_SHK[5*k +: 5]);
            wire [14:0] c = `PICKG(DG_SHC[5*k +: 5]);
            wire _unused_c = &{1'b0, c[13:5]};
            wire _unused_w = &{1'b0, w[13:8]};
            md2_shifter u (
                .clk(clk), .rst_n(rst_q), .we(w[14]), .sel(`OPG(DG_SHK[5*k +: 5], D_SHSH[6*k +: 6])), .d(w[7:0]),
                .cfg_we(c[14]), .cfg_d(c[4:0]), .dr(sh_d[8*k +: 8]), .o(sh_o[k]), .done(sh_done[k])
            );
        end
    endgenerate

    wire [47:0] cn_v;
    wire [2:0]  cn_z;
    localparam [17:0] D_CNLO = {D_CNT2_LO, D_CNT1_LO, D_CNT0_LO};
    localparam [17:0] D_CNHI = {D_CNT2_HI, D_CNT1_HI, D_CNT0_HI};
    generate
        for (k = 0; k < MD_N_COUNTERS; k = k + 1) begin : g_cn
            wire [14:0] w = `PICKG(DG_CNK[5*k +: 5]);
            wire op_lo = `OPG(DG_CNK[5*k +: 5], D_CNLO[6*k +: 6]);
            wire op_hi = `OPG(DG_CNK[5*k +: 5], D_CNHI[6*k +: 6]);
            wire _unused_w = &{1'b0, w[13:8]};
            wire [1:0] sel = op_lo ? 2'd0 : (op_hi ? 2'd1 : 2'd2);
            md2_counter u (.clk(clk), .rst_n(rst_q), .we(w[14]), .sel(sel), .d(w[7:0]), .v(cn_v[16*k +: 16]),
                           .z(cn_z[k]));
        end
    endgenerate

    wire [63:0] lf_s;
    localparam [11:0] D_LFST = {D_LF1_ST, D_LF0_ST};
    localparam [47:0] D_LFB  = {D_LF1_B3, D_LF1_B2, D_LF1_B1, D_LF1_B0, D_LF0_B3, D_LF0_B2, D_LF0_B1, D_LF0_B0};
    generate
        for (k = 0; k < MD_N_LFSRS; k = k + 1) begin : g_lf
            wire [14:0] w = `PICKG(DG_LFK[5*k +: 5]);
            wire _unused_lf = &{1'b0, w[13:8]};
            wire op_st = `OPG(DG_LFK[5*k +: 5], D_LFST[6*k +: 6]);
            wire op_b0 = `OPG(DG_LFK[5*k +: 5], D_LFB[6*(4*k) +: 6]);
            wire op_b1 = `OPG(DG_LFK[5*k +: 5], D_LFB[6*(4*k+1) +: 6]);
            wire op_b2 = `OPG(DG_LFK[5*k +: 5], D_LFB[6*(4*k+2) +: 6]);
            wire [2:0] sel = op_st ? 3'd0 : op_b0 ? 3'd1 : op_b1 ? 3'd2 : op_b2 ? 3'd3 : 3'd4;
            localparam integer PB = HAI_LFSR_BASE - CFG_LO_I + HS_LFSR * k + HO_LFSR_POLY;
            md2_lfsr u (.clk(clk), .rst_n(rst_q), .we(w[14]), .sel(sel), .d(w[7:0]), .poly(cfg[8*PB +: 32]),
                        .s(lf_s[32*k +: 32]));
        end
    endgenerate

    // data RAM, pointer, streams
    wire [1:0]  s_req, s_we, s_gnt, s_bit, s_end, s_mark, s_bb, s_starved, s_word;
    wire [1:0] s_replay_valid;
    wire [63:0] s_replay_word;
    wire [19:0] replay_tick = {1'b0, dc} + 20'd1;
    wire [19:0] replay_interval = {1'b0, s_replay_word[31:13]};
    wire replay_apply = replay & ~frz & s_replay_valid[0] & (replay_tick >= replay_interval);
    wire replay_late = replay_apply & (replay_tick > replay_interval);
    wire [63:0] s_ww;
    wire [21:0] s_addr;
    wire [15:0] s_wd, s_byte;
    wire [23:0] s_pos;
    wire [5:0]  s_bidx;
    wire [31:0] dm_rd;
    localparam [11:0] D_SADV = {D_S1_ADV, D_S0_ADV};
    localparam [11:0] D_SRX  = {D_S1_RX, D_S0_RX};
    localparam [11:0] D_SCTL = {D_S1_CTL, D_S0_CTL};
    generate
        for (k = 0; k < MD_N_STREAMS; k = k + 1) begin : g_s
            wire [14:0] w = `PICKG(DG_SK[5*k +: 5]);
            wire        mctl = `OPG(DG_SK[5*k +: 5], D_SCTL[6*k +: 6]);
            wire        hctl = w_srt & (i_srt == k) & (o_srt == HO_SRT_CTL);
            localparam integer SB = HAI_STREAM_BASE - CFG_LO_I + HS_STREAM * k;
            wire [7:0]  mode = cfg[8*(SB + HO_STREAM_MODE) +: 8];
            wire _unused_s = &{1'b0, w[14:8], w[7:2], mode[7:2]};
            md2_stream #(.CAP(k == 0 ? 1 : 0)) u (
                .clk(clk), .rst_n(rst_q), .frz(frz), .frzd(frzd),
                .cap_en(cen & ~replay), .cap_push(cev), .cap_rec({dc, lvl[12:0]}),
                .replay_en(replay), .replay_apply(replay_apply), .replay_late(replay_late),
                .replay_valid(s_replay_valid[k]), .replay_word(s_replay_word[32*k +: 32]),
                .cfg_mode(mode[0]), .cfg_msb(mode[1]),
                .cfg_start(cfg[8*(SB + HO_STREAM_START) +: 11]),
                .cfg_len(cfg[8*(SB + HO_STREAM_LEN) +: 12]),
                .cfg_mark(cfg[8*(SB + HO_STREAM_MARK) +: 12]),
                .adv(`OPG(DG_SK[5*k +: 5], D_SADV[6*k +: 6])),
                .rx_we(`OPG(DG_SK[5*k +: 5], D_SRX[6*k +: 6])), .rx_bit(w[0]),
                .rewind((mctl & w[0]) | (hctl & h_wd[0])), .flush((mctl & w[1]) | (hctl & h_wd[1])),
                .clr_starved(hctl & h_wd[7]),
                .bit_out(s_bit[k]), .byte_out(s_byte[8*k +: 8]), .g_end(s_end[k]), .g_mark(s_mark[k]),
                .g_byte(s_bb[k]), .starved(s_starved[k]), .pos(s_pos[12*k +: 12]), .bidx(s_bidx[3*k +: 3]),
                .req(s_req[k]), .req_we(s_we[k]), .req_addr(s_addr[11*k +: 11]), .req_wdata(s_wd[8*k +: 8]),
                .req_word(s_word[k]), .req_wword(s_ww[32*k +: 32]),
                .gnt(s_gnt[k]), .rdata(dm_rd)
            );
        end
    endgenerate

    wire       p_rdy, p_haz;
    wire [7:0] p_dat;
    wire [1:0] p_sel = (w_p0[13:8] == D_P0_AL) ? 2'd0 : (w_p0[13:8] == D_P0_AH) ? 2'd1 :
                       (w_p0[13:8] == D_P0_W)  ? 2'd2 : 2'd3;
    wire       dm_ren, dm_we;
    wire [8:0] dm_addr;
    wire [3:0] dm_be;
    wire [31:0] dm_wd;
    md2_mem u_mem (
        .clk(clk), .rst_n(rst_q), .frz(frz), .frzd(frzd),
        .s_req(s_req), .s_we(s_we), .s_addr(s_addr), .s_wd(s_wd), .s_gnt(s_gnt),
        .s0_word(s_word[0]), .s0_wword(s_ww[31:0]),
        .p_we(w_p0[14]), .p_sel(p_sel), .p_d(w_p0[7:0]), .p_rdy(p_rdy), .p_dat(p_dat), .p_haz(p_haz),
        .h_set((h_wr | h_rd) & in_data), .h_wr(h_wr), .h_addr(a_dat[10:0]), .h_d(h_wd),
        .h_land(h_land), .h_land_d(h_land_d),
        .m_ren(dm_ren), .m_we(dm_we), .m_addr(dm_addr), .m_be(dm_be), .m_wd(dm_wd), .m_rd(dm_rd)
    );
    md2_dmem u_dmem (.clk(clk), .ren(dm_ren), .we(dm_we), .addr(dm_addr), .be(dm_be), .wd(dm_wd), .rd(dm_rd));

    // ---------------------------------------------------------------- lines
    generate
        for (k = 0; k < NL; k = k + 1) begin : g_ln
            localparam integer LB = HAI_LINE_BASE - CFG_LO_I + HS_LINE * k;
            wire [14:0] wc = `PICKG(DG_LCTL[5*k +: 5]);
            wire [5:0]  sh;
            genvar j;
            for (j = 0; j < 6; j = j + 1) begin : g_sh
                assign sh[j] = mv_win[j] & (grp[j] == DG_L_SYM) & (xl[2*(j/3) +: 2] == k);
            end
            wire [14:0] ws = pick(sh, c_dst, c_dat);
            wire _unused_s = &{1'b0, ws[7:4], wc[13:3]};
            wire [1:0]  sop = (ws[13:8] == D_L_SYM) ? 2'd0 : ((ws[13:8] == D_L_DBIT) ? 2'd1 : 2'd2);
            wire        hl  = w_lrt & (i_lrt == k);
            md2_line #(.CFGW(8 * HS_LINE)) u (
                .clk(clk), .rst_n(rst_q), .frz(frz), .cfg(cfg[8*LB +: 8*HS_LINE]), .lvl(lvl), .rise(rise),
                .fall(fall),
                .ctl_we(wc[14]), .ctl_d(wc[2:0]), .sym_we(ws[14]), .sym_op(sop), .sym_d(ws[3:0]),
                .h_ph_we({hl & (o_lrt == HO_LRT_PHASE + 1), hl & (o_lrt == HO_LRT_PHASE)}),
                .h_ctl_we(hl & (o_lrt == HO_LRT_CTL)), .h_stat_we(hl & (o_lrt == HO_LRT_STAT)), .h_d(h_wd),
                .beat(l_beat[k]), .tap(l_tap[3*k +: 3]), .in_sym(l_in[2*k +: 2]), .cap(l_cap[5*k +: 5]),
                .sp(l_sp[k]), .ph(l_ph[16*k +: 16]), .run(l_run[k]), .arm(l_arm[k]), .ren(l_ren[k]),
                .fired(l_fired[3*k +: 3]), .held(l_held[k]), .staged(l_staged[4*k +: 4]),
                .committed(l_comm[4*k +: 4]), .tapmiss(l_tapmiss[k]), .seg(l_seg[2*k +: 2]),
                .pina(l_pina[k]), .pinb(l_pinb[k]), .pina_rise(l_parise[k]), .pina_fall(l_pafall[k])
            );
            assign g_line[5*k +: 5] = {l_pinb[k], l_pina[k], l_sp[k], l_in[2*k +: 2]};
        end
    endgenerate

    // ---------------------------------------------------------------- threads and triggers (SPEC 4)
    // trigger events that do not depend on the thread (codes past the table never fire)
    reg [31:0] ev_g;
    always @* begin
        ev_g = 32'd0;
        ev_g[T_L0_BEAT] = l_beat[0]; ev_g[T_L0_TAP0] = l_tap[0]; ev_g[T_L0_TAP1] = l_tap[1]; ev_g[T_L0_TAP2] = l_tap[2];
        ev_g[T_L1_BEAT] = l_beat[1]; ev_g[T_L1_TAP0] = l_tap[3]; ev_g[T_L1_TAP1] = l_tap[4]; ev_g[T_L1_TAP2] = l_tap[5];
        ev_g[T_L2_BEAT] = l_beat[2]; ev_g[T_L2_TAP0] = l_tap[6]; ev_g[T_L2_TAP1] = l_tap[7]; ev_g[T_L2_TAP2] = l_tap[8];
        ev_g[T_L3_BEAT] = l_beat[3]; ev_g[T_L3_TAP0] = l_tap[9]; ev_g[T_L3_TAP1] = l_tap[10];
        ev_g[T_L3_TAP2] = l_tap[11];
        ev_g[T_FLAG0_RISE] = fl[0] & ~flp[0]; ev_g[T_FLAG1_RISE] = fl[1] & ~flp[1];
        ev_g[T_FLAG2_RISE] = fl[2] & ~flp[2]; ev_g[T_FLAG3_RISE] = fl[3] & ~flp[3];
        ev_g[T_FLAG4_RISE] = fl[4] & ~flp[4]; ev_g[T_FLAG5_RISE] = fl[5] & ~flp[5];
        ev_g[T_FLAG6_RISE] = fl[6] & ~flp[6]; ev_g[T_FLAG7_RISE] = fl[7] & ~flp[7];
        ev_g[T_HOST_INV] = inv & ~invp;
    end

    generate
        for (k = 0; k < NT; k = k + 1) begin : g_thr
            localparam integer TB = HAI_THREAD_BASE - CFG_LO_I + HS_THREAD * k;
            wire [7:0] tc = cfg[8*(TB + HO_THREAD_CFG) +: 8];
            assign t_core[k]        = tc[0];
            assign t_line[2*k +: 2] = tc[2:1];
            assign t_trig[5*k +: 5] = tc[7:3];
            assign t_w0c[6*k +: 6]  = cfg[8*(TB + HO_THREAD_W0C) +: 6];
            assign t_w1c[6*k +: 6]  = cfg[8*(TB + HO_THREAD_W1C) +: 6];
            assign t_w0h[8*k +: 8]  = cfg[8*(TB + HO_THREAD_W0H) +: 8];
            assign t_w1h[8*k +: 8]  = cfg[8*(TB + HO_THREAD_W1H) +: 8];
            wire [4:0] ts = tc[7:3];
            wire [1:0] ln = tc[2:1];
            wire ev = ev_g[ts] | ((ts == T_PINA_RISE) & l_parise[ln]) | ((ts == T_PINA_FALL) & l_pafall[ln]) |
                      ((ts == T_PINA_EDGE) & (l_parise[ln] | l_pafall[ln])) |
                      ((ts == T_ALWAYS) & ~t_ready[k] & ~t_running[k]);
            wire c0 = (xt[2:0] == k);
            wire c1 = (xt[5:3] == k);
            wire disp  = (dsp[0] & (disp_e[2:0] == k)) | (dsp[1] & (disp_e[5:3] == k));
            wire pause = (pse[0] & c0) | (pse[1] & c1);
            wire [5:0] own = {{3{c1}}, {3{c0}}};
            wire [5:0] sym_mv = own & mv_valid & {grp[5] == DG_L_SYM, grp[4] == DG_L_SYM, grp[3] == DG_L_SYM,
                                                  grp[2] == DG_L_SYM, grp[1] == DG_L_SYM, grp[0] == DG_L_SYM};
            wire [5:0] stop_mv = own & mv_valid & {grp[5] == DG_T_STOP, grp[4] == DG_T_STOP, grp[3] == DG_T_STOP,
                                                   grp[2] == DG_T_STOP, grp[1] == DG_T_STOP, grp[0] == DG_T_STOP};
            wire       ht = w_trt & (i_trt == k);
            md2_thread u (
                .clk(clk), .rst_n(rst_q), .ev(ev & ~frz), .db(db[k] & ~frz), .disp(disp), .pause(pause),
                .npc((pse[1] & c1) ? npc[15:8] : npc[7:0]), .stop(|stop_mv), .late_set(|sym_mv & ~t_armed[k]),
                .line_beat(l_beat[ln]),
                .h_pc_we(ht & (o_trt == HO_TRT_PC)), .h_stat_we(ht & (o_trt == HO_TRT_STAT)), .h_d(h_wd),
                .pc(t_pc[8*k +: 8]), .en(t_en[k]), .ready(t_ready[k]), .running(t_running[k]),
                .armed(t_armed[k]), .late(t_late[k]), .ovr(t_ovr[k])
            );
        end
    endgenerate

    // ---------------------------------------------------------------- sources and guards (SPEC 6, 7)
    reg [511:0] sv;
    always @* begin
        sv = 512'd0;
        sv[8*S_FLAGS_LO +: 8] = fl[7:0];
        sv[8*S_FLAGS_HI +: 8] = fl[15:8];
        sv[8*S_PINS_LO  +: 8] = lvl[7:0];
        sv[8*S_PINS_HI  +: 8] = {3'd0, lvl[12:8]};
        sv[8*S_ACC +: 8] = acc_a;
        sv[8*S_R0  +: 8] = acc_r[7:0];
        sv[8*S_R1  +: 8] = acc_r[15:8];
        sv[8*S_R2  +: 8] = acc_r[23:16];
        sv[8*S_R3  +: 8] = acc_r[31:24];
        sv[8*S_SH0_D +: 8] = sh_d[7:0];
        sv[8*S_SH1_D +: 8] = sh_d[15:8];
        sv[8*S_SH0_O +: 8] = {7'd0, sh_o[0]};
        sv[8*S_SH1_O +: 8] = {7'd0, sh_o[1]};
        sv[8*S_CNT0_LO +: 8] = cn_v[7:0];
        sv[8*S_CNT1_LO +: 8] = cn_v[23:16];
        sv[8*S_CNT2_LO +: 8] = cn_v[39:32];
        sv[8*S_CNT0_HI +: 8] = cn_v[15:8];
        sv[8*S_CNT1_HI +: 8] = cn_v[31:24];
        sv[8*S_CNT2_HI +: 8] = cn_v[47:40];
        sv[8*S_LF0_B0 +: 8] = lf_s[7:0];
        sv[8*S_LF0_B1 +: 8] = lf_s[15:8];
        sv[8*S_LF0_B2 +: 8] = lf_s[23:16];
        sv[8*S_LF0_B3 +: 8] = lf_s[31:24];
        sv[8*S_LF1_B0 +: 8] = lf_s[39:32];
        sv[8*S_LF1_B1 +: 8] = lf_s[47:40];
        sv[8*S_LF1_B2 +: 8] = lf_s[55:48];
        sv[8*S_LF1_B3 +: 8] = lf_s[63:56];
        sv[8*S_LF0_O +: 8] = {7'd0, lf_s[0]};
        sv[8*S_LF1_O +: 8] = {7'd0, lf_s[32]};
        sv[8*S_P0_D +: 8] = p_dat;
        sv[8*S_S0_BIT +: 8] = {7'd0, s_bit[0]};
        sv[8*S_S1_BIT +: 8] = {7'd0, s_bit[1]};
        sv[8*S_S0_BYTE +: 8] = s_byte[7:0];
        sv[8*S_S1_BYTE +: 8] = s_byte[15:8];
        sv[8*S_HOST_IN +: 8] = inb;
    end
    assign srcs = sv;

    localparam integer GF0 = {26'd0, G_F0};
    localparam integer GPIN0 = {26'd0, G_PIN0};
    reg [63:0] gv;
    integer q;
    always @* begin
        gv = 64'd0;
        gv[G_TRUE] = 1'b1;
        for (q = 0; q < 16; q = q + 1) gv[GF0 + q] = fl[q];          // F0..F15 (one family in machine.py)
        gv[G_SH0_DONE] = sh_done[0]; gv[G_SH1_DONE] = sh_done[1];
        gv[G_SH0_OUT] = sh_o[0];     gv[G_SH1_OUT] = sh_o[1];
        gv[G_CNT0_Z] = cn_z[0]; gv[G_CNT1_Z] = cn_z[1]; gv[G_CNT2_Z] = cn_z[2];
        gv[G_ACC_Z] = acc_z; gv[G_ACC_C] = acc_c; gv[G_ACC_N] = acc_n;
        gv[G_LF0_OUT] = lf_s[0]; gv[G_LF1_OUT] = lf_s[32];
        gv[G_HOST_INV] = inv; gv[G_HOST_OUTE] = ~outv; gv[G_P0_RDY] = p_rdy;
        gv[G_S0_END] = s_end[0];   gv[G_S1_END] = s_end[1];
        gv[G_S0_MARK] = s_mark[0]; gv[G_S1_MARK] = s_mark[1];
        gv[G_S0_BYTE] = s_bb[0];   gv[G_S1_BYTE] = s_bb[1];
        gv[G_S0_BIT] = s_bit[0];   gv[G_S1_BIT] = s_bit[1];
        for (q = 0; q < MD_N_IN_PINS; q = q + 1) gv[GPIN0 + q] = lvl[q];   // PIN0..PIN12 (one family)
        gv[G_L0_RUN] = l_run[0]; gv[G_L1_RUN] = l_run[1]; gv[G_L2_RUN] = l_run[2]; gv[G_L3_RUN] = l_run[3];
    end
    assign guards = gv;

    // ---------------------------------------------------------------- control, flags, mailbox, sticky errors
    wire c_wr_run   = w_ctl & (o_ctl == HO_CTRL_RUN);
    wire c_wr_stk   = w_ctl & (o_ctl == HO_CTRL_STICKY);
    wire c_wr_irqen = w_ctl & (o_ctl == HO_CTRL_IRQEN);
    wire c_wr_db    = w_ctl & (o_ctl == HO_CTRL_DOORBELL);
    wire c_wr_hin   = w_ctl & (o_ctl == HO_CTRL_HOSTIN);
    wire c_wr_hst   = w_ctl & (o_ctl == HO_CTRL_HOSTSTAT);
    wire d_wr_dbg   = w_dbg & (o_dbg == HO_DBG_DBG);
    wire d_wr_mctl  = w_dbg & (o_dbg == HO_DBG_MCTL);
    wire [31:0] cw_dbg_off = {16'd0, cw_pending_addr} - {16'd0, HA_DBG_BASE};
    wire h_ectl = w_dbg & (o_dbg == HO_DBG_ECTL);
    wire h_em0  = w_dbg & (o_dbg == HO_DBG_EMASK);
    wire h_em1  = w_dbg & (o_dbg == HO_DBG_EMASK + 1);
    wire h_rlv0 = w_dbg & (o_dbg == HO_DBG_RLV);
    wire h_rlv1 = w_dbg & (o_dbg == HO_DBG_RLV + 1);
    wire d_wr_ectl = h_ectl | (cw_drain & (cw_dbg_off == HO_DBG_ECTL));
    wire d_wr_em0  = h_em0  | (cw_drain & (cw_dbg_off == HO_DBG_EMASK));
    wire d_wr_em1  = h_em1  | (cw_drain & (cw_dbg_off == HO_DBG_EMASK + 1));
    wire d_wr_rlv0 = h_rlv0 | (cw_drain & (cw_dbg_off == HO_DBG_RLV));
    wire d_wr_rlv1 = h_rlv1 | (cw_drain & (cw_dbg_off == HO_DBG_RLV + 1));
    wire [12:0] replay_levels = replay_apply ?
                    ((rlv & ~emask) | (s_replay_word[12:0] & emask)) : rlv;
    localparam [31:0] MISR_POLY = 32'h04C11DB7;     // machine.MISR_POLY
    wire memhaz_ev  = p_haz | (|rd_pd & ~p_rdy);
    wire err = conflict | memhaz | cw_overrun | (|t_late) | (|t_ovr) | (|l_tapmiss) | (|s_starved);
    always @(posedge clk) begin
        if (!rst_q) begin
            run_g <= 1'b0; conflict <= 1'b0; memhaz <= 1'b0; irq <= 1'b0; irqen <= 2'd0; db <= {NT{1'b0}};
            fl <= 16'd0; flp <= 16'd0; inb <= 8'd0; outb <= 8'd0; inv <= 1'b0; invp <= 1'b0; outv <= 1'b0;
            freeze <= 1'b0; frz <= 1'b0; frzd <= 1'b0; men <= 1'b0; cen <= 1'b0; misr <= 32'd0; emask <= 13'd0;
            cw_overrun <= 1'b0;
            replay <= 1'b0; rlv <= 13'd0; rlv_prev <= 13'd0;
            dc <= 19'd0;
        end else begin
            if (!frz) flp <= fl;
            if (w_flags[14]) fl[w_flags[3:0]] <= (w_flags[13:8] == D_FLAGS_SET);
            if (!frz) invp <= inv;
            if (c_wr_hin)         begin inb <= h_wd; inv <= 1'b1; end
            else if (|rd_hin)     inv <= 1'b0;
            if (w_hout[14])       begin outb <= w_hout[7:0]; outv <= 1'b1; end
            else if (c_wr_hst & h_wd[1]) outv <= 1'b0;
            conflict <= conflict_ev | (conflict & ~(c_wr_stk & h_wd[0]));
            memhaz   <= memhaz_ev   | (memhaz   & ~(c_wr_stk & h_wd[1]));
            cw_overrun <= (cw_write_data & ~cw_accept) | (cw_overrun & ~(c_wr_stk & h_wd[2]));
            irq <= (irqen[0] & outv) | (irqen[1] & err);
            if (c_wr_run)   run_g <= h_wd[0];
            if (c_wr_irqen) irqen <= h_wd[1:0];
            db <= (c_wr_db ? h_wd[NT-1:0] : {NT{1'b0}}) | (frz ? db : {NT{1'b0}});   // held while frozen
            // v3 freeze and step (SPEC v2 12.3)
            frzd <= frz;
            if (d_wr_dbg) begin freeze <= h_wd[0]; frz <= h_wd[0] & ~h_wd[1]; end
            else          frz <= freeze;
            // v3 execution digest (12.2): D = {OEN[7:0], OUT[13:0]}, the pin registers in this cycle
            if (d_wr_mctl) men <= h_wd[0];
            if (d_wr_mctl & h_wd[1]) misr <= 32'd0;
            else if (men & ~frz)     misr <= {misr[30:0], 1'b0} ^ (misr[31] ? MISR_POLY : 32'd0) ^ {10'd0, o_oe, o_out};
            // Edge capture and replay (12.4, 13.2). A host write wins to the same byte.
            if (d_wr_ectl) {replay, cen} <= h_ectl ? h_wd[1:0] : cw_pending_data[1:0];
            if (d_wr_em0)  emask[7:0]  <= h_em0 ? h_wd : cw_pending_data;
            if (d_wr_em1)  emask[12:8] <= h_em1 ? h_wd[4:0] : cw_pending_data[4:0];
            if (!frz) rlv_prev <= rlv;
            rlv[7:0] <= d_wr_rlv0 ? (h_rlv0 ? h_wd : cw_pending_data) : replay_levels[7:0];
            rlv[12:8] <= d_wr_rlv1 ? (h_rlv1 ? h_wd[4:0] : cw_pending_data[4:0]) : replay_levels[12:8];
            if (d_wr_ectl) dc <= 19'd0;                         // any ECTL write restarts DC (12.4)
            else if (!frz) begin
                if (replay_apply | (~replay & ~cen)) dc <= 19'd0;
                else if (cev)               dc <= 19'd1;
                else if (dc != 19'h7FFFF)   dc <= dc + 19'd1;
            end
        end
    end

    // ---------------------------------------------------------------- host register reads (value in cycle R)
    wire [7:0] errsum = {1'b0, cw_overrun, memhaz, conflict, |s_starved, |l_tapmiss, |t_ovr, |t_late};
    wire [1:0] li = i_lrt[1:0];
    wire [2:0] ti = i_trt[2:0];
    wire       si = i_srt[0];
    always @* begin
        rd_val = 8'd0;
        if (in_ctl) begin
            case (o_ctl)
                HO_CTRL_RUN:      rd_val = {7'd0, run_g};
                HO_CTRL_STICKY:   rd_val = {5'd0, cw_overrun, memhaz, conflict};
                HO_CTRL_IRQEN:    rd_val = {6'd0, irqen};
                HO_CTRL_HOSTIN:   rd_val = inb;
                HO_CTRL_HOSTOUT:  rd_val = outb;
                HO_CTRL_HOSTSTAT: rd_val = {6'd0, outv, inv};
                HO_CTRL_ID:       rd_val = 8'hA0 | MD_VERSION[7:0];
                HO_CTRL_ERRSUM:   rd_val = errsum;
                default:          rd_val = 8'd0;
            endcase
        end else if (in_lrt) begin
            case (o_lrt)
                HO_LRT_PHASE:     rd_val = l_ph[16*li +: 8];
                HO_LRT_PHASE + 1: rd_val = l_ph[16*li + 8 +: 8];
                HO_LRT_CTL:       rd_val = {l_held[li], l_fired[3*li +: 3], l_sp[li], l_ren[li], l_arm[li], l_run[li]};
                HO_LRT_SYM:       rd_val = {l_comm[4*li +: 4], l_staged[4*li +: 4]};
                HO_LRT_INS:       rd_val = {1'b0, l_in[2*li +: 2], l_cap[5*li +: 5]};
                HO_LRT_STAT:      rd_val = {7'd0, l_tapmiss[li]};
                default:          rd_val = 8'd0;
            endcase
        end else if (in_trt) begin
            case (o_trt)
                HO_TRT_PC:   rd_val = t_pc[8*ti +: 8];
                HO_TRT_STAT: rd_val = {2'd0, t_ovr[ti], t_late[ti], t_en[ti], t_armed[ti], t_running[ti], t_ready[ti]};
                default:     rd_val = 8'd0;
            endcase
        end else if (in_srt) begin
            case (o_srt)
                HO_SRT_POSL: rd_val = s_pos[12*si +: 8];
                HO_SRT_POSH: rd_val = {s_starved[si], s_bidx[3*si +: 3], s_pos[12*si + 8 +: 4]};
                default:     rd_val = 8'd0;
            endcase
        end else if (in_dbg) begin
            case (o_dbg)
                HO_DBG_DBG:       rd_val = {7'd0, freeze};
                HO_DBG_MCTL:      rd_val = {7'd0, men};
                HO_DBG_ECTL:      rd_val = {6'd0, replay, cen};
                HO_DBG_MISR:      rd_val = misr[7:0];
                HO_DBG_MISR + 1:  rd_val = misr[15:8];
                HO_DBG_MISR + 2:  rd_val = misr[23:16];
                HO_DBG_MISR + 3:  rd_val = misr[31:24];
                HO_DBG_EMASK:     rd_val = emask[7:0];
                HO_DBG_EMASK + 1: rd_val = {3'd0, emask[12:8]};
                HO_DBG_RLV:       rd_val = rlv[7:0];
                HO_DBG_RLV + 1:   rd_val = {3'd0, rlv[12:8]};
                HO_DBG_ACC:       rd_val = acc_a;
                HO_DBG_AFLG:      rd_val = {5'd0, acc_n, acc_c, acc_z};
                HO_DBG_FLAGS:     rd_val = fl[7:0];
                HO_DBG_FLAGS + 1: rd_val = fl[15:8];
                HO_DBG_CST:       rd_val = {3'd0, c_rv[0], c_xv[0], xt[2:0]};
                HO_DBG_CST + 1:   rd_val = {3'd0, c_rv[1], c_xv[1], xt[5:3]};
                HO_DBG_FPC:       rd_val = c_fpc[7:0];
                HO_DBG_FPC + 1:   rd_val = c_fpc[15:8];
                default:          rd_val = 8'd0;
            endcase
        end
    end

    // ---------------------------------------------------------------- output pins (SPEC 8)
    generate
        for (k = 0; k < NO; k = k + 1) begin : g_out
            localparam integer OB = HAI_OUT_BASE - CFG_LO_I + HS_OUT * k;
            wire [7:0]  obind = cfg[8*(OB + HO_OUT_BIND) +: 8];
            wire [7:0]  sel  = cfg[8*(OB + HO_OUT_SEL) +: 8];
            wire _unused_o = &{1'b0, obind[7:5], sel[7:6]};
            wire [31:0] lut  = cfg[8*(OB + HO_OUT_LUT) +: 32];
            wire [1:0]  ln   = obind[1:0];
            wire [3:0]  cm   = l_comm[4*ln +: 4];
            // v3 LIVE (SPEC v2 12.1): bit 3 replaces b2 by PIN[PINA], bit 4 replaces b1 by PIN[PINB] of the line
            wire        b2   = obind[3] ? l_pina[ln] : cm[sel[5:4]];
            wire        b1   = obind[4] ? l_pinb[ln] : cm[sel[3:2]];
            wire [4:0]  idx  = obind[2] ? {l_seg[2*ln +: 2], b2, b1, cm[sel[1:0]]} : 5'd0;
            always @(posedge clk) begin
                if (!rst_q)    o_out[k] <= 1'b0;
                else if (!frz) o_out[k] <= lut[idx];
            end
            if (k < NOE) begin : g_oe
                wire [31:0] oe = cfg[8*(OB + HO_OUT_OE) +: 32];
                always @(posedge clk) begin
                    if (!rst_q)    o_oe[k] <= 1'b0;
                    else if (!frz) o_oe[k] <= oe[idx];
                end
            end
        end
    endgenerate

    assign uo_out  = {o_out[13:8], irq, miso};
    assign uio_out = o_out[7:0];
    assign uio_oe  = o_oe;

    // bits that exist only as configuration-window padding, or that a block does not use
    wire _unused = &{1'b0, ena, s1, sp[15:9], sp[7:0] & 8'd0, cfg, flp[15:8], t_trig, a_dat[15:11], a_prg[15:12], a_prg[2:0] & 3'd0,
                     i_lrt[15:2], i_trt[15:3], i_srt[15:1], o_ctl, o_lrt, o_trt, o_srt, w_flags[7:4], w_hout[13:8],
                     o_dbg, s_word[1], s_ww[63:32], s_replay_valid[1], s_replay_word[63:32]};
endmodule
`undef PICKG
`undef HITG
`undef OPG
`default_nettype wire
