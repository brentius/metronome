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
    reg rst_m, rst_q;
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
    wire [15:0] lvl  = {3'd0, s2[15:11], s2[7:0]};
    wire [15:0] rise = {3'd0, s2[15:11] & ~sp[15:11], s2[7:0] & ~sp[7:0]};
    wire [15:0] fall = {3'd0, ~s2[15:11] & sp[15:11], ~s2[7:0] & sp[7:0]};

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
    wire [15:0] a_cfg = ha - CFG_LO;
    wire [15:0] a_prg = ha - HA_PROG_BASE;
    wire in_ctl = (a_ctl < HSPAN_CTRL);
    wire in_lrt = (a_lrt < HSPAN_LRT);
    wire in_trt = (a_trt < HSPAN_TRT);
    wire in_srt = (a_srt < HSPAN_SRT);
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
    wire w_ctl = h_wr & in_ctl;
    wire w_lrt = h_wr & in_lrt;
    wire w_trt = h_wr & in_trt;
    wire w_srt = h_wr & in_srt;

    // ---------------------------------------------------------------- configuration latches
    wire [8*CFG_BYTES-1:0] cfg;
    md2_cfg_bank #(.BYTES(CFG_BYTES), .MASK(CFG_MASK), .AW(9)) u_cfg (
        .clk(clk), .rst_n(rst_n), .we(h_wr & in_cfg), .waddr(a_cfg[8:0]), .wdata(h_wd), .q(cfg)
    );

    // ---------------------------------------------------------------- global state declared ahead
    reg         run_g, conflict, memhaz, irq;
    reg  [1:0]  irqen;
    reg  [NT-1:0] db;
    reg  [15:0] fl, flp;
    reg  [7:0]  inb, outb;
    reg         inv, invp, outv;
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
                .clk(clk), .rst_n(rst_q), .run_g(run_g), .rdata(pm_rd[k]), .fetch_en(fen[k]),
                .fetch_addr(fadr[8*k +: 8]),
                .t_ready(t_ready), .t_core(t_core), .t_line(t_line), .t_pc(t_pc),
                .t_w0c(t_w0c), .t_w1c(t_w1c), .t_w0h(t_w0h), .t_w1h(t_w1h),
                .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap),
                .pause_o(pse[k]), .npc_o(npc[8*k +: 8]), .disp_o(dsp[k]), .disp_e(disp_e[3*k +: 3]),
                .xt_o(xt[3*k +: 3]), .xl_o(xl[2*k +: 2]),
                .mv_en(c_en[3*k +: 3]), .mv_src(c_src[18*k +: 18]), .mv_dst(c_dst[18*k +: 18]),
                .mv_data(c_dat[24*k +: 24])
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

    // winner of a group key: we, dst, data
    function [14:0] pick;           // {we, dst[5:0], data[7:0]}
        input [5:0]  hit;
        input [35:0] dst;
        input [47:0] dat;
        integer q;
        begin
            pick = 15'd0;
            for (q = 0; q < 6; q = q + 1)
                if (hit[q]) pick = {1'b1, dst[6*q +: 6], dat[8*q +: 8]};
        end
    endfunction
    function [5:0] hits;
        input [5:0] win;
        input [29:0] g;
        input [4:0] want;
        integer q;
        begin
            for (q = 0; q < 6; q = q + 1) hits[q] = win[q] & (g[5*q +: 5] == want);
        end
    endfunction
    wire [29:0] grp_v = {grp[5], grp[4], grp[3], grp[2], grp[1], grp[0]};
    // winner of a plain group (a macro, not a function, so that simulators see every operand)
`define PICKG(G) pick(hits(mv_win, grp_v, G), c_dst, c_dat)

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
    wire [14:0] w_acc   = `PICKG(DG_ACC);
    wire [14:0] w_p0    = `PICKG(DG_P0);
    wire [14:0] w_hout  = `PICKG(DG_HOST_OUT);

    reg [2:0] acc_sel;
    always @* begin
        case (w_acc[13:8])
            D_ACC_LD:  acc_sel = 3'd0;
            D_ACC_ADD: acc_sel = 3'd1;
            D_ACC_SUB: acc_sel = 3'd2;
            D_ACC_AND: acc_sel = 3'd3;
            D_ACC_OR:  acc_sel = 3'd4;
            D_ACC_XOR: acc_sel = 3'd5;
            default:   acc_sel = 3'd6;     // D_ACC_CMP
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
        .clk(clk), .rst_n(rst_q), .we(w_acc[14]), .sel(acc_sel), .d(w_acc[7:0]), .r_we(r_we), .r_d(r_d),
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
            md2_shifter u (
                .clk(clk), .rst_n(rst_q), .we(w[14]), .sel(w[13:8] == D_SHSH[6*k +: 6]), .d(w[7:0]),
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
            wire [1:0] sel = (w[13:8] == D_CNLO[6*k +: 6]) ? 2'd0 : ((w[13:8] == D_CNHI[6*k +: 6]) ? 2'd1 : 2'd2);
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
            wire [5:0]  d = w[13:8];
            wire [2:0] sel = (d == D_LFST[6*k +: 6])     ? 3'd0 :
                             (d == D_LFB[6*(4*k) +: 6])   ? 3'd1 :
                             (d == D_LFB[6*(4*k+1) +: 6]) ? 3'd2 :
                             (d == D_LFB[6*(4*k+2) +: 6]) ? 3'd3 : 3'd4;
            localparam integer PB = HAI_LFSR_BASE - CFG_LO_I + HS_LFSR * k + HO_LFSR_POLY;
            md2_lfsr u (.clk(clk), .rst_n(rst_q), .we(w[14]), .sel(sel), .d(w[7:0]), .poly(cfg[8*PB +: 32]),
                        .s(lf_s[32*k +: 32]));
        end
    endgenerate

    // data RAM, pointer, streams
    wire [1:0]  s_req, s_we, s_gnt, s_bit, s_end, s_mark, s_bb, s_starved;
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
            wire        mctl = w[14] & (w[13:8] == D_SCTL[6*k +: 6]);
            wire        hctl = w_srt & (i_srt == k) & (o_srt == HO_SRT_CTL);
            localparam integer SB = HAI_STREAM_BASE - CFG_LO_I + HS_STREAM * k;
            wire [7:0]  mode = cfg[8*(SB + HO_STREAM_MODE) +: 8];
            wire _unused_s = &{1'b0, w[7:2], mode[7:2]};
            md2_stream u (
                .clk(clk), .rst_n(rst_q),
                .cfg_mode(mode[0]), .cfg_msb(mode[1]),
                .cfg_start(cfg[8*(SB + HO_STREAM_START) +: 11]),
                .cfg_len(cfg[8*(SB + HO_STREAM_LEN) +: 12]),
                .cfg_mark(cfg[8*(SB + HO_STREAM_MARK) +: 12]),
                .adv(w[14] & (w[13:8] == D_SADV[6*k +: 6])),
                .rx_we(w[14] & (w[13:8] == D_SRX[6*k +: 6])), .rx_bit(w[0]),
                .rewind((mctl & w[0]) | (hctl & h_wd[0])), .flush((mctl & w[1]) | (hctl & h_wd[1])),
                .clr_starved(hctl & h_wd[7]),
                .bit_out(s_bit[k]), .byte_out(s_byte[8*k +: 8]), .g_end(s_end[k]), .g_mark(s_mark[k]),
                .g_byte(s_bb[k]), .starved(s_starved[k]), .pos(s_pos[12*k +: 12]), .bidx(s_bidx[3*k +: 3]),
                .req(s_req[k]), .req_we(s_we[k]), .req_addr(s_addr[11*k +: 11]), .req_wdata(s_wd[8*k +: 8]),
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
        .clk(clk), .rst_n(rst_q),
        .s_req(s_req), .s_we(s_we), .s_addr(s_addr), .s_wd(s_wd), .s_gnt(s_gnt),
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
                .clk(clk), .rst_n(rst_q), .cfg(cfg[8*LB +: 8*HS_LINE]), .lvl(lvl), .rise(rise), .fall(fall),
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
                .clk(clk), .rst_n(rst_q), .ev(ev), .db(db[k]), .disp(disp), .pause(pause),
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
    wire memhaz_ev  = p_haz | (|rd_pd & ~p_rdy);
    wire err = conflict | memhaz | (|t_late) | (|t_ovr) | (|l_tapmiss) | (|s_starved);
    always @(posedge clk) begin
        if (!rst_q) begin
            run_g <= 1'b0; conflict <= 1'b0; memhaz <= 1'b0; irq <= 1'b0; irqen <= 2'd0; db <= {NT{1'b0}};
            fl <= 16'd0; flp <= 16'd0; inb <= 8'd0; outb <= 8'd0; inv <= 1'b0; invp <= 1'b0; outv <= 1'b0;
        end else begin
            flp <= fl;
            if (w_flags[14]) fl[w_flags[3:0]] <= (w_flags[13:8] == D_FLAGS_SET);
            invp <= inv;
            if (c_wr_hin)         begin inb <= h_wd; inv <= 1'b1; end
            else if (|rd_hin)     inv <= 1'b0;
            if (w_hout[14])       begin outb <= w_hout[7:0]; outv <= 1'b1; end
            else if (c_wr_hst & h_wd[1]) outv <= 1'b0;
            conflict <= conflict_ev | (conflict & ~(c_wr_stk & h_wd[0]));
            memhaz   <= memhaz_ev   | (memhaz   & ~(c_wr_stk & h_wd[1]));
            irq <= (irqen[0] & outv) | (irqen[1] & err);
            if (c_wr_run)   run_g <= h_wd[0];
            if (c_wr_irqen) irqen <= h_wd[1:0];
            db <= c_wr_db ? h_wd[NT-1:0] : {NT{1'b0}};
        end
    end

    // ---------------------------------------------------------------- host register reads (value in cycle R)
    wire [7:0] errsum = {2'd0, memhaz, conflict, |s_starved, |l_tapmiss, |t_ovr, |t_late};
    wire [1:0] li = i_lrt[1:0];
    wire [2:0] ti = i_trt[2:0];
    wire       si = i_srt[0];
    always @* begin
        rd_val = 8'd0;
        if (in_ctl) begin
            case (o_ctl)
                HO_CTRL_RUN:      rd_val = {7'd0, run_g};
                HO_CTRL_STICKY:   rd_val = {6'd0, memhaz, conflict};
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
        end
    end

    // ---------------------------------------------------------------- output pins (SPEC 8)
    reg [NO-1:0]  o_out;
    reg [NOE-1:0] o_oe;
    generate
        for (k = 0; k < NO; k = k + 1) begin : g_out
            localparam integer OB = HAI_OUT_BASE - CFG_LO_I + HS_OUT * k;
            wire [7:0]  obind = cfg[8*(OB + HO_OUT_BIND) +: 8];
            wire [7:0]  sel  = cfg[8*(OB + HO_OUT_SEL) +: 8];
            wire _unused_o = &{1'b0, obind[7:3], sel[7:6]};
            wire [31:0] lut  = cfg[8*(OB + HO_OUT_LUT) +: 32];
            wire [1:0]  ln   = obind[1:0];
            wire [3:0]  cm   = l_comm[4*ln +: 4];
            wire [4:0]  idx  = obind[2] ? {l_seg[2*ln +: 2], cm[sel[5:4]], cm[sel[3:2]], cm[sel[1:0]]} : 5'd0;
            always @(posedge clk) begin
                if (!rst_q) o_out[k] <= 1'b0;
                else        o_out[k] <= lut[idx];
            end
            if (k < NOE) begin : g_oe
                wire [31:0] oe = cfg[8*(OB + HO_OUT_OE) +: 32];
                always @(posedge clk) begin
                    if (!rst_q) o_oe[k] <= 1'b0;
                    else        o_oe[k] <= oe[idx];
                end
            end
        end
    endgenerate

    assign uo_out  = {o_out[13:8], irq, miso};
    assign uio_out = o_out[7:0];
    assign uio_oe  = o_oe;

    // bits that exist only as configuration-window padding, or that a block does not use
    wire _unused = &{1'b0, ena, s1, sp[15:9], sp[7:0] & 8'd0, cfg, flp[15:8], t_trig, a_dat[15:11], a_prg[15:12], a_prg[2:0] & 3'd0,
                     i_lrt[15:2], i_trt[15:3], i_srt[15:1], o_ctl, o_lrt, o_trt, o_srt, w_flags[7:4], w_hout[13:8]};
endmodule
`undef PICKG
`default_nettype wire
