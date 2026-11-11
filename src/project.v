// Metronome v1 top level (wiki/SPEC.md). Tiny Tapeout wrapper: pin map (SPEC 2), host register decode, global
// source and guard vectors, and the wiring of beat generators, engines, cores, move bus and units.
`timescale 1ns/1ps
`default_nettype none
// The official template keeps its top level in project.v.
/* verilator lint_off DECLFILENAME */
module tt_um_brentius_metronome (
    input  wire [7:0] ui_in,
    output wire [7:0] uo_out,
    input  wire [7:0] uio_in,
    output wire [7:0] uio_out,
    output wire [7:0] uio_oe,
    input  wire       ena,
    input  wire       clk,
    input  wire       rst_n
);
/* verilator lint_on DECLFILENAME */
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    localparam integer NE  = MD_N_ENGINES;
    localparam integer NB  = MD_N_BEATGENS;
    localparam integer NSH = MD_N_SHIFTERS;
    localparam integer NCN = MD_N_COUNTERS;
    localparam integer NLF = MD_N_LFSRS;
    localparam integer NR  = MD_N_ACC_REGS;
    localparam integer NO  = MD_N_OUT_PINS;

    md_layout_check u_layout_check ();

    // ---------------------------------------------------------------------------------------------------------
    // Pins (SPEC 2): synchronisers on ui_in[7:0] (bits 7:0) and uio_in[7:0] (bits 15:8)
    // ---------------------------------------------------------------------------------------------------------
    wire [15:0] s_lvl, s_rise, s_fall;
    md_sync #(.N(16)) u_sync (.clk(clk), .rst_n(rst_n), .raw({uio_in, ui_in}), .lvl(s_lvl), .rise(s_rise),
                              .fall(s_fall));
    // protocol pins P0..P12 = uio_in[0..7], ui_in[3..7]; selects 13..15 read 0
    wire [15:0] pin_lvl  = {3'd0, s_lvl[7:3],  s_lvl[15:8]};
    wire [15:0] pin_rise = {3'd0, s_rise[7:3], s_rise[15:8]};
    wire [15:0] pin_fall = {3'd0, s_fall[7:3], s_fall[15:8]};

    // ---------------------------------------------------------------------------------------------------------
    // Host link and register decode
    // ---------------------------------------------------------------------------------------------------------
    wire        h_we, h_re;
    wire [15:0] h_waddr, h_raddr;
    wire [7:0]  h_wd;
    reg  [7:0]  reg_rd;
    wire        hreq_set, hreq_wr, hland;
    wire [10:0] hreq_addr;
    wire [7:0]  hreq_d, hland_d;
    wire [1:0]  prog_we;
    wire [7:0]  prog_waddr;
    wire [7:0]  prog_be, prog_wd;
    wire        miso;
    md_spi u_spi (
        .clk(clk), .rst_n(rst_n), .sck_r(s_rise[0]), .sck_f(s_fall[0]), .cs_n(s_lvl[1]), .mosi(s_lvl[2]),
        .h_we(h_we), .h_waddr(h_waddr), .h_wd(h_wd), .h_re(h_re), .h_raddr(h_raddr), .reg_rd(reg_rd),
        .hreq_set(hreq_set), .hreq_wr(hreq_wr), .hreq_addr(hreq_addr), .hreq_d(hreq_d),
        .hland(hland), .hland_d(hland_d), .prog_we(prog_we), .prog_waddr(prog_waddr), .prog_be(prog_be),
        .prog_wd(prog_wd),
        .miso(miso)
    );

    // block select: a[15:sh] == (base + idx * stride)[15:sh], stride = 2^sh
    /* verilator lint_off UNUSEDSIGNAL */  // idx[31:16]: block indices are small
    function blk;
        input [15:0] a;
        input [15:0] base;
        input integer idx;
        input integer sh;
        reg [15:0] b;
        begin
            b   = base + (idx[15:0] << sh);
            blk = ((a ^ b) >> sh) == 16'd0;
        end
    endfunction
    /* verilator lint_on UNUSEDSIGNAL */
    // header code + offset as a 32-bit index (keeps the arithmetic width-clean)
    function integer ix;
        input [5:0] base;
        input integer off;
        begin
            ix = {26'd0, base} + off;
        end
    endfunction

    localparam [15:0] LF_BASE   = H_UNIT_BASE + {8'd0, HUNIT_LF0_POLY};
    localparam integer LF_SHIFT = 3;  // LFk.POLY at UNIT_BASE + HUNIT_LF0_POLY + 8k (checked in md_layout_check)

    // ---------------------------------------------------------------------------------------------------------
    // Move bus
    // ---------------------------------------------------------------------------------------------------------
    wire [2:0]  c0_en, c1_en, c0_xe, c1_xe;
    wire [17:0] c0_src, c1_src, c0_dst, c1_dst;
    wire [23:0] c0_data, c1_data;
    wire [5:0]  mv_en   = {c1_en, c0_en};
    wire [35:0] mv_src  = {c1_src, c0_src};
    wire [35:0] mv_dst  = {c1_dst, c0_dst};
    wire [47:0] mv_data = {c1_data, c0_data};

    wire            acc_we, fl_we, fl_sel, ho_we, conflict;
    wire [2:0]      acc_sel;
    wire [3:0]      fl_d;
    wire [7:0]      acc_d, ho_d;
    wire [NR-1:0]   r_we;
    wire [8*NR-1:0] r_d;
    wire [NSH-1:0]  sh_we, sh_sel, shc_we;
    wire [8*NSH-1:0] sh_d;
    wire [5*NSH-1:0] shc_d;
    wire [NCN-1:0]  cn_we;
    wire [2*NCN-1:0] cn_sel;
    wire [8*NCN-1:0] cn_d;
    wire [NLF-1:0]  lf_we;
    wire [3*NLF-1:0] lf_sel;
    wire [8*NLF-1:0] lf_d;
    wire [1:0]      p_we;
    wire [3:0]      p_sel;
    wire [15:0]     p_d;
    wire [NB-1:0]   bgm_we;
    wire [3*NB-1:0] bgm_d;
    wire [NE-1:0]   sym_we, stop_we;
    wire [2*NE-1:0] sym_d;
    md_movebus #(.NE(NE), .NB(NB), .NSH(NSH), .NCN(NCN), .NLF(NLF), .NR(NR), .NP(MD_N_PTRS)) u_movebus (
        .en(mv_en), .dst(mv_dst), .data(mv_data), .xe0(c0_xe), .xe1(c1_xe),
        .acc_we(acc_we), .acc_sel(acc_sel), .acc_d(acc_d), .r_we(r_we), .r_d(r_d),
        .sh_we(sh_we), .sh_sel(sh_sel), .sh_d(sh_d), .shc_we(shc_we), .shc_d(shc_d),
        .cn_we(cn_we), .cn_sel(cn_sel), .cn_d(cn_d), .lf_we(lf_we), .lf_sel(lf_sel), .lf_d(lf_d),
        .p_we(p_we), .p_sel(p_sel), .p_d(p_d), .fl_we(fl_we), .fl_sel(fl_sel), .fl_d(fl_d),
        .bg_we(bgm_we), .bg_d(bgm_d), .ho_we(ho_we), .ho_d(ho_d), .sym_we(sym_we), .sym_d(sym_d),
        .stop_we(stop_we), .conflict(conflict)
    );

    // ---------------------------------------------------------------------------------------------------------
    // Units
    // ---------------------------------------------------------------------------------------------------------
    wire [15:0] f, f_rise;
    md_flags u_flags (.clk(clk), .rst_n(rst_n), .we(fl_we), .sel(fl_sel), .d(fl_d), .f(f), .f_rise(f_rise));

    wire [7:0]      acc_a;
    wire            acc_z, acc_c, acc_n;
    wire [8*NR-1:0] acc_r;
    md_acc #(.NR(NR)) u_acc (.clk(clk), .rst_n(rst_n), .we(acc_we), .sel(acc_sel), .d(acc_d), .r_we(r_we),
                             .r_d(r_d), .a(acc_a), .z(acc_z), .c(acc_c), .n(acc_n), .r(acc_r));

    wire [8*NSH-1:0] sh_dr;
    wire [NSH-1:0]   sh_o, sh_done;
    wire [16*NCN-1:0] cn_v;
    wire [NCN-1:0]   cn_z;
    wire [32*NLF-1:0] lf_s;
    genvar k;
    generate
        for (k = 0; k < NSH; k = k + 1) begin : g_sh
            md_shifter u (.clk(clk), .rst_n(rst_n), .we(sh_we[k]), .sel(sh_sel[k]),
                          .d(sh_d[8*k +: 8]), .cfg_we(shc_we[k]), .cfg_d(shc_d[5*k +: 5]),
                                   .dr(sh_dr[8*k +: 8]), .o(sh_o[k]), .done(sh_done[k]));
        end
        for (k = 0; k < NCN; k = k + 1) begin : g_cn
            md_counter u (.clk(clk), .rst_n(rst_n), .we(cn_we[k]), .sel(cn_sel[2*k +: 2]),
                                   .d(cn_d[8*k +: 8]), .v(cn_v[16*k +: 16]), .z(cn_z[k]));
        end
        for (k = 0; k < NLF; k = k + 1) begin : g_lf
            md_lfsr u (.clk(clk), .rst_n(rst_n), .we(lf_we[k]), .sel(lf_sel[3*k +: 3]), .d(lf_d[8*k +: 8]),
                       .h_we(h_we && blk(h_waddr, LF_BASE, k, LF_SHIFT) && (h_waddr[2] == 1'b0)),
                       .h_byte(h_waddr[1:0]), .h_wd(h_wd), .s(lf_s[32*k +: 32]));
        end
    endgenerate

    wire [1:0]  p_rdy;
    wire [15:0] p_pd;
    wire        ptr_haz;
    wire        m_en, m_we;
    wire [10:0] m_addr;
    wire [7:0]  m_wd, m_rd;
    md_ptrs u_ptrs (
        .clk(clk), .rst_n(rst_n), .we(p_we), .sel(p_sel), .d(p_d),
        .hreq_set(hreq_set), .hreq_wr(hreq_wr), .hreq_addr(hreq_addr), .hreq_d(hreq_d),
        .rdy(p_rdy), .pd(p_pd), .memhaz(ptr_haz), .hland(hland), .hland_d(hland_d),
        .m_en(m_en), .m_we(m_we), .m_addr(m_addr), .m_wd(m_wd), .m_rd(m_rd)
    );
    data_mem u_dmem (.clk(clk), .en(m_en), .we(m_we), .addr(m_addr), .wd(m_wd), .rd(m_rd));

    // source side effects (enabled moves only): HOST.IN read clears INV; Pk.D read with RDY == 0 -> MEMHAZ
    reg hin_rd, pd_haz;
    integer j;
    always @* begin
        hin_rd = 1'b0;
        pd_haz = 1'b0;
        for (j = 0; j < 6; j = j + 1) begin
            if (mv_en[j] && mv_src[6*j +: 6] == S_HOST_IN) hin_rd = 1'b1;
            if (mv_en[j] && mv_src[6*j +: 6] == S_P0_D && !p_rdy[0]) pd_haz = 1'b1;
            if (mv_en[j] && mv_src[6*j +: 6] == S_P1_D && !p_rdy[1]) pd_haz = 1'b1;
        end
    end

    wire          run_g, inv, outv, hostinv_rise, irq;
    wire [7:0]    inb, ctrl_hrd;
    wire [NE-1:0] doorbell, e_err;
    md_ctrl #(.NE(NE)) u_ctrl (
        .clk(clk), .rst_n(rst_n),
        .h_we(h_we && blk(h_waddr, H_CTRL_BASE, 0, 3)), .h_off(h_waddr[2:0]), .h_wd(h_wd),
        .h_roff(h_raddr[2:0]), .h_rd(ctrl_hrd),
        .ho_we(ho_we), .ho_d(ho_d), .hin_rd(hin_rd), .conflict_set(conflict), .memhaz_set(ptr_haz | pd_haz),
        .eng_err(|e_err), .run_g(run_g), .doorbell(doorbell), .inb(inb), .inv(inv), .outv(outv),
        .hostinv_rise(hostinv_rise), .irq(irq)
    );

    // ---------------------------------------------------------------------------------------------------------
    // Beat generators
    // ---------------------------------------------------------------------------------------------------------
    wire [NB-1:0]   bg_beat, bg_sp, bg_run;
    wire [3*NB-1:0] bg_tap;
    wire [2*NB-1:0] bg_seg;
    wire [8*NB-1:0] bg_hrd;
    generate
        for (k = 0; k < NB; k = k + 1) begin : g_bg
            md_beatgen u (
                .clk(clk), .rst_n(rst_n), .h_we(h_we && blk(h_waddr, H_BG_BASE, k, 5)), .h_off(h_waddr[4:0]),
                .h_wd(h_wd), .h_roff(h_raddr[4:0]), .h_rd(bg_hrd[8*k +: 8]), .mv_we(bgm_we[k]),
                .mv_d(bgm_d[3*k +: 3]), .pin_rise(pin_rise), .pin_fall(pin_fall), .beat(bg_beat[k]),
                .tap(bg_tap[3*k +: 3]), .seg(bg_seg[2*k +: 2]), .sp_o(bg_sp[k]), .run_o(bg_run[k])
            );
        end
    endgenerate

    // ---------------------------------------------------------------------------------------------------------
    // Global source and guard vectors (indexed by the header's S_* / G_* codes; engine-relative slots and IMM
    // are filled in per core / per engine)
    // ---------------------------------------------------------------------------------------------------------
    reg [63:0]  grd_g;
    always @* begin
        grd_g = 64'd0;
        grd_g[G_TRUE] = 1'b1;
        for (j = 0; j < 16; j = j + 1)  grd_g[ix(G_F0, j)]       = f[j];
        for (j = 0; j < NSH; j = j + 1) grd_g[ix(G_SH0_DONE, j)] = sh_done[j];
        for (j = 0; j < NSH; j = j + 1) grd_g[ix(G_SH0_OUT, j)]  = sh_o[j];
        for (j = 0; j < NCN; j = j + 1) grd_g[ix(G_CNT0_Z, j)]   = cn_z[j];
        grd_g[G_ACC_Z] = acc_z;
        grd_g[G_ACC_C] = acc_c;
        grd_g[G_ACC_N] = acc_n;
        for (j = 0; j < NLF; j = j + 1) grd_g[ix(G_LF0_OUT, j)]  = lf_s[32*j];
        grd_g[G_HOST_INV]  = inv;
        grd_g[G_HOST_OUTE] = ~outv;
        grd_g[G_P0_RDY]    = p_rdy[0];
        grd_g[G_P1_RDY]    = p_rdy[1];
        for (j = 0; j < MD_N_IN_PINS; j = j + 1) grd_g[ix(G_PIN0, j)] = pin_lvl[j];
        for (j = 0; j < NB; j = j + 1)  grd_g[ix(G_BG0_RUN, j)]  = bg_run[j];
    end

    // ---------------------------------------------------------------------------------------------------------
    // Engines
    // ---------------------------------------------------------------------------------------------------------
    wire [NE-1:0]   e_ready, e_running, e_core, e_sync, e_pina, e_pinb;
    wire [8*NE-1:0] e_pc, e_w0h, e_w1h, e_hrd;
    wire [6*NE-1:0] e_w0c, e_w1c;
    wire [2*NE-1:0] e_in, e_seg, e_com;
    wire [4*NE-1:0] e_cap;
    wire            c0_pause, c1_pause, c0_disp, c1_disp;
    wire [7:0]      c0_npc, c1_npc;
    wire [2:0]      c0_de, c1_de;
    generate
        for (k = 0; k < NE; k = k + 1) begin : g_eng
            wire p0 = c0_pause && (c0_xe == k);
            wire p1 = c1_pause && (c1_xe == k);
            md_engine #(.NB(NB)) u (
                .clk(clk), .rst_n(rst_n), .h_we(h_we && blk(h_waddr, H_ENG_BASE, k, 5)),
                .h_off(h_waddr[4:0]), .h_wd(h_wd), .h_roff(h_raddr[4:0]), .h_rd(e_hrd[8*k +: 8]),
                .doorbell(doorbell[k]), .bg_beat(bg_beat), .bg_tap(bg_tap), .bg_seg(bg_seg), .bg_sp(bg_sp),
                .pin_lvl(pin_lvl), .pin_rise(pin_rise), .pin_fall(pin_fall), .flag_rise(f_rise[7:0]),
                .hostinv_rise(hostinv_rise), .sym_we(sym_we[k]), .sym_d(sym_d[2*k +: 2]),
                .stop_we(stop_we[k]),
                .disp((c0_disp && c0_de == k) || (c1_disp && c1_de == k)),
                .pause(p0 | p1), .pause_pc(p0 ? c0_npc : c1_npc),
                .ready(e_ready[k]), .running(e_running[k]), .core_sel(e_core[k]), .pc(e_pc[8*k +: 8]),
                .w0c(e_w0c[6*k +: 6]), .w1c(e_w1c[6*k +: 6]), .w0h(e_w0h[8*k +: 8]), .w1h(e_w1h[8*k +: 8]),
                .in_sym(e_in[2*k +: 2]), .cap_o(e_cap[4*k +: 4]), .sync(e_sync[k]), .pina(e_pina[k]),
                .pinb(e_pinb[k]), .seg(e_seg[2*k +: 2]), .committed(e_com[2*k +: 2]), .err(e_err[k])
            );
        end
    endgenerate

    // ---------------------------------------------------------------------------------------------------------
    // Cores and program memories
    // ---------------------------------------------------------------------------------------------------------
    wire [63:0] c0_insn, c1_insn;
    wire        c0_fen, c1_fen;
    wire [7:0]  c0_fa, c1_fa;
    md_core #(.C(0), .NE(NE), .NR(NR), .NSH(NSH), .NCN(NCN), .NLF(NLF)) u_core0 (
        .clk(clk), .rst_n(rst_n), .insn(c0_insn), .run_g(run_g), .e_ready(e_ready), .e_core(e_core),
        .e_pc(e_pc), .e_w0c(e_w0c), .e_w1c(e_w1c), .e_w0h(e_w0h), .e_w1h(e_w1h),
        .e_in(e_in), .e_cap(e_cap), .e_sync(e_sync), .e_pina(e_pina), .e_pinb(e_pinb),
        .s_f(f), .s_pin(pin_lvl[12:0]), .s_acc(acc_a), .s_r(acc_r), .s_shd(sh_dr), .s_sho(sh_o), .s_cnt(cn_v),
        .s_lf(lf_s), .s_pd(p_pd), .s_inb(inb), .grd_g(grd_g), .fetch_en(c0_fen), .fetch_addr(c0_fa), .pause_o(c0_pause),
        .npc_o(c0_npc), .disp_o(c0_disp), .disp_e(c0_de), .xe(c0_xe), .mv_en(c0_en), .mv_src(c0_src),
        .mv_dst(c0_dst), .mv_data(c0_data)
    );
    md_core #(.C(1), .NE(NE), .NR(NR), .NSH(NSH), .NCN(NCN), .NLF(NLF)) u_core1 (
        .clk(clk), .rst_n(rst_n), .insn(c1_insn), .run_g(run_g), .e_ready(e_ready), .e_core(e_core),
        .e_pc(e_pc), .e_w0c(e_w0c), .e_w1c(e_w1c), .e_w0h(e_w0h), .e_w1h(e_w1h),
        .e_in(e_in), .e_cap(e_cap), .e_sync(e_sync), .e_pina(e_pina), .e_pinb(e_pinb),
        .s_f(f), .s_pin(pin_lvl[12:0]), .s_acc(acc_a), .s_r(acc_r), .s_shd(sh_dr), .s_sho(sh_o), .s_cnt(cn_v),
        .s_lf(lf_s), .s_pd(p_pd), .s_inb(inb), .grd_g(grd_g), .fetch_en(c1_fen), .fetch_addr(c1_fa), .pause_o(c1_pause),
        .npc_o(c1_npc), .disp_o(c1_disp), .disp_e(c1_de), .xe(c1_xe), .mv_en(c1_en), .mv_src(c1_src),
        .mv_dst(c1_dst), .mv_data(c1_data)
    );
    // host writes take priority over fetches
    prog_mem u_pmem0 (.clk(clk), .ren(c0_fen), .we(prog_we[0]), .addr(prog_we[0] ? prog_waddr : c0_fa),
                      .be(prog_be), .wd(prog_wd), .rd(c0_insn));
    prog_mem u_pmem1 (.clk(clk), .ren(c1_fen), .we(prog_we[1]), .addr(prog_we[1] ? prog_waddr : c1_fa),
                      .be(prog_be), .wd(prog_wd), .rd(c1_insn));

    // ---------------------------------------------------------------------------------------------------------
    // Output cells
    // ---------------------------------------------------------------------------------------------------------
    wire [NO-1:0]   o_out, o_oen;
    generate
        for (k = 0; k < NO; k = k + 1) begin : g_out
            md_outcell #(.NE(NE), .HAS_OE(k < MD_N_OE_PINS ? 1 : 0)) u (
                .clk(clk), .rst_n(rst_n), .h_we(h_we && blk(h_waddr, H_OUT_BASE, k, 3)), .h_off(h_waddr[2:0]),
                .h_wd(h_wd), .e_seg(e_seg), .e_com(e_com),
                .out(o_out[k]), .oen(o_oen[k])
            );
        end
    endgenerate

    // ---------------------------------------------------------------------------------------------------------
    // Host register read mux (AND-OR over block selects). Unmapped addresses, program memory and the
    // write-only configuration registers (D14: output cells, LFSR POLY) read 0.
    // ---------------------------------------------------------------------------------------------------------
    always @* begin
        reg_rd = 8'd0;
        for (j = 0; j < NB; j = j + 1)
            if (blk(h_raddr, H_BG_BASE, j, 5)) reg_rd = reg_rd | bg_hrd[8*j +: 8];
        for (j = 0; j < NE; j = j + 1)
            if (blk(h_raddr, H_ENG_BASE, j, 5)) reg_rd = reg_rd | e_hrd[8*j +: 8];
        if (blk(h_raddr, H_CTRL_BASE, 0, 3)) reg_rd = reg_rd | ctrl_hrd;
    end

    // ---------------------------------------------------------------------------------------------------------
    // Outputs (all registered): O0..O7 = uio_out, O8..O13 = uo_out[2..7], MISO = uo_out[0], IRQ = uo_out[1]
    // ---------------------------------------------------------------------------------------------------------
    assign uio_out = o_out[7:0];
    assign uio_oe  = o_oen[7:0];
    assign uo_out  = {o_out[13:8], irq, miso};

    // ena is unused (TT convention); e_running is for debug only; h_re has no side effects outside md_spi (SPEC 9)
    // s_lvl[0]: SCK is used through its edges; s_rise/s_fall[2:1]: CS_N and MOSI are used as levels;
    // f_rise[15:8]: only flags 0..7 have rise triggers.
    wire unused_ok = &{1'b0, ena, e_running, h_re, o_oen[NO-1:MD_N_OE_PINS], s_lvl[0], s_rise[2:1], s_fall[2:1],
                       f_rise[15:8]};
endmodule
`default_nettype wire
