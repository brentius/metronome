// Metronome v2 sizing wrapper: two pipelined cores (md2_core), their program memories (md2_core_pmem) and six
// thread state slices (md2_core_thread). The commons is a stub: guards, sources and per-line inputs are ports,
// and each core's three move descriptors are outputs. Thread configuration (CORE, LINE, watchers) is a port
// bundle standing in for the v2 latch array. Not part of the submission view (src/); sizing and timing study only.
`timescale 1ns/1ps
`default_nettype none
module md2_core_top (
    input  wire          clk,
    input  wire          rst_n,
    input  wire          run_g,         // RUN_global
    input  wire [5:0]    trig,          // one trigger event per thread
    // host writes to thread state
    input  wire [5:0]    h_pc_we,
    input  wire [7:0]    h_pc_d,
    input  wire [5:0]    h_en_we,
    input  wire          h_en_d,
    // thread configuration (latches in v2)
    input  wire [5:0]    t_core,
    input  wire [11:0]   t_line,
    input  wire [35:0]   t_w0c,
    input  wire [35:0]   t_w1c,
    input  wire [47:0]   t_w0h,
    input  wire [47:0]   t_w1h,
    // program load (bench only; RUN_global = 0 while loading)
    input  wire          pw_en,
    input  wire          pw_core,
    input  wire [7:0]    pw_addr,
    input  wire [63:0]   pw_data,
    // commons stub
    input  wire [63:0]   guards,        // global guard vector; line-relative slots are replaced in the core
    input  wire [19:0]   g_line,        // per line {L.PINB, L.PINA, L.SYNC, L.IN1, L.IN0}
    input  wire [511:0]  srcs,          // 64 x 8 source bundle; IMM, L.IN and L.CAP slots are replaced in the core
    input  wire [7:0]    l_in,          // per line input symbol (2 bits)
    input  wire [19:0]   l_cap,         // per line snapshot (5 bits)
    // per core c: moves and the executing thread
    output wire [5:0]    mv_en,         // {core1 m2..m0, core0 m2..m0}
    output wire [35:0]   mv_dst,
    output wire [47:0]   mv_data,
    output wire [1:0]    x_valid,
    output wire [5:0]    x_thread,
    output wire [3:0]    x_line,
    // thread state (observation)
    output wire [5:0]    t_ready,
    output wire [5:0]    t_running,
    output wire [5:0]    t_en,
    output wire [47:0]   t_pc,
    output wire [5:0]    t_ovr
);
    wire [1:0]  pause, disp, stop;
    wire [15:0] npc;
    wire [5:0]  disp_e, xe;

    genvar c, k;
    generate
        for (c = 0; c < 2; c = c + 1) begin : g_core
            wire        fen;
            wire [7:0]  fadr;
            wire [63:0] rd;
            md2_core_pmem u_pm (
                .clk(clk), .ren(fen), .we(pw_en & (pw_core == c[0])),
                .addr((pw_en & (pw_core == c[0])) ? pw_addr : fadr), .wd(pw_data), .rd(rd)
            );
            md2_core #(.C(c)) u_core (
                .clk(clk), .rst_n(rst_n), .run_g(run_g), .rdata(rd), .fetch_en(fen), .fetch_addr(fadr),
                .t_ready(t_ready), .t_core(t_core), .t_line(t_line), .t_pc(t_pc),
                .t_w0c(t_w0c), .t_w1c(t_w1c), .t_w0h(t_w0h), .t_w1h(t_w1h),
                .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap),
                .pause_o(pause[c]), .npc_o(npc[8*c +: 8]), .disp_o(disp[c]), .disp_e(disp_e[3*c +: 3]),
                .stop_o(stop[c]), .xv_o(x_valid[c]), .xe_o(xe[3*c +: 3]), .xl_o(x_line[2*c +: 2]),
                .mv_en(mv_en[3*c +: 3]), .mv_dst(mv_dst[18*c +: 18]), .mv_data(mv_data[24*c +: 24])
            );
        end
        for (k = 0; k < 6; k = k + 1) begin : g_thr
            // a thread is bound to one core, so at most one core addresses it in a cycle
            wire h0 = (xe[2:0] == k[2:0]);
            wire h1 = (xe[5:3] == k[2:0]);
            wire p0 = pause[0] & h0;
            wire p1 = pause[1] & h1;
            md2_core_thread u_thr (
                .clk(clk), .rst_n(rst_n), .trig(trig[k]),
                .h_pc_we(h_pc_we[k]), .h_pc_d(h_pc_d), .h_en_we(h_en_we[k]), .h_en_d(h_en_d),
                .disp((disp[0] & (disp_e[2:0] == k[2:0])) | (disp[1] & (disp_e[5:3] == k[2:0]))),
                .pause(p0 | p1), .npc(p1 ? npc[15:8] : npc[7:0]),
                .stop((stop[0] & h0) | (stop[1] & h1)),
                .ready(t_ready[k]), .running(t_running[k]), .en(t_en[k]), .pc(t_pc[8*k +: 8]), .ovr(t_ovr[k])
            );
        end
    endgenerate
    assign x_thread = xe;
endmodule
`default_nettype wire
