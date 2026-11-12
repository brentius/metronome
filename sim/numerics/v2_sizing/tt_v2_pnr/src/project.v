/*
 * SPDX-License-Identifier: Apache-2.0
 */
// Metronome v2 place-and-route sizing top. Integrates the v2 sizing blocks in a real Tiny Tapeout context:
// two pipelined cores (md2_core) with their 256x64 program SRAMs, six thread slices (md2_core_thread), thread and
// stream configuration in a latch bank (cfg_latch_bank), one stream (md2_stream) on the 512x32 data SRAM, the v2
// SPI host link (md2_host), and a commons stand-in (md2_commons_stub). Not the v2 design: the host map, the
// commons and the thread start rules are sizing choices, documented in docs/info.md. SPEC v2 fixes the real ones.
`timescale 1ns/1ps
`default_nettype none
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
/* verilator lint_off UNUSEDPARAM */
`undef MD2_DEFS_VH
`include "md2_defs.vh"
/* verilator lint_on UNUSEDPARAM */

    localparam integer CFG_BYTES = 56;      // 6 threads x 8 bytes, then 8 stream bytes
    localparam integer CFG_S0    = 48;

    // ---------------------------------------------------------------- reset: async assert, synchronous release
    // rst_n is used only asynchronously (here and in the latch bank's own synchroniser); the rest of the design
    // resets synchronously on rst_q.
    reg rst_m, rst_q;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rst_m <= 1'b0; rst_q <= 1'b0;
        end else begin
            rst_m <= 1'b1; rst_q <= rst_m;
        end
    end

    // ---------------------------------------------------------------- input pins P12..P0 (2-flop synchronisers)
    reg [12:0] pin_m, pin_s;
    always @(posedge clk) begin
        if (!rst_q) begin
            pin_m <= 13'd0; pin_s <= 13'd0;
        end else begin
            pin_m <= {ui_in[7:3], uio_in};
            pin_s <= pin_m;
        end
    end

    // ---------------------------------------------------------------- host link and address decode
    wire        h_wr, h_rd, miso;
    wire [15:0] ha;
    wire [7:0]  hwd;
    reg         rd_ack;
    reg  [7:0]  rd_data;
    md2_host u_host (
        .clk(clk), .rst_n(rst_q), .sck(ui_in[0]), .cs_n(ui_in[1]), .mosi(ui_in[2]), .miso(miso),
        .wr(h_wr), .rd(h_rd), .addr(ha), .wdata(hwd), .rd_ack(rd_ack), .rd_data(rd_data)
    );
    wire sel_pm  = (ha[15:12] == 4'h0);      // 0x0000-0x0FFF program bytes
    wire sel_dm  = (ha[15:11] == 5'b00010);  // 0x1000-0x17FF data RAM
    wire sel_cfg = (ha[15:6]  == 10'h080);   // 0x2000-0x203F latch configuration
    wire sel_ctl = (ha[15:4]  == 12'h240);   // 0x2400-0x240F control and status

    // ---------------------------------------------------------------- configuration latches
    wire [8*CFG_BYTES-1:0] cfg;
    cfg_latch_bank #(.BYTES(CFG_BYTES)) u_cfg (
        .clk(clk), .rst_n(rst_n), .we(h_wr & sel_cfg), .waddr(ha[5:0]), .wdata(hwd), .q(cfg)
    );

    // ---------------------------------------------------------------- control registers
    reg        run, run_d;
    reg  [5:0] db;                           // doorbell pulse per thread
    wire       w_ctl = h_wr & sel_ctl;
    wire       clr_starved = w_ctl & (ha[3:0] == 4'h3);
    wire       h_in_we     = w_ctl & (ha[3:0] == 4'h4);
    wire       h_out_rd    = h_rd & sel_ctl & (ha[3:0] == 4'h4);
    always @(posedge clk) begin
        if (!rst_q) begin
            run <= 1'b0; run_d <= 1'b0; db <= 6'd0;
        end else begin
            run_d <= run;
            db    <= (w_ctl & (ha[3:0] == 4'h1)) ? hwd[5:0] : 6'd0;
            if (w_ctl & (ha[3:0] == 4'h0)) run <= hwd[0];
        end
    end
    wire run_rise = run & ~run_d;            // threads load EN and the start PC from configuration

    // ---------------------------------------------------------------- thread configuration (latches)
    wire [5:0]  t_core, t_cfg_en;
    wire [11:0] t_line;
    wire [29:0] t_trig;
    wire [35:0] t_w0c, t_w1c;
    wire [47:0] t_w0h, t_w1h, t_start;
    genvar k;
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_tcfg
            wire [63:0] b = cfg[64*k +: 64];
            assign t_core[k]          = b[0];
            assign t_line[2*k +: 2]   = b[2:1];
            assign t_cfg_en[k]        = b[3];
            assign t_trig[5*k +: 5]   = b[12:8];
            assign t_w0c[6*k +: 6]    = b[21:16];
            assign t_w1c[6*k +: 6]    = b[29:24];
            assign t_w0h[8*k +: 8]    = b[39:32];
            assign t_w1h[8*k +: 8]    = b[47:40];
            assign t_start[8*k +: 8]  = b[55:48];
            wire _unused_tcfg = &{1'b0, b[7:4], b[15:13], b[23:22], b[31:30], b[63:56]};
        end
    endgenerate

    // ---------------------------------------------------------------- commons stand-in
    wire [5:0]   mv_en;
    wire [35:0]  mv_dst;
    wire [47:0]  mv_data;
    wire [3:0]   x_line;
    wire [63:0]  guards;
    wire [19:0]  g_line, l_cap;
    wire [511:0] srcs;
    wire [7:0]   l_in, flags_lo, host_out, r0, r1;
    wire [15:0]  sym;
    wire         outv, inv;
    wire         s0_adv, s0_rx_we, s0_rx_bit, s0_ctl_we;
    wire [1:0]   s0_ctl;
    wire         s0_bit, s0_end, s0_mark, s0_bb, s0_starved;
    wire [7:0]   s0_byte;
    md2_commons_stub u_com (
        .clk(clk), .rst_n(rst_q), .mv_en(mv_en), .mv_dst(mv_dst), .mv_data(mv_data), .x_line(x_line),
        .pins(pin_s),
        .s0_adv(s0_adv), .s0_rx_we(s0_rx_we), .s0_rx_bit(s0_rx_bit), .s0_ctl_we(s0_ctl_we), .s0_ctl(s0_ctl),
        .s0_bit(s0_bit), .s0_byte(s0_byte), .s0_end(s0_end), .s0_mark(s0_mark), .s0_bbound(s0_bb),
        .h_in_we(h_in_we), .h_in_d(hwd), .h_out_rd(h_out_rd), .host_out(host_out), .outv(outv), .inv(inv),
        .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap), .flags_lo(flags_lo),
        .r0(r0), .r1(r1), .sym(sym)
    );

    // ---------------------------------------------------------------- triggers
    reg [7:0] flags_d;
    reg [3:0] pina_d;
    reg       inv_d;
    always @(posedge clk) begin
        if (!rst_q) begin
            flags_d <= 8'd0; pina_d <= 4'd0; inv_d <= 1'b0;
        end else begin
            flags_d <= flags_lo;
            pina_d  <= {pin_s[6], pin_s[4], pin_s[2], pin_s[0]};
            inv_d   <= inv;
        end
    end
    wire [7:0] flag_rise = flags_lo & ~flags_d;
    wire [5:0] trig;
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_trig
            wire [4:0] ts  = t_trig[5*k +: 5];
            wire [1:0] ln  = t_line[2*k +: 2];
            wire       pa  = pin_s[2*ln];
            wire       pad = pina_d[ln];
            wire [2:0] fi  = ts[2:0] - T_FLAG0_RISE[2:0];
            assign trig[k] = db[k] | (ts == T_ALWAYS) |
                             ((ts >= T_FLAG0_RISE) & (ts <= T_FLAG7_RISE) & flag_rise[fi]) |
                             ((ts == T_PINA_RISE) & pa & ~pad) | ((ts == T_PINA_FALL) & ~pa & pad) |
                             ((ts == T_PINA_EDGE) & (pa ^ pad)) | ((ts == T_HOST_INV) & inv & ~inv_d);
        end
    endgenerate

    // ---------------------------------------------------------------- cores and program memories
    wire [5:0]  t_ready, t_running, t_en, t_ovr;
    wire [47:0] t_pc;
    wire [1:0]  pause, disp, stop;
    wire [15:0] npc;
    wire [5:0]  disp_e, xe;
    wire [1:0]  fen;
    wire [15:0] fadr;
    wire [63:0] rd0, rd1;
    wire        pm_we0 = h_wr & sel_pm & ~ha[11];
    wire        pm_we1 = h_wr & sel_pm &  ha[11];
    wire [7:0]  pm_be  = 8'd1 << ha[2:0];

    md2_pmem u_pmem0 (
        .clk(clk), .ren(fen[0]), .we(pm_we0), .addr(pm_we0 ? ha[10:3] : fadr[7:0]), .be(pm_be), .wd(hwd), .rd(rd0)
    );
    md2_pmem u_pmem1 (
        .clk(clk), .ren(fen[1]), .we(pm_we1), .addr(pm_we1 ? ha[10:3] : fadr[15:8]), .be(pm_be), .wd(hwd), .rd(rd1)
    );
    wire [1:0] x_valid_unused;
    md2_core #(.C(0)) u_core0 (
        .clk(clk), .rst_n(rst_q), .run_g(run), .rdata(rd0), .fetch_en(fen[0]), .fetch_addr(fadr[7:0]),
        .t_ready(t_ready), .t_core(t_core), .t_line(t_line), .t_pc(t_pc),
        .t_w0c(t_w0c), .t_w1c(t_w1c), .t_w0h(t_w0h), .t_w1h(t_w1h),
        .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap),
        .pause_o(pause[0]), .npc_o(npc[7:0]), .disp_o(disp[0]), .disp_e(disp_e[2:0]),
        .stop_o(stop[0]), .xv_o(x_valid_unused[0]), .xe_o(xe[2:0]), .xl_o(x_line[1:0]),
        .mv_en(mv_en[2:0]), .mv_dst(mv_dst[17:0]), .mv_data(mv_data[23:0])
    );
    md2_core #(.C(1)) u_core1 (
        .clk(clk), .rst_n(rst_q), .run_g(run), .rdata(rd1), .fetch_en(fen[1]), .fetch_addr(fadr[15:8]),
        .t_ready(t_ready), .t_core(t_core), .t_line(t_line), .t_pc(t_pc),
        .t_w0c(t_w0c), .t_w1c(t_w1c), .t_w0h(t_w0h), .t_w1h(t_w1h),
        .guards(guards), .g_line(g_line), .srcs(srcs), .l_in(l_in), .l_cap(l_cap),
        .pause_o(pause[1]), .npc_o(npc[15:8]), .disp_o(disp[1]), .disp_e(disp_e[5:3]),
        .stop_o(stop[1]), .xv_o(x_valid_unused[1]), .xe_o(xe[5:3]), .xl_o(x_line[3:2]),
        .mv_en(mv_en[5:3]), .mv_dst(mv_dst[35:18]), .mv_data(mv_data[47:24])
    );

    // ---------------------------------------------------------------- thread state slices (as md2_core_top)
    generate
        for (k = 0; k < 6; k = k + 1) begin : g_thr
            wire h0 = (xe[2:0] == k[2:0]);
            wire h1 = (xe[5:3] == k[2:0]);
            wire p0 = pause[0] & h0;
            wire p1 = pause[1] & h1;
            md2_core_thread u_thr (
                .clk(clk), .rst_n(rst_q), .trig(trig[k]),
                .h_pc_we(run_rise), .h_pc_d(t_start[8*k +: 8]), .h_en_we(run_rise), .h_en_d(t_cfg_en[k]),
                .disp((disp[0] & (disp_e[2:0] == k[2:0])) | (disp[1] & (disp_e[5:3] == k[2:0]))),
                .pause(p0 | p1), .npc(p1 ? npc[15:8] : npc[7:0]),
                .stop((stop[0] & h0) | (stop[1] & h1)),
                .ready(t_ready[k]), .running(t_running[k]), .en(t_en[k]), .pc(t_pc[8*k +: 8]), .ovr(t_ovr[k])
            );
        end
    endgenerate

    // ---------------------------------------------------------------- stream S0 and the data RAM
    wire [63:0] scfg = cfg[8*CFG_S0 +: 64];
    wire        s_req, s_we;
    wire [8:0]  s_addr;
    wire [31:0] s_wdata, dm_rd;
    wire [3:0]  s_wmask;
    wire [11:0] s_pos;
    wire [2:0]  s_bitidx;
    md2_stream u_s0 (
        .clk(clk), .rst_n(rst_q),
        .cfg_mode(scfg[0]), .cfg_msb(scfg[1]), .cfg_start({scfg[18:16], scfg[15:8]}),
        .cfg_len({scfg[35:32], scfg[31:24]}), .cfg_mark({scfg[51:48], scfg[47:40]}),
        .adv(s0_adv), .rx_bit_we(s0_rx_we), .rx_bit(s0_rx_bit), .ctl_we(s0_ctl_we), .ctl(s0_ctl),
        .clr_starved(clr_starved),
        .bit_out(s0_bit), .byte_out(s0_byte), .g_end(s0_end), .g_mark(s0_mark), .g_byte(s0_bb),
        .starved(s0_starved), .pos(s_pos), .bitidx(s_bitidx),
        .req(s_req), .req_we(s_we), .req_addr(s_addr), .req_wdata(s_wdata), .req_wmask(s_wmask),
        .gnt(s_req), .rdata(dm_rd)
    );
    wire _unused_scfg = &{1'b0, scfg[7:2], scfg[23:19], scfg[39:36], scfg[63:52]};

    // arbiter: the stream first (granted whenever it asks), then the host
    reg        hd_pend, hd_we, hd_rdw;
    reg [10:0] hd_off;
    reg [7:0]  hd_wd;
    wire       hd_gnt = hd_pend & ~s_req;
    always @(posedge clk) begin
        if (!rst_q) begin
            hd_pend <= 1'b0; hd_we <= 1'b0; hd_rdw <= 1'b0; hd_off <= 11'd0; hd_wd <= 8'd0;
        end else begin
            hd_rdw <= hd_gnt & ~hd_we;
            if (hd_gnt) hd_pend <= 1'b0;
            if ((h_wr | h_rd) & sel_dm) begin
                hd_pend <= 1'b1; hd_we <= h_wr; hd_off <= ha[10:0]; hd_wd <= hwd;
            end
        end
    end
    md2_dmem u_dmem (
        .clk(clk),
        .ren(s_req ? ~s_we : (hd_gnt & ~hd_we)),
        .we(s_req ? s_we : (hd_gnt & hd_we)),
        .addr(s_req ? s_addr : hd_off[10:2]),
        .be(s_req ? s_wmask : (4'd1 << hd_off[1:0])),
        .wd(s_req ? s_wdata : {4{hd_wd}}),
        .rd(dm_rd)
    );

    // ---------------------------------------------------------------- host reads
    reg       ack_ctl;
    reg [7:0] ctl_q;
    always @(posedge clk) begin
        if (!rst_q) begin
            ack_ctl <= 1'b0; ctl_q <= 8'd0;
        end else begin
            ack_ctl <= h_rd & ~sel_dm;
            ctl_q   <= 8'd0;
            if (sel_ctl) begin
                case (ha[3:0])
                    4'h0: ctl_q <= {7'd0, run};
                    4'h2: ctl_q <= 8'hA2;
                    4'h3: ctl_q <= {s0_starved, s0_end, t_running};
                    4'h4: ctl_q <= host_out;
                    4'h5: ctl_q <= {outv, inv, t_en};
                    4'h6: ctl_q <= s_pos[7:0];
                    4'h7: ctl_q <= {1'b0, s_bitidx, s_pos[11:8]};
                    4'h8: ctl_q <= {2'd0, t_ovr};
                    4'h9: ctl_q <= {2'd0, t_ready};
                    default: ctl_q <= 8'd0;
                endcase
            end
        end
    end
    reg [7:0] dm_byte;
    always @* begin
        case (hd_off[1:0])
            2'd0:    dm_byte = dm_rd[7:0];
            2'd1:    dm_byte = dm_rd[15:8];
            2'd2:    dm_byte = dm_rd[23:16];
            default: dm_byte = dm_rd[31:24];
        endcase
    end
    always @* begin
        rd_ack  = ack_ctl | hd_rdw;
        rd_data = hd_rdw ? dm_byte : ctl_q;
    end

    // ---------------------------------------------------------------- pins
    assign uo_out  = {^sym[15:8], ^sym[7:4], sym[3:0], outv, miso};
    assign uio_out = r0;
    assign uio_oe  = r1;

    wire _unused = &{1'b0, ena, x_valid_unused};
endmodule
`default_nettype wire
