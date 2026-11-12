// Metronome v2 line l (wiki/SPEC_V2.md section 3): beat generator with hold (3.2, 3.2a), follower mode and the
// edge-sourced tap 0 (3.3), taps with fired bits and TAPMISS (3.4), capture, snapshot and input symbol (3.5), and
// the output symbol with its commit (3.6), including FIRST and the start commit (D28). Configuration arrives as the line's host-map window `cfg` (byte o of the
// window is host offset o, layout machine.LINE_REGS via md2_map.vh); runtime state is in flops here.
// Precedence at the end of a cycle: generator, then a move to Lk.CTL, then a host write of PHASE/CTL/STAT.
`timescale 1ns/1ps
`default_nettype none
module md2_line #(
    parameter integer CFGW = 256                 // 8 * HS_LINE
) (
    input  wire            clk,
    input  wire            rst_n,                // synchronous (rst_q)
    input  wire [CFGW-1:0] cfg,
    input  wire [15:0]     lvl,                  // synchronised pin levels P0..P12 (bits 13..15 are 0)
    input  wire [15:0]     rise,
    input  wire [15:0]     fall,
    // moves (winning write of the line's groups)
    input  wire            ctl_we,               // Lk.CTL
    input  wire [2:0]      ctl_d,
    input  wire            sym_we,               // L.SYM / L.DBIT / L.XOR of this line
    input  wire [1:0]      sym_op,               // 0 SYM, 1 DBIT, 2 XOR
    input  wire [3:0]      sym_d,
    // host writes of the line runtime registers
    input  wire [1:0]      h_ph_we,              // PHASE byte 0 / 1
    input  wire            h_ctl_we,
    input  wire            h_stat_we,
    input  wire [7:0]      h_d,
    // events and state
    output wire            beat,
    output wire [2:0]      tap,
    output wire [1:0]      in_sym,
    output wire [4:0]      cap,                  // {REM, SN}
    output reg             sp,                   // SYNC
    output reg  [15:0]     ph,
    output reg             run,
    output reg             arm,
    output reg             ren,
    output reg  [2:0]      fired,
    output reg             held,
    output reg  [3:0]      staged,
    output reg  [3:0]      committed,
    output reg             tapmiss,
    output wire [1:0]      seg,
    output wire            pina,                 // PIN[PINA], PIN[PINB]
    output wire            pinb,
    output wire            pina_rise,
    output wire            pina_fall
);
/* verilator lint_off UNUSEDPARAM */
`undef MD2_MAP_VH
`include "md2_map.vh"
/* verilator lint_on UNUSEDPARAM */

    // ---------------------------------------------------------------- configuration fields
    wire [15:0] c_inc = cfg[8*HO_LINE_INC +: 16];
    wire [15:0] c_mod = cfg[8*HO_LINE_MOD +: 16];
    wire [15:0] c_t0  = cfg[8*HO_LINE_T0  +: 16];
    wire [15:0] c_t1  = cfg[8*HO_LINE_T1  +: 16];
    wire [15:0] c_t2  = cfg[8*HO_LINE_T2  +: 16];
    wire [15:0] c_pre = cfg[8*HO_LINE_PRE +: 16];
    wire [15:0] c_wlo = cfg[8*HO_LINE_WLO +: 16];
    wire [15:0] c_whi = cfg[8*HO_LINE_WHI +: 16];
    wire [7:0]  c_edge = cfg[8*HO_LINE_EDGE +: 8];
    wire [7:0]  c_t0e  = cfg[8*HO_LINE_T0EDGE +: 8];
    wire [7:0]  c_pins = cfg[8*HO_LINE_PINS +: 8];
    wire [1:0]  c_snap = cfg[8*HO_LINE_SNAP +: 2];
    wire [31:0] c_lut0 = cfg[8*HO_LINE_LUT0 +: 32];
    wire [31:0] c_lut1 = cfg[8*HO_LINE_LUT1 +: 32];
    wire [7:0]  c_hold = cfg[8*HO_LINE_HOLD +: 8];
    wire        c_wen    = c_edge[6];
    wire        c_follow = c_edge[7];
    wire        c_t0src  = c_t0e[6];
    // bits of the window that are not this line's configuration, and T0EDGE bit 7, are unused
    wire        _unused_cfg = &{1'b0, cfg, c_t0e[7]};
    wire [3:0]  c_hpin   = c_hold[3:0];
    wire        c_hlvl   = c_hold[4];
    wire [1:0]  c_htap   = c_hold[6:5];
    wire        c_hen    = c_hold[7];

    // polarity-selected edge of a pin (selects 13..15 have no edges: those bits of rise/fall are 0)
    function esel;
        input [3:0]  pin;
        input [1:0]  pol;
        input [15:0] r;
        input [15:0] f;
        begin
            case (pol)
                2'd1:    esel = r[pin];
                2'd2:    esel = f[pin];
                2'd3:    esel = r[pin] | f[pin];
                default: esel = 1'b0;
            endcase
        end
    endfunction

    // ---------------------------------------------------------------- beat generator (3.2)
    wire        edg   = esel(c_edge[3:0], c_edge[5:4], rise, fall);
    wire        e0    = esel(c_t0e[3:0], c_t0e[5:4], rise, fall);
    wire        inwin = (c_wlo <= c_whi) ? ((c_wlo <= ph) && (ph <= c_whi)) : ((ph >= c_wlo) || (ph <= c_whi));
    wire        start  = edg & arm & ~run;
    wire        accept = edg & run & ren & (~c_wen | inwin);
    wire [16:0] n      = {1'b0, ph} + {1'b0, c_inc};
    wire        over   = (n >= {1'b0, c_mod});
    wire [16:0] nxw    = n - {1'b0, c_mod};
    wire [15:0] nx     = over ? nxw[15:0] : n[15:0];
    wire        _unused_nx = nxw[16];

    // crossing test of a phase tap at T in this cycle's advance (3.4, without the adv term)
    function crossing;
        input [15:0] t;
        input [15:0] p;
        input [15:0] x;
        input        o;
        begin
            crossing = o ? ((t > p) || (t <= x)) : ((p < t) && (t <= x));
        end
    endfunction

    wire [15:0] tk [0:2];
    assign tk[0] = c_t0;
    assign tk[1] = c_t1;
    assign tk[2] = c_t2;
    wire [2:0] tlt;                                   // Tk < MOD
    assign tlt[0] = (c_t0 < c_mod);
    assign tlt[1] = (c_t1 < c_mod);
    assign tlt[2] = (c_t2 < c_mod);

    // hold (3.2a): stall while tap HTAP would be crossed and the pin does not read HLVL
    wire [15:0] th     = (c_htap == 2'd0) ? c_t0 : ((c_htap == 2'd1) ? c_t1 : c_t2);
    wire        h_tok  = (c_htap != 2'd3) & ~((c_htap == 2'd0) & c_t0src) &
                         ((c_htap == 2'd0) ? tlt[0] : ((c_htap == 2'd1) ? tlt[1] : tlt[2]));
    wire        hold   = c_hen & run & ~accept & h_tok & crossing(th, ph, nx, over) & (lvl[c_hpin] != c_hlvl);
    wire        adv    = run & ~accept & ~hold;
    wire        wrap   = adv & over;
    assign beat = c_follow ? accept : wrap;

    // ---------------------------------------------------------------- taps (3.4)
    wire [2:0] en_k, cross_k, next_k, cur_k;
    genvar k;
    generate
        for (k = 0; k < 3; k = k + 1) begin : g_tap
            if (k == 0) begin : g_t0
                wire ph_cross = adv & tlt[0] & crossing(c_t0, ph, nx, over);
                wire ph_next  = ph_cross & beat & over & (c_t0 <= nx);
                assign en_k[0]    = c_t0src ? (c_t0e[5:4] != 2'd0) : tlt[0];
                assign cross_k[0] = c_t0src ? (run & e0) : ph_cross;
                assign next_k[0]  = c_t0src ? (run & e0 & beat) : ph_next;
            end else begin : g_tk
                assign en_k[k]    = tlt[k];
                assign cross_k[k] = adv & tlt[k] & crossing(tk[k], ph, nx, over);
                assign next_k[k]  = cross_k[k] & beat & over & (tk[k] <= nx);
            end
            assign cur_k[k] = cross_k[k] & ~next_k[k];
            assign tap[k]   = (cur_k[k] & ~fired[k]) | next_k[k];
        end
    endgenerate
    reg        first;                             // no boundary yet since the line started (D28)
    // an edge-sourced tap 0 does not count as missed in the starting beat (FIRST, D28)
    wire [2:0] miss_ok    = {2'b11, ~(c_t0src & first)};
    wire       miss_ev    = beat & |(en_k & ~fired & ~cur_k & miss_ok);
    wire [2:0] fired_next = beat ? next_k : (fired | cur_k);
    assign seg = {1'b0, fired[0]} + {1'b0, fired[1]} + {1'b0, fired[2]};

    // taps counted as fired when RUN rises (enabled phase taps at or behind the starting phase)
    function [2:0] start_bits;
        input [15:0] p;
        input [47:0] t;
        input [2:0]  lt;
        input        t0src;
        begin
            start_bits[0] = ~t0src & lt[0] & (t[15:0]  <= p);
            start_bits[1] = lt[1] & (t[31:16] <= p);
            start_bits[2] = lt[2] & (t[47:32] <= p);
        end
    endfunction

    // ---------------------------------------------------------------- capture, snapshot, input symbol (3.5)
    reg  [3:0] w;          // {B1, A2, A1, A0}
    reg  [3:0] sn;
    reg        rem;
    assign pina = lvl[c_pins[3:0]];
    assign pinb = lvl[c_pins[7:4]];
    assign pina_rise = rise[c_pins[3:0]];
    assign pina_fall = fall[c_pins[3:0]];
    wire [3:0] w_next = {tap[1] ? pinb : w[3], tap[2] ? pina : w[2], tap[1] ? pina : w[1], tap[0] ? pina : w[0]};
    wire       snap   = (c_snap == 2'd3) ? beat : tap[c_snap];
    assign cap    = {rem, sn};
    assign in_sym = {c_lut1[cap], c_lut0[cap]};

    // ---------------------------------------------------------------- next state
    reg sc;
    wire       starting;
    wire [15:0] ph_c  = (start | accept) ? c_pre : (adv ? nx : ph);
    wire        run_c = ctl_we ? ctl_d[0] : (run | start);
    wire        arm_c = ctl_we ? ctl_d[1] : (arm & ~start);
    wire        ren_c = ctl_we ? ctl_d[2] : ren;
    wire        run_f = h_ctl_we ? h_d[0] : run_c;
    wire [15:0] ph_f  = h_ph_we[0] ? {ph_c[15:8], h_d} : (h_ph_we[1] ? {h_d, ph_c[7:0]} : ph_c);
    assign starting = run_f & ~run;             // final RUN rises after host/move priority (3.2, 3.4)
    reg  [3:0]  staged_n;
    always @* begin
        staged_n = staged;
        if (sym_we) begin
            case (sym_op)
                2'd0:    staged_n = sym_d;
                2'd1:    staged_n = {staged[3:1], sym_d[0]};
                default: staged_n = staged ^ sym_d;
            endcase
        end
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            ph <= 16'd0; run <= 1'b0; arm <= 1'b0; ren <= 1'b0; sc <= 1'b0; sp <= 1'b0; fired <= 3'd0;
            held <= 1'b0; first <= 1'b0; w <= 4'd0; sn <= 4'd0; rem <= 1'b0; staged <= 4'd0; committed <= 4'd0; tapmiss <= 1'b0;
        end else begin
            held <= hold;
            ph   <= ph_f;
            run  <= run_f;
            arm  <= h_ctl_we ? h_d[1] : arm_c;
            ren  <= h_ctl_we ? h_d[2] : ren_c;
            if (c_follow) begin
                sc <= 1'b0;
                sp <= beat ? 1'b1 : (wrap ? 1'b0 : sp);
            end else begin
                sp <= beat ? sc : sp;
                sc <= accept ? 1'b1 : (beat ? 1'b0 : sc);
            end
            fired <= starting ? start_bits(ph_f, {c_t2, c_t1, c_t0}, tlt, c_t0src) : fired_next;
            first <= starting | (first & ~beat);
            staged <= staged_n;
            if (beat | starting) committed <= staged_n;     // a boundary or a line start commits (3.6)
            tapmiss <= miss_ev | (tapmiss & ~(h_stat_we & h_d[0]));
            w <= w_next;
            if (snap) begin
                sn  <= w_next;
                rem <= in_sym[1];
            end
        end
    end
endmodule
`default_nettype wire
