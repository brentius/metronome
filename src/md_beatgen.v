// Beat generator (SPEC 3). Configuration INC, MOD, T0..T2, PRE, WLO, WHI, WEN, EDGE; state PH, RUN, ARM, REN,
// SC, SP. Produces BEAT, TAP0..2 (combinational, cycle t), SEG (from the PH register) and SP (for E.SYNC).
`timescale 1ns/1ps
`default_nettype none
module md_beatgen (
    input  wire        clk,
    input  wire        rst_n,
    // host register write/read (offsets from BG_REGS)
    input  wire        h_we,
    input  wire [4:0]  h_off,
    input  wire [7:0]  h_wd,
    input  wire [4:0]  h_roff,
    output reg  [7:0]  h_rd,
    // move to BGk.CTL
    input  wire        mv_we,
    input  wire [2:0]  mv_d,
    // synchronised pin edges, P0..P15 (P13..P15 tied 0)
    input  wire [15:0] pin_rise,
    input  wire [15:0] pin_fall,
    output wire        beat,
    output wire [2:0]  tap,
    output wire [1:0]  seg,
    output wire        sp_o,
    output wire        run_o
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    reg [15:0] inc, mod, t0, t1, t2, pre, wlo, whi, ph;
    reg        wen, run, arm, ren, sc, sp;
    reg [5:0]  edg;

    wire [3:0] esel = edg[3:0];
    wire       edge_ev = (edg[4] & pin_rise[esel]) | (edg[5] & pin_fall[esel]);
    // one comparator per distinct relation (shared between window, taps and SEG)
    wire       lo_le_hi = (wlo <= whi);
    wire       lo_le_ph = (wlo <= ph);
    wire       ph_le_hi = (ph <= whi);
    wire       inwin = lo_le_hi ? (lo_le_ph & ph_le_hi) : (lo_le_ph | ph_le_hi);
    wire       start  = edge_ev & arm & ~run;
    wire       accept = edge_ev & run & ren & (~wen | inwin);
    wire [16:0] n    = {1'b0, ph} + {1'b0, inc};
    wire [17:0] dif  = {1'b0, n} - {2'b0, mod};      // wrap = no borrow (n >= MOD), shares the subtractor
    wire        wrap = ~dif[17];
    // SPEC 9a.6: the 17-bit sum is reduced once and stored in 16 bits (INC < MOD is a program obligation).
    wire [16:0] nxf  = wrap ? dif[16:0] : n;
    wire [15:0] nx   = nxf[15:0];
    wire        adv  = run & ~accept;

    // per tap: Tk < MOD, Tk > PH (its complement is PH >= Tk for SEG), Tk <= nx
    wire [2:0] t_lt_mod = {t2 < mod, t1 < mod, t0 < mod};
    wire [2:0] t_gt_ph  = {t2 > ph,  t1 > ph,  t0 > ph};
    wire [2:0] t_le_nx  = {t2 <= nx, t1 <= nx, t0 <= nx};
    wire [2:0] hit_t    = wrap ? (t_gt_ph | t_le_nx) : (t_gt_ph & t_le_nx);
    wire [2:0] seg_t    = t_lt_mod & ~t_gt_ph;

    assign beat  = adv & wrap;
    assign tap   = {3{adv}} & t_lt_mod & hit_t;
    assign seg   = {1'b0, seg_t[0]} + {1'b0, seg_t[1]} + {1'b0, seg_t[2]};
    assign sp_o  = sp;
    assign run_o = run;

    // host write decode
    wire hw_phl = h_we && (h_off == HBG_PHASE[4:0]);
    wire hw_phh = h_we && (h_off == HBG_PHASE[4:0] + 5'd1);
    wire hw_ctl = h_we && (h_off == HBG_CTL[4:0]);

    reg [15:0] ph_n;
    always @* begin
        ph_n = (start || accept) ? pre : (run ? nx : ph);
        // SPEC-AMBIGUITY: a host write to one PHASE byte overrides that byte only; the other byte takes its
        // normal next value.
        if (hw_phl) ph_n[7:0]  = h_wd;
        if (hw_phh) ph_n[15:8] = h_wd;
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            inc <= 16'd0; mod <= 16'd0; t0 <= 16'd0; t1 <= 16'd0; t2 <= 16'd0;
            pre <= 16'd0; wlo <= 16'd0; whi <= 16'd0; ph <= 16'd0;
            wen <= 1'b0; run <= 1'b0; arm <= 1'b0; ren <= 1'b0; sc <= 1'b0; sp <= 1'b0;
            edg <= 6'd0;
        end else begin
            ph <= ph_n;
            sc <= accept ? 1'b1 : (beat ? 1'b0 : sc);
            if (beat) sp <= sc;
            // RUN/ARM/REN: host CTL write > move to BGk.CTL > natural update
            if (hw_ctl) begin
                run <= h_wd[0]; arm <= h_wd[1]; ren <= h_wd[2]; wen <= h_wd[3];
            end else if (mv_we) begin
                run <= mv_d[0]; arm <= mv_d[1]; ren <= mv_d[2];
            end else begin
                run <= run | start;
                arm <= arm & ~start;
            end
            if (h_we) begin
                case (h_off)
                    HBG_INC[4:0]:        inc[7:0]  <= h_wd;
                    HBG_INC[4:0] + 5'd1: inc[15:8] <= h_wd;
                    HBG_MOD[4:0]:        mod[7:0]  <= h_wd;
                    HBG_MOD[4:0] + 5'd1: mod[15:8] <= h_wd;
                    HBG_T0[4:0]:         t0[7:0]   <= h_wd;
                    HBG_T0[4:0] + 5'd1:  t0[15:8]  <= h_wd;
                    HBG_T1[4:0]:         t1[7:0]   <= h_wd;
                    HBG_T1[4:0] + 5'd1:  t1[15:8]  <= h_wd;
                    HBG_T2[4:0]:         t2[7:0]   <= h_wd;
                    HBG_T2[4:0] + 5'd1:  t2[15:8]  <= h_wd;
                    HBG_PRE[4:0]:        pre[7:0]  <= h_wd;
                    HBG_PRE[4:0] + 5'd1: pre[15:8] <= h_wd;
                    HBG_WLO[4:0]:        wlo[7:0]  <= h_wd;
                    HBG_WLO[4:0] + 5'd1: wlo[15:8] <= h_wd;
                    HBG_WHI[4:0]:        whi[7:0]  <= h_wd;
                    HBG_WHI[4:0] + 5'd1: whi[15:8] <= h_wd;
                    HBG_EDGE[4:0]:       edg       <= h_wd[5:0];
                    default: ;
                endcase
            end
        end
    end

    // host read (D14: only PHASE and CTL are readable; configuration registers are write-only and read 0)
    always @* begin
        case (h_roff)
            HBG_PHASE[4:0]:        h_rd = ph[7:0];
            HBG_PHASE[4:0] + 5'd1: h_rd = ph[15:8];
            HBG_CTL[4:0]:          h_rd = {4'd0, wen, ren, arm, run};
            default:               h_rd = 8'd0;
        endcase
    end

    // nxf[16] is dropped (SPEC 9a.6); dif[16] only matters through wrap.
    wire unused_ok = &{1'b0, nxf[16]};
endmodule
`default_nettype wire
