// Engine (SPEC 4): trigger binding, capture, input symbol, staged/committed output symbol, burst state and sticky
// LATE/OVR. The watcher configuration is exported; the core evaluates the watchers of the engine it dispatches.
`timescale 1ns/1ps
`default_nettype none
module md_engine #(
    parameter integer NB = 4        // beat generators
) (
    input  wire          clk,
    input  wire          rst_n,
    // host register write/read (offsets from ENG_REGS)
    input  wire          h_we,
    input  wire [4:0]    h_off,
    input  wire [7:0]    h_wd,
    input  wire [4:0]    h_roff,
    output reg  [7:0]    h_rd,
    input  wire          doorbell,      // host DOORBELL write with bit ID set, this cycle
    // beat generators
    input  wire [NB-1:0]   bg_beat,
    input  wire [3*NB-1:0] bg_tap,      // {TAP2,TAP1,TAP0} per generator
    input  wire [2*NB-1:0] bg_seg,
    input  wire [NB-1:0]   bg_sp,
    // pins P0..P15 (P13..P15 tied 0), flags, host mailbox
    input  wire [15:0]   pin_lvl,
    input  wire [15:0]   pin_rise,
    input  wire [15:0]   pin_fall,
    input  wire [7:0]    flag_rise,
    input  wire          hostinv_rise,
    // move bus (after conflict resolution)
    input  wire          sym_we,
    input  wire [1:0]    sym_d,
    input  wire          stop_we,
    // cores
    input  wire          disp,          // a core dispatches this engine this cycle
    input  wire          pause,         // the core executing this engine pauses this cycle
    input  wire [7:0]    pause_pc,
    output reg           ready,
    output reg           running,
    output wire          core_sel,
    output reg  [7:0]    pc,
    output reg  [5:0]    w0c,
    output reg  [5:0]    w1c,
    output reg  [7:0]    w0h,
    output reg  [7:0]    w1h,
    output wire [1:0]    in_sym,
    output wire [3:0]    cap_o,
    output wire          sync,
    output wire          pina,
    output wire          pinb,
    output wire [1:0]    seg,           // SEG of this engine's beat generator
    output reg  [1:0]    committed,
    output wire          err            // LATE | OVR
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    // configuration
    reg        en, core;
    reg [1:0]  bg;
    reg [4:0]  trig;
    reg [3:0]  pa_sel, pb_sel;
    reg [15:0] lut0, lut1;
    // state
    reg        armed, late, ovr;
    reg [1:0]  staged;
    reg [3:0]  cap;     // {B1, A2, A1, A0}

    assign core_sel = core;
    assign pina = pin_lvl[pa_sel];
    assign pinb = pin_lvl[pb_sel];

    // selected beat generator
    wire       b_beat = bg_beat[bg];
    wire [2:0] b_tap  = bg_tap[3*bg +: 3];
    assign seg  = bg_seg[2*bg +: 2];
    assign sync = bg_sp[bg];

    assign in_sym = {lut1[cap], lut0[cap]};
    assign cap_o  = cap;

    // trigger events, indexed by the TRIG codes from the header (layout checked in md_layout_check)
    reg [31:0] ev;
    integer g, k;
    always @* begin
        ev = 32'd0;
        for (g = 0; g < NB; g = g + 1) begin
            ev[{27'd0, T_BG0_BEAT} + 4 * g] = bg_beat[g];
            ev[{27'd0, T_BG0_TAP0} + 4 * g] = bg_tap[3 * g];
            ev[{27'd0, T_BG0_TAP1} + 4 * g] = bg_tap[3 * g + 1];
            ev[{27'd0, T_BG0_TAP2} + 4 * g] = bg_tap[3 * g + 2];
        end
        for (k = 0; k < 8; k = k + 1)
            ev[{27'd0, T_FLAG0_RISE} + k] = flag_rise[k];
        ev[T_PINA_RISE] = pin_rise[pa_sel];
        ev[T_PINA_FALL] = pin_fall[pa_sel];
        ev[T_PINA_EDGE] = pin_rise[pa_sel] | pin_fall[pa_sel];
        ev[T_HOST_INV]  = hostinv_rise;
        ev[T_ALWAYS]    = ~ready & ~running;
    end
    wire trig_ev = en & (ev[trig] | doorbell);
    wire busy    = ready | running;
    wire acc_t   = trig_ev & ~busy;

    assign err = late | ovr;

    // host write decode
    wire hw_pc   = h_we && (h_off == HENG_PC[4:0]);
    wire hw_cfg  = h_we && (h_off == HENG_CFG[4:0]);
    wire hw_stat = h_we && (h_off == HENG_STAT[4:0]);

    always @(posedge clk) begin
        if (!rst_n) begin
            en <= 1'b0; core <= 1'b0; bg <= 2'd0; trig <= 5'd0; pa_sel <= 4'd0; pb_sel <= 4'd0;
            lut0 <= 16'd0; lut1 <= 16'd0; w0c <= 6'd0; w1c <= 6'd0; w0h <= 8'd0; w1h <= 8'd0;
            pc <= 8'd0; ready <= 1'b0; running <= 1'b0; armed <= 1'b0; late <= 1'b0; ovr <= 1'b0;
            staged <= 2'd0; committed <= 2'd0; cap <= 4'd0;
        end else begin
            // capture
            if (b_tap[0]) cap[0] <= pina;
            if (b_tap[1]) begin cap[1] <= pina; cap[3] <= pinb; end
            if (b_tap[2]) cap[2] <= pina;
            // burst state (disp requires READY, so it never coincides with an accepted trigger)
            if (disp)        ready <= 1'b0;
            else if (acc_t)  ready <= 1'b1;
            if (disp)        running <= 1'b1;
            else if (pause)  running <= 1'b0;
            if (acc_t)       armed <= 1'b1;
            else if (b_beat) armed <= 1'b0;
            // symbols
            if (sym_we) staged <= sym_d;
            if (b_beat) committed <= sym_we ? sym_d : staged;
            // sticky errors. SPEC-AMBIGUITY: a host STAT clear in the same cycle as a set wins (host priority).
            if (hw_stat && h_wd[5])            ovr <= 1'b0;
            else if (trig_ev && busy)          ovr <= 1'b1;
            if (hw_stat && h_wd[4])            late <= 1'b0;
            else if (sym_we && !armed)         late <= 1'b1;
            // PC: host write > pause
            if (hw_pc)       pc <= h_wd;
            else if (pause)  pc <= pause_pc;
            // EN: host CFG write > E.STOP
            if (hw_cfg) begin
                en <= h_wd[0]; core <= h_wd[1]; bg <= h_wd[3:2];
            end else if (stop_we) begin
                en <= 1'b0;
            end
            if (h_we) begin
                case (h_off)
                    HENG_TRIG[4:0]:         trig <= h_wd[4:0];
                    HENG_PINS[4:0]:         begin pa_sel <= h_wd[3:0]; pb_sel <= h_wd[7:4]; end
                    HENG_LUT0[4:0]:         lut0[7:0]  <= h_wd;
                    HENG_LUT0[4:0] + 5'd1:  lut0[15:8] <= h_wd;
                    HENG_LUT1[4:0]:         lut1[7:0]  <= h_wd;
                    HENG_LUT1[4:0] + 5'd1:  lut1[15:8] <= h_wd;
                    HENG_W0C[4:0]:          w0c <= h_wd[5:0];
                    HENG_W0H[4:0]:          w0h <= h_wd;
                    HENG_W1C[4:0]:          w1c <= h_wd[5:0];
                    HENG_W1H[4:0]:          w1h <= h_wd;
                    default: ;
                endcase
            end
        end
    end

    // host read (D14: only PC, SYM and STAT are readable; configuration registers are write-only and read 0)
    always @* begin
        case (h_roff)
            HENG_PC[4:0]:           h_rd = pc;
            HENG_SYM[4:0]:          h_rd = {4'd0, committed, staged};
            HENG_STAT[4:0]:         h_rd = {2'd0, ovr, late, 1'b0, armed, running, ready};
            default:                h_rd = 8'd0;
        endcase
    end
endmodule
`default_nettype wire
