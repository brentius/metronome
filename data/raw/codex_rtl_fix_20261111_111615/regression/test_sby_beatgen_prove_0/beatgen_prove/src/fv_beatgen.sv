// Formal properties for md_beatgen (SPEC 3, 9a.6, 9a.10). Bound into the DUT scope (sees internal names).
// Proof model: free inputs, free initial state. Properties on combinational outputs carry the program
// obligation (INC < MOD, PH < MOD) as an antecedent, never as an assumption, so nothing is vacuous.
module fv_beatgen_props (
    input wire clk, input wire rst_n, input wire h_we, input wire [7:0] h_wd, input wire mv_we,
    input wire [2:0] mv_d, input wire [15:0] ph, input wire [15:0] inc, input wire [15:0] mod,
    input wire [15:0] pre, input wire [15:0] t0, input wire [15:0] t1, input wire [15:0] t2,
    input wire [15:0] wlo, input wire [15:0] whi, input wire run, input wire arm, input wire ren,
    input wire wen, input wire sc, input wire sp, input wire start, input wire accept, input wire adv,
    input wire edge_ev, input wire inwin, input wire wrap, input wire [15:0] nx,
    input wire beat, input wire [2:0] tap, input wire [1:0] seg,
    input wire hw_phl, input wire hw_phh, input wire hw_ctl
);
    // ---- previous-cycle shadow of inputs and combinational values
    reg pv = 1'b0;
    reg p_rstn, p_hwctl, p_phl, p_phh, p_mv, p_start, p_accept, p_beat, p_run, p_arm, p_ren, p_wen, p_sc, p_sp;
    reg [7:0] p_hwd; reg [2:0] p_mvd;
    reg [15:0] p_ph, p_pre, p_nx, p_mod;
    reg p_okph;
    always @(posedge clk) begin
        pv <= 1'b1;
        p_rstn <= rst_n; p_hwctl <= hw_ctl; p_phl <= hw_phl; p_phh <= hw_phh; p_mv <= mv_we;
        p_start <= start; p_accept <= accept; p_beat <= beat; p_run <= run; p_arm <= arm; p_ren <= ren;
        p_wen <= wen; p_sc <= sc; p_sp <= sp; p_hwd <= h_wd; p_mvd <= mv_d;
        p_ph <= ph; p_pre <= pre; p_nx <= nx; p_mod <= mod;
        p_okph <= (ph < mod) && (inc < mod) && (pre < mod);
    end
    // the first cycle is a reset cycle, so "after reset" properties are not vacuous at depth 0
    always @(posedge clk) if (!pv) assume(!rst_n);

    wire ok = (ph < mod) && (inc < mod);           // SPEC 9a.6 program obligation + PH range
    wire [31:0] n32 = {16'd0, ph} + {16'd0, inc};
    wire [31:0] m32 = {16'd0, mod};

    // ---------- combinational (every cycle) ----------
    // SPEC 3: start and accept are exclusive (start needs !RUN, accept needs RUN).
    always @(*) assert (!(start && accept));
    // SPEC 3: when not running, or when an edge is accepted, BEAT and all TAPs are 0.
    always @(*) assert (adv == (run && !accept));
    always @(*) if (!adv) assert (!beat && tap == 3'b000);
    // SPEC 3: accept requires RUN, REN and (WEN -> inwin); start requires ARM and !RUN.
    always @(*) if (accept) assert (run && ren && (!wen || inwin) && edge_ev);
    always @(*) if (start)  assert (!run && arm && edge_ev);
    // SPEC 3: BEAT holds exactly when PH+INC wraps (n >= MOD), while advancing.
    always @(*) if (ok) assert (beat == (adv && (n32 >= m32)));
    // SPEC 3 / 9a.6: with INC<MOD and PH<MOD, nx = (PH+INC) mod MOD and nx < MOD (PH stays < MOD).
    always @(*) if (ok) assert (nx < mod);
    always @(*) if (ok) assert ({16'd0, nx} == ((n32 >= m32) ? n32 - m32 : n32));
    // SPEC 3: TAPk fires iff Tk<MOD and Tk (or Tk+MOD) lies in (PH, PH+INC] (independent formulation).
    // SPEC 9a.10: Tk >= MOD never fires.
    wire [31:0] a0 = {16'd0, t0}, a1 = {16'd0, t1}, a2 = {16'd0, t2};
    wire x0 = (t0 < mod) && ((a0 > {16'd0,ph} && a0 <= n32) || (a0 + m32 > {16'd0,ph} && a0 + m32 <= n32));
    wire x1 = (t1 < mod) && ((a1 > {16'd0,ph} && a1 <= n32) || (a1 + m32 > {16'd0,ph} && a1 + m32 <= n32));
    wire x2 = (t2 < mod) && ((a2 > {16'd0,ph} && a2 <= n32) || (a2 + m32 > {16'd0,ph} && a2 + m32 <= n32));
    always @(*) if (ok) assert (tap == {adv && x2, adv && x1, adv && x0});
    always @(*) if (t0 >= mod) assert (!tap[0]);
    always @(*) if (t1 >= mod) assert (!tap[1]);
    always @(*) if (t2 >= mod) assert (!tap[2]);
    // SPEC 3 / 9a.10: SEG = number of taps passed (PH >= Tk) among those below MOD; no tap below MOD -> 0.
    wire [1:0] segx = ((t0 < mod && ph >= t0) ? 2'd1 : 2'd0) + ((t1 < mod && ph >= t1) ? 2'd1 : 2'd0)
                    + ((t2 < mod && ph >= t2) ? 2'd1 : 2'd0);
    always @(*) assert (seg == segx);
    always @(*) if (mod == 16'd0) assert (seg == 2'd0);
    // SPEC 9a.10: T0=T1=T2=0 with MOD>0: SEG = 3.
    always @(*) if (t0 == 0 && t1 == 0 && t2 == 0 && mod != 0) assert (seg == 2'd3);
    // SPEC 3 (window): independent encoding of inwin.
    wire inw_x = (wlo <= whi) ? (ph >= wlo && ph <= whi) : !(ph < wlo && ph > whi);
    always @(*) assert (inwin == inw_x);

    // ---------- sequential (one-step transition relation, after a non-reset cycle) ----------
    wire past_ok = pv && p_rstn;
    // reset (SPEC 3 initial state): all state cleared
    always @(posedge clk) if (pv && !p_rstn)
        assert (run == 0 && arm == 0 && ren == 0 && wen == 0 && sc == 0 && sp == 0 && ph == 0 && inc == 0 && mod == 0);
    // SPEC 3: RUN/ARM/REN/WEN update. Host CTL write > move to CTL > natural (RUN'=RUN||start, ARM'=ARM&&!start).
    always @(posedge clk) if (past_ok && p_hwctl)
        assert ({wen, ren, arm, run} == p_hwd[3:0]);
    always @(posedge clk) if (past_ok && !p_hwctl && p_mv)
        assert (run == p_mvd[0] && arm == p_mvd[1] && ren == p_mvd[2] && wen == p_wen);
    always @(posedge clk) if (past_ok && !p_hwctl && !p_mv)
        assert (run == (p_run || p_start) && arm == (p_arm && !p_start) && ren == p_ren && wen == p_wen);
    // SPEC 3: PH' = (start||accept) ? PRE : (RUN ? nx : PH); a move to CTL leaves PH unaffected;
    // a host PHASE byte write overrides that byte only (SPEC-AMBIGUITY marker in RTL).
    wire [15:0] ph_exp = (p_start || p_accept) ? p_pre : (p_run ? p_nx : p_ph);
    always @(posedge clk) if (past_ok) begin
        assert (ph[7:0]  == (p_phl ? p_hwd : ph_exp[7:0]));
        assert (ph[15:8] == (p_phh ? p_hwd : ph_exp[15:8]));
    end
    // SPEC 3: SC' = accept ? 1 : (BEAT ? 0 : SC); SP' = BEAT ? SC : SP.
    always @(posedge clk) if (past_ok) begin
        assert (sc == (p_accept ? 1'b1 : (p_beat ? 1'b0 : p_sc)));
        assert (sp == (p_beat ? p_sc : p_sp));
    end
    // PH < MOD invariant (SPEC 9a.6): if last cycle PH, INC, PRE < MOD and MOD is unchanged and no host
    // PHASE write, PH stays < MOD (one-step implication, hence inductive).
    always @(posedge clk) if (past_ok && p_okph && mod == p_mod && !p_phl && !p_phh)
        assert (ph < mod);
    // non-vacuity covers
    always @(posedge clk) begin
        cover (past_ok && p_beat);
        cover (past_ok && p_start);
        cover (past_ok && p_accept);
        cover (ok && tap[0] && beat);
        cover (ok && tap[1] && !beat);
        cover (ok && tap == 3'b111);
    end
endmodule

bind md_beatgen fv_beatgen_props fv_props (.*);
