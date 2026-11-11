// Formal properties for md_engine (SPEC 4, 9a.1), NB = 4. Bound into the DUT scope.
// Input assumptions (interface obligations of neighbouring units, each checked elsewhere or by construction):
//  A1  pin_lvl/rise/fall bits 15:13 are 0 (SPEC 4: pins >= 13 read 0; the top level ties them);
//  A2  disp implies ready (a core only dispatches a READY engine; the RTL comment relies on this);
//  A3  the first cycle is a reset cycle.
// Everything else is free: arbitrary host writes, move bus, beat generator outputs, guards.
module fv_engine_props (
    input wire clk, input wire rst_n,
    input wire h_we, input wire [4:0] h_off, input wire [7:0] h_wd, input wire doorbell,
    input wire [3:0] bg_beat, input wire [11:0] bg_tap,
    input wire [15:0] pin_lvl, input wire [15:0] pin_rise, input wire [15:0] pin_fall,
    input wire [7:0] flag_rise, input wire hostinv_rise,     input wire sym_we, input wire [1:0] sym_d, input wire stop_we,
    input wire disp, input wire pause, input wire [7:0] pause_pc,
    input wire ready, input wire running, input wire [1:0] in_sym,
    input wire [3:0] cap_o, input wire [1:0] committed, input wire err,
    input wire en, input wire [1:0] bg, input wire [4:0] trig, input wire [3:0] pa_sel,
    input wire [15:0] lut0, input wire [15:0] lut1, input wire [7:0] pc,
    input wire armed, input wire late, input wire ovr, input wire [1:0] staged, input wire [3:0] cap,
    input wire pina, input wire pinb, input wire sync
);
    `undef MD_DEFS_VH
    `include "md_defs.vh"
    reg pv = 1'b0;
    always @(posedge clk) begin pv <= 1'b1; if (!pv) assume(!rst_n); end
    always @(*) assume (pin_lvl[15:13] == 0 && pin_rise[15:13] == 0 && pin_fall[15:13] == 0);   // A1
    always @(*) if (disp) assume (ready);                                                      // A2

    // ---- independent reference for the trigger event (SPEC 4 "Trigger event"; codes from ISA_TABLES)
    wire [3:0] bgb = bg_beat;
    function evref;
        input [4:0] c;
        begin
            case (c)
                5'd1:  evref = bg_beat[0];  5'd2:  evref = bg_tap[0];  5'd3:  evref = bg_tap[1];  5'd4:  evref = bg_tap[2];
                5'd5:  evref = bg_beat[1];  5'd6:  evref = bg_tap[3];  5'd7:  evref = bg_tap[4];  5'd8:  evref = bg_tap[5];
                5'd9:  evref = bg_beat[2];  5'd10: evref = bg_tap[6];  5'd11: evref = bg_tap[7];  5'd12: evref = bg_tap[8];
                5'd13: evref = bg_beat[3];  5'd14: evref = bg_tap[9];  5'd15: evref = bg_tap[10]; 5'd16: evref = bg_tap[11];
                5'd17: evref = flag_rise[0]; 5'd18: evref = flag_rise[1]; 5'd19: evref = flag_rise[2]; 5'd20: evref = flag_rise[3];
                5'd21: evref = flag_rise[4]; 5'd22: evref = flag_rise[5]; 5'd23: evref = flag_rise[6]; 5'd24: evref = flag_rise[7];
                5'd25: evref = pin_rise[pa_sel];
                5'd26: evref = pin_fall[pa_sel];
                5'd27: evref = pin_rise[pa_sel] | pin_fall[pa_sel];
                5'd28: evref = hostinv_rise;
                5'd29: evref = !ready && !running;
                default: evref = 1'b0;                       // 0 = NONE and 30, 31: never fire (SPEC 9a.1)
            endcase
        end
    endfunction
    wire trig_r  = en && (evref(trig) || doorbell);          // doorbell also requires EN
    wire busy    = ready || running;
    wire acc_r   = trig_r && !busy;
    // beat generator selected by BG
    wire b_beat = bg_beat[bg];
    wire [2:0] b_tap = bg_tap[3*bg +: 3];

    // SPEC 4: EN=0 means no trigger is accepted (E.STOP: no new triggers).
    // (checked through the sequential property below; also the trigger-code table is checked via trig_r.)

    // ---- combinational: input symbol, watcher dispatch address
    // SPEC 4: IN = {LUT1[CAP], LUT0[CAP]}
    always @(*) assert (in_sym == {lut1[cap], lut0[cap]});
    // (watcher evaluation moved to the core in the current RTL; the engine only exports W0C/W1C/W0H/W1H)
    always @(*) assert (err == (late || ovr));
    // pinA/pinB read the selected pin level
    always @(*) assert (pina == pin_lvl[pa_sel]);

    // ---- shadow of previous cycle
    reg p_rstn, p_trig, p_acc, p_busy, p_disp, p_pause, p_sym_we, p_stop_we, p_beat, p_hwstat_ovr, p_hwstat_late;
    reg p_alw; always @(posedge clk) p_alw <= en && trig == 5'd29 && !doorbell && !ready && !running;
    reg p_hwcfg, p_hwpc, p_ready, p_running, p_armed, p_late, p_ovr, p_en, p_pina, p_pinb;
    reg [1:0] p_sym_d, p_staged, p_committed; reg [2:0] p_tap; reg [7:0] p_hwd, p_pause_pc, p_pc; reg [3:0] p_cap;
    always @(posedge clk) begin
        p_rstn <= rst_n; p_trig <= trig_r; p_acc <= acc_r; p_busy <= busy; p_disp <= disp; p_pause <= pause;
        p_sym_we <= sym_we; p_stop_we <= stop_we; p_beat <= b_beat; p_tap <= b_tap; p_sym_d <= sym_d;
        p_hwstat_ovr  <= h_we && h_off == HENG_STAT[4:0] && h_wd[5];
        p_hwstat_late <= h_we && h_off == HENG_STAT[4:0] && h_wd[4];
        p_hwcfg <= h_we && h_off == HENG_CFG[4:0]; p_hwpc <= h_we && h_off == HENG_PC[4:0];
        p_hwd <= h_wd; p_pause_pc <= pause_pc; p_pc <= pc; p_cap <= cap; p_pina <= pina; p_pinb <= pinb;
        p_ready <= ready; p_running <= running; p_armed <= armed; p_late <= late; p_ovr <= ovr; p_en <= en;
        p_staged <= staged; p_committed <= committed;
    end
    wire ok1 = pv && p_rstn;

    // reset
    always @(posedge clk) if (pv && !p_rstn)
        assert (!en && !ready && !running && !armed && !late && !ovr && staged == 0 && committed == 0 && pc == 0);

    // SPEC 4 trigger: if READY||RUNNING then OVR'=1 and the trigger is dropped (READY unchanged);
    // otherwise READY'=1 and ARMED'=1. Dispatch (needs READY) clears READY and sets RUNNING; pause clears RUNNING.
    always @(posedge clk) if (ok1) begin
        assert (ready == (p_disp ? 1'b0 : (p_acc ? 1'b1 : p_ready)));
        assert (running == (p_disp ? 1'b1 : (p_pause ? 1'b0 : p_running)));
        assert (armed == (p_acc ? 1'b1 : (p_beat ? 1'b0 : p_armed)));    // trigger wins over the beat clear
        // sticky errors; host STAT write of 1 to the bit has priority over a same-cycle set (SPEC-AMBIGUITY in RTL)
        assert (ovr  == (p_hwstat_ovr  ? 1'b0 : ((p_trig && p_busy) ? 1'b1 : p_ovr)));
        assert (late == (p_hwstat_late ? 1'b0 : ((p_sym_we && !p_armed) ? 1'b1 : p_late)));
        // SPEC 4 symbols: E.SYM sets STAGED; BEAT commits (same-cycle E.SYM wins over STAGED)
        assert (staged == (p_sym_we ? p_sym_d : p_staged));
        assert (committed == (p_beat ? (p_sym_we ? p_sym_d : p_staged) : p_committed));
        // SPEC 4 capture
        assert (cap[0] == (p_tap[0] ? p_pina : p_cap[0]));
        assert (cap[1] == (p_tap[1] ? p_pina : p_cap[1]));
        assert (cap[3] == (p_tap[1] ? p_pinb : p_cap[3]));
        assert (cap[2] == (p_tap[2] ? p_pina : p_cap[2]));
        // PC: host write > pause; otherwise stable
        assert (pc == (p_hwpc ? p_hwd : (p_pause ? p_pause_pc : p_pc)));
        // EN: host CFG write > E.STOP; otherwise stable (SPEC 4 Stop)
        assert (en == (p_hwcfg ? p_hwd[0] : (p_stop_we ? 1'b0 : p_en)));
    end
    // SPEC 4: a trigger is accepted only while EN; with EN=0 (after E.STOP) nothing becomes READY.
    always @(posedge clk) if (ok1 && !p_en && !p_disp) assert (!ready || p_ready);
    // SPEC 4 ALWAYS: only fires when idle, so it can never raise OVR on its own.
    always @(posedge clk) if (ok1 && p_alw) assert (!ovr || p_ovr);
    // invariant: READY and RUNNING are exclusive (needs A2); also the burst that is dispatched implies EN was
    // seen at acceptance (no direct check; see covers).
    always @(posedge clk) if (pv) assert (!(ready && running));

    always @(posedge clk) begin
        cover (ok1 && p_acc && ready && armed);
        cover (ok1 && p_trig && p_busy && ovr && !p_ovr);
        cover (ok1 && p_sym_we && !p_armed && late && !p_late);
        cover (ok1 && p_beat && p_sym_we && committed == p_sym_d && committed != p_staged);
        cover (ok1 && p_acc && p_beat && armed);
        cover (ok1 && p_stop_we && !en && p_en);
        cover (ok1 && p_tap[1] && cap[3] != p_cap[3]);
    end
endmodule

bind md_engine fv_engine_props fv_props (.*);
