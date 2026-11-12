// Timing monitors for the configuration latches in a back-annotated (SDF) gate-level run. Icarus applies SDF path
// delays but does not enforce the cells' $setuphold/$width checks, so these modules check the latch pins directly.
// Instantiated per latch / per clock gate by the generated cfg_probe.vh (gen_cfg_probe.py); they report into
// counters in module `tb` and only count after the test sets tb.chk_arm (reset done, nets settled).
//
// Limits (ns) are at or beyond the slow-corner SDF of run v2pnr_r4_20261112T0921 for sg13cmos5l_dlhrq_1:
// SETUP (D to negedge GATE) 0.290, HOLD -0.275 (negative), WIDTH (posedge GATE) 0.143.
`timescale 1ns / 1ps

module cfg_latch_chk #(parameter real SETUP = 0.30, parameter real HOLD = 0.05, parameter real WIDTH = 0.15) (
    input wire d, input wire g, input wire q
);
    realtime t_d = -1.0e9, t_rise = -1.0e9, t_fall = -1.0e9;
    always @(d) begin
        if (tb.chk_arm) begin
            if (g === 1'b1) tb.chk_open_change = tb.chk_open_change + 1;   // D moved while the latch was open
            if ($realtime - t_fall < HOLD) begin
                tb.chk_hold_err = tb.chk_hold_err + 1;
                if (tb.chk_hold_err <= 5) $display("CFGCHK hold %m at %t", $realtime);
            end
            if (d !== 1'b0 && d !== 1'b1) tb.chk_x = tb.chk_x + 1;
        end
        t_d = $realtime;
    end
    always @(posedge g) t_rise = $realtime;
    always @(negedge g) begin
        t_fall = $realtime;
        if (tb.chk_arm) begin
            if (t_fall - t_d < SETUP) begin
                tb.chk_setup_err = tb.chk_setup_err + 1;
                if (tb.chk_setup_err <= 5) $display("CFGCHK setup %m at %t (D moved %0.3f ns before close)",
                                                    $realtime, t_fall - t_d);
            end
            if (t_fall - t_rise < WIDTH) begin
                tb.chk_width_err = tb.chk_width_err + 1;
                if (tb.chk_width_err <= 5) $display("CFGCHK width %m at %t (%0.3f ns)", $realtime, t_fall - t_rise);
            end
        end
    end
    // Q latency from the gate opening: shows the SDF delays are in effect (0 in a zero-delay run).
    always @(q) if (tb.chk_arm && g === 1'b1 && $realtime - t_rise < 5.0) begin
        if ($realtime - t_rise < tb.chk_q_lat_min) tb.chk_q_lat_min = $realtime - t_rise;
        if ($realtime - t_rise > tb.chk_q_lat_max) tb.chk_q_lat_max = $realtime - t_rise;
        if (q !== 1'b0 && q !== 1'b1) tb.chk_x = tb.chk_x + 1;
    end
endmodule

// Counts rising edges of one byte's gated clock (the write strobe); also flags a pulse narrower than WIDTH.
module cfg_gate_cnt #(parameter real WIDTH = 0.15) (input wire g);
    integer pulses = 0;
    realtime t_rise = -1.0e9;
    always @(posedge g) begin
        t_rise = $realtime;
        if (tb.chk_arm) pulses = pulses + 1;
    end
    always @(negedge g) if (tb.chk_arm && $realtime - t_rise < WIDTH) tb.chk_width_err = tb.chk_width_err + 1;
endmodule
