// Self-test of the latch timing monitors in cfg_latch_chk.v (the negative control for test_cfg.py): inject one of
// each violation on a single monitored latch and require each counter to see exactly what was injected.
//   iverilog -g2012 -o chk_selftest.vvp cfg_latch_chk.v chk_selftest.v && vvp chk_selftest.vvp
`timescale 1ns / 1ps
module tb;
    reg chk_arm = 1'b0;
    integer chk_setup_err = 0, chk_hold_err = 0, chk_width_err = 0, chk_open_change = 0, chk_x = 0;
    real chk_q_lat_min = 1.0e9, chk_q_lat_max = 0.0;
    reg d = 1'b0, g = 1'b0, q = 1'b0;
    cfg_latch_chk u_chk (.d(d), .g(g), .q(q));
    cfg_gate_cnt  u_gck (.g(g));

    task check_counts(input integer s, input integer h, input integer w, input integer o, input integer x, input integer p);
        if (chk_setup_err !== s || chk_hold_err !== h || chk_width_err !== w || chk_open_change !== o ||
            chk_x !== x || u_gck.pulses !== p) begin
            $display("SELFTEST FAIL at %t: setup %0d/%0d hold %0d/%0d width %0d/%0d open %0d/%0d x %0d/%0d pulses %0d/%0d",
                     $realtime, chk_setup_err, s, chk_hold_err, h, chk_width_err, w, chk_open_change, o, chk_x, x,
                     u_gck.pulses, p);
            $fatal(1);
        end
    endtask

    initial begin
        #1 chk_arm = 1'b1;
        // 1. clean write: D settles, gate opens 2 ns later, Q follows 0.3 ns after, gate closes 8 ns later,
        //    D moves 2 ns after the close
        #5 d = 1'b1;
        #2 g = 1'b1;
        #0.3 q = 1'b1;
        #7.7 g = 1'b0;
        #2 d = 1'b0;
        #1 check_counts(0, 0, 0, 0, 0, 1);
        // 2. setup: D moves 0.1 ns before the gate closes (also counts as moving while open)
        #5 g = 1'b1;
        #5 d = 1'b1;
        #0.1 g = 1'b0;
        #1 check_counts(1, 0, 0, 1, 0, 2);
        // 3. hold: D moves 0.02 ns after the gate closes
        #5 g = 1'b1;
        #5 g = 1'b0;
        #0.02 d = 1'b0;
        #1 check_counts(1, 1, 0, 1, 0, 3);
        // 4. width: a 0.1 ns gate pulse (counted by the latch monitor and by the gate counter)
        #5 g = 1'b1;
        #0.1 g = 1'b0;
        #1 check_counts(1, 1, 2, 1, 0, 4);
        // 5. D moves while the latch is open, well before the close (no setup error)
        #5 g = 1'b1;
        #1 d = 1'b1;
        #5 g = 1'b0;
        #1 check_counts(1, 1, 2, 2, 0, 5);
        // 6. X on D
        #5 d = 1'bx;
        #1 check_counts(1, 1, 2, 2, 1, 5);
        $display("SELFTEST PASS: every injected violation counted once, the clean write counted none");
        $finish;
    end
endmodule
