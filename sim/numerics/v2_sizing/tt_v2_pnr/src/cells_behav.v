// Behavioural models of the two IHP sg13cmos5l cells used by cfg_latch_bank. Simulation only (never synthesized;
// the flow uses the library cells). Function matches build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib:
//   dlhrq_1: latch (clear = !RESET_B, data_in = D, enable = GATE): transparent while GATE high, async clear.
//   lgcp_1 : clock_gating_integrated_cell "latch_posedge"; statetable: int_GATE follows GATE while CLK low, holds
//            while CLK high; GCLK = CLK & int_GATE.
// Lint waiver note (this file only): DECLFILENAME (two cell models share one file); these cells ARE latches by
// definition, so LATCH/COMBDLY are suppressed here; the wrapper itself has no waivers.
// Guarded so the file may stay in a synthesis source list: with USE_IHP_CELLS defined it is empty.
`ifndef USE_IHP_CELLS
/* verilator lint_off DECLFILENAME */
/* verilator lint_off LATCH */
/* verilator lint_off COMBDLY */
module cfg_dlhrq_beh (input D, input GATE, input RESET_B, output reg Q);
    always @* begin
        if (!RESET_B)  Q = 1'b0;
        else if (GATE) Q = D;
    end
endmodule

module cfg_lgcp_beh (input CLK, input GATE, output GCLK);
    reg int_gate;
    always @* if (!CLK) int_gate = GATE;
    assign GCLK = CLK & int_gate;
endmodule
/* verilator lint_on COMBDLY */
/* verilator lint_on LATCH */
`endif
