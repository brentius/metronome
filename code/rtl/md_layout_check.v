// Elaboration-time checks of the assumptions the RTL makes about code/rtl/gen/md_defs.vh: families of ports,
// guards and triggers are contiguous (the RTL indexes them as FIRST + k), and the sizes the pin map and field
// widths are written for. A failed check instantiates an undefined module, so every tool stops at elaboration.
`timescale 1ns/1ps
`default_nettype none
module md_layout_check;
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    localparam [0:0] OK =
        // guards
        (G_TRUE == 0) && (G_F15 == G_F0 + 15) && (G_SH3_DONE == G_SH0_DONE + 3) && (G_SH3_OUT == G_SH0_OUT + 3) &&
        (G_CNT3_Z == G_CNT0_Z + 3) && (G_LF1_OUT == G_LF0_OUT + 1) && (G_P1_RDY == G_P0_RDY + 1) &&
        (G_PIN12 == G_PIN0 + 12) && (G_BG3_RUN == G_BG0_RUN + 3) &&
        // sources
        (S_ZERO == 0) && (S_R3 == S_R0 + 3) && (S_SH3_D == S_SH0_D + 3) && (S_SH3_O == S_SH0_O + 3) &&
        (S_CNT3_LO == S_CNT0_LO + 3) && (S_CNT3_HI == S_CNT0_HI + 3) && (S_LF0_B3 == S_LF0_B0 + 3) &&
        (S_LF1_B0 == S_LF0_B0 + 4) && (S_LF1_B3 == S_LF0_B0 + 7) && (S_P1_D == S_P0_D + 1) &&
        // destinations
        (D_NULL == 0) && (D_R3 == D_R0 + 3) && (D_SH3_LD == D_SH0_LD + 3) && (D_SH3_SH == D_SH0_SH + 3) &&
        (D_SH3_CFG == D_SH0_CFG + 3) && (D_CNT3_LO == D_CNT0_LO + 3) && (D_CNT3_HI == D_CNT0_HI + 3) &&
        (D_CNT3_DEC == D_CNT0_DEC + 3) && (D_LF1_ST == D_LF0_ST + 1) && (D_LF0_B3 == D_LF0_B0 + 3) &&
        (D_LF1_B0 == D_LF0_B0 + 4) && (D_LF1_B3 == D_LF0_B0 + 7) && (D_P1_AL == D_P0_AL + 1) &&
        (D_P1_AH == D_P0_AH + 1) && (D_P1_W == D_P0_W + 1) && (D_P1_R == D_P0_R + 1) &&
        (D_BG3_CTL == D_BG0_CTL + 3) &&
        // triggers
        (T_BG0_TAP0 == T_BG0_BEAT + 1) && (T_BG0_TAP1 == T_BG0_BEAT + 2) && (T_BG0_TAP2 == T_BG0_BEAT + 3) &&
        (T_BG1_BEAT == T_BG0_BEAT + 4) && (T_BG3_TAP2 == T_BG0_BEAT + 15) && (T_FLAG7_RISE == T_FLAG0_RISE + 7) &&
        // sizes the RTL is written for
        (MD_N_CORES == 2) && (MD_N_ENGINES <= 8) && (MD_N_BEATGENS == 4) && (MD_N_FLAGS == 16) &&
        (MD_N_PTRS == 2) && (MD_N_IN_PINS == 13) && (MD_N_OUT_PINS == 14) && (MD_N_OE_PINS == 8) &&
        (MD_BG_WIDTH == 16) && (MD_PROG_WORDS == 256) && (MD_DATA_BYTES == 2048) &&
        (F_COND_W == 6) && (F_IMM_W == 8) && (F_M0_SRC_W == 6) && (F_M0_DST_W == 6) && (F_M0_GUARD_W == 2) &&
        (HUNIT_LF1_POLY == HUNIT_LF0_POLY + 8);
    generate
        if (OK == 0) begin : g_err
            md_defs_layout_mismatch u_err ();
        end
    endgenerate
endmodule
`default_nettype wire
