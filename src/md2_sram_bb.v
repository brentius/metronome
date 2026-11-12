// Metronome v2: black-box declarations of the two IHP SRAM macros used by md2_pmem and md2_dmem, for synthesis and
// lint. The layout comes from the PDK through MACROS in src/config.json. Simulation defines SIM and uses IHP's
// behavioural models (test/sram_model) instead, so this file is empty then.
`ifndef SIM
`default_nettype none
/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNDRIVEN */
/* verilator lint_off UNUSEDSIGNAL */
(* blackbox *)
module RM_IHPSG13_1P_256x64_c2_bm_bist (
    input  wire        A_CLK,
    input  wire        A_MEN,
    input  wire        A_WEN,
    input  wire        A_REN,
    input  wire [7:0]  A_ADDR,
    input  wire [63:0] A_DIN,
    input  wire        A_DLY,
    output wire [63:0] A_DOUT,
    input  wire [63:0] A_BM,
    input  wire        A_BIST_CLK,
    input  wire        A_BIST_EN,
    input  wire        A_BIST_MEN,
    input  wire        A_BIST_WEN,
    input  wire        A_BIST_REN,
    input  wire [7:0]  A_BIST_ADDR,
    input  wire [63:0] A_BIST_DIN,
    input  wire [63:0] A_BIST_BM
);
endmodule

(* blackbox *)
module RM_IHPSG13_1P_512x32_c2_bm_bist (
    input  wire        A_CLK,
    input  wire        A_MEN,
    input  wire        A_WEN,
    input  wire        A_REN,
    input  wire [8:0]  A_ADDR,
    input  wire [31:0] A_DIN,
    input  wire        A_DLY,
    output wire [31:0] A_DOUT,
    input  wire [31:0] A_BM,
    input  wire        A_BIST_CLK,
    input  wire        A_BIST_EN,
    input  wire        A_BIST_MEN,
    input  wire        A_BIST_WEN,
    input  wire        A_BIST_REN,
    input  wire [8:0]  A_BIST_ADDR,
    input  wire [31:0] A_BIST_DIN,
    input  wire [31:0] A_BIST_BM
);
endmodule
/* verilator lint_on UNUSEDSIGNAL */
/* verilator lint_on UNDRIVEN */
/* verilator lint_on DECLFILENAME */
`default_nettype wire
`endif
