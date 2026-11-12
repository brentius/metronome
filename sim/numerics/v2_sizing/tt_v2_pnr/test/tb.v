`default_nettype none
`timescale 1ns / 1ps

/* This testbench just instantiates the module and makes some convenient wires
   that can be driven / tested by the cocotb test.py.
*/
module tb ();

  // Dump the signals to a FST file. You can view it with gtkwave or surfer.
  initial begin
    $dumpfile("tb.fst");
    $dumpvars(0, tb);
    #1;
  end

  // Wire up the inputs and outputs:
  reg clk;
  reg rst_n;
  reg ena;
  reg [7:0] ui_in;
  reg [7:0] uio_in;
  wire [7:0] uo_out;
  wire [7:0] uio_out;
  wire [7:0] uio_oe;

  tt_um_brentius_metronome user_project (
      .ui_in  (ui_in),    // Dedicated inputs
      .uo_out (uo_out),   // Dedicated outputs
      .uio_in (uio_in),   // IOs: Input path
      .uio_out(uio_out),  // IOs: Output path
      .uio_oe (uio_oe),   // IOs: Enable path (active high: 0=input, 1=output)
      .ena    (ena),      // enable - goes high when design is selected
      .clk    (clk),      // clock
      .rst_n  (rst_n)     // not reset
  );

`ifdef SDF_FILE
  // Back-annotated gate-level run (run_local.py --gl NETLIST --sdf FILE): signoff delays of one corner.
  initial $sdf_annotate(`SDF_FILE, user_project);
`endif

`ifdef CFG_PROBE
  // Configuration-latch probe and timing monitors (gen_cfg_probe.py, cfg_latch_chk.v); counters read by test_cfg.py.
  reg chk_arm = 1'b0;
  integer chk_setup_err = 0, chk_hold_err = 0, chk_width_err = 0, chk_open_change = 0, chk_x = 0;
  real chk_q_lat_min = 1.0e9, chk_q_lat_max = 0.0;
  `include "cfg_probe.vh"
`endif

endmodule
