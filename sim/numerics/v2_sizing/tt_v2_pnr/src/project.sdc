# Metronome v2 timing constraints: LibreLane's base SDC plus one exception (HARDEN_LEDGER U10 r3).
source $::env(SCRIPTS_DIR)/base.sdc

# Configuration latch D inputs (cfg_latch_bank, sg13cmos5l_dlhrq_1 instances u_l). data1 is loaded only on a write
# edge E1 and the selected byte's gate opens at E2, one cycle later; the write spacing rule (no `we` on consecutive
# edges, checked in simulation, guaranteed by md2_host's one strobe per SPI byte) keeps data1 stable until that
# gate closes. So the data path from data1 to the latch D pins has two cycles to settle before the gate opens and no
# time is borrowed through the latch. The hold check stays at its single-cycle default.
set cfg_latch_d [get_pins {*u_l/D}]
puts "\[INFO] config latch D pins under the 2-cycle setup exception: [llength $cfg_latch_d]"
set_multicycle_path -setup 2 -to $cfg_latch_d
set_multicycle_path -hold 1 -to $cfg_latch_d
