import Metronome.Bridge.StreamBuf

/-! Axiom audit for `Metronome/Bridge/StreamBuf.lean` (round 2026-11-22). -/

open Metronome.Bridge.StreamBuf

#print axioms BufRelX.toBufRel
#print axioms BufRelX.capture_wb
#print axioms BufRelX.wb_eq
#print axioms BufRelX.wv_eq
#print axioms BufRelX.nb_eq
#print axioms BufRelX.nv_eq
#print axioms bufRelX_reset
#print axioms bufRelX_abs_reset
#print axioms wb_step_unfrozen
#print axioms wv_step_unfrozen
#print axioms nb_step_unfrozen
#print axioms nv_step_unfrozen
#print axioms bufRelX_step_unfrozen
#print axioms wb_step_frozen
#print axioms wv_step_frozen
#print axioms nb_step_frozen
#print axioms nv_step_frozen
#print axioms bufRelX_step_frozen
#print axioms frozen_ld_false
#print axioms ld_frozen_hold
#print axioms abs_step_frozen_flush
#print axioms abs_step_frozen_rewind_flush
#print axioms frozen_rel_flush
#print axioms frozen_rel_rewind_flush
#print axioms frozen_landing_witness
#print axioms frozen_landing_ld
#print axioms frozen_landing_bufrelX_fails
#print axioms mach_frozen_landing
#print axioms mach_frozen_rewind_landing
#print axioms wb_frozen_landing
#print axioms nb_frozen_landing
#print axioms modeOf_eq_three
#print axioms ld_frozen_eq
#print axioms rq_frozen_hold
#print axioms nv_frozen_hold
#print axioms starved_frozen
#print axioms bufRelX_step_frozen_landing
#print axioms bufRelX_step_frozen_landing_rewind
#print axioms wS4_not_shape
#print axioms frozen_landing_invalid_nv_disagrees
#print axioms abs_step_frozen_landing
#print axioms frozen_rel_landing_flush
#print axioms frozen_rel_landing_rewind_flush
#print axioms shapeModeOK_reset
#print axioms nv_step_true_or
#print axioms rpl_nv_wv
#print axioms shapeOK_step
#print axioms shapeModeOK_step
#print axioms shapeOK_break_witness
#print axioms nv_step_cap_false
#print axioms shapeOK_step_cap_false
#print axioms heldLanding_frozen_landing
#print axioms nv_step_unfrozen_ab
#print axioms wv_step_unfrozen_ab
#print axioms wb_step_unfrozen_guarded
#print axioms nb_step_unfrozen_guarded
#print axioms wb_nb_unfrozen_capF
#print axioms no_overlap_step
#print axioms bufRel_step_unfrozen_guarded
#print axioms buf_step
#print axioms bufRelX_step
#print axioms bufRelX_step_abs#print axioms wb_frozen_tx_landing
#print axioms capRel_step_witness
#print axioms capWb_reachable_witness
#print axioms dbgHwb_of_wv
#print axioms dbgHwb_of_replayValid
#print axioms dbgHwb_unguarded_false
#print axioms capModeOK_reset
#print axioms capModeOK_step
#print axioms contentsWb_of_capModeOK
#print axioms capWb_hchange_excluded
