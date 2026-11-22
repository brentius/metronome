import Metronome.ChipCut.Discharge.CoreUnits
import Metronome.ChipCut.Discharge.MoveFabric

/-! `#print axioms` for the round-c premises, the thread `CORE` slot, the guard
vector unpacking and the guard/source slot dispatch. -/

#print axioms Metronome.ChipCut.Discharge.premise_cores
#print axioms Metronome.ChipCut.Discharge.premise_units
#print axioms Metronome.ChipCut.Discharge.rel_coreOf
#print axioms Metronome.ChipCut.Discharge.mine_false_bit
#print axioms Metronome.ChipCut.Discharge.core_next_congr
#print axioms Metronome.ChipCut.Discharge.core_next_ir_irrel
#print axioms Metronome.ChipCut.Discharge.guardVec_bit
#print axioms Metronome.ChipCut.Discharge.bitOf_setBit_same
#print axioms Metronome.ChipCut.Discharge.bitOf_setBit_ne
#print axioms Metronome.ChipCut.Discharge.bitOf_lowMask_lt
#print axioms Metronome.ChipCut.Discharge.bitOf_lowMask_ge
#print axioms Metronome.ChipCut.Discharge.guardV_global
#print axioms Metronome.ChipCut.Discharge.srcV_global
#print axioms Metronome.ChipCut.Discharge.rel_ready
#print axioms Metronome.ChipCut.Discharge.rel_pcOf
#print axioms Metronome.ChipCut.Discharge.rel_lineOf
#print axioms Metronome.ChipCut.Discharge.rel_w0cOf
#print axioms Metronome.ChipCut.Discharge.rel_w1cOf
#print axioms Metronome.ChipCut.Discharge.rel_w0hOf
#print axioms Metronome.ChipCut.Discharge.rel_w1hOf
#print axioms Metronome.ChipCut.Discharge.rel_core_sIr
#print axioms Metronome.ChipCut.Discharge.rel_run
#print axioms Metronome.ChipCut.Discharge.tPc_slot
#print axioms Metronome.ChipCut.Discharge.tCore_bit
#print axioms Metronome.ChipCut.Discharge.guards_bit
#print axioms Metronome.ChipCut.Discharge.srcs_byte
#print axioms Metronome.ChipCut.Discharge.accIn_sel
#print axioms Metronome.ChipCut.Discharge.acc_hit_ne_seven
#print axioms Metronome.ChipCut.Discharge.agrees_machine_units
#print axioms Metronome.ChipCut.Discharge.bgetLE_lt
#print axioms Metronome.ChipCut.Discharge.runStep_cores
#print axioms Metronome.ChipCut.Discharge.runStep_units
#print axioms Metronome.ChipCut.Discharge.MoveFabric.resolveAux_null
#print axioms Metronome.ChipCut.Discharge.MoveFabric.resolveAux_filter_some
#print axioms Metronome.ChipCut.Discharge.MoveFabric.resolveMoves_filter_some
