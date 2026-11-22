import Metronome.ChipCut.Discharge.MemHostCfg

open Metronome Metronome.ChipCut Metronome.ChipCut.Discharge
open BankWire

#check cfgView_maskImg
#check cfgMask_poly
#check cfgView_of_masked
#check cfgView_bankImg
#check cfgPoly_bankImg
#check cfgMask_live_cfg
#check BankRel
#check rel_reset
#check maskedZero_release_trace
#check bank_live_cfg
#check bank_decode_of_rel
#check premise_bank
#check trace_cfg_size

#print axioms cfgView_maskImg
#print axioms cfgMask_poly
#print axioms cfgMask_live_cfg
#print axioms bank_decode_of_rel
#print axioms premise_bank
#print axioms rel_reset
#print axioms maskedZero_release_trace
#print axioms trace_refines
#print axioms trace_cfg_size

-- Offset 17 has seven latches. It contradicts the former all-or-none premise.
example : cfgMaskFin ⟨17, by decide⟩ = 0x7F := by decide

-- AMBIG 4: OUT[8].OE is a machine write address with no latch at offset 0x188.
example : cfgMaskB 0x188 = 0 ∧ Machine.Config.isCfgAddr 0x2188 = true := by
  decide +kernel

example (c : Machine.Config) : (c.out 8).oe = 0 := rfl
