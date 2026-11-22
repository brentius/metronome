import Metronome.ChipCut.Discharge.Glue

open Metronome

-- The four premise theorems: exactly the `Premises` field types, in order.
#check @Metronome.ChipCut.Discharge.premise_sync
#check @Metronome.ChipCut.Discharge.premise_ctrl
#check @Metronome.ChipCut.Discharge.premise_out
#check @Metronome.ChipCut.Discharge.premise_oen

-- Which `Premises` fields they instantiate.
#check @Metronome.ChipCut.Premises.sync
#check @Metronome.ChipCut.Premises.ctrl
#check @Metronome.ChipCut.Premises.out
#check @Metronome.ChipCut.Premises.oen
