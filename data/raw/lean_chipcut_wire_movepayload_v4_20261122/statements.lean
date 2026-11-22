import Metronome.ChipCut.Discharge.MovePayloadWire

/-! # Exact statements of the five `OpenWiring` field theorems -/

set_option pp.universes false
set_option pp.explicit false

open Metronome
open Metronome.ChipCut.Discharge.MovePayloadWire

#check @unitFlagPQ
#check @p0Move
#check @cwMove
#check @ctrlMemhaz
#check @ctrlCwovr
#check @mhcP0Move_isSome
#check @hPQ_p0
#check @hPQ_cw
#check @pdScan
#check @mhcDrains_eq
#check @DstFlagP0CwTable
