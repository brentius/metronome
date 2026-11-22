-- OBSOLETE intermediate draft (kept as evidence, does not compile):
-- it assumed `Discharge.HostPinWire` was importable and used `hrel.dbg.cen`
-- (a nested conjunction, not a structure) and `host_sck_spacing` from
-- `Discharge.HostPinWire`.  The delivered adapters are in
-- `Metronome/ChipCut/Assembly.lean`.
import Metronome.ChipCut.Discharge.Glue
import Metronome.ChipCut.Discharge.LineThread
import Metronome.ChipCut.Discharge.CoreUnits
import Metronome.ChipCut.Discharge.MemHostCfg
import Metronome.ChipCut.Discharge.StreamDbg
import Metronome.ChipCut.Discharge.GuardSrc
import Metronome.ChipCut.Discharge.HostPinWire
import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.ChipCut.Discharge.CoreCombCbs
import Metronome.ChipCut.Discharge.MoveFabricUnits
import Metronome.ChipCut.Discharge.MoveFabricKeyed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut

open Metronome

/-- The machine's per-stream mode of the cycle is the bridge's `modeOf`. -/
theorem asm_machMode_congr (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Discharge.machMode m k = Discharge.machMode (absChip s) k := by
  have hc : m.cfg = (absChip s).cfg := by rw [hrel.cfg]; rfl
  unfold Discharge.machMode Machine.streamMode
  rw [hc, hrel.dbg.cen, hrel.dbg.rpl]
  rfl

theorem asm_streamWire_mode (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    Discharge.machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
  (asm_machMode_congr s m hrel k).trans (Discharge.absMode_eq s pin k)

/-- `premise_p0`'s landing hypothesis from the `LandingP0` invariant. -/
theorem asm_p0_open_land (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (h : Discharge.LandingP0 s) :
    (m.ramOwner == 3) = (s.p0.land && !(memIn s pin).frzd) := by
  rw [hrel.ramOwner, h]
  rfl

/-- `DbgWire.hword` is definitional. -/
theorem asm_dbg_hword (s : State) (pin : Machine.PinIn) :
    (dbgCtrlIn s pin).replayWord = (streamAt s 0).wb := rfl

/-- `HostPinInv` along the product trace. -/
theorem asm_hostPinInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, Discharge.HostPinInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact Discharge.hostPinInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact Discharge.hostPinInv_step _ _ ih

end Metronome.ChipCut
