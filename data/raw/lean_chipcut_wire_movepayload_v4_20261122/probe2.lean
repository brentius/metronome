import Metronome.ChipCut.Discharge.Glue
import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false

namespace Metronome.ChipCut.Discharge.MovePayloadWire

open Metronome
open Metronome.ChipCut.Discharge

/-- The Glue-local `machineServed` is `mhcServed`. -/
example (m : Machine.State) (pin : Machine.PinIn) :
    machineServed m pin = mhcServed m pin := rfl

/-- `pWe` is the `isSome` of the pointer move. -/
example (i : Mem.Input) : (Bridge.Mem.mvOf i).isSome = i.pWe := by
  unfold Bridge.Mem.mvOf
  split <;> simp_all

/-- The cut's `drain` with the `cqIn` fields substituted. -/
example (s : State) (pin : Machine.PinIn) :
    CoreQueue.drain s.cq (cqIn s pin) = cwDrain s := rfl

/-- `Config.isNone` is the negation of `isSome`. -/
example (o : Option (Nat × Nat)) : o.isNone = !o.isSome := by
  cases o <;> rfl

/-- The machine's core-drain term of `cwNext`'s bank-port let. -/
theorem cwNext_coreDrain_val (cw : Machine.CwSt) (hostCfg : Option (Nat × Nat)) (frozen : Bool) :
    (if cw.hh then
        (match hostCfg with
         | some (a, v) => (some (cw.hha.toNat, cw.hhd.toNat), true, a, v, false)
         | none => (some (cw.hha.toNat, cw.hhd.toNat), false, 0, 0, false))
      else
        match hostCfg with
        | some (a, v) =>
          if cw.bwp then (none, true, a, v, false) else (some (a, v), false, 0, 0, false)
        | none =>
          if (!frozen && cw.cwv && (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) &&
              !cw.bwp) = true then
            (some (cw.cwqa.toNat, cw.cwqd.toNat), false, 0, 0, true)
          else (none, false, 0, 0, false)).2.2.2.snd =
      (!cw.hh && hostCfg.isNone && !frozen && cw.cwv &&
        (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) && !cw.bwp) := by
  cases hh : cw.hh
  · cases hc : hostCfg
    · by_cases hd : (!frozen && cw.cwv && (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) &&
          !cw.bwp) = true <;> simp [hh, hc, hd]
    · cases hb : cw.bwp <;> simp [hh, hc, hb]
  · cases hc : hostCfg <;> simp [hh, hc]

end Metronome.ChipCut.Discharge.MovePayloadWire
