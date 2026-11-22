import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false

namespace Metronome.ChipCut.Discharge.MovePayloadWire

open Metronome
open Metronome.ChipCut.Discharge

/-- `mhcServed` is `machServed`-free : the Glue local arbiter is the MemHostCfg one. -/
example (m : Machine.State) (pin : Machine.PinIn) :
    Glue.machineServed m pin = Discharge.mhcServed m pin := rfl

/-- The machine's p0 hazard component. -/
example (p : Machine.P0St) (mv : Option Machine.P0Move) (served landNow : Bool)
    (ramOut lane : Nat) (frz : Bool) :
    (Machine.p0Next p mv served landNow ramOut lane frz).2 =
      (mv.isSome && (match p.req with | .none => false | _ => true) && !served) := rfl

/-- `Mem.haz`. -/
example (s : State) (pin : Machine.PinIn) :
    Mem.haz s.p0 (memIn s pin) =
      ((memIn s pin).pWe && Mem.pending s.p0 && !Mem.grantP0 s.p0 (memIn s pin)) := rfl

/-- The queue drain is the cut's `cwDrain`. -/
example (s : State) (pin : Machine.PinIn) :
    CoreQueue.drain s.cq (cqIn s pin) = cwDrain s := rfl

/-- `pWe` is the `isSome` of the pointer move. -/
example (i : Mem.Input) : (Bridge.Mem.mvOf i).isSome = i.pWe := by
  cases i.pWe <;> rfl

/-- The three `CW` destination codes share one write group. -/
example : Moves.dgTable 58 = Moves.dgTable 59 ∧ Moves.dgTable 58 = Moves.dgTable 60 := by
  decide

/-- The cut's `cwCode`/`cwData`/`bitAt` on the packed `CW` word. -/
example (s : State) (pin : Machine.PinIn) :
    CoreQueue.cwCode (cwWord s pin) = (gw s pin 58).dst := by
  simp only [cwWord, CoreQueue.cwCode, CoreCtl.GroupWord.pack]
  exact CoreCtl.makeWord_dst _ _ _

example (s : State) (pin : Machine.PinIn) :
    CoreQueue.cwData (cwWord s pin) = (gw s pin 58).data := by
  simp only [cwWord, CoreQueue.cwData, CoreCtl.GroupWord.pack]
  exact CoreCtl.makeWord_data _ _ _

example (s : State) (pin : Machine.PinIn) :
    CoreQueue.bitAt (cwWord s pin) 14 = (gw s pin 58).we := by
  simp only [cwWord, CoreQueue.bitAt, CoreCtl.GroupWord.pack]
  exact CoreCtl.makeWord_we _ _ _

/-- `flagsSetDst` is code 5. -/
example : Metronome.Glue.flagsSetDst = (5 : BitVec 6) := rfl

/-- The `p0Sel` values of the four pointer codes. -/
example : (Strobes.p0Sel (BitVec.ofNat 6 43)).toNat = 0 := by decide
example : (Strobes.p0Sel (BitVec.ofNat 6 44)).toNat = 1 := by decide
example : (Strobes.p0Sel (BitVec.ofNat 6 45)).toNat = 2 := by decide
example : (Strobes.p0Sel (BitVec.ofNat 6 46)).toNat = 3 := by decide

/-- The machine's `cwNext` overrun, as the four-way match on the move. -/
example (m : Machine.State) (pin : Machine.PinIn) :
    (Discharge.mhcCwo m pin).ovr =
      (match Discharge.mhcCwMove m pin with
        | some ⟨0, _⟩ => false
        | some ⟨1, _⟩ => false
        | some ⟨_, _⟩ => m.cw.cwv && !(!m.dbg.frz && m.cw.cwv &&
            (if m.cw.cwv && Machine.Config.isCfgAddr m.cw.cwqa.toNat then
              (!m.cw.hh && (Discharge.mhcHostCfg m pin).isNone && !m.dbg.frz &&
                m.cw.cwv && Machine.Config.isCfgAddr m.cw.cwqa.toNat && !m.cw.bwp)
            else true))
        | none => false) := by
  simp only [Discharge.mhcCwo, Machine.cwNext]
  rfl

/-- `(ctrlInTrue m pin).cwovr` is the machine's `cwNext` overrun. -/
example (m : Machine.State) (pin : Machine.PinIn) :
    (Discharge.ctrlInTrue m pin).cwovr = (Discharge.mhcCwo m pin).ovr := rfl

/-- `ctrlInTrue`'s `memhaz` is the two-term hazard. -/
example (m : Machine.State) (pin : Machine.PinIn) :
    (Discharge.ctrlInTrue m pin).memhaz =
      ((!m.p0.rdy && (Discharge.ltAllMoves m).any (fun mv => match Machine.srcOp mv.src with
          | .pD => true | _ => false)) ||
        (Machine.p0Next m.p0 (Discharge.mhcP0Move m pin) (Glue.machineServed m pin == 3)
          (m.ramOwner == 3) m.ramOut.toNat m.ramLane.toNat m.dbg.frz).2) := by
  simp only [Discharge.ctrlInTrue, Discharge.ltAllMoves]
  rfl

end Metronome.ChipCut.Discharge.MovePayloadWire
