import Metronome.ChipCut.Wire

set_option autoImplicit false
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.ChipCut.Discharge.MovePayloadWire

open Metronome
open Metronome.ChipCut

/-- The arbiter's `coreIssue` is "the grant is `.core`", in boolean form. -/
theorem step_coreIssue (st : Config.State) (inp : Config.Input) (c : Config.Write) :
    (match Config.grant st inp with
      | .host w => (true, false, w)
      | .core w => (true, true, w)
      | .idle => (false, false, c)).2.fst =
    (!st.heldValid && !st.previousWrite && !inp.hostValid && inp.coreValid) := by
  unfold Config.grant
  by_cases hh : st.heldValid = true <;> by_cases hp : st.previousWrite = true <;>
    by_cases hv : inp.hostValid = true <;> by_cases hc : inp.coreValid = true <;>
    simp [hh, hp, hv, hc]

/-- The arbiter cut's `coreIssue` in closed form. -/
theorem arbIn_coreIssue (s : State) :
    (arbStep s).coreIssue =
      (!s.arb.heldValid && !s.arb.previousWrite && !(hostCfgOf s).isSome &&
        ((s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) && !s.freeze.frz)) := by
  have h := step_coreIssue (Config.beforeEdge s.arb (arbIn s)) (arbIn s) (arbIn s).core
  simp only [arbStep, Config.step]
  refine h.trans ?_
  simp [Config.beforeEdge, arbIn, Bridge.CfgWrite.cfgIn]

/-- The host slot's `pending` bit is the pointer request. -/
theorem pending_req (b : Mem.State) (h : b.req ≠ (3 : BitVec 2)) :
    (match (Bridge.Mem.absP0 b).req with | .none => false | _ => true) = Mem.pending b := by
  rcases Bridge.Mem.req_cases b h with h0 | h1 | h2
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h0]
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h1]
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h2]

/-- The machine's `p0Next` hazard component. -/
theorem p0Next_haz (p : Machine.P0St) (mv : Option Machine.P0Move) (served landNow : Bool)
    (ramOut lane : Nat) (frz : Bool) :
    (Machine.p0Next p mv served landNow ramOut lane frz).2 =
      (mv.isSome && (match p.req with | .none => false | _ => true) && !served) := rfl

/-- The cut's queue overrun event, in `pending`/`drain` form. -/
theorem accept_not (st : CoreQueue.State) (i : CoreQueue.Input) :
    (CoreQueue.writeData i && !CoreQueue.accept st i) =
      (CoreQueue.writeData i && st.pending && !CoreQueue.drain st i) := by
  unfold CoreQueue.accept
  by_cases hw : CoreQueue.writeData i = true <;>
    by_cases hp : st.pending = true <;>
    by_cases hd : CoreQueue.drain st i = true <;>
    simp [hw, hp, hd]

end Metronome.ChipCut.Discharge.MovePayloadWire
