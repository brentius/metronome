import Metronome.Machine.Core

/-! §4 Threads: trigger events, overrun, disarm, late writes, stop, dispatch and pause; §9 thread runtime host
writes; §12.3 no trigger in a frozen cycle. -/

namespace Metronome.Machine

open Util Tables

/-- §4 `event(TRIG)` in cycle t: `Lg.BEAT`, `Lg.TAPk` of line g; `FLAGk.RISE = F[k] && !FP[k]`;
`PINA.RISE/FALL/EDGE` of `PIN[PINA]` of the thread's line; `HOST.INV = INV && !INVP`; `ALWAYS = !READY && !RUNNING`;
`NONE` never (and codes beyond the table never fire, 9a.1). -/
def trigEvent (s : State) (cv : CfgView) (p : PinView) (lcs : Vector LineComb 4) (t : Nat) : Bool :=
  let tc := vget cv.threads t
  let ts := vget s.threads t
  let pina := (vget cv.lines tc.line).pina
  match trigOp tc.trig with
  | .none => false
  | .beat g => (vget lcs g).beat
  | .tap g k => (vget lcs g).tap[k]!
  | .flagRise k => bit s.units.f k && !bit s.units.fp k
  | .pinaRise => p.rise pina
  | .pinaFall => p.fall pina
  | .pinaEdge => p.rise pina || p.fall pina
  | .hostInv => s.ctrl.inv && !s.ctrl.invp
  | .always => !ts.ready && !ts.running

/-- §4 Inputs to thread t in cycle t from its line, the cores, the moves and the host. -/
structure ThreadIn where
  /-- `trig = EN && (event(TRIG) || DB[t])` (0 in a frozen cycle, §12.3) -/
  trig : Bool := false
  /-- its line has `BEAT` -/
  beat : Bool := false
  /-- an enabled symbol move by this thread while `ARMED == 0` -/
  late : Bool := false
  /-- winning move to `T.STOP` by this thread -/
  stop : Bool := false
  dispatch : Bool := false
  /-- a pause of this thread, with `npc` -/
  pause : Option Nat := none
  hPC : Option Nat := none
  hStat : Option Nat := none

/-- §4 / §9 Thread next state.

* On `trig`: if `READY || RUNNING` then `OVR' = 1` and the trigger is dropped; otherwise `READY' = 1, ARMED' = 1`.
* Disarm: line `BEAT` gives `ARMED' = 0` unless a trigger is accepted in the same cycle.
* Late write sets `LATE' = 1`; `T.STOP` gives `EN' = 0` unless the host writes `EN` in the same cycle.
* Dispatch `READY' = 0, RUNNING' = 1`; pause `RUNNING' = 0, PC' = npc`; a host `PC` write wins over the pause.
* Host `STAT` write: `EN` from bit 3; bits 4, 5 clear `LATE`, `OVR` (a flag set in the same cycle stays set). -/
def threadNext (ts : ThreadSt) (i : ThreadIn) : ThreadSt :=
  let busy := ts.ready || ts.running
  let acc := i.trig && !busy
  let hs := i.hStat.getD 0
  { pc := match i.hPC with
      | some v => bv 8 v
      | none => match i.pause with
        | some n => bv 8 n
        | none => ts.pc
    en := match i.hStat with
      | some v => nbit v 3
      | none => if i.stop then false else ts.en
    ready := if acc then true else if i.dispatch then false else ts.ready
    running := if i.dispatch then true else if i.pause.isSome then false else ts.running
    armed := if acc then true else if i.beat then false else ts.armed
    late := (ts.late && !nbit hs 4) || i.late
    ovr := (ts.ovr && !nbit hs 5) || (i.trig && busy) }

end Metronome.Machine
