/-
# ChipCut discharge: the `streams` and `dbg` premise fields

`Metronome.ChipCut.Premises` (in `ChipCut/Proof.lean`) has one field per
component group; `CHIPCUT_NOTES.md` §3.4.1 lists for each the bridge theorem
that proves it and the remaining wiring fact.  This file discharges the two
fields assigned to it:

* `streams` — `Bridge.StreamB.abs_step_unfrozen`, the relational frozen step
  (`frozen_rel` below; the bridge's `abs_step_frozen` states an exact-state
  equality against `abs s` and so cannot be applied to a *related*, not equal,
  machine state), the mode/CAP map and the configuration decode.
* `dbg` — `Bridge.Debug.dbg_step_bridge` for the eight fields it covers, plus the
  freeze bookkeeping (`FREEZE`/`FRZ`/`FRZD`, `Metronome.CoreCtl`'s
  `freeze_next`/`frz_next`/`frzd_next`) which the bridge leaves out.

Everything here is *definitional plumbing plus the existing bridge theorems*: the
projections of the machine's inline `runStep` records (this file's `mach*`
definitions mirror `Machine.runStep`'s `let` bindings), the correspondence of
the cut's `activeStep` inputs with the machine's records, and the assembly.  The
still-open obligations are explicit named hypotheses; `DISCHARGE_STREAMDBG_NOTES.md`
records each one, why it is open and its witness where the two sides disagree.

## What is proved unconditionally, and what is a named hypothesis

Proved here (no hypothesis beyond `ChipRel`/`Inv`/`active` and the named wiring):

* the `runStep`/`activeStep` projections of every field used;
* the stream configuration decode (`cfgOf_streamIn`) and the mode map
  (`machMode_eq`);
* the whole frozen-cycle `streams` field (`frozen_rel` without a host rewind,
  `frozen_rel_rewind` with one: the cut's frozen step applies §6.3's rewind
  override, the machine's landing test is false under the bridge's landing
  hypothesis, and `BufRel` is preserved reflexively);
* the machine's host write is the cut's (`machHw_eq`), and hence every host-map
  byte `hwByte (machHw m) blk inst reg = if hwIsSome s blk inst reg then some
  (hwData s).toNat else none` (`hwByte_hwOf`);
* the debug freeze/frz/frzd bookkeeping (`dbg_freeze`, `dbg_frz`, `dbg_frzd`)
  from `CoreCtl`'s spec;
* the ten `dbg` fields that `ChipRel.dbg` already relates.

Named hypotheses (see the notes; all are wiring facts that no bridge states):

* `streams_open_moves` — the `Sk.ADV`/`Sk.RX`/`Sk.CTL` picks (machine
  `resolveMoves` winners against `Strobes.opg`/`Moves.pickWord`; needs the
  `MoveAgree` construction, the `cores` thread's `Core.Rel` item);
* `streams_open_served` — `served == k+1` against `Mem.grantS0`/`grantS1`;
* `streams_open_landnow` — `ramOwner == k+1` against the cut's `LD && !FRZD`
  (a trace invariant, not a single-cycle relation);
* `hostctl` — no stream flush acts in the frozen cycle: §12.3 ignores a host
  stream flush while frozen, so the chip never presents one.  A host `SRT.CTL`
  *rewind* and the `STARVED` clear are legal in a frozen cycle and are bridged
  (`frozen_rel_rewind`), so they are not a side condition;
* `bufrel` — `BufRel` preservation over the three recorded replay-buffer
  corners (`BRIDGE_UNITS_STREAM_NOTES.md`);
* `dbg`'s `DbgWire` — `dbg_step_bridge`'s interface equalities (the `DBG`
  byte-window decode, the single-drain exclusivity, the exact first replay
  slot, the capture/replay comparisons) and the frozen-cycle exclusion
  (`dbg_step_bridge` takes `i.frz = false`; the recorded divergence there is
  `RLVP`).
-/

import Metronome.ChipCut.Proof
import Metronome.Bridge.Stream
import Metronome.Bridge.StreamBuf
import Metronome.Bridge.Debug
import Metronome.Bridge.Host
import Metronome.Bridge.Mem
import Metronome.CoreCtl

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## A `Vector.ofFn` projection for `Fin` indices -/

theorem vecGet_ofFn {α : Type} {n : Nat} (f : (i : Fin n) → α) (k : Fin n) :
    (Vector.ofFn f)[k] = f k := by
  simp

/-! ## A zero move bus presents no strobe -/

/-- A zero move-enable word gives a zero hit mask. -/
theorem hitsMask_zero (grp : BitVec 30) (G : BitVec 5) :
    Moves.hitsMask (0 : BitVec 6) grp G = 0 := by
  simp [Moves.hitsMask, Moves.bits6, Moves.hitAt, CoreCtl.bitAt]

/-- A zero hit mask presents no destination. -/
theorem dsteqMask_zero (dst : BitVec 36) (D : BitVec 6) :
    Strobes.dsteqMask (0 : BitVec 6) dst D = false := by
  simp [Strobes.dsteqMask, CoreCtl.bitAt]

/-- **A frozen cycle presents no move strobe** (`frozenNoMove` gives `mvEn = 0`). -/
theorem opg_zero (grp : BitVec 30) (dst : BitVec 36) (G : BitVec 5) (D : BitVec 6) :
    Strobes.opg (0 : BitVec 6) grp dst G D = false := by
  have h : Moves.hitsMask (0 : BitVec 6) grp G = 0 := hitsMask_zero grp G
  unfold Strobes.opg
  rw [h]
  exact dsteqMask_zero dst D

/-! ## The machine's per-cycle records, projected out of `runStep`

`Machine.runStep` builds the line/thread/core/stream inputs inline.  The
definitions below are verbatim copies of its `let` bindings, so the projection
lemmas are definitional (`rfl` or `simp [Machine.runStep]`). -/

/-- The machine's per-cycle line combinations. -/
def machLcs (m : Machine.State) : Vector Machine.LineComb 4 :=
  Vector.ofFn fun l => Machine.lineComb (Machine.cfgView m.cfg).lines[l] m.lines[l]
    (Machine.pinView m.sync m.dbg) m.dbg.frz

/-- The machine's per-cycle core combinations. -/
def machCbs (m : Machine.State) : Vector Machine.CoreComb 2 :=
  Vector.ofFn fun c => Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
    c.val m.dbg.frz

/-- The machine's six moves this cycle. -/
def machAllMoves (m : Machine.State) : List Machine.Move :=
  (machCbs m)[0].moves ++ (machCbs m)[1].moves

/-- The machine's move arbitration result. -/
def machWs (m : Machine.State) : List Machine.Move :=
  (Machine.resolveMoves (machAllMoves m)).1

/-- The machine's per-stream mode. -/
def machMode (m : Machine.State) (k : Fin 2) : Nat :=
  Machine.streamMode (Machine.cfgView m.cfg).streams[k] k.val m.dbg

/-- The machine's per-requester stream request. -/
def machSreq (m : Machine.State) (k : Fin 2) : Machine.RamReq :=
  Machine.streamReq (machMode m k) m.streams[k]

/-- The machine's arbiter result. -/
def machServed (m : Machine.State) : Nat :=
  Machine.arbiter (machSreq m 0) (machSreq m 1) (Machine.p0Req m.p0) (Machine.hostReq m.host)
    m.dbg.frz

/-- The machine's capture event of the cycle. -/
def machCevRec (m : Machine.State) : Bool × Nat :=
  Machine.captureEvent m.dbg (Machine.pinView m.sync m.dbg) m.dbg.frz

/-- The machine's replay `apply`/`late` of the cycle. -/
def machApplyLate (m : Machine.State) : Bool × Bool :=
  Machine.replayApply m.dbg m.streams[0] m.dbg.frz

/-- The machine's host write of the cycle (`Machine.hostNext`'s second output). -/
def machHw (m : Machine.State) : Option Machine.HostWr :=
  (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
    (machServed m == 4)).2

/-- The machine's drained core write of the cycle. -/
def machCw (m : Machine.State) : Option Machine.HostWr :=
  let cvm : Option Machine.CwMove := (machWs m).findSome? fun mm =>
    match Machine.dstOp mm.dst with
    | .cwAl => some ⟨0, mm.v⟩
    | .cwAh => some ⟨1, mm.v⟩
    | .cwD => some ⟨2, mm.v⟩
    | _ => none
  let window := !(Machine.Util.bit m.rqh 0 && Machine.Util.bit m.rqh 1)
  let hostCfg := match machHw m with
    | some w => if Machine.Config.isCfgAddr w.addr then some (w.addr, w.v) else none
    | none => none
  (Machine.cwNext m.cw hostCfg cvm window m.dbg.frz).rt

/-- The machine's per-cycle stream input, exactly `runStep`'s inline record. -/
def machStreamIn (m : Machine.State) (k : Fin 2) : Machine.StreamIn :=
  let ws := machWs m
  let sel (f : Machine.DstOp → Option Nat) : Option Nat :=
    ws.findSome? fun mm => f (Machine.dstOp mm.dst) |>.map fun _ => mm.v
  { adv := (sel fun d => match d with
      | .sAdv j => if j == k.val then some 0 else none
      | _ => none).isSome
    rx := sel fun d => match d with
      | .sRx j => if j == k.val then some 0 else none
      | _ => none
    ctlMove := sel fun d => match d with
      | .sCtl j => if j == k.val then some 0 else none
      | _ => none
    hCtl := Machine.Util.hwByte (machHw m) "SRT" k.val "CTL"
    served := machServed m == k.val + 1
    landNow := m.ramOwner == k.val + 1
    ramOut := m.ramOut.toNat
    cev := k.val == 0 && (machCevRec m).1
    record := (machCevRec m).2
    apply := k.val == 0 && (machApplyLate m).1
    late := k.val == 0 && (machApplyLate m).2 }

/-- The machine's next debug block. -/
def machDbgNext (m : Machine.State) : Machine.DbgSt :=
  Machine.dbgNext m (machHw m) (machCw m) (machCevRec m).1 (machApplyLate m).1 m.dbg.frz

/-- **The stream projection.**  The machine's stream `k` after `runStep` is
`streamNext` at the cycle's mode and the cycle's input record. -/
theorem runStep_streams (m : Machine.State) (pin : Machine.PinIn) (k : Fin 2) :
    (Machine.runStep m pin).1.streams[k] =
      Machine.streamNext (Machine.cfgView m.cfg).streams[k] (machMode m k)
        m.streams[k] (machStreamIn m k) m.dbg.frz := by
  simp only [Machine.runStep, machMode, machStreamIn, machWs, machAllMoves, machCbs, machLcs,
    machServed, machSreq, machCevRec, machApplyLate, machHw, vecGet_ofFn, Vector.getElem_ofFn,
    Fin.eta]
  rfl

/-- **The debug projection.**  The machine's debug block after `runStep` is
`dbgNext` at the cycle's host write, drained core write, capture event, replay
`apply` and freeze sample. -/
theorem runStep_dbg (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.dbg = machDbgNext m := by
  simp only [Machine.runStep, machDbgNext, machHw, machCw, machWs, machAllMoves, machCbs,
    machLcs, machServed, machSreq, machCevRec, machApplyLate, machMode, vecGet_ofFn,
    Vector.getElem_ofFn, Fin.eta]
  rfl

/-- The cut's stream `k` after one active cycle. -/
theorem activeStep_streams (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    (activeStep s pin).streams[k] =
      Stream.step (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) := by
  simp only [activeStep, streamAt, vecGet_ofFn, Vector.getElem_ofFn, Fin.eta]

/-- The cut's stream 0 after one active cycle (the `streamAt` form used by the
next-state `BufRel`). -/
theorem activeStep_streamAt_zero (s : State) (pin : Machine.PinIn) :
    streamAt (activeStep s pin) (↑(0 : Fin 2)) =
      Stream.step (↑(0 : Fin 2) == 0) (streamAt s (↑(0 : Fin 2)))
        (streamIn s pin (↑(0 : Fin 2))) := by
  rw [show (↑(0 : Fin 2) : Nat) = 0 from rfl]
  simp only [activeStep, streamAt, vecGet_ofFn, Vector.getElem_ofFn, Fin.eta]
  rfl

/-- The cut's stream 1 after one active cycle. -/
theorem activeStep_streamAt_one (s : State) (pin : Machine.PinIn) :
    streamAt (activeStep s pin) (↑(1 : Fin 2)) =
      Stream.step (↑(1 : Fin 2) == 0) (streamAt s (↑(1 : Fin 2)))
        (streamIn s pin (↑(1 : Fin 2))) := by
  rw [show (↑(1 : Fin 2) : Nat) = 1 from rfl]
  simp only [activeStep, streamAt, vecGet_ofFn, Vector.getElem_ofFn, Fin.eta]
  rfl

/-- The cut's debug control block after one active cycle. -/
theorem activeStep_dbgCtrl (s : State) (pin : Machine.PinIn) :
    (activeStep s pin).dbgCtrl = Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin) := by
  simp only [activeStep]

/-- The cut's debug digest block after one active cycle. -/
theorem activeStep_dbgDigest (s : State) (pin : Machine.PinIn) :
    (activeStep s pin).dbgDigest = Debug.Digest.step s.dbgDigest (dbgDigestIn s pin) := by
  simp only [activeStep]

/-- The cut's freeze register after one active cycle. -/
theorem activeStep_freeze (s : State) (pin : Machine.PinIn) :
    (activeStep s pin).freeze = CoreCtl.freezeStep s.freeze (freezeIn s pin) := by
  simp only [activeStep]

/-! ## The cut's stream configuration and mode -/

/-- `cfgOf` of the cut's stream input is the machine's decoded stream
configuration (`activeStep` builds every field from `cfgView s.cont.cfg`, and the
machine's decode masks `START` to 11 and `LEN`/`MARK` to 12 bits). -/
theorem cfgOf_streamIn (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    Bridge.StreamB.cfgOf (streamIn s pin k.val) =
      (Machine.cfgView s.cont.cfg).streams[k] := by
  have h11 : (0 : Nat) < 2 ^ 11 := by decide
  have h12 : (0 : Nat) < 2 ^ 12 := by decide
  match k with
  | ⟨0, _⟩ =>
    simp [Bridge.StreamB.cfgOf, streamIn, Machine.cfgView, Machine.Config.stream,
      Machine.Util.nbits, Machine.Util.cfgLE, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact ⟨Nat.mod_lt _ h11, Nat.mod_lt _ h12, Nat.mod_lt _ h12⟩
  | ⟨1, _⟩ =>
    simp [Bridge.StreamB.cfgOf, streamIn, Machine.cfgView, Machine.Config.stream,
      Machine.Util.nbits, Machine.Util.cfgLE, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact ⟨Nat.mod_lt _ h11, Nat.mod_lt _ h12, Nat.mod_lt _ h12⟩

/-! ## `DbgRel` projections -/

theorem DbgRel.freeze_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.freeze = s.freeze.freeze := by
  obtain ⟨h1, _, _, _, _, _, _, _, _, _, _⟩ := h; exact h1

theorem DbgRel.frz_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.frz = s.freeze.frz := by
  obtain ⟨_, h2, _, _, _, _, _, _, _, _, _⟩ := h; exact h2

theorem DbgRel.frzd_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.frzd = s.freeze.frzd := by
  obtain ⟨_, _, h3, _, _, _, _, _, _, _, _⟩ := h; exact h3

theorem DbgRel.men_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.men = s.dbgDigest.men := by
  obtain ⟨_, _, _, h4, _, _, _, _, _, _, _⟩ := h; exact h4

theorem DbgRel.misr_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.misr = s.dbgDigest.misr := by
  obtain ⟨_, _, _, _, h5, _, _, _, _, _, _⟩ := h; exact h5

theorem DbgRel.cen_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.cen = s.dbgCtrl.cen := by
  obtain ⟨_, _, _, _, _, h6, _, _, _, _, _⟩ := h; exact h6

theorem DbgRel.rpl_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.rpl = s.dbgCtrl.replay := by
  obtain ⟨_, _, _, _, _, _, h7, _, _, _, _⟩ := h; exact h7

theorem DbgRel.emask_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.emask = s.dbgCtrl.emask := by
  obtain ⟨_, _, _, _, _, _, _, h8, _, _, _⟩ := h; exact h8

theorem DbgRel.dc_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.dc = s.dbgCtrl.dc := by
  obtain ⟨_, _, _, _, _, _, _, _, h9, _, _⟩ := h; exact h9

theorem DbgRel.rlv_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.rlv = s.dbgCtrl.rlv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := h; exact h10

theorem DbgRel.rlvp_eq {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.rlvp = s.dbgCtrl.rlvPrev := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11⟩ := h; exact h11

/-- **The relational frozen stream step.**  In a frozen cycle with no rewind, no
landing and no move input, the machine's `streamNext` holds every register except
`STARVED` (which follows the host clear), and the cut's frozen step holds the
same registers, so `AbsRelB` is preserved.  This is the relational form the
frozen cycle needs; `Bridge.StreamB.abs_step_frozen` states exact state equality
against `abs s`, which is not available for a related machine state.  The
frozen cycle with a host rewind (§12.3) is `frozen_rel_rewind` below. -/
theorem frozen_rel (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg) (mode : Nat)
    (h : Bridge.StreamB.AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false) (hfl : i.flush = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    Bridge.StreamB.AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c mode m (Bridge.StreamB.absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hlandB : (m.ld && (s.ld && !i.frzd)) = false := by
    by_cases hs : s.ld = true
    · have hz : i.frzd = true := hland hs
      simp [hs, hz]
    · simp [hs]
  have hmach : Machine.streamNext c mode m (Bridge.StreamB.absIn cap s i) true =
      { m with starved := m.starved && !i.clrStarved } := by
    have hrewB : (Machine.Util.nbit (Bridge.StreamB.ctlVal i) 0 ||
        Machine.Util.nbit (Bridge.StreamB.clrVal i) 0) = false := by
      rw [Bridge.StreamB.nbit_ctl0, Bridge.StreamB.nbit_clr0, hrew]
      rfl
    simp only [Machine.streamNext, Bridge.StreamB.absIn, Option.getD_some, hrewB, hrew,
      hlandB, hfrz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.and_self,
      Bridge.StreamB.nbit_clr7, Bool.or_false]
  rw [hmach]
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hz0 : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · have hz : i.frzd = true := hland hl
      simp only [hl, hz, Bool.not_true, Bool.and_false, Bool.true_and]
    · have hlf : s.ld = false := by simpa using hl
      simp [hlf]
  have hwb : (Stream.step cap s i).wb = s.wb := by
    have htx : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
      simp [Bool.and_assoc, hz0]
    have hcen : (Stream.cen cap i && Stream.push cap s i && !(s.pv && !i.gnt) && !i.frz) =
        false := by simp [hfrz]
    simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, if_false, if_true, htx, hcen,
      hfrz, Bool.false_eq_true, Bool.and_false, Bool.and_true]
  have hwv : (Stream.step cap s i).wv = s.wv := hfrz0.2.2.2.2.2.2.2.1
  have hrq' : (Stream.step cap s i).rq = s.rq := hfrz0.2.2.2.2.2.2.2.2
  have hld' : (Stream.step cap s i).ld = s.ld := by
    simp only [Stream.step, Stream.ldNext, hreset, Bool.not_true, if_false, if_true, hrew, hfrz,
      Bool.false_eq_true]
  have hnb : (Stream.step cap s i).nb = s.nb := by
    have h1 : (Stream.rpl cap i && s.ld && !i.frzd && i.frz) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h2 : (Stream.rpl cap i && s.ld && !i.frzd && Stream.occupied s i) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    simp only [Stream.step, Stream.nbNext, h3, Bool.false_eq_true, if_false, if_true, h1, h2,
      Bool.and_false]
  have hnv : (Stream.step cap s i).nv = s.nv := by
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    have h4 : (cap && i.rewind) = false := by simp [hrew]
    simp only [Stream.step, Stream.nvNext, h3, Bool.false_eq_true, if_false, if_true, h4, hfrz]
  have hst : (Stream.step cap s i).starved = (s.starved && !i.clrStarved) := by
    have h1 : Stream.starveTx cap s i = false := by
      simp [Stream.starveTx, Stream.advT, hadv]
    have h2 : Stream.starveRx cap s i = false := by
      simp [Stream.starveRx, Stream.push, Stream.done, Stream.bitin, Stream.fl, hrx, hfl, hpush,
        hfrz]
    have h3 : (Stream.rpl cap i && i.replayLate) = false := by rw [hlate]; simp
    simp only [Stream.step, Stream.starvedNext, hreset, Bool.not_true, if_false, if_true,
      Stream.starveEvent, h1, h2, h3, Bool.false_or, Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfrz0.1, hpos]
  · rw [hfrz0.2.1, hbidx]
  · rw [hfrz0.2.2.1, hba]
  · rw [hfrz0.2.2.2.1, hcur]
  · rw [hfrz0.2.2.2.2.1, hcv]
  · rw [hrq', hrq]
  · rw [hld', hld]
  · rw [hfrz0.2.2.2.2.2.1, hpend]
  · rw [hfrz0.2.2.2.2.2.2.1, hpv]
  · rw [hst]
    rw [hstar]
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hwv]; exact hbuf.wv_eq
    · rw [hnv]; exact hbuf.nv_eq ‹cap = true›
    · intro hh
      rw [hwb]
      exact hbuf.wb_of_wv (by rw [← hwv]; exact hh)
    · intro hh
      rw [hnb]
      exact hbuf.nb_of_nv ‹cap = true› (by rw [← hnv]; exact hh)
  · intro hc
    obtain ⟨hwb0, hwv0, hnb0⟩ := hbuf.2.1 hc
    exact ⟨by rw [hwb]; exact hwb0, by rw [hwv]; exact hwv0, by rw [hnb]; exact hnb0⟩
  · intro hc
    exact hbuf.2.2 ⟨by rw [← hrq']; exact hc.1, by rw [← hld']; exact hc.2⟩

/-- **The relational frozen step with a host rewind.**  SPEC_V2 §12.3 keeps the
stream `CTL` rewind (and the `STARVED` clear) running while frozen; the bridge
proves that cycle too: `Bridge.StreamB.abs_step_frozen_rewind` for the state
equality, here relationally.  The cut's rewind override is
`Stream.rewind_overrides` (§6.3: `POS' = 0`, `BIDX' = 0`, `BA' = START`,
`CUR' = 0`, `CV' = WV' = RQ' = LD' = PV' = 0`), `PEND` and `WB`/`NB` hold, and
`STARVED' = STARVED && !CTL[7]` on both sides because a frozen cycle raises no
starve event.  `hstart` is the only configuration field the rewind reads
(`BA'`); the caller instantiates `c` with the bridge's `cfgOf`. -/
theorem frozen_rel_rewind (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg) (mode : Nat)
    (h : Bridge.StreamB.AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hstart : Machine.Util.bv 11 c.start = i.cfgStart)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false) (hfl : i.flush = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    Bridge.StreamB.AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c mode m (Bridge.StreamB.absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hbaq, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hlandB : (m.ld && (s.ld && !i.frzd)) = false := by
    by_cases hs : s.ld = true
    · have hz : i.frzd = true := hland hs
      simp [hs, hz]
    · simp [hs]
  have hz0 : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · have hz : i.frzd = true := hland hl
      simp only [hl, hz, Bool.not_true, Bool.and_false, Bool.true_and]
    · have hlf : s.ld = false := by simpa using hl
      simp [hlf]
  have hmach : Machine.streamNext c mode m (Bridge.StreamB.absIn cap s i) true =
      { m with
        pos := 0,
        bidx := 0,
        ba := Machine.Util.bv 11 c.start,
        cur := 0,
        cv := false,
        wv := false,
        rq := false,
        ld := false,
        pv := false,
        starved := m.starved && !i.clrStarved,
        nv := false } := by
    have hrewT : (Machine.Util.nbit (Bridge.StreamB.ctlVal i) 0 ||
        Machine.Util.nbit (Bridge.StreamB.clrVal i) 0) = true := by
      rw [Bridge.StreamB.nbit_ctl0, Bridge.StreamB.nbit_clr0, hrew]
      rfl
    simp only [Machine.streamNext, Bridge.StreamB.absIn, Option.getD_some, hrewT, hlandB,
      hfrz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.and_self,
      Bridge.StreamB.nbit_clr7, Bool.or_false]
  rw [hmach]
  have hwb : (Stream.step cap s i).wb = s.wb := by
    have htx : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
      simp [Bool.and_assoc, hz0]
    have hcen : (Stream.cen cap i && Stream.push cap s i && !(s.pv && !i.gnt) && !i.frz) =
        false := by simp [hfrz]
    simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, if_false, if_true, htx, hcen,
      hfrz, Bool.false_eq_true, Bool.and_false, Bool.and_true]
  have hnb : (Stream.step cap s i).nb = s.nb := by
    have h1 : (Stream.rpl cap i && s.ld && !i.frzd && i.frz) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h2 : (Stream.rpl cap i && s.ld && !i.frzd && Stream.occupied s i) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    simp only [Stream.step, Stream.nbNext, h3, Bool.false_eq_true, if_false, if_true, h1, h2,
      Bool.and_false]
  have hnv : cap = true → (Stream.step cap s i).nv = false := by
    intro hc
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    have h4 : (cap && i.rewind) = true := by simp [hc, hrew]
    simp only [Stream.step, Stream.nvNext, h3, Bool.false_eq_true, if_false, if_true, h4]
  have hpend' : (Stream.step cap s i).pend = s.pend := by
    simp [Stream.step, Stream.pendNext, hreset, hfrz]
  have hst : (Stream.step cap s i).starved = (s.starved && !i.clrStarved) := by
    have h1 : Stream.starveTx cap s i = false := by
      simp [Stream.starveTx, Stream.advT, hadv]
    have h2 : Stream.starveRx cap s i = false := by
      simp [Stream.starveRx, Stream.push, Stream.done, Stream.bitin, Stream.fl, hrx, hfl, hpush,
        hfrz]
    have h3 : (Stream.rpl cap i && i.replayLate) = false := by rw [hlate]; simp
    simp only [Stream.step, Stream.starvedNext, hreset, Bool.not_true, if_false, if_true,
      Stream.starveEvent, h1, h2, h3, Bool.false_or, Bool.false_eq_true]
  obtain ⟨hwpos, hwbidx, hwba, hwcur, hwcv, hwwv, hwrq, hwld, hwpv⟩ :=
    Stream.rewind_overrides cap s i hrew hreset
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hwpos
  · exact hwbidx
  · exact hwba.trans hstart.symm
  · exact hwcur
  · exact hwcv
  · exact hwrq
  · exact hwld
  · exact hpend'.trans hpend
  · exact hwpv
  · rw [hst, hstar]
  · refine ⟨?_, ?_, ?_⟩
    · intro _
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hwwv
      · exact hnv ‹cap = true›
      · intro hh
        rw [hwwv] at hh
        exact Bool.noConfusion hh
      · intro hh
        rw [hnv ‹cap = true›] at hh
        exact Bool.noConfusion hh
    · intro hc
      obtain ⟨hwb0, _, hnb0⟩ := hbuf.2.1 hc
      exact ⟨hwb.trans hwb0, hwwv, hnb.trans hnb0⟩
    · intro hc
      rw [hwrq] at hc
      exact Bool.noConfusion hc.1

/-! ## The bridge's `absIn` at stream `k` -/

/-- The cut's stream input with the machine's per-stream capture/replay gating
(`runStep` inserts `cev`/`apply`/`late` into `S0` only). -/
def gatedIn (k : Fin 2) (i : Stream.Input) : Stream.Input :=
  { i with capPush := ((k.val == 0) && i.capPush), replayApply := ((k.val == 0) && i.replayApply), replayLate := ((k.val == 0) && i.replayLate) }

/-- The bridge's input record at stream `k`. -/
def absInOf (k : Fin 2) (s : Stream.State) (i : Stream.Input) : Machine.StreamIn :=
  Bridge.StreamB.absIn (k.val == 0) s (gatedIn k i)

theorem gatedIn_zero (i : Stream.Input) : gatedIn 0 i = i := rfl

theorem absIn_gatedIn_one (cap : Bool) (s : Stream.State) (i : Stream.Input) :
    Bridge.StreamB.absIn cap s (gatedIn 1 i) =
      Bridge.StreamB.absIn cap s
        { i with capPush := false, replayApply := false, replayLate := false } := by
  simp [Bridge.StreamB.absIn, gatedIn, Bridge.StreamB.ctlVal, Bridge.StreamB.clrVal]

/-- With `CAP = 0` the machine's stream step does not read the capture/replay
inputs: `modeOf false i` is `0` or `1`, and both branches of `streamAuto` ignore
`cev`, `apply` and `late`. -/
theorem streamNext_gate_irrel (s : Stream.State) (i : Stream.Input)
    (c : Machine.StreamCfg) (m : Machine.StreamSt) (frz : Bool) (kg : Bool)
    (hkg : kg = false) :
    Machine.streamNext c (Bridge.StreamB.modeOf kg i) m
        (Bridge.StreamB.absIn kg s (gatedIn 1 i)) frz
      = Machine.streamNext c (Bridge.StreamB.modeOf kg i) m
          (Bridge.StreamB.absIn kg s i) frz := by
  subst hkg
  rw [absIn_gatedIn_one]
  rcases Bridge.StreamB.mode_cases false i with
    ⟨h3, hrpl, _, _, _⟩ | ⟨h2, hcen, _, _, _⟩ | ⟨h1, _, _, _, _⟩ | ⟨h0, _, _, _, _⟩
  · simp [Stream.rpl] at hrpl
  · simp [Stream.cen] at hcen
  · rw [h1]
    simp [Machine.streamNext, Machine.Util.streamAuto, Bridge.StreamB.absIn,
      Bridge.StreamB.ctlVal, Bridge.StreamB.clrVal]
  · rw [h0]
    simp [Machine.streamNext, Machine.Util.streamAuto, Bridge.StreamB.absIn,
      Bridge.StreamB.ctlVal, Bridge.StreamB.clrVal]

/-- The `BufRel` part of `AbsRelB`. -/
theorem AbsRelB.bufRel {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : Bridge.StreamB.AbsRelB cap s m) : Bridge.StreamB.BufRel cap s m := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hb⟩ := h
  exact hb

/-- **The machine's `StreamIn` against the bridge's `absInOf`, in the quantities
`Machine.streamNext` reads.**  `streamNext_congr` uses exactly these thirteen
facts; everything else in `StreamIn` (the full `Sk.RX` byte, the raw
`Sk.CTL`/host `CTL` bytes) is only read through them. -/
structure StreamInputAgree (m : Machine.State) (st : Stream.State) (i : Stream.Input)
    (k : Fin 2) : Prop where
  /-- `Sk.ADV` is exact. -/
  adv : (machStreamIn m k).adv = (absInOf k st i).adv
  /-- `Sk.RX`'s presence. -/
  rxSome : (machStreamIn m k).rx.isSome = (absInOf k st i).rx.isSome
  /-- `Sk.RX`'s low bit (the asserted value is 0 or 1). -/
  rxBit : Machine.Util.nbit ((machStreamIn m k).rx.getD 0) 0 =
    Machine.Util.nbit ((absInOf k st i).rx.getD 0) 0
  /-- The combined `rewind` bit. -/
  rewind : (Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 0 ||
      Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 0) =
    (Machine.Util.nbit ((absInOf k st i).ctlMove.getD 0) 0 ||
      Machine.Util.nbit ((absInOf k st i).hCtl.getD 0) 0)
  /-- The combined `flush` bit; only read unfrozen (§12.3). -/
  flush : m.dbg.frz = false →
    (Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
        Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1) =
      (Machine.Util.nbit ((absInOf k st i).ctlMove.getD 0) 1 ||
        Machine.Util.nbit ((absInOf k st i).hCtl.getD 0) 1)
  /-- The combined `STARVED` clear bit. -/
  clr : Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 7 =
    Machine.Util.nbit ((absInOf k st i).hCtl.getD 0) 7
  served : (machStreamIn m k).served = (absInOf k st i).served
  /-- The landing is only read while the stream's own `LD` is up. -/
  landNow : m.streams[k].ld = true →
    (machStreamIn m k).landNow = (absInOf k st i).landNow
  ramOut : (machStreamIn m k).ramOut = (absInOf k st i).ramOut
  cev : (machStreamIn m k).cev = (absInOf k st i).cev
  record : (machStreamIn m k).record = (absInOf k st i).record
  apply : (machStreamIn m k).apply = (absInOf k st i).apply
  late : (machStreamIn m k).late = (absInOf k st i).late

/-! ## The stream wiring hypothesis

The per-cycle stream input is built from four independent wiring facts, none of
which an existing bridge states (each is a cross-component decode):

* `mode` — the machine's `streamMode` is the bridge's `modeOf` (`streamMode_zero`
  with `ChipRel.dbg` for the `CEN`/`RPL` bits);
* `input` — the machine's `StreamIn` record is the bridge's `absIn`: the move
  picks (`Sk.ADV`/`Sk.RX`/`Sk.CTL`), the arbiter's `served`, the landing
  (`ramOwner` against `LD && !FRZD`), the capture record and the replay
  `apply`/`late`;
* `bufrel` — the replay-buffer relation at the next state (the three recorded
  corners of `BRIDGE_UNITS_STREAM_NOTES.md`; now *proved* from `StreamRelX` +
  `streamShapeInv`, `Assembly.lean`'s `streamBufrel_of`).

The two former fields are gone: `hostctl` (no stream flush acts in a frozen
cycle, §12.3) and `landing` (`LD → FRZD` is **false**, `streamWire_landing_false`
below).  `premise_streams` now closes the frozen cycle with B1's
`frozen_rel_landing_flush`/`_rewind_flush`, which *cover* the landing exception:
they need only the mode branch of `LD` (`hldmode`, from `ldModeInv`) and the
replay shape `ShapeOK` (`hshp`, from `streamShapeInv`), so the flush side
condition is gone too. -/
structure StreamWire (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  /-- The machine's per-stream mode is the bridge's `modeOf`. -/
  mode : ∀ k : Fin 2, machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)
  /-- The machine's `StreamIn` record against the bridge's `absInOf`, in exactly
  the quantities `Machine.streamNext` reads (`streamNext_congr`'s hypotheses):
  the `Sk.ADV` move, the `Sk.RX` *presence and low bit*, the three combined
  `Sk.CTL` bits, and the exact arbiter/landing/capture/replay fields. -/
  input : ∀ k : Fin 2, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k
  /-- `BufRel` at the next state (the three recorded replay-buffer corners). -/
  bufrel : ∀ k : Fin 2, Bridge.StreamB.BufRel (k.val == 0)
    (streamAt (activeStep s pin) k.val) (Machine.step m pin).streams[k]

/-! ## `StreamWire.landing` is false: the frozen-landing corner

`StreamWire.landing` says `LD = true → FRZD = true`, i.e. no stream has a read
outstanding on a cycle whose `FRZD` is set ("`abs_step_frozen`'s landing
exception does not fire").  It is **false**: `Stream.ldNext` *holds* `LD` in a
frozen cycle (`if i.frz then s.ld`), and `FRZD` is the *previous* cycle's `FRZ`
(`CoreCtl.freezeStep`: `frzd' = s.frz`).  So a host freeze one cycle after a
served read gives `LD = 1, FRZD = 0` — exactly the corner
`DISCHARGE_STREAMDBG_NOTES.md` §3.1 records ("a host freeze one cycle after a
served read is reachable and *both* readings land there").

The witness is constructive at the component level: two `Stream.step` cycles take
a transmit stream from `Stream.resetState` to `LD = 1` (a request, then a served
grant), a third (frozen) cycle holds it, and `CoreCtl.freezeStep` from
`frz = false` on a host `DBG.FREEZE` write (`data = 1`) gives `FRZ = 1,
FRZD = 0` in that same cycle; the product state assembled from them has `LD = 1`
and `FRZD = 0`.

Consequence: the frozen-cycle bridge (`frozen_rel`/`abs_step_frozen`) cannot be
applied on that cycle.  The corner is *benign* (both readings store the RAM word
in `WB`, see the notes) but the bridge must cover `LD ∧ !FRZD`; it is not a cut
wiring bug.  B1's `frozen_rel_landing_flush` now does cover it, so the field was
**removed** from `StreamWire` (round 10) and `premise_streams` uses that bridge. -/

/-- The transmit-mode stream input of the witness: `cfgLen = 1` so the stream is
not at `END`; no move, capture or replay input. -/
def szIn (gnt frz : Bool) : Stream.Input where
  resetN := true
  frz := frz
  frzd := false
  capEn := false
  capPush := false
  capRec := 0
  replayEn := false
  replayApply := false
  replayLate := false
  cfgMode := false
  cfgMsb := false
  cfgStart := 0
  cfgLen := 1
  cfgMark := 0
  adv := false
  rxWe := false
  rxBit := false
  rewind := false
  flush := false
  clrStarved := false
  gnt := gnt
  rdata := 0

theorem sz_rq : (Stream.step true Stream.resetState (szIn false false)).rq = true := by decide

theorem sz_ld :
    (Stream.step true (Stream.step true Stream.resetState (szIn false false))
      (szIn true false)).ld = true := by decide

theorem sz_ld_frz :
    (Stream.step true
      (Stream.step true (Stream.step true Stream.resetState (szIn false false))
        (szIn true false)) (szIn false true)).ld = true := by decide

/-- The freeze registers after a host `DBG.FREEZE` write (`data = 1`, step bit 0)
from the reset pair: `FRZ = 1` and `FRZD = 0` in the same cycle. -/
theorem sz_freeze :
    CoreCtl.freezeStep ⟨false, false, false⟩ { resetN := true, dbgWrite := true, data := 1 } =
      ⟨true, true, false⟩ := by decide

/-- Two streams, the first one the witness state. -/
def szVec (st : Stream.State) : Vector Stream.State 2 :=
  Vector.ofFn fun k : Fin 2 => if k.val = 0 then st else Stream.resetState

/-- The product state of the corner: stream 0 in the witness state, the freeze
registers frozen with `FRZD` still clear. -/
def szState (st : Stream.State) (cont : Contents) : State :=
  { resetState cont with streams := szVec st, freeze := ⟨true, true, false⟩ }

theorem szState_ld (st : Stream.State) (cont : Contents) (h : st.ld = true) :
    (streamAt (szState st cont) 0).ld = true := by
  show ((szVec st)[0]).ld = true
  simp [szVec, h]

/-- **`StreamWire.landing` is not an invariant**: there is a product state with
a read outstanding and `FRZD` clear (the frozen-landing corner). -/
theorem streamWire_landing_false (cont : Contents) :
    ∃ (s : State) (pin : Machine.PinIn),
      (streamAt s 0).ld = true ∧ (streamIn s pin 0).frzd = false :=
  ⟨szState _ cont, default, szState_ld _ cont sz_ld_frz, rfl⟩

/-- **`Machine.streamNext` reads only what the projected input agreement
provides.**  Two `StreamIn` records that agree on `adv`, the `rx` *presence* and
low bit, the three combined control bits (`rewind`/`flush`/`clrStarved`), and the
exact `served`/`landNow` (only while `LD`)/`ramOut`/`cev`/`record`/`apply`/`late`
give the same next stream state.  `flush` is only read unfrozen (`§12.3`), hence
the guard. -/
theorem streamNext_congr (c : Machine.StreamCfg) (mode : Nat) (st : Machine.StreamSt)
    (i1 i2 : Machine.StreamIn) (frz : Bool)
    (hadv : i1.adv = i2.adv)
    (hrxSome : i1.rx.isSome = i2.rx.isSome)
    (hrxBit : Machine.Util.nbit (i1.rx.getD 0) 0 = Machine.Util.nbit (i2.rx.getD 0) 0)
    (hserved : i1.served = i2.served)
    (hland : st.ld = true → i1.landNow = i2.landNow)
    (hram : i1.ramOut = i2.ramOut)
    (hcev : i1.cev = i2.cev) (hrec : i1.record = i2.record)
    (happly : i1.apply = i2.apply) (hlate : i1.late = i2.late)
    (hrew : (Machine.Util.nbit (i1.ctlMove.getD 0) 0 || Machine.Util.nbit (i1.hCtl.getD 0) 0) =
      (Machine.Util.nbit (i2.ctlMove.getD 0) 0 || Machine.Util.nbit (i2.hCtl.getD 0) 0))
    (hflush : frz = false →
      (Machine.Util.nbit (i1.ctlMove.getD 0) 1 || Machine.Util.nbit (i1.hCtl.getD 0) 1) =
      (Machine.Util.nbit (i2.ctlMove.getD 0) 1 || Machine.Util.nbit (i2.hCtl.getD 0) 1))
    (hclr : Machine.Util.nbit (i1.hCtl.getD 0) 7 = Machine.Util.nbit (i2.hCtl.getD 0) 7) :
    Machine.streamNext c mode st i1 frz = Machine.streamNext c mode st i2 frz := by
  by_cases hld : st.ld = true
  · have hland' := hland hld
    by_cases hf : frz = true
    · subst hf
      unfold Machine.streamNext
      simp only [hld, Bool.true_and, hland', hram, hrew, hclr]
      simp
    · have hf' : frz = false := by simpa using hf
      subst hf'
      have hfl := hflush rfl
      unfold Machine.streamNext Machine.Util.streamAuto
      simp only [hld, Bool.true_and, hland', hram, hadv, hrxSome, hrxBit, hserved, hcev, hrec,
        happly, hlate, hrew, hclr, hfl]
      simp [hfl]
  · have hld' : st.ld = false := by simpa using hld
    by_cases hf : frz = true
    · subst hf
      unfold Machine.streamNext
      simp only [hld', Bool.false_and, Bool.false_eq_true, if_false, hram, hrew, hclr]
      simp
    · have hf' : frz = false := by simpa using hf
      subst hf'
      have hfl := hflush rfl
      unfold Machine.streamNext Machine.Util.streamAuto
      simp only [hld', Bool.false_and, Bool.false_eq_true, if_false, hram, hadv, hrxSome, hrxBit,
        hserved, hcev, hrec, happly, hlate, hrew, hclr, hfl]
      simp [hfl]

/-- The machine's next stream `k` at the bridge's configuration, mode and input
record (the post-step machine state is the `runStep` branch of `Machine.step` on
an active cycle).  `hin` is the projected input agreement of
`StreamInputAgree`; `streamNext_congr` replaces the machine's record by the
bridge's `absIn`, and `streamNext_gate_irrel` drops the `k = 0` capture/replay
gate for stream 1. -/
theorem streamsNext_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) (k : Fin 2)
    (hcfg : (Machine.cfgView m.cfg).streams[k] = Bridge.StreamB.cfgOf (streamIn s pin k.val))
    (hmode : machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hin : StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k) :
    (Machine.step m pin).streams[k] =
      Machine.streamNext (Bridge.StreamB.cfgOf (streamIn s pin k.val))
        (Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
        m.streams[k] (Bridge.StreamB.absIn (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val)) m.dbg.frz := by
  have hmr : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hstep : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hmr]
  rw [hstep, runStep_streams, hmode, hcfg]
  have hcongr := streamNext_congr (Bridge.StreamB.cfgOf (streamIn s pin k.val))
    (Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) m.streams[k]
    (machStreamIn m k) (absInOf k (streamAt s k.val) (streamIn s pin k.val)) m.dbg.frz
    hin.adv hin.rxSome hin.rxBit hin.served hin.landNow hin.ramOut hin.cev hin.record
    hin.apply hin.late hin.rewind hin.flush hin.clr
  rw [hcongr]
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, hlt⟩ =>
    exact streamNext_gate_irrel (streamAt s 1) (streamIn s pin 1)
      (Bridge.StreamB.cfgOf (streamIn s pin 1)) m.streams[1] m.dbg.frz
      (↑(⟨1, hlt⟩ : Fin 2) == 0) (by rfl)

/-- The `streams` premise at stream 0 (`CAP = 0` code `0 == 0`). -/
theorem streams_field_0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) (hw : StreamWire s m pin)
    (hldmode : ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
        Stream.rpl (k.val == 0) (streamIn s pin k.val) = true)
    (hshp : ∀ k : Fin 2, Bridge.StreamBuf.ShapeOK (streamAt s k.val)) :
    Bridge.StreamB.AbsRelB ((0 : Fin 2).val == 0) (streamAt (activeStep s pin) 0)
      (Machine.step m pin).streams[(0 : Fin 2)] := by
  have hcf : (Machine.cfgView m.cfg).streams[(0 : Fin 2)] =
      Bridge.StreamB.cfgOf (streamIn s pin 0) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin 0).symm
  have hnext := streamsNext_eq s m pin hrel hact (0 : Fin 2) hcf (hw.mode 0)
    (hw.input 0)
  have hrelk := hrel.streams (0 : Fin 2)
  change Bridge.StreamB.AbsRelB ((0 : Fin 2).val == 0)
    ((activeStep s pin).streams[(0 : Fin 2)]) (Machine.step m pin).streams[(0 : Fin 2)]
  rw [activeStep_streams]
  by_cases hf : s.freeze.frz = true
  · -- frozen: the relational frozen step, no replay-buffer hypothesis needed
    have hmf : m.dbg.frz = true := by rw [DbgRel.frz_eq hrel.dbg]; exact hf
    rw [hnext, hmf]
    have hmv : mvEn s pin = 0 := frozenNoMove s pin hf
    have hadv : (streamIn s pin 0).adv = false := by
      show strobe s pin (BitVec.ofNat 6 (47 + 0)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hrx : (streamIn s pin 0).rxWe = false := by
      show strobe s pin (BitVec.ofNat 6 (49 + 0)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hpush : (streamIn s pin 0).capPush = false := by
      show Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s)
        (fallVec s) s.dbgCtrl.emask = false
      simp [Debug.Ctrl.cev, hf]
    have hlate : (streamIn s pin 0).replayLate = false := by
      show Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb = false
      simp [Debug.Ctrl.late, hf]
    by_cases hrew : (streamIn s pin 0).rewind = true
    · exact Bridge.StreamBuf.frozen_rel_landing_rewind_flush ((0 : Fin 2).val == 0)
        (streamAt s 0) (streamIn s pin 0) m.streams[(0 : Fin 2)]
        (Bridge.StreamB.cfgOf (streamIn s pin 0)) hrelk hact hf hrew
        (Bridge.StreamB.cfgStart_bv (streamIn s pin 0)).symm
        (hldmode (0 : Fin 2)) hadv hrx hpush hlate
    · have hrew' : (streamIn s pin 0).rewind = false := by
        cases h : (streamIn s pin 0).rewind <;> simp_all
      exact Bridge.StreamBuf.frozen_rel_landing_flush ((0 : Fin 2).val == 0)
        (streamAt s 0) (streamIn s pin 0) m.streams[(0 : Fin 2)]
        (Bridge.StreamB.cfgOf (streamIn s pin 0)) hrelk hact hf hrew'
        (hldmode (0 : Fin 2)) (hshp (0 : Fin 2)) hadv hrx hpush hlate
  · have hf' : s.freeze.frz = false := by simpa using hf
    have hmf : m.dbg.frz = false := by rw [DbgRel.frz_eq hrel.dbg]; exact hf'
    rw [hnext, hmf]
    have hb := hw.bufrel (0 : Fin 2)
    rw [activeStep_streamAt_zero] at hb
    rw [hnext] at hb
    rw [hmf] at hb
    obtain ⟨hp, hb', hba, hc, hcv, hrq', hld', hpd, hpv', hst⟩ :=
      Bridge.StreamB.abs_step_unfrozen ((0 : Fin 2).val == 0) (streamAt s 0)
        (streamIn s pin 0) m.streams[(0 : Fin 2)] hact hf' hrelk
    exact ⟨hp, hb', hba, hc, hcv, hrq', hld', hpd, hpv', hst, hb⟩

/-- The `streams` premise at stream 1 (`CAP = 0` code `1 == 0`). -/
theorem streams_field_1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) (hw : StreamWire s m pin)
    (hldmode : ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
        Stream.rpl (k.val == 0) (streamIn s pin k.val) = true)
    (hshp : ∀ k : Fin 2, Bridge.StreamBuf.ShapeOK (streamAt s k.val)) :
    Bridge.StreamB.AbsRelB ((1 : Fin 2).val == 0) (streamAt (activeStep s pin) 1)
      (Machine.step m pin).streams[(1 : Fin 2)] := by
  have hcf : (Machine.cfgView m.cfg).streams[(1 : Fin 2)] =
      Bridge.StreamB.cfgOf (streamIn s pin 1) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin 1).symm
  have hnext := streamsNext_eq s m pin hrel hact (1 : Fin 2) hcf (hw.mode 1)
    (hw.input 1)
  have hrelk := hrel.streams (1 : Fin 2)
  change Bridge.StreamB.AbsRelB ((1 : Fin 2).val == 0)
    ((activeStep s pin).streams[(1 : Fin 2)]) (Machine.step m pin).streams[(1 : Fin 2)]
  rw [activeStep_streams]
  by_cases hf : s.freeze.frz = true
  · -- frozen: the relational frozen step, no replay-buffer hypothesis needed
    have hmf : m.dbg.frz = true := by rw [DbgRel.frz_eq hrel.dbg]; exact hf
    rw [hnext, hmf]
    have hmv : mvEn s pin = 0 := frozenNoMove s pin hf
    have hadv : (streamIn s pin 1).adv = false := by
      show strobe s pin (BitVec.ofNat 6 (47 + 1)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hrx : (streamIn s pin 1).rxWe = false := by
      show strobe s pin (BitVec.ofNat 6 (49 + 1)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hpush : (streamIn s pin 1).capPush = false := by
      show Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s)
        (fallVec s) s.dbgCtrl.emask = false
      simp [Debug.Ctrl.cev, hf]
    have hlate : (streamIn s pin 1).replayLate = false := by
      show Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb = false
      simp [Debug.Ctrl.late, hf]
    by_cases hrew : (streamIn s pin 1).rewind = true
    · exact Bridge.StreamBuf.frozen_rel_landing_rewind_flush ((1 : Fin 2).val == 0)
        (streamAt s 1) (streamIn s pin 1) m.streams[(1 : Fin 2)]
        (Bridge.StreamB.cfgOf (streamIn s pin 1)) hrelk hact hf hrew
        (Bridge.StreamB.cfgStart_bv (streamIn s pin 1)).symm
        (hldmode (1 : Fin 2)) hadv hrx hpush hlate
    · have hrew' : (streamIn s pin 1).rewind = false := by
        cases h : (streamIn s pin 1).rewind <;> simp_all
      exact Bridge.StreamBuf.frozen_rel_landing_flush ((1 : Fin 2).val == 0)
        (streamAt s 1) (streamIn s pin 1) m.streams[(1 : Fin 2)]
        (Bridge.StreamB.cfgOf (streamIn s pin 1)) hrelk hact hf hrew'
        (hldmode (1 : Fin 2)) (hshp (1 : Fin 2)) hadv hrx hpush hlate
  · have hf' : s.freeze.frz = false := by simpa using hf
    have hmf : m.dbg.frz = false := by rw [DbgRel.frz_eq hrel.dbg]; exact hf'
    rw [hnext, hmf]
    have hb := hw.bufrel (1 : Fin 2)
    rw [activeStep_streamAt_one] at hb
    rw [hnext] at hb
    rw [hmf] at hb
    obtain ⟨hp, hb', hba, hc, hcv, hrq', hld', hpd, hpv', hst⟩ :=
      Bridge.StreamB.abs_step_unfrozen ((1 : Fin 2).val == 0) (streamAt s 1)
        (streamIn s pin 1) m.streams[(1 : Fin 2)] hact hf' hrelk
    exact ⟨hp, hb', hba, hc, hcv, hrq', hld', hpd, hpv', hst, hb⟩

/-! ## The debug premise

The `dbg` field is `DbgRel (activeStep s pin) (Machine.step m pin).dbg`, i.e. the
eleven `Machine.DbgSt` registers.  Ten of them are `Bridge.Debug.dbg_step_bridge`
(the eight it states) plus the freeze bookkeeping (`FREEZE`/`FRZ`/`FRZD`), which
that bridge leaves out; `Metronome.CoreCtl`'s `freeze_next`/`frz_next`/`frzd_next`
are the cut's transition.

The bridge's interface facts are wiring, not `ChipRel` facts, so they are the
fields of `DbgWire`.  `dbg_step_bridge` itself is stated for `i.frz = false`, but
every field it composes is bridged here for **both** `FRZ` values: the register
transitions are the cut's `Debug.Ctrl.step`/`Debug.Digest` next-state functions
(the `rlvp` field is `if frz then rlvPrev else rlv`, matching the fixed machine
`dbgNext`), so `premise_dbg` covers frozen cycles too. -/

/-- The machine's `nbit` of a byte's value is the cut's `CoreCtl.bitAt`. -/
theorem nbit_core (x : BitVec 8) (i : Nat) :
    Machine.Util.nbit x.toNat i = CoreCtl.bitAt x i := by
  rw [show CoreCtl.bitAt x i = Debug.bitAt x i from rfl]
  exact (Bridge.Debug.bitAt_eq_nbit x i).symm

theorem ctrl_step_replay (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input) (h : i.resetN = true) :
    (Debug.Ctrl.step s i).replay = Debug.Ctrl.replayNext s i := by
  simp [Debug.Ctrl.step, h]

theorem ctrl_step_cen (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input) (h : i.resetN = true) :
    (Debug.Ctrl.step s i).cen = Debug.Ctrl.cenNext s i := by
  simp [Debug.Ctrl.step, h]

theorem ctrl_step_emask (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input) (h : i.resetN = true) :
    (Debug.Ctrl.step s i).emask = Debug.Ctrl.emaskNext s.emask i := by
  simp [Debug.Ctrl.step, h]

theorem ctrl_step_rlv (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input) (h : i.resetN = true) :
    (Debug.Ctrl.step s i).rlv = Debug.Ctrl.rlvNext s i := by
  simp [Debug.Ctrl.step, h]

theorem ctrl_step_rlvPrev (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input)
    (h : i.resetN = true) :
    (Debug.Ctrl.step s i).rlvPrev = Debug.Ctrl.rlvPrevNext s i := by
  simp [Debug.Ctrl.step, h]

theorem ctrl_step_dc (s : Debug.Ctrl.State) (i : Debug.Ctrl.Input) (h : i.resetN = true) :
    (Debug.Ctrl.step s i).dc = Debug.Ctrl.dcNext s i := by
  simp [Debug.Ctrl.step, h]

theorem digest_step_men (s : Debug.Digest.State) (i : Debug.Digest.Input)
    (h : i.resetN = true) :
    (Debug.Digest.step s i).men = Debug.Digest.menNext s.men i := by
  simp [Debug.Digest.step, h]

theorem digest_step_misr (s : Debug.Digest.State) (i : Debug.Digest.Input)
    (h : i.resetN = true) :
    (Debug.Digest.step s i).misr = Debug.Digest.misrNext s.men s.misr i := by
  simp [Debug.Digest.step, h]

theorem dbgNext_freeze (m : Machine.State) :
    (machDbgNext m).freeze =
      (match Machine.Util.hwByte (machHw m) "DBG" 0 "DBG" with
       | some v => Machine.Util.nbit v 0
       | none => m.dbg.freeze) := rfl

theorem dbgNext_frz (m : Machine.State) :
    (machDbgNext m).frz =
      (match Machine.Util.hwByte (machHw m) "DBG" 0 "DBG" with
       | some v => Machine.Util.nbit v 0 && !Machine.Util.nbit v 1
       | none => m.dbg.freeze) := rfl

theorem dbgNext_frzd (m : Machine.State) : (machDbgNext m).frzd = m.dbg.frz := rfl

theorem machDbgNext_eq (m : Machine.State) :
    machDbgNext m = Machine.dbgNext m (machHw m) (machCw m) (machCevRec m).1
      (machApplyLate m).1 m.dbg.frz := rfl

/-- The debug wiring: the `dbg_step_bridge` interface facts (host/`DBG` window
byte decode, drain byte exclusivity, the first replay slot and the capture/replay
comparisons).  No `FRZ` hypothesis: the frozen cycle is bridged field by field. -/
structure DbgWire (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  /-- The host `DBG` byte (`FREEZE`/`FRZ`/`FRZD` write). -/  hdbg : Machine.Util.hwByte (machHw m) "DBG" 0 "DBG" =
    (if (freezeIn s pin).dbgWrite then some (freezeIn s pin).data.toNat else none)
  /-- The host `MCTL` byte. -/
  hmctl : Machine.Util.hwByte (machHw m) "DBG" 0 "MCTL" =
    (if (dbgDigestIn s pin).dWrMctl then some (dbgDigestIn s pin).hWd.toNat else none)
  /-- The host-then-drain `ECTL` byte. -/
  hectl : Bridge.Debug.pickByte (machHw m) (machCw m) "ECTL" =
    (Bridge.Debug.Port.mk (dbgCtrlIn s pin).dWrEctl (dbgCtrlIn s pin).hEctl
      (dbgCtrlIn s pin).hWd (dbgCtrlIn s pin).cwData).ok
  /-- The machine's `EMASK` register after the step is the cut's.  This is W6's
  `DbgMapWire.dbgEmaskValue_of`; it replaces the six per-port `EMASK`/`RLV` host
  and drain byte leaves (the fixed `Wire.lean` makes `hEm0`/`hRlv0` byte-0
  strobes, `project.v` 662/664). -/
  dbgEmaskValue : (machDbgNext m).emask =
    (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask
  /-- The machine's `RLV` register after the step is the cut's (W6's
  `DbgMapWire.dbgRlvValue_of`, under the `hwb`/`happly` fields). -/
  dbgRlvValue : (machDbgNext m).rlv =
    (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv
  hword : (dbgCtrlIn s pin).replayWord = (streamAt s 0).wb
  /-- The replay `apply` comparison. -/
  happly : (machApplyLate m).1 =
    Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
      (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
      (dbgCtrlIn s pin).replayWord
  /-- The capture edge event. -/
  hcev : (machCevRec m).1 =
    Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay (dbgCtrlIn s pin).frz
      (dbgCtrlIn s pin).rise (dbgCtrlIn s pin).fall s.dbgCtrl.emask

/-- **The `dbg` premise**: the eleven `Machine.DbgSt` registers after one active
cycle, **frozen or not** (the frozen `RLVP` holds on both sides: `if frz then
rlvPrev else rlv`). -/
theorem premise_dbg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hw : DbgWire s m pin) :
    DbgRel (activeStep s pin) (Machine.step m pin).dbg := by
  have hmr : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hstep : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hmr]
  have hdi : m.dbg.frz = (dbgDigestIn s pin).frz := by
    rw [DbgRel.frz_eq hrel.dbg]; rfl
  have hdo : (dbgDigestIn s pin).oOut = m.out := by rw [hrel.out]; rfl
  have hde : (dbgDigestIn s pin).oEe = m.oen := by rw [hrel.oen]; rfl
  have h12 : (machDbgNext m).cen = Debug.Ctrl.cenNext s.dbgCtrl (dbgCtrlIn s pin) ∧
      (machDbgNext m).rpl = Debug.Ctrl.replayNext s.dbgCtrl (dbgCtrlIn s pin) := by
    rw [machDbgNext_eq]
    exact Bridge.Debug.ectl_bridge s.dbgCtrl m (dbgCtrlIn s pin) (machHw m) (machCw m)
      (machCevRec m).1 (machApplyLate m).1 m.dbg.frz
      (DbgRel.cen_eq hrel.dbg) (DbgRel.rpl_eq hrel.dbg) hw.hectl
  obtain ⟨hc1, hc2⟩ := h12
  have hc5 : (machDbgNext m).dc = Debug.Ctrl.dcNext s.dbgCtrl (dbgCtrlIn s pin) := by
    rw [machDbgNext_eq]
    exact Bridge.Debug.dc_bridge s.dbgCtrl m (dbgCtrlIn s pin) (machHw m) (machCw m)
      (machCevRec m).1 (machApplyLate m).1 m.dbg.frz (DbgRel.dc_eq hrel.dbg)
      (DbgRel.rpl_eq hrel.dbg) (DbgRel.cen_eq hrel.dbg)
      (Bridge.Debug.ectl_isSome (dbgCtrlIn s pin) (machHw m) (machCw m) hw.hectl)
      ((DbgRel.frz_eq hrel.dbg).trans (by rfl)) hw.happly hw.hcev
  have hc6 : (machDbgNext m).men =
      Debug.Digest.menNext s.dbgDigest.men (dbgDigestIn s pin) := by
    rw [machDbgNext_eq]
    exact Bridge.Debug.men_bridge s.dbgDigest.men (dbgDigestIn s pin) m (machHw m)
      (DbgRel.men_eq hrel.dbg) hw.hmctl
  have hc7 : (machDbgNext m).misr =
      Debug.Digest.misrNext s.dbgDigest.men s.dbgDigest.misr (dbgDigestIn s pin) := by
    rw [machDbgNext_eq]
    exact Bridge.Debug.misr_bridge s.dbgDigest.men s.dbgDigest.misr (dbgDigestIn s pin) m
      (machHw m) (DbgRel.men_eq hrel.dbg) (DbgRel.misr_eq hrel.dbg) hdi hrel.out hrel.oen
      hw.hmctl
  have hc8 : (machDbgNext m).rlvp =
      Debug.Ctrl.rlvPrevNext s.dbgCtrl (dbgCtrlIn s pin) := by
    by_cases hfz : (dbgCtrlIn s pin).frz = true
    · -- frozen: both sides hold `RLVP`
      have hmfrz : m.dbg.frz = true := by
        rw [DbgRel.frz_eq hrel.dbg]; exact hfz
      simp [machDbgNext_eq, Bridge.Debug.dbgNext_rlvp, Debug.Ctrl.rlvPrevNext, hmfrz, hfz,
        DbgRel.rlvp_eq hrel.dbg]
    · have hfz' : (dbgCtrlIn s pin).frz = false := by
        cases h : (dbgCtrlIn s pin).frz <;> simp_all
      have hmfrz : m.dbg.frz = false := by
        rw [DbgRel.frz_eq hrel.dbg]; exact hfz'
      simp [machDbgNext_eq, Bridge.Debug.dbgNext_rlvp, Debug.Ctrl.rlvPrevNext, hmfrz, hfz',
        DbgRel.rlv_eq hrel.dbg]
  rw [hstep, runStep_dbg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- FREEZE
    rw [activeStep_freeze, CoreCtl.freeze_next, dbgNext_freeze, hw.hdbg]
    have hrst : (freezeIn s pin).resetN = true := hact
    by_cases hwr : (freezeIn s pin).dbgWrite = true
    · simp [hrst, hwr]
      rw [nbit_core]
      rfl
    · simp [hrst, hwr]
      exact DbgRel.freeze_eq hrel.dbg
  · -- FRZ
    rw [activeStep_freeze, CoreCtl.frz_next, dbgNext_frz, hw.hdbg]
    have hrst : (freezeIn s pin).resetN = true := hact
    by_cases hwr : (freezeIn s pin).dbgWrite = true
    · simp [hrst, hwr]
      rw [nbit_core, nbit_core]
      rfl
    · simp [hrst, hwr]
      exact DbgRel.freeze_eq hrel.dbg
  · -- FRZD
    rw [activeStep_freeze, CoreCtl.frzd_next, dbgNext_frzd]
    have hrst : (freezeIn s pin).resetN = true := hact
    simp [hrst]
    exact DbgRel.frz_eq hrel.dbg
  · -- MEN
    rw [activeStep_dbgDigest]
    rw [hc6]
    exact (digest_step_men s.dbgDigest (dbgDigestIn s pin) hact).symm
  · -- MISR
    rw [activeStep_dbgDigest]
    rw [hc7]
    exact (digest_step_misr s.dbgDigest (dbgDigestIn s pin) hact).symm
  · -- CEN
    rw [activeStep_dbgCtrl]
    rw [hc1]
    exact (ctrl_step_cen s.dbgCtrl (dbgCtrlIn s pin) hact).symm
  · -- RPL
    rw [activeStep_dbgCtrl]
    rw [hc2]
    exact (ctrl_step_replay s.dbgCtrl (dbgCtrlIn s pin) hact).symm
  · -- EMASK
    rw [activeStep_dbgCtrl]
    exact hw.dbgEmaskValue
  · -- DC
    rw [activeStep_dbgCtrl]
    rw [hc5]
    exact (ctrl_step_dc s.dbgCtrl (dbgCtrlIn s pin) hact).symm
  · -- RLV
    rw [activeStep_dbgCtrl]
    exact hw.dbgRlvValue
  · -- RLVP
    rw [activeStep_dbgCtrl]
    rw [hc8]
    exact (ctrl_step_rlvPrev s.dbgCtrl (dbgCtrlIn s pin) hact).symm

/-- **The `streams` premise.**  One active cycle, both streams. -/
theorem premise_streams (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hw : StreamWire s m pin)
    (hldmode : ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
        Stream.rpl (k.val == 0) (streamIn s pin k.val) = true)
    (hshp : ∀ k : Fin 2, Bridge.StreamBuf.ShapeOK (streamAt s k.val)) :
    ∀ k : Fin 2, Bridge.StreamB.AbsRelB (k.val == 0) (streamAt (activeStep s pin) k.val)
      (Machine.step m pin).streams[k] := by
  intro k
  match k with
  | ⟨0, _⟩ => exact streams_field_0 s m pin hrel hact hw hldmode hshp
  | ⟨1, _⟩ => exact streams_field_1 s m pin hrel hact hw hldmode hshp

end Metronome.ChipCut.Discharge
