/-
# ChipCut premise discharge: the `lines` and `threads` fields

This file discharges two fields of `Metronome.ChipCut.Premises`
(`Metronome/ChipCut/Proof.lean`) for one active cycle, from the current-state
relation `ChipRel s m` and the reachability invariant `Inv s`:

* `premise_lines`: `(Machine.step m pin).lines[l] = Bridge.Line.absSt (lineAt (activeStep s pin) l)` for every line `l`;
* `premise_threads`: `(Machine.step m pin).threads[t] = Bridge.Thread.absState (threadAt (activeStep s pin) t)` for every thread `t`.

## Method

1. Under `runRst s pin = true` the machine takes its active branch
   (`machine_step_runStep`), since `ChipRel.rstQ` identifies the cut's `rst_q`
   with the machine's `rq`.
2. `Machine.runStep` builds its `LineIn`/`ThreadIn` records inline.  The
   definitions `ltLineIn`/`ltThreadIn` name exactly those records, so the
   projections (`runStep_lines`, `runStep_threads`) are definitional.
3. The cut-side input records (`Wire.lineIn`, `Step.threadIn`) and the
   machine's records are shown equal field by field under `ChipRel`
   (`lineIn_eq`, `threadIn_eq`), and the bridge theorems
   `Bridge.Line.step_bridge'` and `Bridge.Thread.step_eq` turn the cut's step
   into the machine's `lineNext`/`threadNext`.

## Proved here, and the named residual hypotheses

Proved from `ChipRel`/`Inv`/`runRst` (and, for the last two, from the two named
records below) with no extra hypothesis:

* the machine's active-branch projection (`machine_step_runStep`);
* the machine's per-cycle input records, named for the first time
  (`ltLineIn`, `ltThreadIn`) with their definitional projections
  (`runStep_lines_vec`, `runStep_threads_vec`, `runStep_lines`,
  `runStep_threads`) -- `CHIPCUT_NOTES.md` §3.4.1 records that the absence of
  these projection functions is what kept the premise bodies as post-step
  comparisons;
* the state-field congruences `(absChip s).sync = m.sync` (`sync_eq`),
  `(absChip s).dbg = m.dbg` (`dbg_eq`) and the line-combination equality
  `lcs_eq` (`lcsOf s = ltLcs m`) from `ChipRel`;
* the §4 trigger input: `trigEvent` reads only fields the relation fixes
  (`trigEvent_eq`), so `Step.threadIn`'s `ev`/`db` give the machine's `trig`
  (`trig_eq`);
* the two record equalities `lineIn_eq`/`threadIn_eq` follow from the bundle
  below, and the `Bridge.Line.step_bridge'`/`Bridge.Thread.step_eq`
  applications (`premise_lines`, `premise_threads`) are complete modulo the
  bundle;
* the first `Bridge.Thread.step_eq` side condition, `no_accept_of_disp`
  (`Not (accept and disp)`), from the machine's dispatch rule: `pickThread` only
  returns `READY` threads (`pickThread_some`, `corePick_ready`,
  `ltThreadIn_dispatch_ready`) while `Thread.accept` needs
  `!(READY || RUNNING)`.

Named residual hypotheses (each is another `Premises` field's bridge output;
see `DISCHARGE_LINETHREAD_NOTES.md`):

* `hcfg` (`premise_lines`): the `lineCfgOf`/`cfgView` decode-encode round trip,
  i.e. the `hcfg` argument of `Bridge.Line.step_bridge'`.  This is one of the
  *trusted chip-top decode interfaces* listed in `CHIPCUT_NOTES.md` §4
  ("the configuration decode inverse (`lineCfgOf`, `outCfgOf`) ... premises,
  not wiring bugs", §3.2).  It is provable from the range bounds of the
  `Config.line` decode (every `LineCfg` field is a `2^w`-bounded bit field or
  `nbits` extract), which the notes record as future work;
* `WireAgree` (both premises), field by field:
  - `pinAgree`, `pinLvl`, `pinPrev` -- the §2 `PinAgree` of
    `Bridge.Line.step_bridge'` and the machine/cut pin-view identification.
    These follow from `Bridge.Debug.level_toNat`/`previous_toNat`/`rise_bit`/
    `fall_bit` plus the byte split `pinVec (ui ++ uio) = (ui >>> 3) ++ uio`
    (a `bv_decide` fact) and the `Nat` arithmetic of `Machine.Util.protoPins`;
  - `sym`, `ctl` -- the `L.CTL`/`L.SYM` move picks
    (`Bridge.Moves.resolveMoves_pick`, `winnerGroup_eq_singleton`), which need
    `Bridge.Core.moves_bridge` (the cores' move outputs, item 4) and the
    destination-name table hypotheses of the `DstKindTable` class;
  - `hPhase`, `hCtl`, `hTapmissClr`, `hPC`, `hStat` -- the §9 host byte strobes
    of `Bridge.Host.hw_bridge` (the write the machine issues this cycle);
  - `beat` -- `Bridge.Line.beat_bridge` under `PinAgree` and `hcfg`;
  - `late`, `stop`, `dispatch`, `pause` -- the `T.STOP`/late move picks and the
    cores' combinational dispatch/pause outputs (`Bridge.Core`, item 4);
  - `pauseDisp` -- the second `Bridge.Thread.step_eq` priority side condition.
    A pause targets the executing thread `XT` of a core, which is never `READY`
    on a reachable cycle (a dispatch clears `READY` and sets `RUNNING`; a
    trigger on a running thread is an overrun).  Its proof needs the machine
    invariant "the executing thread is not `READY`", which is not part of `Inv`
    (four fields); the notes give the proof sketch.  The *first* side condition
    is not a hypothesis: see `no_accept_of_disp`.

No disagreement between the cut and the machine was found in this field pair:
every residual above is a *missing derivation*, not a counterexample.
-/

import Metronome.ChipCut.Proof

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. The active branch of the machine -/

/-- `runRst` asserts the sampled `rst_n`. -/
theorem runRst_rstn {s : State} {pin : Machine.PinIn} (h : runRst s pin = true) :
    pin.rstn = true :=
  (Bool.and_eq_true_iff.mp (by simpa [runRst] using h)).2

/-- `runRst` asserts the cut's `rst_q`. -/
theorem runRst_rstQ {s : State} {pin : Machine.PinIn} (h : runRst s pin = true) :
    s.rst.rstQ = true :=
  (Bool.and_eq_true_iff.mp (by simpa [runRst] using h)).1

/-- On an active cycle the machine's `rq` sample is high (`ChipRel.rstQ`). -/
theorem machine_rq {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (h : runRst s pin = true) : (m.rq && pin.rstn) = true := by
  have hq : m.rq = true := by rw [<- hrel.rstQ]; exact runRst_rstQ h
  rw [hq, runRst_rstn h]
  rfl

/-- On an active cycle the machine takes `runStep`, not `resetStep`. -/
theorem machine_step_runStep {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (h : runRst s pin = true) :
    Machine.step m pin = (Machine.runStep m pin).1 := by
  simp [Machine.step, Machine.stepObs, machine_rq hrel h]

/-! ## 2. The machine's per-cycle component inputs, named

`Machine.runStep` builds the enabled moves, the four `LineIn` records and the
six `ThreadIn` records inline.  The definitions below name exactly those terms,
so the projection lemmas are definitional unfoldings and the wiring obligation
can be stated as an equality of the input records. -/

/-- The machine's two cores' combinational outputs. -/
def ltCbs (m : Machine.State) : Vector Machine.CoreComb 2 :=
  Vector.ofFn fun c =>
    Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) c.val m.dbg.frz

/-- The machine's four line combination bundles. -/
def ltLcs (m : Machine.State) : Vector Machine.LineComb 4 :=
  Vector.ofFn fun l =>
    Machine.lineComb ((Machine.cfgView m.cfg).lines[l]) (m.lines[l])
      (Machine.pinView m.sync m.dbg) m.dbg.frz

/-- The machine's enabled moves of both cores, in `(core, move index)` order. -/
def ltAllMoves (m : Machine.State) : List Machine.Move :=
  (ltCbs m)[0].moves ++ (ltCbs m)[1].moves

/-- The machine's winning moves. -/
def ltWs (m : Machine.State) : List Machine.Move :=
  (Machine.resolveMoves (ltAllMoves m)).1

/-- The machine's host write of the cycle.  `Machine.hostNext`'s written word
reads only the host state, so the arbiter's `served` flag is irrelevant
(`hostNext_hw`). -/
def ltHw (m : Machine.State) : Option Machine.HostWr :=
  if m.host.wPend then
    some { addr := m.host.addr.toNat, v := m.host.wData.toNat, loc := Machine.hostLocate m.host.addr.toNat }
  else none

/-- The written word of `Machine.hostNext` is `ltHw`, for every `served`. -/
theorem hostNext_hw (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) :
    (Machine.hostNext m cv p served).2 = ltHw m := rfl

/-- Line `l`'s `LineIn` record in `Machine.runStep`. -/
def ltLineIn (m : Machine.State) (l : Fin 4) : Machine.LineIn where
  sym := (ltWs m).findSome? fun mv =>
    match Machine.dstOp mv.dst with
    | .lsym op => if mv.line == l.val then some { op := op, v := mv.v } else none
    | _ => none
  ctlMove := (ltWs m).findSome? fun mv =>
    match Machine.dstOp mv.dst with
    | .lCtl k => if k == l.val then some mv.v else none
    | _ => none
  hPhase := Machine.Util.hwAt (ltHw m) "LRT" l.val "PHASE"
  hCtl := Machine.Util.hwByte (ltHw m) "LRT" l.val "CTL"
  hTapmissClr := Machine.Util.nbit ((Machine.Util.hwByte (ltHw m) "LRT" l.val "STAT").getD 0) 0

/-- Thread `t`'s `ThreadIn` record in `Machine.runStep`. -/
def ltThreadIn (m : Machine.State) (t : Fin 6) : Machine.ThreadIn where
  trig := !m.dbg.frz && (m.threads[t]).en &&
    (Machine.trigEvent m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) (ltLcs m) t.val ||
      Machine.Util.bit m.ctrl.db t.val)
  beat := (Machine.Util.vget (ltLcs m) (Machine.Util.vget (Machine.cfgView m.cfg).threads t.val).line).beat
  late := (ltAllMoves m).any fun mv => mv.thread == t.val && !mv.armed &&
    (match Machine.dstOp mv.dst with
      | .lsym _ => true
      | _ => false)
  stop := (ltWs m).any fun mv => mv.thread == t.val &&
    (match Machine.dstOp mv.dst with
      | .stop => true
      | _ => false)
  dispatch := (List.range 2).any fun c =>
    (Machine.Util.vget (ltCbs m) c).disp &&
      (Machine.Util.vget (ltCbs m) c).dispThread == t.val
  pause := (List.range 2).findSome? fun c =>
    if (Machine.Util.vget (ltCbs m) c).pse &&
        (Machine.Util.vget m.cores c).xt.toNat == t.val
      then some (Machine.Util.vget (ltCbs m) c).npc else none
  hPC := Machine.Util.hwByte (ltHw m) "TRT" t.val "PC"
  hStat := Machine.Util.hwByte (ltHw m) "TRT" t.val "STAT"

/-- A valid `vget` is the vector entry. -/
theorem vget_eq {a : Type} {n : Nat} [Inhabited a] (v : Vector a n) {i : Nat} (h : i < n) :
    Machine.Util.vget v i = v[i]'h := by
  simp [Machine.Util.vget, h]

/-- **Projection: the machine's next lines, as a vector.** -/
theorem runStep_lines_vec (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.lines =
      Vector.ofFn fun l : Fin 4 =>
        Machine.lineNext ((Machine.cfgView m.cfg).lines[l]) (m.lines[l]) ((ltLcs m)[l])
          (Machine.pinView m.sync m.dbg) (ltLineIn m l) m.dbg.frz := rfl

/-- **Projection: the machine's next threads, as a vector.** -/
theorem runStep_threads_vec (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.threads =
      Vector.ofFn fun t : Fin 6 =>
        Machine.threadNext (m.threads[t]) (ltThreadIn m t) := rfl

/-- **Projection: the machine's next line `l`.** -/
theorem runStep_lines (m : Machine.State) (pin : Machine.PinIn) (l : Fin 4) :
    (Machine.runStep m pin).1.lines[l] =
      Machine.lineNext ((Machine.cfgView m.cfg).lines[l]) (m.lines[l])
        ((ltLcs m)[l]) (Machine.pinView m.sync m.dbg) (ltLineIn m l) m.dbg.frz := by
  rw [runStep_lines_vec]
  simp

/-- **Projection: the machine's next thread `t`.** -/
theorem runStep_threads (m : Machine.State) (pin : Machine.PinIn) (t : Fin 6) :
    (Machine.runStep m pin).1.threads[t] =
      Machine.threadNext (m.threads[t]) (ltThreadIn m t) := by
  rw [runStep_threads_vec]
  simp

/-! ## 3. State-field congruences between `m` and `absChip s` -/

/-- Bit-vector plumbing: the high byte of a word. -/
theorem trunc8_hi (a b : BitVec 8) : BitVec.truncate 8 (BitVec.ushiftRight (a ++ b) 8) = a := by
  bv_decide

/-- Bit-vector plumbing: the low byte of a word. -/
theorem trunc8_lo (a b : BitVec 8) : BitVec.truncate 8 (a ++ b) = b := by
  bv_decide

/-- The machine synchroniser words are exactly the cut's (`ChipRel.sync`). -/
theorem sync_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).sync = m.sync := by
  obtain ⟨h1, h2, h3⟩ := hrel.sync
  simp only [absChip, h1, h2, h3, trunc8_hi, trunc8_lo]

/-- The machine debug block is exactly the cut's (`ChipRel.dbg`). -/
theorem dbg_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).dbg = m.dbg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hrel.dbg
  simp only [absChip]
  rw [<- h1, <- h2, <- h3, <- h4, <- h5, <- h6, <- h7, <- h8, <- h9, <- h10, <- h11]

/-- The selected line at a `Fin` index is the vector entry. -/
theorem lineAt_fin (s : State) (l : Fin 4) : lineAt s l.val = s.lines[l] := by
  match l with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-- The selected thread at a `Fin` index is the vector entry. -/
theorem threadAt_fin (s : State) (t : Fin 6) : threadAt s t.val = s.threads[t] := by
  match t with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- The machine threads are the cut's, read with `vget`. -/
theorem threads_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) {t : Nat} (ht : t < 6) :
    Machine.Util.vget m.threads t = Bridge.Thread.absState (threadAt s t) := by
  rw [vget_eq (v := m.threads) ht]
  exact hrel.threads ⟨t, ht⟩

/-- The abstraction's threads, read with `vget`, are the cut's. -/
theorem absChip_threads_vget {s : State} {t : Nat} (ht : t < 6) :
    Machine.Util.vget (absChip s).threads t = Bridge.Thread.absState (threadAt s t) := by
  rw [vget_eq (v := (absChip s).threads) ht]
  simp only [absChip, Vector.getElem_ofFn]
  congr 1
  exact (threadAt_fin s ⟨t, ht⟩).symm

/-- The debug freeze flag is the cut's. -/
theorem dbg_frz {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.dbg.frz = s.freeze.frz := hrel.dbg.2.1

/-- The machine's unit flags are the cut's (`UnitsRel.f`). -/
theorem units_f {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.units.f = s.glue.fl := hrel.units.1

/-- The machine's previous unit flags are the cut's (`UnitsRel.fp`). -/
theorem units_fp {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.units.fp = s.glue.flp := hrel.units.2.1

/-- The machine's `INV` mailbox flag is the cut's (`CtrlRel.inv`). -/
theorem ctrl_inv {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.ctrl.inv = s.glue.inv := by
  obtain ⟨_, _, _, _, _, _, h7, _, _, _, _, _⟩ := hrel.ctrl
  exact h7

/-- The machine's `INV` previous flag is the cut's (`CtrlRel.invp`). -/
theorem ctrl_invp {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.ctrl.invp = s.glue.invp := by
  obtain ⟨_, _, _, _, _, _, _, h8, _, _, _, _⟩ := hrel.ctrl
  exact h8

/-- The machine's doorbell register is the cut's (`CtrlRel.db`). -/
theorem ctrl_db {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    m.ctrl.db = s.glue.db := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _⟩ := hrel.ctrl
  exact h11

/-- `trigEvent` reads only fields the relation fixes. -/
theorem trigEvent_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) (t : Nat)
    (ht : t < 6) (cv : Machine.CfgView) (p : Machine.PinView)
    (lcs : Vector Machine.LineComb 4) :
    Machine.trigEvent m cv p lcs t = Machine.trigEvent (absChip s) cv p lcs t := by
  have hthreads : Machine.Util.vget m.threads t = Machine.Util.vget (absChip s).threads t := by
    rw [threads_eq hrel ht, absChip_threads_vget ht]
  unfold Machine.trigEvent
  dsimp only
  cases Machine.trigOp (Machine.Util.vget cv.threads t).trig <;>
    simp only [absChip, units_f hrel, units_fp hrel, ctrl_inv hrel, ctrl_invp hrel, hthreads]

/-- Out-of-range-free `!` access is the entry. -/
theorem getElem!_eq_get {a : Type} {n : Nat} [Inhabited a] (v : Vector a n) {i : Nat}
    (h : i < n) : v[i]! = v.get ⟨i, h⟩ := by
  simp only [getElem!_def]
  rw [getElem?_pos]
  rfl

/-- The cut's line combination bundle `l` is the machine's. -/
theorem lcs_get {s : State} {m : Machine.State} (hrel : ChipRel s m) (l : Fin 4) :
    (lcsOf s)[l] = (ltLcs m)[l] := by
  have hcfg : Machine.cfgView s.cont.cfg = Machine.cfgView m.cfg := by rw [hrel.cfg]
  have hsync : (absChip s).sync = m.sync := sync_eq hrel
  have hdbg : (absChip s).dbg = m.dbg := dbg_eq hrel
  have hfrz : s.freeze.frz = m.dbg.frz := (dbg_frz hrel).symm
  have hline : m.lines[(l : Nat)] = Bridge.Line.absSt (lineAt s l.val) := hrel.lines l
  have hbang : (Machine.cfgView m.cfg).lines[l.val]! = (Machine.cfgView m.cfg).lines[l] :=
    getElem!_eq_get _ l.isLt
  simp only [lcsOf, ltLcs, Fin.getElem_fin, Vector.getElem_ofFn, hcfg, hbang, hsync, hdbg, hfrz, hline]

/-- The cut's line combination bundles are the machine's. -/
theorem lcs_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    lcsOf s = ltLcs m := by
  apply Vector.ext
  intro l hl
  exact lcs_get hrel ⟨l, hl⟩

/-- The cut's synchronised pins as a line pin view (the `Bridge.Line` pin
abstraction), read from the cut's own synchroniser and replay registers. -/
def pinAbs (s : State) : Bridge.Line.PinAbs where
  lvl := (Debug.Pins.level (Debug.Pins.pinVec s.sync.s2) s.dbgCtrl.rlv s.dbgCtrl.emask
    s.dbgCtrl.replay).toNat
  prev := (Debug.Pins.previous (Debug.Pins.pinVec s.sync.sp) s.dbgCtrl.rlvPrev s.dbgCtrl.emask
    s.dbgCtrl.replay).toNat

/-- `Machine.lineComb` reads the pin view only through `lvl` and `prev`. -/
theorem lineComb_pin_congr (c : Machine.LineCfg) (st : Machine.LineSt) (p q : Machine.PinView)
    (f : Bool) (hl : p.lvl = q.lvl) (hp : p.prev = q.prev) :
    Machine.lineComb c st p f = Machine.lineComb c st q f := by
  cases p
  cases q
  simp only at hl hp
  subst hl
  subst hp
  simp [Machine.lineComb, Machine.PinView.pin, Machine.PinView.rise, Machine.PinView.fall,
    Machine.PinView.edgeSel]

/-- `Machine.lineNext` reads the pin view only through `lvl` and `prev`. -/
theorem lineNext_pin_congr (c : Machine.LineCfg) (st : Machine.LineSt) (cb : Machine.LineComb)
    (p q : Machine.PinView) (i : Machine.LineIn) (f : Bool)
    (hl : p.lvl = q.lvl) (hp : p.prev = q.prev) :
    Machine.lineNext c st cb p i f = Machine.lineNext c st cb q i f := by
  cases p
  cases q
  simp only at hl hp
  subst hl
  subst hp
  simp [Machine.lineNext, Machine.PinView.pin]


/-- The §4 trigger input of `Step.threadIn` is the machine's `trig`. -/
theorem trig_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) (pin : Machine.PinIn)
    (t : Fin 6) :
    (ltThreadIn m t).trig =
      Metronome.Thread.trig (threadAt s t.val) (threadIn s pin t.val) := by
  have hfrz : s.freeze.frz = m.dbg.frz := (dbg_frz hrel).symm
  have hen : (threadAt s t.val).en = (m.threads[t]).en := by
    rw [hrel.threads t]
    rfl
  have hdb : s.glue.db = m.ctrl.db := (ctrl_db hrel).symm
  have hev : Machine.trigEvent (absChip s) (Machine.cfgView s.cont.cfg)
        (Machine.pinView (absChip s).sync (absChip s).dbg) (lcsOf s) t.val =
      Machine.trigEvent m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (ltLcs m) t.val := by
    rw [lcs_eq hrel, sync_eq hrel, dbg_eq hrel, hrel.cfg]
    exact (trigEvent_eq hrel t.val t.isLt _ _ _).symm
  simp only [ltThreadIn, Metronome.Thread.trig, threadIn, hfrz, hen, hdb, hev]
  cases h1 : m.dbg.frz <;> cases h2 : (m.threads[t]).en <;>
    cases h3 : Machine.trigEvent m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (ltLcs m) t.val <;>
    cases h4 : Machine.Util.bit m.ctrl.db t.val <;> rfl

/-- A dispatch picks a `READY` thread. -/
theorem pickThread_some {m : Machine.State} {cv : Machine.CfgView} {c e : Nat}
    (h : Machine.pickThread m cv c = some e) :
    ((Machine.Util.vget cv.threads e).core == c) = true ∧
      (Machine.Util.vget m.threads e).ready = true := by
  unfold Machine.pickThread at h
  have hp := List.find?_some h
  exact ⟨(Bool.and_eq_true_iff.mp hp).1, (Bool.and_eq_true_iff.mp hp).2⟩

/-- The dispatch choice of one core's combinational bundle (the `pick` local of
`Machine.coreComb`). -/
def corePick (m : Machine.State) (cv : Machine.CfgView) (_p : Machine.PinView) (c : Nat)
    (f : Bool) : Option Nat :=
  if (!f && ((Machine.Util.vget m.cores c).xv && !f &&
        Machine.insnField (Machine.Util.vget m.cores c).ir Machine.Tables.FIELD_pause == 1 ||
      !(Machine.Util.vget m.cores c).xv && !(Machine.Util.vget m.cores c).rv) && m.ctrl.run) = true
    then Machine.pickThread m cv c else none

/-- The core's `disp` is the dispatch choice's `isSome`. -/
theorem coreComb_disp (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (c : Nat) (f : Bool) :
    (Machine.coreComb m cv p c f).disp = (corePick m cv p c f).isSome := rfl

/-- The core's `dispThread` is the dispatch choice's index. -/
theorem coreComb_dispThread (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (c : Nat) (f : Bool) :
    (Machine.coreComb m cv p c f).dispThread = (corePick m cv p c f).getD 0 := rfl

/-- A dispatch of `t` implies that `t` is `READY`. -/
theorem corePick_ready {m : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {c : Nat} {f : Bool} {t : Nat}
    (h : (corePick m cv p c f).isSome = true) (ht : (corePick m cv p c f).getD 0 = t) :
    (Machine.Util.vget m.threads t).ready = true := by
  cases hp : corePick m cv p c f with
  | none => rw [hp] at h; exact absurd h (by decide)
  | some e =>
    have het : e = t := by
      rw [hp] at ht
      simpa using ht
    rw [het] at hp
    unfold corePick at hp
    by_cases hc : (!f && ((Machine.Util.vget m.cores c).xv && !f &&
          Machine.insnField (Machine.Util.vget m.cores c).ir Machine.Tables.FIELD_pause == 1 ||
        !(Machine.Util.vget m.cores c).xv && !(Machine.Util.vget m.cores c).rv) && m.ctrl.run) = true
    · rw [if_pos hc] at hp
      exact (pickThread_some hp).2
    · rw [if_neg (by simpa using hc)] at hp
      exact absurd hp (by simp)

/-- A dispatch of thread `t` implies that the machine's thread `t` is `READY`. -/
theorem ltThreadIn_dispatch_ready (m : Machine.State) (t : Fin 6)
    (h : (ltThreadIn m t).dispatch = true) : (m.threads[t]).ready = true := by
  have hany : ((List.range 2).any fun c =>
      (Machine.Util.vget (ltCbs m) c).disp &&
        (Machine.Util.vget (ltCbs m) c).dispThread == t.val) = true := h
  obtain ⟨c, hc, hpred⟩ := List.any_eq_true.mp hany
  have hc2 : c < 2 := by simpa using hc
  have hdisp : (Machine.Util.vget (ltCbs m) c).disp = true :=
    (Bool.and_eq_true_iff.mp hpred).1
  have hthr : ((Machine.Util.vget (ltCbs m) c).dispThread == t.val) = true :=
    (Bool.and_eq_true_iff.mp hpred).2
  have hcbs : Machine.Util.vget (ltCbs m) c =
      Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) c m.dbg.frz := by
    rw [vget_eq (v := ltCbs m) hc2]
    simp [ltCbs]
  have hk : (corePick m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) c m.dbg.frz).isSome
      = true := by
    rw [<- coreComb_disp, <- hcbs]
    exact hdisp
  have ht : (corePick m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) c m.dbg.frz).getD 0
      = t.val := by
    rw [<- coreComb_dispThread, <- hcbs]
    simpa using hthr
  have hready := corePick_ready (p := Machine.pinView m.sync m.dbg) hk ht
  rw [vget_eq (v := m.threads) t.isLt] at hready
  exact hready

/-! ## 4. The remaining wiring facts, as a named bundle

Each field below is one input record field of `Wire.lineIn`/`Step.threadIn`
against the machine's `ltLineIn`/`ltThreadIn`.  They are exactly the
"remaining wiring/side condition" column of `CHIPCUT_NOTES.md` §3.4.1 for items
2 (`lines`) and 3 (`threads`):

* `sym`, `ctl` -- the `L.CTL`/`L.SYM` move picks of `Bridge.Moves.resolveMoves_pick`
  and `winnerGroup_eq_singleton`, which need `Bridge.Core.moves_bridge` (the
  cores' move outputs, item 4) and the destination-name table hypotheses of the
  `DstKindTable` class;
* `hPhase`, `hCtl`, `hTapmissClr`, `hPC`, `hStat` -- the §9 host byte strobes of
  `Bridge.Host.hw_bridge` (the host write of the cycle);
* `beat` -- `Bridge.Line.beat_bridge` under `PinAgree` and the `hcfg` round trip;
* `late`, `stop`, `dispatch`, `pause` -- the move picks for `T.STOP`/late and the
  cores' combinational dispatch/pause outputs (`Bridge.Core`, item 4);
* `pauseDisp` -- the second `Bridge.Thread.step_eq` priority side condition.  A
  pause targets the executing thread `XT`, which is never `READY` (dispatch
  clears `READY` and sets `RUNNING`; a trigger on a running thread is an
  overrun), so a pause and a dispatch never target the same thread.  Its proof
  needs the machine invariant "the executing thread is not `READY`", which is
  not part of `Inv`.  The *first* side condition is not a field here: it is
  proved (`no_accept_of_disp`). -/
structure WireAgree (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  /-- the §2 pin agreement of `Bridge.Debug.level_toNat`/`rise_bit`/`fall_bit` -/
  pinAgree : ∀ l : Fin 4, Bridge.Line.PinAgree (pinAbs s) (lineIn s pin l.val)
  /-- the machine pin view's level is the cut's (the `{ui, uio}` byte split of §2) -/
  pinLvl : (Machine.pinView m.sync m.dbg).lvl = (pinAbs s).lvl
  /-- the machine pin view's previous level is the cut's -/
  pinPrev : (Machine.pinView m.sync m.dbg).prev = (pinAbs s).prev
  /-- the `L.SYM` pick, in the projected (`% 16`) form: the cut's `symD` is a
  nibble (`truncate 4`), the machine keeps the winner's whole data byte
  (`MoveFabric.sym_data_witness` refutes the exact form).  `Machine.lineNext`
  reads it only through `stagedNext`'s `bv 4 v` / `v % 2` (`lineNext_trunc`). -/
  sym : ∀ l : Fin 4, (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
    (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v))
  /-- the `Lk.CTL` pick, in the projected (`% 8`) form: the cut's `ctlD` is a
  `BitVec 3` (`ctl_data_witness` refutes the exact form), and
  `Machine.lineNext` reads only `nbit v 0..2` (`lineNext_trunc`). -/
  ctl : ∀ l : Fin 4, (ltLineIn m l).ctlMove.map (fun v => v % 8) =
    (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove
  /-- the host `PHASE` byte write -/
  hPhase : ∀ l : Fin 4, (ltLineIn m l).hPhase = (Bridge.Line.absIn (lineIn s pin l.val)).hPhase
  /-- the host `CTL` byte write -/
  hCtl : ∀ l : Fin 4, (ltLineIn m l).hCtl = (Bridge.Line.absIn (lineIn s pin l.val)).hCtl
  /-- the host `STAT` byte write (the `TAPMISS` clear bit) -/
  hTapmissClr : ∀ l : Fin 4,
    (ltLineIn m l).hTapmissClr = (Bridge.Line.absIn (lineIn s pin l.val)).hTapmissClr
  /-- the thread's line `BEAT` -/
  beat : ∀ t : Fin 6, (ltThreadIn m t).beat =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).beat
  /-- the late-symbol write of the thread -/
  late : ∀ t : Fin 6, (ltThreadIn m t).late =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).late
  /-- the `T.STOP` write of the thread -/
  stop : ∀ t : Fin 6, (ltThreadIn m t).stop =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).stop
  /-- the thread's dispatch -/
  dispatch : ∀ t : Fin 6, (ltThreadIn m t).dispatch =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).dispatch
  /-- the thread's pause (with its `npc`) -/
  pause : ∀ t : Fin 6, (ltThreadIn m t).pause =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).pause
  /-- the host `PC` byte write -/
  hPC : ∀ t : Fin 6, (ltThreadIn m t).hPC =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hPC
  /-- the host `STAT` byte write -/
  hStat : ∀ t : Fin 6, (ltThreadIn m t).hStat =
    (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hStat
  /-- `Bridge.Thread.step_eq` side condition 2 (side condition 1 is derived:
  `no_accept_of_disp`) -/
  pauseDisp : ∀ t : Fin 6,
    Not ((threadIn s pin t.val).pause = true ∧ (threadIn s pin t.val).disp = true)

/-- Extensionality for the machine's `LineIn` record (the structure carries no
generated `ext` theorem). -/
theorem lineIn_ext {a b : Machine.LineIn} (h1 : a.sym = b.sym) (h2 : a.ctlMove = b.ctlMove)
    (h3 : a.hPhase = b.hPhase) (h4 : a.hCtl = b.hCtl) (h5 : a.hTapmissClr = b.hTapmissClr) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Extensionality for the machine's `ThreadIn` record. -/
theorem threadIn_ext {a b : Machine.ThreadIn} (h1 : a.trig = b.trig) (h2 : a.beat = b.beat)
    (h3 : a.late = b.late) (h4 : a.stop = b.stop) (h5 : a.dispatch = b.dispatch)
    (h6 : a.pause = b.pause) (h7 : a.hPC = b.hPC) (h8 : a.hStat = b.hStat) : a = b := by
  cases a
  cases b
  simp_all

/-- The first `Bridge.Thread.step_eq` side condition, from the machine's
dispatch rule: an accepted trigger and a dispatch exclude each other (a dispatch
picks a `READY` thread, an accepted trigger requires `!(READY || RUNNING)`). -/
theorem no_accept_of_disp {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hwire : WireAgree s m pin) (t : Fin 6) :
    Not (Metronome.Thread.accept (threadAt s t.val) (threadIn s pin t.val) = true ∧
      (threadIn s pin t.val).disp = true) := by
  rintro ⟨hacc, hdispc⟩
  have hdispm : (ltThreadIn m t).dispatch = true := by
    rw [hwire.dispatch t]
    exact hdispc
  have hready : (m.threads[t]).ready = true := ltThreadIn_dispatch_ready m t hdispm
  have hreadyCut : (threadAt s t.val).ready = true := by
    have hh := hready
    rw [hrel.threads t] at hh
    exact hh
  have hbusy : Metronome.Thread.busy (threadAt s t.val) = true := by
    unfold Metronome.Thread.busy
    rw [hreadyCut]
    rfl
  have hfalse : Metronome.Thread.accept (threadAt s t.val) (threadIn s pin t.val) = false := by
    simp [Metronome.Thread.accept, hbusy]
  rw [hfalse] at hacc
  exact absurd hacc (by decide)

/-- `nbit` at `k` only reads the low `k+1` bits (`Nat.testBit`). -/
theorem lineNbit_testBit (x k : Nat) : Machine.Util.nbit x k = x.testBit k := by
  unfold Machine.Util.nbit
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rfl

theorem nbit_mod8 (x k : Nat) (hk : k < 3) :
    Machine.Util.nbit (x % 8) k = Machine.Util.nbit x k := by
  rw [lineNbit_testBit, lineNbit_testBit,
    show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]
  simp [hk]

/-- The three `nbit` shapes `Machine.lineNext` reads from `ctlMove`. -/
theorem nbit_mod8_0 (v : Nat) : Machine.Util.nbit (v % 8) 0 = Machine.Util.nbit v 0 :=
  nbit_mod8 v 0 (by decide)

theorem nbit_mod8_1 (v : Nat) : Machine.Util.nbit (v % 8) 1 = Machine.Util.nbit v 1 :=
  nbit_mod8 v 1 (by decide)

theorem nbit_mod8_2 (v : Nat) : Machine.Util.nbit (v % 8) 2 = Machine.Util.nbit v 2 :=
  nbit_mod8 v 2 (by decide)

theorem bv4_mod16 (x : Nat) : Machine.Util.bv 4 (x % 16) = Machine.Util.bv 4 x := by
  unfold Machine.Util.bv
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show (16 : Nat) = 2 ^ 4 from rfl]
  exact Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (Nat.le_refl 4))

/-- `stagedNext` only reads the low nibble of the `L.SYM` data byte. -/
theorem stagedNext_mod16 (st : Machine.LineSt) (o : Option Machine.SymWrite) :
    Machine.stagedNext st (o.map (fun w => { w with v := w.v % 16 })) =
      Machine.stagedNext st o := by
  cases o with
  | none => rfl
  | some w =>
    obtain ⟨op, v⟩ := w
    simp only [Option.map_some, Machine.stagedNext]
    by_cases h1 : op = 1
    · subst h1; simp [bv4_mod16]
    · by_cases h2 : op = 2
      · subst h2; simp
      · by_cases h3 : op = 3
        · subst h3; simp [bv4_mod16]
        · simp [h1, h2, h3]

/-- `stagedNext` at an explicitly truncated `L.SYM` write. -/
theorem stagedNext_mod16_some (st : Machine.LineSt) (w : Machine.SymWrite) :
    Machine.stagedNext st (some { w with v := w.v % 16 }) =
      Machine.stagedNext st (some w) := by
  have h := stagedNext_mod16 st (some w)
  simpa [Option.map_some] using h

/-- The `ctlMove` match of `Machine.lineNext` only reads `nbit v 0..2`. -/
theorem ctlTriple_mod8 (o : Option Nat) (a b c : Bool) :
    (match o.map (fun v => v % 8) with
      | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
      | none => (a, b, c)) =
    (match o with
      | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
      | none => (a, b, c)) := by
  cases o with
  | none => rfl
  | some v =>
    rw [Option.map_some]
    show (Machine.Util.nbit (v % 8) 0, Machine.Util.nbit (v % 8) 1,
        Machine.Util.nbit (v % 8) 2) =
      (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
    rw [nbit_mod8 v 0 (by decide), nbit_mod8 v 1 (by decide), nbit_mod8 v 2 (by decide)]

/-! ### The projected (`% 16`, `% 8`) line input

`WireAgree.sym`/`.ctl` are the *projected* forms (the exact ones are false:
`MoveFabric.sym_data_witness`/`ctl_data_witness`).  `Machine.lineNext` reads
`sym` only through `stagedNext` (`bv 4 v`, `v % 2`) and `ctlMove` only through
`nbit v 0..2`, so truncating the two fields does not change the next line,
which is `lineNext_trunc`; `lineIn_proj_eq` then identifies the truncated
machine record with the bridge's `absIn` of the cut input. -/

/-- The machine's line input with the two data fields projected. -/
def lineInTrunc (i : Machine.LineIn) : Machine.LineIn where
  sym := i.sym.map (fun w => { w with v := w.v % 16 })
  ctlMove := i.ctlMove.map (fun v => v % 8)
  hPhase := i.hPhase
  hCtl := i.hCtl
  hTapmissClr := i.hTapmissClr

/-- **The record-level truncation of the line input.** -/
theorem lineNext_trunc (c : Machine.LineCfg) (st : Machine.LineSt) (cb : Machine.LineComb)
    (p : Machine.PinView) (f : Bool) (i : Machine.LineIn) :
    Machine.lineNext c st cb p i f = Machine.lineNext c st cb p (lineInTrunc i) f := by
  obtain ⟨sy, ct, ph, hc, ht⟩ := i
  cases sy <;> cases ct <;>
    simp only [Machine.lineNext, lineInTrunc, nbit_mod8_0, nbit_mod8_1,
      nbit_mod8_2, Option.map_none, Option.map_some, stagedNext_mod16_some] <;>
    rfl

/-- The projected machine line input is the bridge's `absIn` of the cut input. -/
theorem lineIn_proj_eq {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hwire : WireAgree s m pin) (l : Fin 4) :
    lineInTrunc (ltLineIn m l) = Bridge.Line.absIn (lineIn s pin l.val) := by
  refine lineIn_ext ?_ ?_ (hwire.hPhase l) (hwire.hCtl l) (hwire.hTapmissClr l)
  · show (ltLineIn m l).sym.map (fun w => { w with v := w.v % 16 }) = _
    have hmap : (ltLineIn m l).sym.map (fun w => { w with v := w.v % 16 }) =
        ((ltLineIn m l).sym.map (fun w => (w.op, w.v % 16))).map
          (fun p => ({ op := p.1, v := p.2 } : Machine.SymWrite)) := by
      rw [Option.map_map]
      rfl
    rw [hmap, hwire.sym l]
    cases (Bridge.Line.absIn (lineIn s pin l.val)).sym with
    | none => rfl
    | some w => cases w; rfl
  · exact hwire.ctl l

/-- The thread input record of `Step.threadIn` is the `Bridge.Thread` abstraction
of it: `trig` is `trig_eq`, the rest is the bundle. -/
theorem threadIn_eq {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hwire : WireAgree s m pin) (t : Fin 6) :
    ltThreadIn m t = Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val) :=
  threadIn_ext (trig_eq hrel pin t) (hwire.beat t) (hwire.late t) (hwire.stop t)
    (hwire.dispatch t) (hwire.pause t) (hwire.hPC t) (hwire.hStat t)

/-! ## 5. The two premises -/

/-- The cut's next thread is `Thread.step` on the cut's input record. -/
theorem activeStep_thread (s : State) (pin : Machine.PinIn) (t : Fin 6) :
    threadAt (activeStep s pin) t.val = Thread.step (threadAt s t.val) (threadIn s pin t.val) := by
  have hvec : (activeStep s pin).threads = Vector.ofFn fun i : Fin 6 =>
      Thread.step (threadAt s i.val) (threadIn s pin i.val) := rfl
  rw [threadAt_fin, hvec]
  simp

/-- The cut's next line is `Line.step` on the cut's input record. -/
theorem activeStep_line (s : State) (pin : Machine.PinIn) (l : Fin 4) :
    lineAt (activeStep s pin) l.val = Line.step (lineAt s l.val) (lineIn s pin l.val) := by
  have hvec : (activeStep s pin).lines = Vector.ofFn fun i : Fin 4 =>
      Line.step (lineAt s i.val) (lineIn s pin i.val) := rfl
  rw [lineAt_fin, hvec]
  simp

/-- **The `lines` premise.** -/
theorem premise_lines (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hcfg : ∀ l : Fin 4, (Machine.cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l.val))
    (hwire : WireAgree s m pin) :
    ∀ l : Fin 4,
      (Machine.step m pin).lines[l] = Bridge.Line.absSt (lineAt (activeStep s pin) l.val) := by
  intro l
  have hreset : (lineIn s pin l.val).resetN = true := hact
  have hbr := Bridge.Line.step_bridge' (lineAt s l.val) (lineIn s pin l.val)
    ((Machine.cfgView m.cfg).lines[l]) (hcfg l) (pinAbs s) (hwire.pinAgree l) hreset
  rw [machine_step_runStep hrel hact, runStep_lines, activeStep_line, hbr]
  have hmlcs : (ltLcs m)[l] = Machine.lineComb ((Machine.cfgView m.cfg).lines[l])
      (m.lines[l]) (Machine.pinView m.sync m.dbg) m.dbg.frz := by simp [ltLcs]
  have hfrz : (lineIn s pin l.val).frz = s.freeze.frz := rfl
  rw [hmlcs, hrel.lines l, dbg_frz hrel, hfrz]
  conv =>
    lhs
    rw [lineNext_trunc]
  rw [lineIn_proj_eq hwire l]
  rw [lineComb_pin_congr ((Machine.cfgView m.cfg).lines[l])
    (Bridge.Line.absSt (lineAt s l.val)) (Machine.pinView m.sync m.dbg)
    (Bridge.Line.PinAbs.view (pinAbs s)) s.freeze.frz hwire.pinLvl hwire.pinPrev]
  rw [lineNext_pin_congr ((Machine.cfgView m.cfg).lines[l])
    (Bridge.Line.absSt (lineAt s l.val))
    (Machine.lineComb ((Machine.cfgView m.cfg).lines[l]) (Bridge.Line.absSt (lineAt s l.val))
      (Bridge.Line.PinAbs.view (pinAbs s)) s.freeze.frz)
    (Machine.pinView m.sync m.dbg) (Bridge.Line.PinAbs.view (pinAbs s))
    (Bridge.Line.absIn (lineIn s pin l.val)) s.freeze.frz hwire.pinLvl hwire.pinPrev]

/-- **The `threads` premise.** -/
theorem premise_threads (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwire : WireAgree s m pin) :
    ∀ t : Fin 6,
      (Machine.step m pin).threads[t] =
        Bridge.Thread.absState (threadAt (activeStep s pin) t.val) := by
  intro t
  have hreset : (threadIn s pin t.val).resetN = true := hact
  have hbr := Bridge.Thread.step_eq (threadAt s t.val) (threadIn s pin t.val) hreset
    (no_accept_of_disp hrel hwire t) (hwire.pauseDisp t)
  rw [machine_step_runStep hrel hact, runStep_threads, activeStep_thread, hbr]
  rw [threadIn_eq hrel hwire t, hrel.threads t]

end Metronome.ChipCut.Discharge
