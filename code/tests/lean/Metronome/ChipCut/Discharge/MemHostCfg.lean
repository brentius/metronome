/-
# ChipCut: discharging the `p0`, `hostReq`, `host`, `cw`, `bank` and `contents` premises

This file restates the six `Premises` fields of `Metronome/ChipCut/Proof.lean`
that concern the data-RAM path, the host link, the configuration-write path and
the memory/config contents as **current-state wiring obligations**, and proves
each field from `ChipRel`/`Inv`/the active reset sample plus the named wiring
facts that are not yet available as lemmas of the component bridges (one
`<field>_open_*` hypothesis per remaining obligation; see
`DISCHARGE_MEMHOSTCFG_NOTES.md`).

The machine's per-cycle quantities are projected out of `Machine.runStep`'s
inline `let` chain by the `mhc*` definitions below (the projection functions
`CHIPCUT_NOTES.md` §3.4 said were missing), each with a `rfl`-level projection
lemma.  The cut-side inputs are the `Wire.lean` definitions.

No `sorry`, no `native_decide`.
-/

import Metronome.ChipCut.Proof
import Metronome.Bridge.Mem
import Metronome.Bridge.Host
import Metronome.Bridge.CfgWrite

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## Machine-side projections of one `runStep`

`Machine.runStep` builds every per-cycle quantity inline.  The definitions below
copy the relevant prefix of that `let` chain so that a premise field can be
stated as "the cut's input record equals the machine's input record".  They are
definitionally the machine's own locals, which the `step*` lemmas below use. -/

/-- The machine's per-core combinational bundle of this cycle. -/
def mhcCbs (m : Machine.State) (pin : Machine.PinIn) : Vector Machine.CoreComb 2 :=
  let frozen := m.dbg.frz
  let cv := Machine.cfgView m.cfg
  let p := Machine.pinView m.sync m.dbg
  Vector.ofFn fun c => Machine.coreComb m cv p c.val frozen

/-- The machine's resolved winner list of this cycle. -/
def mhcWs (m : Machine.State) (pin : Machine.PinIn) : List Machine.Move :=
  let cbs := mhcCbs m pin
  let allMoves := cbs[0].moves ++ cbs[1].moves
  let (ws, _) := Machine.resolveMoves allMoves
  ws

/-- The machine's `P0` move (the `P0.AL`/`AH`/`W`/`R` winner). -/
def mhcP0Move (m : Machine.State) (pin : Machine.PinIn) : Option Machine.P0Move :=
  (mhcWs m pin).findSome? fun mm => match Machine.dstOp mm.dst with
    | .pAl => some ⟨0, mm.v⟩
    | .pAh => some ⟨1, mm.v⟩
    | .pW => some ⟨2, mm.v⟩
    | .pR => some ⟨3, mm.v⟩
    | _ => none

/-- The machine's `CW` move (the `CW.AL`/`AH`/`D` winner). -/
def mhcCwMove (m : Machine.State) (pin : Machine.PinIn) : Option Machine.CwMove :=
  (mhcWs m pin).findSome? fun mm => match Machine.dstOp mm.dst with
    | .cwAl => some ⟨0, mm.v⟩
    | .cwAh => some ⟨1, mm.v⟩
    | .cwD => some ⟨2, mm.v⟩
    | _ => none

/-- The machine's per-stream modes of this cycle. -/
def mhcModes (m : Machine.State) (pin : Machine.PinIn) : Vector Nat 2 :=
  Vector.ofFn fun k => Machine.streamMode (Machine.cfgView m.cfg).streams[k] k.val m.dbg

/-- The machine's per-stream requests of this cycle. -/
def mhcModesReq (m : Machine.State) (pin : Machine.PinIn) : Vector Machine.RamReq 2 :=
  Vector.ofFn fun k => Machine.streamReq (mhcModes m pin)[k] m.streams[k]

/-- The machine's request list of this cycle. -/
def mhcReqs (m : Machine.State) (pin : Machine.PinIn) : List Machine.RamReq :=
  [(mhcModesReq m pin)[0], (mhcModesReq m pin)[1], Machine.p0Req m.p0, Machine.hostReq m.host]

/-- The machine's arbiter result: the served requester (`0` none, `1` S0, `2` S1,
`3` P0, `4` host). -/
def mhcServed (m : Machine.State) (pin : Machine.PinIn) : Nat :=
  Machine.arbiter ((mhcModesReq m pin)[0]) ((mhcModesReq m pin)[1]) (Machine.p0Req m.p0)
    (Machine.hostReq m.host) m.dbg.frz

/-- The machine's served RAM access of this cycle. -/
def mhcReq (m : Machine.State) (pin : Machine.PinIn) : Machine.RamReq :=
  if mhcServed m pin == 0 then Machine.RamReq.none
  else (mhcReqs m pin).getD (mhcServed m pin - 1) .none

/-- The machine's RAM access of this cycle (new RAM, RAM output, written bytes). -/
def mhcRam (m : Machine.State) (pin : Machine.PinIn) : ByteArray × Nat × List Nat :=
  Machine.ramAccess m.dmem m.ramOut.toNat (mhcReq m pin)

/-- The machine's RAM-output owner of this cycle. -/
def mhcOwner (m : Machine.State) (pin : Machine.PinIn) : Nat :=
  (match mhcReq m pin with
   | .rd _ l => (mhcServed m pin, l)
   | _ => (0, 0)).1

/-- The machine's RAM-output lane of this cycle. -/
def mhcLaneN (m : Machine.State) (pin : Machine.PinIn) : Nat :=
  (match mhcReq m pin with
   | .rd _ l => (mhcServed m pin, l)
   | _ => (0, 0)).2

/-- The machine's host write of this cycle (`W = t`). -/
def mhcHw (m : Machine.State) (pin : Machine.PinIn) : Option Machine.HostWr :=
  (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
    (mhcServed m pin == 4)).2

/-- The machine's configuration-write window (`§1`: the two cycles after `rst_q`
rises). -/
def mhcWindow (m : Machine.State) : Bool := !(Machine.Util.bit m.rqh 0 && Machine.Util.bit m.rqh 1)

/-- The machine's host configuration write offered to the arbiter (`runStep`'s
`hostCfg` local). -/
def mhcHostCfg (m : Machine.State) (pin : Machine.PinIn) : Option (Nat × Nat) :=
  let hw := mhcHw m pin
  let hwIsCfg := match hw with
    | some w => Machine.Config.isCfgAddr w.addr
    | none => false
  if hwIsCfg then hw.map fun w => (w.addr, w.v) else none

/-- The machine's configuration-write result of this cycle. -/
def mhcCwo (m : Machine.State) (pin : Machine.PinIn) : Machine.CwOut :=
  Machine.cwNext m.cw (mhcHostCfg m pin) (mhcCwMove m pin) (mhcWindow m) m.dbg.frz

/-- The machine's core `c` fetch address of this cycle. -/
def mhcFetch (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2) : Option Nat :=
  (mhcCbs m pin)[c].fetch

/-- The machine's program-memory write of this cycle. -/
def mhcPw (m : Machine.State) (pin : Machine.PinIn) : Option (Nat × Nat × Nat) :=
  match mhcHw m pin with
  | some w =>
    if w.addr < Machine.Tables.DATA_BASE then
      some (w.addr / Machine.Tables.STRIDE_PROG_CORE, w.addr % Machine.Tables.STRIDE_PROG_CORE, w.v)
    else none
  | none => none

/-! ## Projection lemmas -/

/-- Indexing a `Vector.ofFn` at a `Fin` is the function value (the `Fin` proof is
irrelevant). -/
theorem vget_ofFn {α : Type} {n : Nat} (f : Fin n → α) (c : Fin n) :
    (Vector.ofFn f)[c] = f c := by simp

/-- The `p0` field of one machine step, from the machine's own locals. -/
theorem step_p0 (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).p0 =
      (Machine.p0Next m.p0 (mhcP0Move m pin) (mhcServed m pin == 3) (m.ramOwner == 3)
        m.ramOut.toNat m.ramLane.toNat m.dbg.frz).1 := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The host request slot of one machine step. -/
theorem step_host_req (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).host.req =
      (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (mhcServed m pin == 4)).1.req := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The host link of one machine step. -/
theorem step_host (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).host =
      (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (mhcServed m pin == 4)).1 := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The configuration-write registers of one machine step. -/
theorem step_cw (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).cw = (mhcCwo m pin).st := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The configuration latches of one machine step (`§1` W+2: the write performed
in `t-1` enters the latches at the end of `t`). -/
theorem step_cfg (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).cfg = Machine.cfgNext m.cfg m.cw := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The program memory of one machine step. -/
theorem step_pmem (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).pmem = (match mhcPw m pin with
      | some (c, a, v) =>
        Machine.Util.vset m.pmem c (Machine.Util.bset (Machine.Util.vget m.pmem c) a v)
      | none => m.pmem) := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  rfl

/-- The data RAM, RAM output register and owner/lane of one machine step. -/
theorem step_ram (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).dmem = (mhcRam m pin).1 ∧
      (Machine.step m pin).ramOut = Machine.Util.bv 32 (mhcRam m pin).2.1 ∧
      (Machine.step m pin).ramOwner = mhcOwner m pin ∧
      (Machine.step m pin).ramLane = Machine.Util.bv 2 (mhcLaneN m pin) := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The program-memory output register of core `c` after one machine step. -/
theorem step_mout (m : Machine.State) (pin : Machine.PinIn)
    (hq : (m.rq && pin.rstn) = true) (c : Fin 2) :
    (Machine.step m pin).cores[c].mout =
      (Machine.coreNext m.cores[c] (Machine.cfgView m.cfg) (mhcCbs m pin)[c]
        ((mhcCbs m pin)[c].fetch.map fun a => Machine.progWord m.pmem[c] a) m.dbg.frz).mout := by
  have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  rw [hmach]
  simp only [Machine.runStep, mhcCbs]
  rw [vget_ofFn]

/-! ## The pointer: `Premises.p0`

`Bridge.Mem.p0_step_eq` gives the *cut's* next pointer from `p0Next (absP0 s.p0)`.
What it does not state is the machine's `stale` bit, the one field where the two
sides differ outside a landing (`Bridge/Mem.lean`'s comment names a
`stale_bridge` that the module does not export).  `p0Next_rel` proves the
`p0Next` congruence (the machine reads `stale` only while landing, `§9a.3`) and
`p0Next_stale_landRdy` proves the stale/`landRdy` correspondence in a landing
cycle. -/

/-- `p0Next` congruence: with `P0Rel a b`, `p0Next a` and `p0Next (absP0 b)`
agree on `ptr`, `d`, `rdy`, `req` and `land`, and on `stale` under a landing. -/
theorem p0Next_rel (a : Machine.P0St) (b : Mem.State) (mv : Option Machine.P0Move)
    (srv landNow : Bool) (ramOut lane : Nat) (frz : Bool) (h : P0Rel a b) :
    (Machine.p0Next a mv srv landNow ramOut lane frz).1.ptr =
        (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.ptr ∧
      (Machine.p0Next a mv srv landNow ramOut lane frz).1.d =
        (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.d ∧
      (Machine.p0Next a mv srv landNow ramOut lane frz).1.rdy =
        (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.rdy ∧
      (Machine.p0Next a mv srv landNow ramOut lane frz).1.req =
        (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.req ∧
      (Machine.p0Next a mv srv landNow ramOut lane frz).1.land =
        (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.land ∧
      ((Machine.p0Next a mv srv landNow ramOut lane frz).1.land = true →
        (Machine.p0Next a mv srv landNow ramOut lane frz).1.stale =
          (Machine.p0Next (Bridge.Mem.absP0 b) mv srv landNow ramOut lane frz).1.stale) := by
  obtain ⟨hptr, hd, hrdy, hreq, hland, hstale⟩ := h
  -- the pointer carrying the machine's stale bit: every field is the abstract one
  have ha' : ({ a with stale := !b.landRdy } : Machine.P0St) = Bridge.Mem.absP0 b := by
    obtain ⟨ap, ad, ar, aq, al, as_⟩ := a
    simp only at hptr hd hrdy hreq hland
    simp only [Bridge.Mem.absP0]
    rw [hptr, hd, hrdy, hreq, hland]
  rw [← ha']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Machine.p0Next]
  · simp only [Machine.p0Next]
  · simp only [Machine.p0Next]
    by_cases hm : mv.isSome = true
    · simp [hm]
    · by_cases hp : (a.land && !frz) = true
      · have hal : a.land = true := (Bool.and_eq_true_iff.mp hp).1
        simp [hm, hp, hstale hal]
      · simp [hm, hp]
  · simp only [Machine.p0Next]
  · simp only [Machine.p0Next]
  · simp only [Machine.p0Next]
    intro hL
    by_cases hg : (srv && (match a.req with
          | Machine.PReq.fetch => true | _ => false)) = true
    · have hgt := Bool.and_eq_true_iff.mp hg
      simp only [hgt.1, hgt.2, true_and]
      split <;> simp_all
    · have h2 : (a.land && !(a.land && !frz)) = true := by
        have h3 : (srv && (match a.req with
              | Machine.PReq.fetch => true | _ => false)) ||
            (a.land && !(a.land && !frz)) = true := hL
        rw [Bool.or_eq_true] at h3
        rcases h3 with hh | hh
        · exact absurd hh hg
        · exact hh
      have hal : a.land = true := (Bool.and_eq_true_iff.mp h2).1
      have hgf : (srv = true ∧ (match a.req with
            | Machine.PReq.fetch => true | _ => false) = true) → False := by
        intro hc
        exact hg (by rw [hc.1, hc.2]; rfl)
      simp [hgf, hstale hal]

/-- The `DbgRel` projection used by the pointer/contents wiring. -/
theorem dbgRel_frz {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.frz = s.freeze.frz := h.2.1

/-- The `DbgRel` projection of `FRZD`. -/
theorem dbgRel_frzd {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    d.frzd = s.freeze.frzd := h.2.2.1

/-! ### Boolean plumbing for the stale/`landRdy` correspondence -/

/-- `!(if c then x else y)` pushes the negation into both branches. -/
theorem not_ite_bool (c x y : Bool) : (!(if c then x else y)) = (if c then !x else !y) := by
  cases c <;> rfl

/-- The pointer move's presence is the move's `pWe` input. -/
theorem mvOf_isSome (i : Mem.Input) : (Bridge.Mem.mvOf i).isSome = i.pWe := by
  unfold Bridge.Mem.mvOf
  by_cases h : i.pWe = true <;> simp [h]

/-- The stale/`landRdy` decision: with a landing (`h`) and the served-fetch guard
false in a frozen cycle (`hfrz`), the machine's `stale` branch is the cut's
`!landRdy` branch. -/
theorem stale_abs (sf mv lrdy frz land : Bool)
    (h : (sf || (land && !(land && !frz))) = true) (hfrz : frz = true → sf = false) :
    (if sf then mv else lrdy) = (if !frz then mv else lrdy) := by
  cases frz <;> cases sf <;> cases land <;> cases mv <;> cases lrdy <;> simp_all

/-- The machine's `stale` bit is the complement of the cut's `landRdy` in a
landing cycle (`stale_bridge`): a served fetch leaves `!landRdy` clear, and a
frozen landing cycle keeps the cut's `landRdy`. -/
theorem p0Next_stale_landRdy (b : Mem.State) (i : Mem.Input) (hreset : i.resetN = true) :
    (Machine.p0Next (Bridge.Mem.absP0 b) (Bridge.Mem.mvOf i) (Mem.grantP0 b i)
        (b.land && !i.frzd) i.ramWord.toNat b.landLane.toNat i.frz).1.land = true →
      (Machine.p0Next (Bridge.Mem.absP0 b) (Bridge.Mem.mvOf i) (Mem.grantP0 b i)
        (b.land && !i.frzd) i.ramWord.toNat b.landLane.toNat i.frz).1.stale =
        !(Mem.step b i).landRdy := by
  intro hL
  simp only [Machine.p0Next, Bridge.Mem.absP0, Mem.step, Mem.landNext, Mem.landRdyNext,
    Mem.grantP0, not_ite_bool, Bool.not_not, hreset] at hL ⊢
  rw [← mvOf_isSome i]
  exact stale_abs _ _ _ _ _ hL (by intro hf; simp [hf])

/-! ## The pointer field -/

/-- `p0Next` reads the lane only through `d' := if landNow then … else p.d`: with
`landNow = false` the lane is irrelevant. -/
theorem p0Next_lane_irrel (p : Machine.P0St) (mv : Option Machine.P0Move)
    (served landNow : Bool) (ramOut l1 l2 : Nat) (fr : Bool) (h : landNow = false) :
    Machine.p0Next p mv served landNow ramOut l1 fr =
      Machine.p0Next p mv served landNow ramOut l2 fr := by
  simp [Machine.p0Next, h]

/-- **`Premises.p0`.**  The next pointer state is related: `Bridge.Mem.p0_step_eq`
on the cut side, the `p0Next` congruence on the machine side, the landing
interface (`p0_open_land`, `p0_open_lane`) and the move/arbiter wiring
(`p0_open_move`, `p0_open_served`).  The lane hypothesis is the `!FRZD`-guarded
`laneInv` form: `p0Next` reads the lane only through its landing data
(`if landNow then … else p.d`), and `landNow` is exactly the guard. -/
theorem premise_p0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (p0_open_move : mhcP0Move m pin = Bridge.Mem.mvOf (memIn s pin))
    (p0_open_served : (mhcServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin))
    (p0_open_land : (m.ramOwner == 3) = (s.p0.land && !(memIn s pin).frzd))
    (p0_open_lane : s.p0.land = true → s.freeze.frzd = false →
      s.cont.ramLane = s.p0.landLane) :
    P0Rel (Machine.step m pin).p0 (activeStep s pin).p0 := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  rw [step_p0 m pin hq]
  have hro : m.ramOut.toNat = (memIn s pin).ramWord.toNat := by
    rw [hrel.ramOut]; rfl
  have hfrz : m.dbg.frz = (memIn s pin).frz := dbgRel_frz hrel.dbg
  rw [p0_open_move, p0_open_served, p0_open_land, hro, hfrz]
  -- `p0Next` reads the lane only when `land && !FRZD`, which is the lane guard
  have hstep : Machine.p0Next m.p0 (Bridge.Mem.mvOf (memIn s pin))
        (Mem.grantP0 s.p0 (memIn s pin)) (s.p0.land && !(memIn s pin).frzd)
        ((memIn s pin).ramWord).toNat m.ramLane.toNat (memIn s pin).frz =
      Machine.p0Next m.p0 (Bridge.Mem.mvOf (memIn s pin))
        (Mem.grantP0 s.p0 (memIn s pin)) (s.p0.land && !(memIn s pin).frzd)
        ((memIn s pin).ramWord).toNat s.p0.landLane.toNat (memIn s pin).frz := by
    by_cases hln : (s.p0.land && !(memIn s pin).frzd) = true
    · have h1 : s.p0.land = true := (Bool.and_eq_true_iff.mp hln).1
      have h2 : (memIn s pin).frzd = false := by
        have h2' := (Bool.and_eq_true_iff.mp hln).2
        simpa using h2'
      have hlr : s.freeze.frzd = false := by simpa [memIn] using h2
      rw [hrel.ramLane, p0_open_lane h1 hlr]
    · exact p0Next_lane_irrel m.p0 (Bridge.Mem.mvOf (memIn s pin))
        (Mem.grantP0 s.p0 (memIn s pin)) (s.p0.land && !(memIn s pin).frzd)
        ((memIn s pin).ramWord).toNat m.ramLane.toNat s.p0.landLane.toNat
        (memIn s pin).frz (by simpa using hln)
  rw [hstep]
  show P0Rel (Machine.p0Next m.p0 (Bridge.Mem.mvOf (memIn s pin))
      (Mem.grantP0 s.p0 (memIn s pin)) (s.p0.land && !(memIn s pin).frzd)
      ((memIn s pin).ramWord).toNat s.p0.landLane.toNat (memIn s pin).frz).1
    (Mem.step s.p0 (memIn s pin))
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
    Bridge.Mem.p0_step_eq s.p0 (memIn s pin) hact hinv.reqNeThree hinv.staleRdy
      (s.p0.land && !(memIn s pin).frzd) ((memIn s pin).ramWord).toNat
      s.p0.landLane.toNat rfl rfl rfl
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
    p0Next_rel m.p0 s.p0 (Bridge.Mem.mvOf (memIn s pin)) (Mem.grantP0 s.p0 (memIn s pin))
      (s.p0.land && !(memIn s pin).frzd) ((memIn s pin).ramWord).toNat
      s.p0.landLane.toNat (memIn s pin).frz hrel.p0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc1.trans hb1.symm
  · exact hc2.trans hb2.symm
  · exact hc3.trans hb3.symm
  · exact hc4.trans hb4.symm
  · exact hc5.trans hb5.symm
  · intro hL
    rw [hc6 hL]
    exact p0Next_stale_landRdy s.p0 (memIn s pin) hact
      (by rw [← hc5]; exact hL)

/-! ## The host slot: `Premises.hostReq`

`Bridge.Mem.slot_step` gives the cut's next host slot from its `hSet`/`hWr`/`hAddr`
input; `Bridge.Mem.hostNext_slot` gives the machine's from `rPend`/`wPend`.  The
remaining wiring facts are the data-window decode (`inData` ↔ the machine's
`DATA_BASE .. DATA_BASE + DATA_BYTES` test, `dataAddr` ↔ the RAM byte address) —
proved below — the served bit (one named hypothesis), and the fact that the write
and read strobes are not simultaneously up (a reachable-state invariant, named
`hostReq_open_strobe`). -/

/-- The data window test of `Wire.lean` at the bit level. -/
theorem inData_bv (a : BitVec 16) :
    inData a = true ↔ (0x1000 : BitVec 16) ≤ a ∧ a < (0x1800 : BitVec 16) := by
  unfold inData dataOff
  bv_decide

/-- The data window test of `Wire.lean` is the data window `0x1000 .. 0x1800` of
the host map. -/
theorem inData_toNat (a : BitVec 16) :
    inData a = true ↔ 0x1000 ≤ a.toNat ∧ a.toNat < 0x1800 := by
  rw [inData_bv]
  constructor
  · rintro ⟨h1, h2⟩
    rw [BitVec.le_def] at h1
    rw [BitVec.lt_def] at h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [BitVec.le_def]; simpa using h1
    · rw [BitVec.lt_def]; simpa using h2

/-- The same test in the machine's `DATA_BASE`/`DATA_BYTES` coordinates. -/
theorem inData_ramWindow (a : BitVec 16) :
    inData a = true ↔ Machine.Tables.DATA_BASE ≤ a.toNat ∧
      a.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES := by
  rw [inData_toNat]
  exact Iff.rfl

/-- The machine's data-window `Bool` test is the cut's `inData`. -/
theorem dataWindow_decide (a : BitVec 16) :
    ((Machine.Tables.DATA_BASE ≤ a.toNat) &&
      (a.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES)) = inData a := by
  unfold Machine.Tables.DATA_BASE Machine.Tables.DATA_BYTES
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, inData_toNat]

/-- The machine's write-window test with the write strobe in front. -/
theorem and_window (w : Bool) (a : BitVec 16) :
    ((w && (Machine.Tables.DATA_BASE ≤ a.toNat) &&
      (a.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES))) =
      (w && inData a) := by
  rw [Bool.and_assoc, dataWindow_decide]

/-- A window offset subtraction does not wrap when the address is in the
window. -/
theorem sub1000_toNat (a : BitVec 16) (h : 0x1000 ≤ a.toNat) :
    (a - 0x1000).toNat = a.toNat - 0x1000 := by
  apply BitVec.toNat_sub_of_not_usubOverflow
  have hno : BitVec.usubOverflow a (0x1000 : BitVec 16) = false := by
    simp only [BitVec.usubOverflow, decide_eq_false_iff_not]
    have h4096 : (BitVec.toNat (0x1000 : BitVec 16)) = 4096 := by decide
    omega
  simpa using hno

/-- The host-map data address is the machine's RAM byte address in the window. -/
theorem dataAddr_eq (a : BitVec 16) (h : inData a = true) :
    HostMap.dataAddr a = Machine.Util.bv 11 (a.toNat - 0x1000) := by
  have hsub := sub1000_toNat a ((inData_toNat a).mp h).1
  apply BitVec.eq_of_toNat_eq
  simp only [HostMap.dataAddr, HostMap.base, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Machine.Util.bv, BitVec.toNat_ofNat]
  rw [hsub]

/-- The machine's data-window test as a `Nat` hypothesis pair. -/
theorem dataWindow_test (a : Nat) (h1 : Machine.Tables.DATA_BASE ≤ a)
    (h2 : a < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) :
    (Machine.Tables.DATA_BASE ≤ a && a < Machine.Tables.DATA_BASE +
      Machine.Tables.DATA_BYTES) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

/-- A host read of a data-window address is a data-RAM read at the window
offset. -/
theorem hostRead_inr (m : Machine.State) (cv : Machine.CfgView) (a : Nat)
    (h1 : Machine.Tables.DATA_BASE ≤ a)
    (h2 : a < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) :
    Machine.hostRead m cv a = .inr (a - Machine.Tables.DATA_BASE) := by
  simp only [Machine.hostRead]
  rw [if_pos (dataWindow_test a h1 h2)]

/-- A host read outside the data window is never a data-RAM read. -/
theorem hostRead_not_inr (m : Machine.State) (cv : Machine.CfgView) (a : Nat)
    (h : ¬ (Machine.Tables.DATA_BASE ≤ a ∧
      a < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES)) :
    ∀ v, Machine.hostRead m cv a ≠ .inr v := by
  intro v hv
  simp only [Machine.hostRead] at hv
  rw [if_neg (by
    intro hc
    rw [Bool.and_eq_true] at hc
    exact h ⟨(decide_eq_true_eq.mp hc.1), (decide_eq_true_eq.mp hc.2)⟩)] at hv
  cases hloc : Machine.hostLocate a <;> simp_all

/-- **The machine's new host request of this cycle** is the cut's.  A read
request wins on the machine side exactly when the address is in the data window
(`hostRead_inr`), the write strobe is the same (`LinkRel.wr`), and the write and
read strobes are never up together (`hstrobe`); outside the window neither side
issues a data-RAM request. -/
theorem hostNew_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hstrobe : ¬ (s.hostCmd.wr = true ∧ s.hostCmd.rd = true)) :
    (match (if m.host.rPend then
        some (Machine.hostRead m (Machine.cfgView m.cfg) m.host.addr.toNat) else none) with
      | some (.inr a) => some (Machine.HReq.read (Machine.Util.bv 11 a))
      | _ => if m.host.wPend && Machine.Tables.DATA_BASE ≤ m.host.addr.toNat &&
            m.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES then
          some (Machine.HReq.write
            (Machine.Util.bv 11 (m.host.addr.toNat - Machine.Tables.DATA_BASE)) m.host.wData)
        else none)
      = (if ((s.hostCmd.wr || s.hostCmd.rd) && inData s.hostCmd.addr) then
          some (if s.hostCmd.wr then
            Machine.HReq.write (HostMap.dataAddr s.hostCmd.addr) s.hostCmd.wdata
          else Machine.HReq.read (HostMap.dataAddr s.hostCmd.addr))
        else none) := by
  have hagree : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
    HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
  have hlink : Bridge.Host.LinkRel s.hostCmd m := by
    rw [← hagree]
    exact hrel.host.base
  have hrd : m.host.rPend = s.hostCmd.rd := hlink.rd.symm
  have hwr : m.host.wPend = s.hostCmd.wr := hlink.wr.symm
  have haddr : m.host.addr = s.hostCmd.addr := hlink.addr.symm
  have hwdata : m.host.wPend = true → m.host.wData = s.hostCmd.wdata := by
    intro h
    exact (hlink.wdata (by rw [← hwr]; exact h)).symm
  rw [hrd, hwr, haddr]
  -- the outside-window form of the machine's window test
  have houtF : ∀ (h : inData s.hostCmd.addr = false),
      ¬ (Machine.Tables.DATA_BASE ≤ s.hostCmd.addr.toNat ∧
        s.hostCmd.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) := by
    intro h hc
    have hb : ((Machine.Tables.DATA_BASE ≤ s.hostCmd.addr.toNat) &&
        (s.hostCmd.addr.toNat < Machine.Tables.DATA_BASE +
          Machine.Tables.DATA_BYTES)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact hc
    rw [dataWindow_decide, h] at hb
    exact Bool.false_ne_true hb
  cases hw : s.hostCmd.wr
  case false =>
    cases hr : s.hostCmd.rd
    case false =>
      cases hin : inData s.hostCmd.addr <;> simp [hw, hr, hin, and_window]
    case true =>
      cases hin : inData s.hostCmd.addr
      case true =>
        obtain ⟨hlo, hhi⟩ := (inData_toNat s.hostCmd.addr).mp hin
        rw [hostRead_inr m (Machine.cfgView m.cfg) s.hostCmd.addr.toNat
          (by show (0x1000 : Nat) ≤ _; exact hlo)
          (by show _ < (0x1800 : Nat); exact hhi)]
        simp [hw, hr, hin, dataAddr_eq s.hostCmd.addr hin, Machine.Tables.DATA_BASE]
      case false =>
        have hnotinr := hostRead_not_inr m (Machine.cfgView m.cfg) s.hostCmd.addr.toNat
          (houtF hin)
        cases hread : Machine.hostRead m (Machine.cfgView m.cfg) s.hostCmd.addr.toNat
        · simp [hw, hr, hin]
        · exact absurd hread (hnotinr _)
  case true =>
    cases hr : s.hostCmd.rd
    case false =>
      cases hin : inData s.hostCmd.addr
      case true =>
        obtain ⟨hlo, hhi⟩ := (inData_toNat s.hostCmd.addr).mp hin
        have hlo' : (0x1000 : Nat) ≤ s.hostCmd.addr.toNat := hlo
        have hhi' : s.hostCmd.addr.toNat < (0x1800 : Nat) := hhi
        simp [hw, hr, hin, and_window, dataAddr_eq s.hostCmd.addr hin,
          hwdata (by rw [hwr]; exact hw), hlo', hhi', decide_eq_true_eq,
          Machine.Tables.DATA_BASE, Machine.Tables.DATA_BYTES]
      case false =>
        simp only [hw, hr, hin, and_window, Bool.and_false, Bool.false_eq_true, if_false]
    case true =>
      exact absurd ⟨hw, hr⟩ hstrobe

/-- **`Premises.hostReq`.**  The machine's host data-RAM slot after the step is
the cut's `absSlot` of its next pointer state: the same served grant
(`hostReq_open_served`) and the same newly issued request (`hostNew_eq`). -/
theorem premise_hostReq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hostReq_open_served : (mhcServed m pin == 4) = Mem.grantHost s.p0 (memIn s pin))
    (hostReq_open_strobe : ¬ (s.hostCmd.wr = true ∧ s.hostCmd.rd = true)) :
    (Machine.step m pin).host.req = Bridge.Mem.absSlot (activeStep s pin).p0 := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  rw [step_host_req m pin hq,
    Bridge.Mem.hostNext_slot m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)]
  have hcut := Bridge.Mem.slot_step s.p0 (memIn s pin) hact
  rw [show (activeStep s pin).p0 = Mem.step s.p0 (memIn s pin) from rfl, hcut]
  rw [hrel.hostReq, hostReq_open_served]
  congr 1
  show (match (if m.host.rPend then
        some (Machine.hostRead m (Machine.cfgView m.cfg) m.host.addr.toNat) else none) with
      | some (.inr a) => some (Machine.HReq.read (Machine.Util.bv 11 a))
      | _ => if m.host.wPend && Machine.Tables.DATA_BASE ≤ m.host.addr.toNat &&
            m.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES then
          some (Machine.HReq.write
            (Machine.Util.bv 11 (m.host.addr.toNat - Machine.Tables.DATA_BASE)) m.host.wData)
        else none)
      = (if ((s.hostCmd.wr || s.hostCmd.rd) && inData s.hostCmd.addr) then
          some (if s.hostCmd.wr then
            Machine.HReq.write (HostMap.dataAddr s.hostCmd.addr) s.hostCmd.wdata
          else Machine.HReq.read (HostMap.dataAddr s.hostCmd.addr))
        else none)
  exact hostNew_eq s m pin hrel hinv hostReq_open_strobe

/-! ## The host link: `Premises.host`

`Bridge.Host.linkRelR_step` needs the pin view of the cut's sampled pins
(proved here from `SyncRel`), the register/data-window decode (`regRead`, proved
here), the RAM landing byte (from `Contents`), and two named facts: the
register-read value (`host_open_regVal`: the machine's register decode on the
related states, the trusted chip-top interface the cut uses) and the
completing-cycle quietness (`host_open_quiet`: a write strobe or a `rack`/landing
acknowledgement never coincides with the 8th bit of a byte — a one-cycle-pulse
property of reachable link states, not of an arbitrary state). -/

/-- Sampled SCK: bit 8 of `{ui, uio}` is `ui[0]`. -/
theorem pin_sck_eq (a b : BitVec 8) :
    SpiPins.bit (a ++ b) 8 = Machine.Util.bit a 0 := by
  unfold SpiPins.bit Machine.Util.bit
  bv_decide

/-- Sampled `CS_N`: bit 9 of `{ui, uio}` is `ui[1]`. -/
theorem pin_csn_eq (a b : BitVec 8) :
    SpiPins.bit (a ++ b) 9 = Machine.Util.bit a 1 := by
  unfold SpiPins.bit Machine.Util.bit
  bv_decide

/-- Sampled MOSI: bit 10 of `{ui, uio}` is `ui[2]`. -/
theorem pin_mosi_eq (a b : BitVec 8) :
    SpiPins.bit (a ++ b) 10 = Machine.Util.bit a 2 := by
  unfold SpiPins.bit Machine.Util.bit
  bv_decide

/-- The cut's sampled SCK is the machine's `PinView.sck`. -/
theorem sck_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    SpiPins.sck s.sync = (Machine.pinView m.sync m.dbg).sck := by
  obtain ⟨-, hs2, -⟩ := hrel.sync
  rw [SpiPins.sck, hs2]
  exact pin_sck_eq m.sync.ui2 m.sync.uio2

/-- The cut's sampled `CS_N` is the machine's `PinView.csn`. -/
theorem csN_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    SpiPins.csN s.sync = (Machine.pinView m.sync m.dbg).csn := by
  obtain ⟨-, hs2, -⟩ := hrel.sync
  rw [SpiPins.csN, hs2]
  exact pin_csn_eq m.sync.ui2 m.sync.uio2

/-- The cut's sampled MOSI is the machine's `PinView.mosi`. -/
theorem mosi_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    SpiPins.mosi s.sync = (Machine.pinView m.sync m.dbg).mosi := by
  obtain ⟨-, hs2, -⟩ := hrel.sync
  rw [SpiPins.mosi, hs2]
  exact pin_mosi_eq m.sync.ui2 m.sync.uio2

/-- The cut's rising SCK edge is the machine's `PinView.sckRise`. -/
theorem sckRise_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (SpiPins.sck s.sync && !SpiPins.sckPrev s.sync) =
      (Machine.pinView m.sync m.dbg).sckRise := by
  obtain ⟨-, hs2, hsp⟩ := hrel.sync
  rw [SpiPins.sck, SpiPins.sckPrev, hs2, hsp]
  simp only [Machine.pinView]
  rw [pin_sck_eq m.sync.ui2 m.sync.uio2, pin_sck_eq m.sync.uip m.sync.uiop]

/-- The host-link input's pin view is the machine's `PinView` on the pins the
link reads. -/
theorem pinOf_hostReadIn (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) :
    (Bridge.Host.pinOfR (hostReadIn s pin)).sck = (Machine.pinView m.sync m.dbg).sck ∧
      (Bridge.Host.pinOfR (hostReadIn s pin)).csn = (Machine.pinView m.sync m.dbg).csn ∧
      (Bridge.Host.pinOfR (hostReadIn s pin)).mosi = (Machine.pinView m.sync m.dbg).mosi ∧
      (Bridge.Host.pinOfR (hostReadIn s pin)).sckRise =
        (Machine.pinView m.sync m.dbg).sckRise := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sck_bridge s m hrel
  · exact csN_bridge s m hrel
  · exact mosi_bridge s m hrel
  · exact sckRise_bridge s m hrel

/-- `hostNext` reads only `csn`, `sckRise` and `mosi` of its pin view. -/
theorem hostNext_pin_congr (m : Machine.State) (cv : Machine.CfgView)
    (p p' : Machine.PinView) (served : Bool)
    (hcsn : p.csn = p'.csn) (hrise : p.sckRise = p'.sckRise) (hmosi : p.mosi = p'.mosi) :
    (Machine.hostNext m cv p served).1 = (Machine.hostNext m cv p' served).1 := by
  simp only [Machine.hostNext, hcsn, hrise, hmosi]

/-- The `regRead` test is the complement of the machine's data-window test. -/
theorem regRead_eq (m : Machine.State) (cv : Machine.CfgView) :
    Bridge.Host.regRead m cv =
      !((Machine.Tables.DATA_BASE ≤ m.host.addr.toNat) &&
        (m.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES)) := by
  unfold Bridge.Host.regRead
  simp only [Machine.hostRead]
  by_cases h : ((Machine.Tables.DATA_BASE ≤ m.host.addr.toNat) &&
      (m.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES)) = true
  · rw [if_pos h]
    simp [h]
  · have hf : ((Machine.Tables.DATA_BASE ≤ m.host.addr.toNat) &&
        (m.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES)) = false := by
      cases hv : ((Machine.Tables.DATA_BASE ≤ m.host.addr.toNat) &&
          (m.host.addr.toNat < Machine.Tables.DATA_BASE +
            Machine.Tables.DATA_BYTES)) <;> simp_all
    rw [if_neg h]
    cases Machine.hostLocate m.host.addr.toNat <;> simp [hf]

/-- The `LinkRel` on the cut's own command state (from `Inv.hostAgrees`). -/
theorem linkRel_cut (s : State) (m : Machine.State) (hinv : Inv s) (hrel : ChipRel s m) :
    Bridge.Host.LinkRel s.hostCmd m := by
  have hagree : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
    HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
  rw [← hagree]
  exact hrel.host.base

/-- The register-read test agrees: both sides ask whether the address is outside
the data window. -/
theorem regRead_bridge (s : State) (m : Machine.State) (hinv : Inv s) (hrel : ChipRel s m) :
    Bridge.Host.regRead (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regRead m (Machine.cfgView m.cfg) := by
  have haddr : m.host.addr = s.hostCmd.addr := (linkRel_cut s m hinv hrel).addr.symm
  rw [regRead_eq, regRead_eq]
  rw [show (absChip s).host.addr = s.hostCmd.addr from rfl, haddr]

/-- The RAM landing byte agrees (`Contents`'s RAM output and lane). -/
theorem ramByte_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Bridge.Host.ramByte (absChip s) = Bridge.Host.ramByte m := by
  simp only [Bridge.Host.ramByte, absChip, hrel.ramOut, hrel.ramLane]

/-- **`Premises.host`.**  `Bridge.Host.linkRelR_step` with the pin view of the
cut's sampled pins, the landing byte, the `regRead` decode, and the two named
side conditions. -/
theorem premise_host (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (host_open_regVal : Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg))
    (host_open_quiet : HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd)
        (hostReadIn s pin).toHostCmd = true →
      (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false ∧
        HostCmd.ackBit (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd =
          false) :
    Bridge.Host.LinkRelR (activeStep s pin).hostRead (activeStep s pin).hostCmd.cmd
      (Machine.step m pin) := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  obtain ⟨-, hpincsn, hpinmosi, hpinrise⟩ := pinOf_hostReadIn s m pin hrel
  have hstep := Bridge.Host.linkRelR_step s.hostRead s.hostCmd.cmd m
    (hostReadIn s pin) (Machine.cfgView m.cfg) (mhcServed m pin == 4) hact hrel.host
    (by rw [hostReadIn, hostLand, hrel.ramOwner])
    (by rw [hostReadIn, regRead_bridge s m hinv hrel])
    (by rw [hostReadIn, ramByte_bridge s m hrel])
    (by rw [hostReadIn, host_open_regVal])
    host_open_quiet
  have hcutEq : HostCmd.step (s.hostRead.toHostCmd s.hostCmd.cmd)
      (hostReadIn s pin).toHostCmd = HostCmd.step s.hostCmd (hostCmdIn s pin) := by
    have hagree : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
      HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
    rw [← hagree]
    rfl
  have hpinEq : (Machine.hostNext m (Machine.cfgView m.cfg)
        (Bridge.Host.pinOfR (hostReadIn s pin)) (mhcServed m pin == 4)).1 =
      (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (mhcServed m pin == 4)).1 :=
    hostNext_pin_congr m (Machine.cfgView m.cfg) _ _ _
      hpincsn hpinrise hpinmosi
  refine linkRelR_host_congr
    (m' := { m with host := (Machine.hostNext m (Machine.cfgView m.cfg)
      (Bridge.Host.pinOfR (hostReadIn s pin)) (mhcServed m pin == 4)).1 }) ?_ ?_
  · show (Machine.step m pin).host = (Machine.hostNext m (Machine.cfgView m.cfg)
      (Bridge.Host.pinOfR (hostReadIn s pin)) (mhcServed m pin == 4)).1
    rw [step_host m pin hq]
    exact hpinEq.symm
  · change Bridge.Host.LinkRelR (HostRead.step s.hostRead (hostReadIn s pin))
      (HostCmd.step s.hostCmd (hostCmdIn s pin)).cmd
      { m with host := (Machine.hostNext m (Machine.cfgView m.cfg)
        (Bridge.Host.pinOfR (hostReadIn s pin)) (mhcServed m pin == 4)).1 }
    rw [← hcutEq]
    exact hstep

/-! ## The latch bank: `Premises.bank`

`Step.lean` steps the bank with the arbiter's **stage** state
(`s.arb.previousWrite`, `s.arb.staged`), which is what `Bank.lean` specifies (the
`we1`/`addr1`/`data1` registered in the stage, visible from W+2) and exactly what
`Machine.cfgNext` applies (`§1` W+2).  `CwRel` identifies the two stage states
(`bwp` with `previousWrite`, and the guarded payloads with `staged.addr` /
`staged.data`).
The relation carries the fixed RTL mask. Full image size guarantees that
each implemented byte is writable. -/

/-- A byte write to an in-range index. -/
theorem bget_bset_self (a : ByteArray) (i v : Nat) (h : i < a.size) :
    Machine.Util.bget (Machine.Util.bset a i v) i = v % 256 := by
  obtain ⟨bs⟩ := a
  simp only [Machine.Util.bget, Machine.Util.bset, ByteArray.size, ByteArray.get!, ByteArray.set!]
    at h ⊢
  rw [if_pos h, Array.getElem!_set!_self bs i (UInt8.ofNat (v % 256)) h]
  simp

/-- A byte write to another index leaves the byte alone. -/
theorem bget_bset_ne (a : ByteArray) (i j v : Nat) (hij : i ≠ j) :
    Machine.Util.bget (Machine.Util.bset a i v) j = Machine.Util.bget a j := by
  obtain ⟨bs⟩ := a
  simp only [Machine.Util.bget, Machine.Util.bset, ByteArray.size, ByteArray.get!, ByteArray.set!]
  by_cases h : i < bs.size
  · rw [if_pos h, Array.getElem!_set!_ne bs i j (UInt8.ofNat (v % 256)) hij]
  · rw [if_neg h]

/-- The bank offset of a byte is its index. -/
theorem bank_addrOf_toNat (k : Fin Bank.BYTES) : (Bank.addrOf k).toNat = k.val := by
  simp only [Bank.addrOf, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans k.isLt (by decide : Bank.BYTES < 512))

/-- A nine-bit address whose value is a byte index is that offset. -/
theorem bank_addr_of_toNat {a : BitVec 9} {k : Fin Bank.BYTES} (h : a.toNat = k.val) :
    a = Bank.addrOf k := by
  apply BitVec.eq_of_toNat_eq
  rw [h, bank_addrOf_toNat]

/-- The machine's performed-write address, as a `Nat`. -/
theorem bpa_toNat (staged_addr : BitVec 9) :
    (Machine.Util.bv 16 (Bridge.CfgWrite.addrOf staged_addr)).toNat
      = Machine.Tables.LINE_BASE + staged_addr.toNat := by
  rw [Machine.Util.bv, BitVec.toNat_ofNat, Bridge.CfgWrite.addrOf, Bridge.CfgWrite.CFG_LO,
    Machine.Tables.LINE_BASE, Nat.mod_eq_of_lt]
  have := staged_addr.isLt
  omega

/-- The configuration byte at the written offset, after a performed write. -/
theorem cfgByte_write_self (c : Machine.Config) (a v o : Nat)
    (hsize : c.img.size = Machine.Util.cfgSize)
    (hcfg : Machine.Config.isCfgAddr a = true)
    (hidx : a - Machine.Tables.LINE_BASE = o) (ho : o < Machine.Util.cfgSize) :
    Machine.Util.cfgByte (Machine.Config.write c a v) (Machine.Tables.LINE_BASE + o)
      = v % 256 := by
  have hwr : Machine.Config.write c a v
      = ⟨Machine.Util.bset c.img (a - Machine.Tables.LINE_BASE) v⟩ := by
    simp only [Machine.Config.write, hcfg]
    rfl
  rw [hwr]
  simp only [Machine.Util.cfgByte]
  rw [show Machine.Tables.LINE_BASE + o - Machine.Tables.LINE_BASE = o from by omega, ← hidx]
  exact bget_bset_self c.img (a - Machine.Tables.LINE_BASE) v (by rw [hsize]; omega)

/-- The configuration byte at another offset is unchanged by a performed
write. -/
theorem cfgByte_write_ne (c : Machine.Config) (a v o : Nat)
    (hcfg : Machine.Config.isCfgAddr a = true)
    (hne : a - Machine.Tables.LINE_BASE ≠ o) :
    Machine.Util.cfgByte (Machine.Config.write c a v) (Machine.Tables.LINE_BASE + o)
      = Machine.Util.cfgByte c (Machine.Tables.LINE_BASE + o) := by
  have hwr : Machine.Config.write c a v
      = ⟨Machine.Util.bset c.img (a - Machine.Tables.LINE_BASE) v⟩ := by
    simp only [Machine.Config.write, hcfg]
    rfl
  rw [hwr]
  simp only [Machine.Util.cfgByte]
  rw [show Machine.Tables.LINE_BASE + o - Machine.Tables.LINE_BASE = o from by omega]
  exact bget_bset_ne c.img (a - Machine.Tables.LINE_BASE) o v hne

/-- A configuration write at another offset leaves the byte alone (or does not
happen at all). -/
theorem cfgByte_cfgNext_ne (c : Machine.Config) (a v o : Nat)
    (hne : a - Machine.Tables.LINE_BASE ≠ o) :
    Machine.Util.cfgByte (Machine.Config.write c a v) (Machine.Tables.LINE_BASE + o)
      = Machine.Util.cfgByte c (Machine.Tables.LINE_BASE + o) := by
  by_cases hcfg : Machine.Config.isCfgAddr a = true
  · exact cfgByte_write_ne c a v o hcfg hne
  · have hwr : Machine.Config.write c a v = c := by
      simp [Machine.Config.write, hcfg]
    rw [hwr]

/-- A nonzero mask byte of a related bank is accepted by the machine decoder. -/
theorem bank_live_cfg {b : Bank.State} {c : Machine.Config} (h : BankRel b c)
    (k : Fin Bank.BYTES) (hk : b.mask k ≠ 0) :
    Machine.Config.isCfgAddr (Machine.Tables.LINE_BASE + k.val) = true := by
  apply BankWire.cfgMask_live_cfg k
  simpa only [h.1] using hk

/-- The observable latch outputs decode to the configuration used by the cuts. -/
theorem bank_decode_of_rel {b : Bank.State} {c : Machine.Config} (h : BankRel b c) :
    Machine.cfgView (BankWire.bankImg b) = Machine.cfgView c ∧
    ∀ i : Fin 2, (BankWire.bankImg b).poly i.val = c.poly i.val := by
  have hread (k : Fin Bank.BYTES) :
      Bank.read b k = BitVec.ofNat 8 (Machine.Util.bget c.img k.val) &&& BankWire.cfgMaskFin k := by
    simpa only [h.1, Machine.Util.cfgByte, Nat.add_sub_cancel_left] using h.2 k
  exact ⟨BankWire.cfgView_bankImg b c hread, BankWire.cfgPoly_bankImg b c hread⟩

/-- **`Premises.bank`.** The staged write preserves all implemented bits of
the latch-image relation, including partially latched bytes. -/
theorem premise_bank (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (bank_open_size : m.cfg.img.size = Machine.Util.cfgSize) :
    BankRel (activeStep s pin).bank (Machine.step m pin).cfg := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  obtain ⟨-, -, -, -, hbwp, -, hbpa, hbpd, -, -⟩ := hrel.cw
  rw [step_cfg m pin hq]
  refine ⟨hrel.bank.1, ?_⟩
  intro k
  change Bank.read (Bank.step s.bank s.arb.previousWrite s.arb.staged.addr
      s.arb.staged.data) k =
    BitVec.ofNat 8 (Machine.Util.cfgByte (Machine.cfgNext m.cfg m.cw)
      (Machine.Tables.LINE_BASE + k.val)) &&& s.bank.mask k
  rw [Bank.step_read]
  by_cases hk : s.bank.mask k = 0
  · split <;> simp [Bank.read, hk]
  have hklt : k.val < Machine.Util.cfgSize := by
    rw [BankWire.cfgSize_eq]
    exact k.isLt
  by_cases hw : s.arb.previousWrite = true
  · have hbwp' : m.cw.bwp = true := by rw [hbwp]; exact hw
    have hbpaN : m.cw.bpa.toNat = Machine.Tables.LINE_BASE + s.arb.staged.addr.toNat := by
      rw [hbpa hbwp']; exact bpa_toNat s.arb.staged.addr
    have hbpdN : m.cw.bpd.toNat = s.arb.staged.data.toNat := by rw [hbpd hbwp']
    rw [Machine.cfgNext, if_pos hbwp', hbpaN, hbpdN]
    by_cases hidx : s.arb.staged.addr.toNat = k.val
    · have hg : Bank.gateOpen s.arb.previousWrite s.arb.staged.addr k = true :=
        Bank.gateOpen_eq_true.mpr ⟨hw, bank_addr_of_toNat hidx⟩
      rw [if_pos hg, hidx]
      rw [cfgByte_write_self m.cfg (Machine.Tables.LINE_BASE + k.val) s.arb.staged.data.toNat
        k.val bank_open_size (bank_live_cfg hrel.bank k hk) (by omega) hklt,
        Nat.mod_eq_of_lt s.arb.staged.data.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hg : ¬Bank.gateOpen s.arb.previousWrite s.arb.staged.addr k = true := by
        intro hg
        exact hidx (by rw [(Bank.gateOpen_eq_true.mp hg).2, bank_addrOf_toNat])
      rw [if_neg hg, cfgByte_cfgNext_ne m.cfg
        (Machine.Tables.LINE_BASE + s.arb.staged.addr.toNat) s.arb.staged.data.toNat
        k.val (by omega)]
      exact hrel.bank.2 k
  · have hbwp' : m.cw.bwp ≠ true := by rwa [hbwp]
    have hg : ¬Bank.gateOpen s.arb.previousWrite s.arb.staged.addr k = true :=
      fun hg => hw (Bank.gateOpen_eq_true.mp hg).1
    rw [if_neg hg, Machine.cfgNext, if_neg hbwp']
    exact hrel.bank.2 k

/-- Applying a staged write preserves the configuration image length. -/
theorem cfgNext_img_size (c : Machine.Config) (cw : Machine.CwSt) :
    (Machine.cfgNext c cw).img.size = c.img.size := by
  unfold Machine.cfgNext
  split
  · unfold Machine.Config.write
    split
    · unfold Machine.Util.bset
      split
      · exact ByteArray.size_set! _ _ _
      · rfl
    · rfl
  · rfl

/-- A full configuration image stays full, including across resets. -/
theorem step_cfg_size (m : Machine.State) (pin : Machine.PinIn)
    (hsize : m.cfg.img.size = Machine.Util.cfgSize) :
    (Machine.step m pin).cfg.img.size = Machine.Util.cfgSize := by
  by_cases hr : (m.rq && pin.rstn) = true
  · rw [step_cfg m pin hr, cfgNext_img_size, hsize]
  · have hfalse : (m.rq && pin.rstn) = false := by simpa using hr
    have hstep : Machine.step m pin = Machine.resetStep m pin := by
      simp [Machine.step, Machine.stepObs, hfalse]
    rw [hstep]
    cases hp : pin.rstn
    · simp [Machine.resetStep, hp, Machine.Config.zero, Machine.Util.bzero, ByteArray.size]
    · simp [Machine.resetStep, hp, cfgNext_img_size, hsize]

/-- The assembler can use the image-size requirement solely at time zero. -/
theorem trace_cfg_size (pins : Nat → Machine.PinIn) (m : Machine.State)
    (hsize : m.cfg.img.size = Machine.Util.cfgSize) (n : Nat) :
    (machineStateAt pins m n).cfg.img.size = Machine.Util.cfgSize := by
  induction n with
  | zero => exact hsize
  | succ n ih =>
    rw [machineStateAt_succ]
    exact step_cfg_size _ _ ih

/-! ## The contents: `Premises.contents`

`ContentsEq` compares the machine's own memory/config path after the step with the
same path of the canonical abstraction (`contentsNext` is `runStep (absChip s)`),
so it is a *machine-vs-machine congruence*.  The configuration byte, the program
memory, the host-write agreement and the `coreNext` memory-output congruence are
proved; the program-memory output and the RAM path need the per-cycle core bundle
and the arbiter's served request to agree with the abstraction
(`contents_open_cbs`, `contents_open_req`, `contents_open_served`). -/

/-- The host write of the cycle agrees: same strobe, same address, and the same
data byte while the strobe is up. -/
theorem mhcHw_bridge (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hinv : Inv s) (hrel : ChipRel s m) : mhcHw m pin = mhcHw (absChip s) pin := by
  have hlink : Bridge.Host.LinkRel s.hostCmd m := linkRel_cut s m hinv hrel
  have hwr : m.host.wPend = s.hostCmd.wr := hlink.wr.symm
  have haddr : m.host.addr = s.hostCmd.addr := hlink.addr.symm
  have hwdata : m.host.wPend = true → m.host.wData = s.hostCmd.wdata := by
    intro h
    exact (hlink.wdata (by rw [← hwr]; exact h)).symm
  have h1 : mhcHw m pin = (if m.host.wPend then some ⟨m.host.addr.toNat, m.host.wData.toNat,
      Machine.hostLocate m.host.addr.toNat⟩ else none) := rfl
  have h2 : mhcHw (absChip s) pin = (if s.hostCmd.wr then some ⟨s.hostCmd.addr.toNat,
      s.hostCmd.wdata.toNat, Machine.hostLocate s.hostCmd.addr.toNat⟩ else none) := rfl
  rw [h1, h2, hwr, haddr]
  by_cases hw : s.hostCmd.wr = true
  · have hwd : m.host.wData = s.hostCmd.wdata := hwdata (by rw [hwr]; exact hw)
    rw [hw, hwd]
  · have hwf : s.hostCmd.wr = false := by cases h : s.hostCmd.wr <;> simp_all
    rw [hwf]
    simp only [Bool.false_eq_true, if_false]

/-- `coreNext`'s memory output depends only on the read fields of the core. -/
theorem coreNext_mout_congr (a b : Machine.CoreSt) (cv : Machine.CfgView)
    (cb : Machine.CoreComb) (word : Option Nat) (frozen : Bool)
    (hmout : a.mout = b.mout) :
    (Machine.coreNext a cv cb word frozen).mout = (Machine.coreNext b cv cb word frozen).mout := by
  by_cases hf : frozen = true
  · simp [Machine.coreNext, hf, hmout]
  · have hf' : frozen = false := by cases frozen <;> simp_all
    cases word with
    | none => simp [Machine.coreNext, hf', hmout]
    | some w => simp [Machine.coreNext, hf']

/-- The canonical abstraction's program-memory output register. -/
theorem absChip_mout (s : State) (c : Fin 2) : (absChip s).cores[c].mout = s.cont.mout[c.val] := by
  simp [absChip, Bridge.Core.absCore, vget_ofFn]

/-- Indexing a `Vector.ofFn` at a `Nat` index. -/
theorem vgetNat_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, h⟩ :=
  vget_ofFn f ⟨i, h⟩

/-- **`Premises.contents`.**  The configuration byte and the program memory are
proved from `ChipRel`; the program-memory output and the RAM path are a
machine-vs-machine congruence whose remaining inputs are the per-cycle core
bundle and the arbiter's served request
(`contents_open_cbs`, `contents_open_req`, `contents_open_served`). -/
theorem premise_contents (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (contents_open_cbs : ∀ c : Fin 2, (mhcCbs m pin)[c] = (mhcCbs (absChip s) pin)[c])
    (contents_open_req : mhcReq m pin = mhcReq (absChip s) pin)
    (contents_open_served : mhcServed m pin = mhcServed (absChip s) pin) :
    ContentsEq s m pin := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hq2 : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hact
  have hmach : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hq2]
  have hhw : mhcHw m pin = mhcHw (absChip s) pin := mhcHw_bridge s m pin hinv hrel
  have hpw : mhcPw m pin = mhcPw (absChip s) pin := by simp only [mhcPw, hhw]
  have hfrz : m.dbg.frz = (absChip s).dbg.frz := by rw [dbgRel_frz hrel.dbg]; rfl
  have hcfgA : (absChip s).cfg = s.cont.cfg := rfl
  have hpmemA : (absChip s).pmem = s.cont.pmem := rfl
  have hdmemA : (absChip s).dmem = s.cont.dmem := rfl
  have hramOutA : (absChip s).ramOut = s.cont.ramOut := rfl
  have hram : mhcRam m pin = mhcRam (absChip s) pin := by
    simp only [mhcRam, hrel.dmem, hrel.ramOut, hdmemA, hramOutA, contents_open_req]
  have howner : mhcOwner m pin = mhcOwner (absChip s) pin := by
    simp only [mhcOwner, contents_open_req, contents_open_served]
  have hlaneN : mhcLaneN m pin = mhcLaneN (absChip s) pin := by
    simp only [mhcLaneN, contents_open_req, contents_open_served]
  have hramM := step_ram m pin hq
  have hramA := step_ram (absChip s) pin hq2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- program-memory output
    intro c
    rw [step_mout m pin hq c]
    have hcont : (activeStep s pin).cont.mout[c.val] =
        (Machine.step (absChip s) pin).cores[c].mout := by
      show (contentsNext s pin).mout[c.val] = _
      simp only [contentsNext]
      rw [vgetNat_ofFn _ _ c.isLt, ← hmach]
      rfl
    rw [hcont, step_mout (absChip s) pin hq2 c]
    have hcs : m.cores[c].mout = (absChip s).cores[c].mout := by
      rw [hrel.mout c]
      exact (absChip_mout s c).symm
    rw [contents_open_cbs c, hrel.cfg, hcfgA, hrel.pmem, hpmemA, hfrz]
    exact coreNext_mout_congr m.cores[c] (absChip s).cores[c]
      (Machine.cfgView s.cont.cfg) ((mhcCbs (absChip s) pin)[c])
      (((mhcCbs (absChip s) pin)[c]).fetch.map fun a => Machine.progWord s.cont.pmem[c] a)
      (absChip s).dbg.frz hcs
  · -- configuration latches
    rw [step_cfg m pin hq]
    show Machine.cfgNext m.cfg m.cw = ((Machine.runStep (absChip s) pin).1).cfg
    rw [← hmach, step_cfg (absChip s) pin hq2]
    rw [show (absChip s).cfg = m.cfg from hrel.cfg.symm]
    rw [show (absChip s).cw = Bridge.CfgWrite.cwOf s.cq s.arb from rfl]
    exact cfgNext_cwRel hrel.cw rfl
  · -- program memory
    rw [step_pmem m pin hq]
    show (match mhcPw m pin with
        | some (c, a, v) =>
          Machine.Util.vset m.pmem c (Machine.Util.bset (Machine.Util.vget m.pmem c) a v)
        | none => m.pmem) = ((Machine.runStep (absChip s) pin).1).pmem
    rw [← hmach, step_pmem (absChip s) pin hq2]
    rw [show (absChip s).pmem = m.pmem from hrel.pmem.symm, hpw]
  · -- data RAM
    rw [hramM.1]
    show (mhcRam m pin).1 = ((Machine.runStep (absChip s) pin).1).dmem
    rw [← hmach, hramA.1, hram]
  · -- RAM output register
    rw [hramM.2.1]
    show Machine.Util.bv 32 (mhcRam m pin).2.1 = ((Machine.runStep (absChip s) pin).1).ramOut
    rw [← hmach, hramA.2.1, hram]
  · -- RAM output owner
    rw [hramM.2.2.1]
    show mhcOwner m pin = ((Machine.runStep (absChip s) pin).1).ramOwner
    rw [← hmach, hramA.2.2.1, howner]
  · -- RAM output lane
    rw [hramM.2.2.2]
    show Machine.Util.bv 2 (mhcLaneN m pin) = ((Machine.runStep (absChip s) pin).1).ramLane
    rw [← hmach, hramA.2.2.2, hlaneN]

/-! ## The configuration write: `Premises.cw`

The unfrozen case is the composed bridge `Bridge.CfgWrite.cfg_compose_bridge` plus
`staged_bpa`/`held_bridge` for the guarded bank-port payloads.  The machine's own
`cwNext` is identified with the bridge's form by `cwNext_st_congr` (a `cwNext`
congruence over the fields it *reads*: `cwa`, `cwv`, `cwqa`, `cwqd`, `bwp`, `hh`
and the `hh`-guarded `hha`/`hhd`), so the remaining wiring facts are the `CW`
move (`cw_open_move`) and the closed release window (`cw_open_window`, AMBIG
1/2).  The host configuration write is `cw_open_hostCfg`; AMBIG 19 (a host
configuration write arriving while `HH` waits) is carried as `cw_open_h19`, as
`Bridge.CfgWrite` does.  A frozen cycle is the D50 case (the machine's `cwNext`
takes `frozen`): `cw_open_frozen` proves it from the zero move bus. -/

/-- A `cwNext` congruence over the registers it reads (`bpa`/`bpd` are outputs
and are not compared). -/
theorem cwNext_st_congr (cw cw' : Machine.CwSt) (hostCfg : Option (Nat × Nat))
    (mv : Option Machine.CwMove) (window frozen : Bool)
    (hcwa : cw.cwa = cw'.cwa) (hcwv : cw.cwv = cw'.cwv) (hcwqa : cw.cwqa = cw'.cwqa)
    (hcwqd : cw.cwqd = cw'.cwqd) (hbwp : cw.bwp = cw'.bwp) (hhh : cw.hh = cw'.hh)
    (hhha : cw.hh = true → cw.hha = cw'.hha) (hhhd : cw.hh = true → cw.hhd = cw'.hhd) :
    (Machine.cwNext cw hostCfg mv window frozen).st
      = (Machine.cwNext cw' hostCfg mv window frozen).st := by
  simp only [Machine.cwNext]
  rw [← hhh, ← hcwa, ← hcwv, ← hcwqa, ← hcwqd, ← hbwp]
  cases hh : cw.hh
  · simp only [hh, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hh, if_true, reduceIte]
    rw [← hhha hh, ← hhhd hh]

/-- **The machine's `cwNext` form of this cycle** is the bridge's: the host
configuration write, the `CW` move, a closed window and an unfrozen cycle, with
`m.cw` agreeing with `Bridge.CfgWrite.cwOf s.cq s.arb` on the fields `cwNext`
reads (`CwRel`). -/
theorem cwNext_abs_bridge (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (cw_open_hostCfg : mhcHostCfg m pin = hostCfgOf s)
    (cw_open_move : mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin))
    (cw_open_window : mhcWindow m = false) (hfrz : m.dbg.frz = false) :
    (mhcCwo m pin).st = (Machine.cwNext (Bridge.CfgWrite.cwOf s.cq s.arb)
      (hostCfgOf s) (Bridge.CfgWrite.mvOf (cqIn s pin)) false false).st := by
  have h := cwNext_st_congr m.cw (Bridge.CfgWrite.cwOf s.cq s.arb) (hostCfgOf s)
    (Bridge.CfgWrite.mvOf (cqIn s pin)) false false
    hrel.cw.cwa hrel.cw.cwv hrel.cw.cwqa hrel.cw.cwqd hrel.cw.bwp hrel.cw.hh
    (fun hh => hrel.cw.hha hh) (fun hh => hrel.cw.hhd hh)
  rw [mhcCwo, cw_open_hostCfg, cw_open_move, cw_open_window, hfrz]
  exact h

/-! ### The frozen cycle (D50)

In a frozen cycle the cut presents no move (`frozenNoMove`), so its `CW` write
group is empty and the queue holds; the machine's `cwNext` takes `frozen = true`
with no move, and the arbiter's `coreValid` gate (`… && !frz`) is off, which is
the machine's `frozen` gate.  `cw_open_frozen` is the frozen analogue of
`Bridge.CfgWrite.arbiter_bridge` + `queue_fields_arb`; `cw_open_hostCfg` is the
host-configuration-write agreement the unfrozen case needs as well. -/

/-- A zero move-enable word gives a zero hit mask. -/
theorem hitsMask_zero6 (grp : BitVec 30) (G : BitVec 5) :
    Moves.hitsMask (0 : BitVec 6) grp G = 0 := by
  simp [Moves.hitsMask, Moves.bits6, Moves.hitAt, CoreCtl.bitAt]

/-- In a frozen cycle the `CW` write group is empty: no move strobe, so no pick. -/
theorem gw_frozen (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true) :
    gw s pin 58 = ⟨false, 0, 0⟩ := by
  unfold gw
  rw [frozenNoMove s pin hf, hitsMask_zero6]
  exact Moves.pickWord_none _ _ _ rfl

/-- In a frozen cycle the packed `CW` word is zero, so the queue sees no write. -/
theorem cwWord_frozen (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true) :
    cwWord s pin = 0 := by
  unfold cwWord
  rw [gw_frozen s pin hf]
  decide

/-- The queue's three write decodes are all clear in a frozen cycle. -/
theorem cqIn_writes_frozen (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true) :
    CoreQueue.writeData (cqIn s pin) = false ∧
      CoreQueue.writeLow (cqIn s pin) = false ∧
      CoreQueue.writeHigh (cqIn s pin) = false := by
  have hw := cwWord_frozen s pin hf
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [CoreQueue.writeData, CoreQueue.writeLow, CoreQueue.writeHigh, cqIn, hw,
      CoreQueue.bitAt]

/-- **The queue holds in a frozen cycle.**  Nothing drains, nothing is accepted,
and the address counter and the queued entry are unchanged. -/
theorem cq_step_frozen (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true)
    (hreset : runRst s pin = true) :
    (CoreQueue.step s.cq (cqIn s pin)).addr = s.cq.addr ∧
      (CoreQueue.step s.cq (cqIn s pin)).pending = s.cq.pending ∧
      (CoreQueue.step s.cq (cqIn s pin)).pendingAddr = s.cq.pendingAddr ∧
      (CoreQueue.step s.cq (cqIn s pin)).pendingData = s.cq.pendingData := by
  obtain ⟨hD, hL, hH⟩ := cqIn_writes_frozen s pin hf
  have hdrain : CoreQueue.drain s.cq (cqIn s pin) = false := by
    simp [CoreQueue.drain, cqIn, hf]
  have hacc : CoreQueue.accept s.cq (cqIn s pin) = false := by
    simp [CoreQueue.accept, hD]
  have hrn : (cqIn s pin).resetN = true := hreset
  have hlow : CoreQueue.nextLow s.cq (cqIn s pin) = CoreQueue.lowByte s.cq.addr := by
    simp [CoreQueue.nextLow, hacc, hL, hrn]
  have hhigh : CoreQueue.nextHigh s.cq (cqIn s pin) = CoreQueue.highByte s.cq.addr := by
    simp [CoreQueue.nextHigh, hacc, hL, hH, hrn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show CoreQueue.pack (CoreQueue.nextLow s.cq (cqIn s pin))
      (CoreQueue.nextHigh s.cq (cqIn s pin)) = s.cq.addr
    rw [hlow, hhigh]
    exact Bridge.CfgWrite.pack_round s.cq.addr
  · simp [CoreQueue.step, hacc, hdrain, hrn]
  · simp [CoreQueue.step, hacc, hrn]
  · simp [CoreQueue.step, hacc, hrn]

/-- **The machine's `cwNext` holds in a frozen cycle**: with no move and
`frozen = true`, the queue registers are unchanged. -/
theorem cwNext_frozen_queue (cw : Machine.CwSt) (hostCfg : Option (Nat × Nat))
    (window : Bool) :
    (Machine.cwNext cw hostCfg none window true).st.cwa = cw.cwa ∧
      (Machine.cwNext cw hostCfg none window true).st.cwv = cw.cwv ∧
      (Machine.cwNext cw hostCfg none window true).st.cwqa = cw.cwqa ∧
      (Machine.cwNext cw hostCfg none window true).st.cwqd = cw.cwqd := by
  simp [Machine.cwNext, Bridge.CfgWrite.bv_toNat]

/-- **The host configuration write agrees.**  The machine's host write is the
cut's `hwOf` (`mhcHw_bridge` plus the canonical abstraction), so the offered
configuration write is the cut's `hostCfgOf`. -/
theorem cw_open_hostCfg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hinv : Inv s) (hrel : ChipRel s m) : mhcHostCfg m pin = hostCfgOf s := by
  have hhw : mhcHw m pin = hwOf s := by
    rw [mhcHw_bridge s m pin hinv hrel]
    rfl
  unfold mhcHostCfg hostCfgOf
  rw [hhw]
  cases h : hwOf s with
  | none => rfl
  | some wv =>
    obtain ⟨a, v, loc⟩ := wv
    simp

/-- An offered configuration write is a decoded configuration address. -/
theorem hostCfgOf_isCfg (s : State) :
    ∀ a v, hostCfgOf s = some (a, v) → Machine.Config.isCfgAddr a = true := by
  intro a v hv
  unfold hostCfgOf hwOf at hv
  split at hv
  · rename_i hw
    split at hv
    · rename_i hic
      cases hv
      exact hic
    · simp at hv
  · simp at hv

/-- The nine-bit offset of an offered configuration write recovers its address. -/
theorem addrOf_offOf_hostCfg {hostCfg : Option (Nat × Nat)}
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true)
    {a v : Nat} (h : hostCfg = some (a, v)) :
    Bridge.CfgWrite.addrOf (Bridge.CfgWrite.offOf a) = a := by
  have hb := Bridge.CfgWrite.isCfgAddr_window a (hcfg a v h)
  exact Bridge.CfgWrite.addrOf_offOf_window a hb.1 (by omega)

/-- The machine's per-core move list is empty in a frozen cycle. -/
theorem coreComb_moves_frozen (s : Machine.State) (cv : Machine.CfgView)
    (p : Machine.PinView) (c : Nat) : (Machine.coreComb s cv p c true).moves = [] := by
  simp [Machine.coreComb]

/-- **The machine's `CW` move is `none` in a frozen cycle** (`coreComb` emits no
moves, so the arbitration finds no winner). -/
theorem mhcCwMove_frozen (m : Machine.State) (pin : Machine.PinIn)
    (hf : m.dbg.frz = true) : mhcCwMove m pin = none := by
  unfold mhcCwMove mhcWs mhcCbs
  simp [hf, coreComb_moves_frozen, Machine.resolveMoves]

/-- A `Nat` below `2 ^ 16` as a 16-bit word reads back as itself. -/
theorem bv16_toNat (x : Nat) (h : x < 65536) :
    (Machine.Util.bv 16 x).toNat = x := by
  rw [Machine.Util.bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A configuration address fits in 16 bits. -/
theorem addrOf_lt (o : BitVec 9) : Bridge.CfgWrite.addrOf o < 65536 := by
  simp only [Bridge.CfgWrite.addrOf, Bridge.CfgWrite.CFG_LO]
  have := o.isLt
  omega

/-- **The bank port in a frozen cycle.**  With the arbiter's `coreValid` gated
off, the machine's `cwNext` (`frozen = true`, no move) and the configuration
arbiter cut describe the same bank-port cycle: same `BWP`, same `HH`, and the
same staged and held payloads.  `h19` excludes the AMBIG 19 overlap (a host
configuration write arriving while `HH` waits). -/
theorem frozen_bank_port (q : CoreQueue.State) (cw : Machine.CwSt) (c : Config.State)
    (hostCfg : Option (Nat × Nat)) (window : Bool)
    (hwin : window = false)
    (hh : cw.hh = c.heldValid) (hbwp : cw.bwp = c.previousWrite)
    (hhha : cw.hh = true → cw.hha = Machine.Util.bv 16 (Bridge.CfgWrite.addrOf c.held.addr))
    (hhhd : cw.hh = true → cw.hhd = c.held.data)
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true) :
    let mach := Machine.cwNext cw hostCfg none window true
    let cut := Config.step c { Bridge.CfgWrite.cfgIn q hostCfg with coreValid := false }
    mach.st.bwp = cut.next.previousWrite ∧
      mach.st.hh = cut.next.heldValid ∧
      (mach.st.bwp = true →
        mach.st.bpa = Machine.Util.bv 16 (Bridge.CfgWrite.addrOf cut.next.staged.addr)) ∧
      (mach.st.bwp = true → mach.st.bpd = cut.next.staged.data) ∧
      (mach.st.hh = true →
        mach.st.hha = Machine.Util.bv 16 (Bridge.CfgWrite.addrOf cut.next.held.addr)) ∧
      (mach.st.hh = true → mach.st.hhd = cut.next.held.data) := by
  subst hwin
  obtain ⟨pw0, hv0, ⟨haddr, hdata⟩, ⟨saddr, sdata⟩⟩ := c
  have hbw16 := addrOf_lt haddr
  simp only at hh hbwp
  cases hv : hv0
  · cases pw : pw0
    · cases hcf : hostCfg
      · simp [Machine.cwNext, Config.step, Config.grant, Config.beforeEdge,
          Bridge.CfgWrite.cfgIn, hh, hbwp, hv, pw, hcf, Bridge.CfgWrite.bv_toNat]
      · have hinv := addrOf_offOf_hostCfg hcfg hcf
        simp [Machine.cwNext, Config.step, Config.grant, Config.beforeEdge,
          Bridge.CfgWrite.cfgIn, hh, hbwp, hv, pw, hcf, Bridge.CfgWrite.bv_toNat, hinv]
    · cases hcf : hostCfg
      · simp [Machine.cwNext, Config.step, Config.grant, Config.beforeEdge,
          Bridge.CfgWrite.cfgIn, hh, hbwp, hv, pw, hcf, Bridge.CfgWrite.bv_toNat]
      · have hinv := addrOf_offOf_hostCfg hcfg hcf
        simp [Machine.cwNext, Config.step, Config.grant, Config.beforeEdge,
          Bridge.CfgWrite.cfgIn, hh, hbwp, hv, pw, hcf, Bridge.CfgWrite.bv_toNat, hinv]
  · have hhh : cw.hh = true := by rw [hh, hv]
    have hha' := hhha hhh
    have hhd' := hhhd hhh
    cases hcf : hostCfg
    · cases pw : pw0 <;>
        simp [Machine.cwNext, Config.step, Config.grant, Config.beforeEdge,
          Bridge.CfgWrite.cfgIn, hh, hbwp, hha', hhd', hv, pw, hcf,
          bv16_toNat _ hbw16, Bridge.CfgWrite.bv_toNat]
    · exact absurd ⟨hv, by simp [hcf]⟩ h19

/-- **`cw_open_frozen` (D50).**  In a frozen cycle the cut presents no `CW`
strobe (`frozenNoMove`), so the queue holds (`cq_step_frozen`); with
`frozen = true` and no move the machine's `cwNext` holds the same registers
(`cwNext_frozen_queue`, `mhcCwMove_frozen`); and the bank port is
`frozen_bank_port`, the frozen analogue of `arbiter_bridge` + `queue_fields_arb`
(the arbiter's `coreValid` gate and the machine's `frozen` gate agree). -/
theorem cw_open_frozen (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hwin : mhcWindow m = false) :
    s.freeze.frz = true →
      CwRel (mhcCwo m pin).st (CoreQueue.step s.cq (cqIn s pin)) (arbStep s).next := by
  intro hf
  have hfrzeq : m.dbg.frz = true := by rw [dbgRel_frz hrel.dbg]; exact hf
  have hhost := cw_open_hostCfg s m pin hinv hrel
  have hmv := mhcCwMove_frozen m pin hfrzeq
  have harb : arbStep s = Config.step s.arb
      { Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s) with coreValid := false } := by
    simp [arbStep, arbIn, hf]
  obtain ⟨hbwpM, hhhM, hbpaM, hbpdM, hhhaM, hhhdM⟩ :=
    frozen_bank_port s.cq m.cw s.arb (hostCfgOf s) false rfl
      hrel.cw.hh hrel.cw.bwp hrel.cw.hha hrel.cw.hhd h19 (hostCfgOf_isCfg s)
  have hq := cq_step_frozen s pin hf hact
  have hm := cwNext_frozen_queue m.cw (hostCfgOf s) false
  have hmach : mhcCwo m pin = Machine.cwNext m.cw (hostCfgOf s) none false true := by
    simp only [mhcCwo, hhost, hmv, hwin, hfrzeq]
  rw [hmach, harb]
  refine ⟨?_, ?_, ?_, ?_, hbwpM, hhhM, hbpaM, hbpdM, hhhaM, hhhdM⟩
  · rw [hm.1, hrel.cw.cwa, hq.1]
  · rw [hm.2.1, hrel.cw.cwv, hq.2.1]
  · rw [hm.2.2.1, hrel.cw.cwqa, hq.2.2.1]
  · rw [hm.2.2.2, hrel.cw.cwqd, hq.2.2.2]

/-- **`Premises.cw`.**  The unfrozen case is `Bridge.CfgWrite.cfg_compose_bridge`
plus `staged_bpa`/`held_bridge`, on the machine's `cwNext` form
(`cwNext_abs_bridge`), with the host configuration write `cw_open_hostCfg`; the
frozen case is `cw_open_frozen` (D50). -/
theorem premise_cw (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (cw_open_h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (cw_open_move : mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin))
    (cw_open_window : mhcWindow m = false) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  rw [step_cw m pin hq]
  by_cases hf : s.freeze.frz = true
  · exact cw_open_frozen s m pin hrel hinv hact cw_open_h19 cw_open_window hf
  · have hff : s.freeze.frz = false := by cases h : s.freeze.frz <;> simp_all
    have hfrzeq : m.dbg.frz = false := by
      rw [dbgRel_frz hrel.dbg]; exact hff
    rw [cwNext_abs_bridge s m pin hrel (cw_open_hostCfg s m pin hinv hrel) cw_open_move
      cw_open_window hfrzeq]
    have harb : arbStep s = Config.step s.arb (Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s)) := by
      simp [arbStep, arbIn, Bridge.CfgWrite.cfgIn, hff]
    rw [show (activeStep s pin).cq = CoreQueue.step s.cq (cqIn s pin) from rfl]
    rw [show (activeStep s pin).arb
        = (Config.step s.arb (Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s))).next from by
      show (arbStep s).next = _
      rw [harb]]
    have hcfg : ∀ a v, hostCfgOf s = some (a, v) → Machine.Config.isCfgAddr a = true :=
      hostCfgOf_isCfg s
    have hcore : (cqIn s pin).coreIssue =
        (Config.step s.arb (Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s))).coreIssue := by
      show (arbStep s).coreIssue = _
      rw [harb]
    obtain ⟨hcwa, hcwv, hcwqa, hcwqd, hbwp, hhh, -⟩ :=
      Bridge.CfgWrite.cfg_compose_bridge s.cq s.arb (hostCfgOf s) (cqIn s pin) hact
        (by simpa [cqIn] using hff) cw_open_h19 (by rfl) hcore
    have hstaged := Bridge.CfgWrite.staged_bpa s.cq s.arb (hostCfgOf s) cw_open_h19 hcfg
    have hheld := Bridge.CfgWrite.held_bridge s.cq s.arb (hostCfgOf s) cw_open_h19 hcfg
    have hbank : ∀ (hb : (Machine.cwNext (Bridge.CfgWrite.cwOf s.cq s.arb) (hostCfgOf s)
        (Bridge.CfgWrite.mvOf (cqIn s pin)) false false).st.bwp = true),
        (Config.step s.arb (Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s))).bankWrite = true := by
      intro hb
      have h2 : (Config.step s.arb (Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s))).next.previousWrite
          = true := by rw [← hbwp]; exact hb
      simpa [Config.step, Config.beforeEdge, Bridge.CfgWrite.cfgIn] using h2
    refine ⟨hcwa, hcwv, hcwqa, hcwqd, hbwp, hhh, ?_, ?_, ?_, ?_⟩
    · intro hb
      exact (hstaged (hbank hb)).1
    · intro hb
      exact (hstaged (hbank hb)).2
    · intro hh
      exact (hheld hh).1
    · intro hh
      exact (hheld hh).2

end Metronome.ChipCut.Discharge
