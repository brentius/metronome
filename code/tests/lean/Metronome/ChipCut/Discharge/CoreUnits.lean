/-
# ChipCut premise discharge: `cores` and `units` (round b)

This file discharges the `Premises.cores` and `Premises.units` fields of
`Metronome.ChipCut.Proof` against the component bridges.

Round a found that `ChipCut.packBools`/`packNs`/`pack8s` stored the slots
reversed; that is fixed in `ChipCut/State.lean`/`Wire.lean` (`item 0` is now the
low bits, `ChipCut.packBools_getLsbD`), so the slot lemmas of §3 read `f k`
again.  Round b also weakens `ChipRel`'s core clause to `xv → ir = ir'`
(`CoreRegsRel`), so `cores_open_ir_guard` is gone: §4 proves the cut's `IR`
difference is unobservable (`core_next_congr`).

What is proved from `ChipRel`/`Inv`: the three register-file `Bridge.Core.Rel`
fields (`rel_core` at the machine's `IR`, `rel_run`, `rel_rrOk`) and seven of the
eight thread-file input slots (`rel_ready` … `rel_w1hOf`).

What remains as an explicit input hypothesis (`CoreInputBus`, `UnitInputs`) and
why is recorded in `DISCHARGE_COREUNITS_NOTES.md`; it is the guard/source vector
wiring (`Bridge.Glue.guard_slot_*`/`src_slot_*` + the guard/line/source leaf
equalities), the thread `CORE` bit (the `coreIn.tCore` encoding disagrees with
the RTL for core 0, §7) and the machine's resolved-move groups.
-/
import Metronome.ChipCut.Proof
import Metronome.Bridge.Core
import Metronome.Bridge.Units
import Metronome.Bridge.Moves
import Metronome.Bridge.Glue

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. Packers (item 0 in the low bits) -/

/-- `Core.slice` as a `getLsbD` window. -/
theorem slice_getLsbD {w : Nat} (v : BitVec w) (lo n j : Nat) (hj : j < n) :
    (Core.slice v lo n).getLsbD j = v.getLsbD (lo + j) := by
  simp [Core.slice, BitVec.getLsbD_ushiftRight, hj]

/-- `packBools`: slot `k` is item `k` (`ChipCut.packBools_getLsbD`). -/
theorem packBools_bit (n : Nat) (f : Nat → Bool) (k : Nat) (hk : k < n) :
    Core.bitOf (ChipCut.packBools n f) k = f k := by
  rw [Bridge.Core.bitOf_eq_getLsbD, ChipCut.packBools_getLsbD]
  simp [hk]

/-- `packNs`: item `k` is the word at bits `w*k …`. -/
theorem packNs_getLsbD : ∀ (w n : Nat) (f : Nat → BitVec w) (k j : Nat), k < n → j < w →
    (ChipCut.packNs w n f).getLsbD (w * k + j) = (f k).getLsbD j
  | w, 0, _, k, _, hk, _ => by omega
  | w, n + 1, f, k, j, hk, hj => by
    rw [show ChipCut.packNs w (n + 1) f =
        (f n ++ ChipCut.packNs w n f).cast (by rw [Nat.mul_succ, Nat.add_comm]) from rfl,
      BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hkn : k = n
    · subst hkn
      rw [if_neg (by omega)]
      congr 1
      omega
    · have hklt : k < n := by omega
      rw [if_pos (by
        have : w * (k + 1) ≤ w * n := Nat.mul_le_mul_left w (by omega)
        rw [Nat.mul_succ] at this
        omega)]
      exact packNs_getLsbD w n f k j hklt hj

/-- The cut's packed word of slot `k` is `f k`. -/
theorem packNs_slice (w n : Nat) (f : Nat → BitVec w) (k : Nat) (hk : k < n) :
    Core.slice (ChipCut.packNs w n f) (w * k) w = f k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [slice_getLsbD _ _ _ _ hj]
  exact packNs_getLsbD w n f k j hk hj

theorem pack8s_getLsbD : ∀ (n : Nat) (f : Nat → BitVec 8) (k j : Nat), k < n → j < 8 →
    (ChipCut.pack8s n f).getLsbD (8 * k + j) = (f k).getLsbD j
  | 0, _, k, _, hk, _ => by omega
  | n + 1, f, k, j, hk, hj => by
    rw [show ChipCut.pack8s (n + 1) f =
        (f n ++ ChipCut.pack8s n f).cast (by omega) from rfl,
      BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hkn : k = n
    · subst hkn
      rw [if_neg (by omega)]
      congr 1
      omega
    · have hklt : k < n := by omega
      rw [if_pos (by omega)]
      exact pack8s_getLsbD n f k j hklt hj

/-- The cut's packed byte of slot `k` is `f k`. -/
theorem pack8s_slice (n : Nat) (f : Nat → BitVec 8) (k : Nat) (hk : k < n) :
    Core.slice (ChipCut.pack8s n f) (8 * k) 8 = f k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [slice_getLsbD _ _ _ _ hj]
  exact pack8s_getLsbD n f k j hk hj

/-- `Fin`-indexed `Vector.get` of `Vector.ofFn`. -/
theorem vec_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  rfl

/-- The `[·]`-notation form used by the component vectors. -/
theorem vec_get_ofFn' {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  show (Vector.ofFn f).get i = f i
  exact vec_get_ofFn f i

/-! ## 2. Machine-side projections of `Machine.runStep` -/

/-- The machine's combinational core bundle of core `c` this cycle. -/
def mCoreComb (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2) : Machine.CoreComb :=
  Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) c.val m.dbg.frz

/-- The machine's next core state of core `c` (`runStep`'s `cores'` entry). -/
def mCoreNext (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2) : Machine.CoreSt :=
  Machine.coreNext m.cores[c] (Machine.cfgView m.cfg) (mCoreComb m pin c)
    ((mCoreComb m pin c).fetch.map fun a => Machine.progWord m.pmem[c.val] a) m.dbg.frz

/-- The six machine moves of the cycle (`cbs[0].moves ++ cbs[1].moves`). -/
def mAllMoves (m : Machine.State) (pin : Machine.PinIn) : List Machine.Move :=
  (mCoreComb m pin 0).moves ++ (mCoreComb m pin 1).moves

/-- The machine's resolved (winning) moves. -/
def mWs (m : Machine.State) (pin : Machine.PinIn) : List Machine.Move :=
  (Machine.resolveMoves (mAllMoves m pin)).1

/-- The machine's per-cycle unit write groups (`runStep`'s `ui`). -/
def mUnitsIn (m : Machine.State) (pin : Machine.PinIn) : Machine.UnitsIn :=
  let ws := mWs m pin
  { flag := ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .fset => some (true, mv.v)
      | .fclr => some (false, mv.v)
      | _ => none
    acc := ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .acc op => some (op, mv.v)
      | _ => none
    reg := Vector.ofFn fun k => ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .reg j => if j == k.val then some mv.v else none
      | _ => none
    sh := Vector.ofFn fun k => ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .shLd j => if j == k.val then some (true, mv.v) else none
      | .shSh j => if j == k.val then some (false, mv.v) else none
      | _ => none
    shCfg := Vector.ofFn fun k => ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .shCfg j => if j == k.val then some mv.v else none
      | _ => none
    cnt := Vector.ofFn fun k => ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .cntLo j => if j == k.val then some (0, mv.v) else none
      | .cntHi j => if j == k.val then some (1, mv.v) else none
      | .cntDec j => if j == k.val then some (2, mv.v) else none
      | _ => none
    lf := Vector.ofFn fun k => ws.findSome? fun mv => match Machine.dstOp mv.dst with
      | .lfSt j => if j == k.val then some (none, mv.v) else none
      | .lfB j b => if j == k.val then some (some b, mv.v) else none
      | _ => none }

theorem step_active (m : Machine.State) (pin : Machine.PinIn) (hq : (m.rq && pin.rstn) = true) :
    Machine.step m pin = (Machine.runStep m pin).1 := by
  simp only [Machine.step, Machine.stepObs, hq, if_true]

theorem runStep_cores (m : Machine.State) (pin : Machine.PinIn) (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).cores = Vector.ofFn (fun c : Fin 2 => mCoreNext m pin c) := by
  rw [step_active m pin hq]
  simp only [Machine.runStep, mCoreNext, mCoreComb]
  rfl

theorem runStep_units (m : Machine.State) (pin : Machine.PinIn) (hq : (m.rq && pin.rstn) = true) :
    (Machine.step m pin).units = Machine.unitsNext m.cfg m.units (mUnitsIn m pin) m.dbg.frz := by
  rw [step_active m pin hq]
  simp only [Machine.runStep, mUnitsIn, mWs, mAllMoves, mCoreComb]
  rfl

/-! ## 3. What `Wire.coreIn` carries (slot `k` is item `k`) -/

theorem tReady_bit (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.bitOf (coreIn s pin c).tReady e = (threadAt s e).ready := by
  simp only [coreIn]
  rw [packBools_bit 6 (fun t => (threadAt s t).ready) e he]

theorem tCore_bit (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.bitOf (coreIn s pin c).tCore e =
      (((Machine.cfgView s.cont.cfg).threads[e]!).core == 1) := by
  simp only [coreIn]
  rw [packBools_bit 6
    (fun t => ((Machine.cfgView s.cont.cfg).threads[t]!.core == 1)) e he]

theorem tLine_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tLine (2 * e) 2 =
      BitVec.ofNat 2 ((Machine.cfgView s.cont.cfg).threads[e]!).line := by
  simp only [coreIn]
  rw [packNs_slice 2 6
    (fun t => BitVec.ofNat 2 ((Machine.cfgView s.cont.cfg).threads[t]!).line) e he]

theorem tPc_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tPc (8 * e) 8 = (threadAt s e).pc := by
  simp only [coreIn]
  rw [packNs_slice 8 6 (fun t => (threadAt s t).pc) e he]

theorem tW0c_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tW0c (6 * e) 6 =
      BitVec.ofNat 6 ((Machine.cfgView s.cont.cfg).threads[e]!).w0c := by
  simp only [coreIn]
  rw [packNs_slice 6 6
    (fun t => BitVec.ofNat 6 ((Machine.cfgView s.cont.cfg).threads[t]!).w0c) e he]

theorem tW1c_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tW1c (6 * e) 6 =
      BitVec.ofNat 6 ((Machine.cfgView s.cont.cfg).threads[e]!).w1c := by
  simp only [coreIn]
  rw [packNs_slice 6 6
    (fun t => BitVec.ofNat 6 ((Machine.cfgView s.cont.cfg).threads[t]!).w1c) e he]

theorem tW0h_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tW0h (8 * e) 8 =
      BitVec.ofNat 8 ((Machine.cfgView s.cont.cfg).threads[e]!).w0h := by
  simp only [coreIn]
  rw [packNs_slice 8 6
    (fun t => BitVec.ofNat 8 ((Machine.cfgView s.cont.cfg).threads[t]!).w0h) e he]

theorem tW1h_slot (s : State) (pin : Machine.PinIn) (c e : Nat) (he : e < 6) :
    Core.slice (coreIn s pin c).tW1h (8 * e) 8 =
      BitVec.ofNat 8 ((Machine.cfgView s.cont.cfg).threads[e]!).w1h := by
  simp only [coreIn]
  rw [packNs_slice 8 6
    (fun t => BitVec.ofNat 8 ((Machine.cfgView s.cont.cfg).threads[t]!).w1h) e he]

theorem guards_bit (s : State) (pin : Machine.PinIn) (c k : Nat) (hk : k < 64) :
    Core.bitOf (coreIn s pin c).guards k = Glue.guardAt k (guardsOf s) := by
  simp only [coreIn]
  rw [packBools_bit 64 (fun k => Glue.guardAt k (guardsOf s)) k hk]

theorem srcs_byte (s : State) (pin : Machine.PinIn) (c k : Nat) (hk : k < 64) :
    Core.slice (coreIn s pin c).srcs (8 * k) 8 = Glue.srcAt k (sourcesOf s) := by
  simp only [coreIn]
  rw [pack8s_slice 64 (fun k => Glue.srcAt k (sourcesOf s)) k hk]

theorem accIn_sel (s : State) (pin : Machine.PinIn) (m : Nat) (hm : m < 6) :
    Units.Acc.opSel (accIn s pin) m =
      Units.Acc.opCodeOf (BitVec.truncate 6
        (BitVec.ushiftRight (mvDst s pin) (6 * m))) := by
  simp only [accIn, Units.Acc.opSel]
  exact packNs_slice 3 6
    (fun m => Units.Acc.opCodeOf (BitVec.truncate 6
      (BitVec.ushiftRight (mvDst s pin) (6 * m)))) m hm

theorem accIn_rWe (s : State) (pin : Machine.PinIn) (m : Nat) (hm : m < 4) :
    Core.bitOf (accIn s pin).rWe m =
      (gw s pin (BitVec.ofNat 6 (14 + m))).we := by
  simp only [accIn]
  rw [packBools_bit 4 (fun k => (gw s pin (BitVec.ofNat 6 (14 + k))).we) m hm]

theorem accIn_rD (s : State) (pin : Machine.PinIn) (m : Nat) (hm : m < 4) :
    Core.slice (accIn s pin).rD (8 * m) 8 =
      (gw s pin (BitVec.ofNat 6 (14 + m))).data := by
  simp only [accIn]
  rw [packNs_slice 8 4 (fun k => (gw s pin (BitVec.ofNat 6 (14 + k))).data) m hm]

/-! ## 4. The weakened `IR` clause -/

theorem coreNat_fin2 (c : Fin 2) : Bridge.Core.coreNat (c.val == 1) = c.val := by
  have h : c.val = 0 ∨ c.val = 1 := by omega
  rcases h with h | h <;> simp [Bridge.Core.coreNat, h]

/-- `CoreRegsRel` is transitive through a `Core.State` middle (the `mout` is not
part of the relation). -/
theorem coreRegsRel_trans {a a' : Core.State} {w : BitVec 64} {b : Machine.CoreSt}
    (h1 : CoreRegsRel a b) (h2 : CoreRegsRel a' (Bridge.Core.absCore w a)) :
    CoreRegsRel a' b := by
  obtain ⟨h1a, h1b, h1c, h1d, h1e, h1f, h1g⟩ := h1
  obtain ⟨h2a, h2b, h2c, h2d, h2e, h2f, h2g⟩ := h2
  refine ⟨h1a.trans h2a, fun hx => (h1b (h2a.trans hx)).trans (h2b hx), h1c.trans h2c,
    h1d.trans h2d, h1e.trans h2e, h1f.trans h2f, h1g.trans h2g⟩

/-- The cut's core state with the machine's `IR`: the field the weakened
`ChipRel` does not pin. -/
def sIr (s : State) (m : Machine.State) (c : Fin 2) : Core.State :=
  { s.cores[c.val] with ir := m.cores[c].ir }

/-- With `XV = 0` the cut's `IR` is unobservable: replacing it changes no next
register, and the guarded `IR` clause holds (`ir'` is `i.rdata` unless frozen, and
a frozen cycle with `XV = 0` has `XV' = 0`). -/
theorem core_next_ir_irrel (c : Bool) (s : Core.State) (i : Core.Input) (w : BitVec 64)
    (hx : s.xv = false) :
    CoreRegsRel (Core.next c s i)
      (Bridge.Core.absCore w (Core.next c ({ s with ir := w }) i)) := by
  rcases s with ⟨xv, rv, fpc, xt, xl, rr, ir⟩
  subst hx
  by_cases hf : i.frz = true
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Core.next, hf, Bridge.Core.absCore]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Core.next, hf, Bridge.Core.absCore, Core.xa, Core.ra, Core.jmp, Core.pse, Core.load,
        Core.free, Core.disp, Core.dispE, Core.dLine, Core.fetchEn, Core.fetchAddr, Core.dpc,
        Core.watcher0, Core.watcher1, Core.dW0c, Core.dW1c, Core.dW0h, Core.dW1h, Core.dPc,
        Core.rrNext]

/-- **The cut's own `IR` deviation is unobservable.**  Two cut core states agreeing
on `XV`, `RV`, `FPC`, `XT`, `XL`, `RR` and on `IR` whenever `XV` is set (the
weakened `CoreRegsRel`) have `CoreRegsRel`-related next states. -/
theorem core_next_congr (c : Bool) (s1 s2 : Core.State) (i : Core.Input) (mout : BitVec 64)
    (hxv : s1.xv = s2.xv) (hxvir : s1.xv = true → s1.ir = s2.ir)
    (hrv : s1.rv = s2.rv) (hfpc : s1.fpc = s2.fpc) (hxt : s1.xt = s2.xt)
    (hxl : s1.xl = s2.xl) (hrr : s1.rr = s2.rr) :
    CoreRegsRel (Core.next c s1 i) (Bridge.Core.absCore mout (Core.next c s2 i)) := by
  by_cases hx : s1.xv = true
  · have hs : s1 = s2 := by
      cases s1
      cases s2
      simp_all
    rw [hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Core.next, Bridge.Core.absCore]
  · have hx1 : s1.xv = false := by simpa using hx
    have hs : s2 = { s1 with ir := s2.ir } := by
      cases s1
      cases s2
      simp_all
    rw [hs]
    exact core_next_ir_irrel c s1 i s2.ir hx1

/-! ## 5. Thread-file slots, the input bus and `premise_cores` -/

theorem vget_threads (m : Machine.State) (e : Nat) (he : e < 6) :
    Machine.Util.vget m.threads e = m.threads[(⟨e, he⟩ : Fin 6)] := by
  show m.threads[e]! = m.threads[(⟨e, he⟩ : Fin 6)]
  show (m.threads[e]?).getD default = m.threads[(⟨e, he⟩ : Fin 6)]
  rw [Vector.getElem?_eq_getElem he]
  rfl

theorem vec_get!_eq_get {α : Type} {n : Nat} [Inhabited α] (v : Vector α n) (e : Nat)
    (he : e < n) : v[e]! = v[(⟨e, he⟩ : Fin n)] := by
  show (v[e]?).getD default = v[(⟨e, he⟩ : Fin n)]
  rw [Vector.getElem?_eq_getElem he]
  rfl

theorem thread_line_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.line < 4 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.nbits]
  exact Nat.mod_lt _ (by decide)

theorem thread_w0c_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.w0c < 64 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.nbits]
  exact Nat.mod_lt _ (by decide)

theorem thread_w1c_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.w1c < 64 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.nbits]
  exact Nat.mod_lt _ (by decide)

theorem thread_w0h_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.w0h < 256 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.cfgByte, Machine.Util.bget]
  exact (c.img.get! _).toNat_lt

theorem thread_w1h_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.w1h < 256 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.cfgByte, Machine.Util.bget]
  exact (c.img.get! _).toNat_lt

/-- `Bridge.Core.Rel`'s `READY` clause from `ChipRel`. -/
theorem rel_ready (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget m.threads e).ready = Core.bitOf (coreIn s pin c.val).tReady e := by
  show (m.threads[e]!).ready = _
  rw [tReady_bit s pin c.val e he, vec_get!_eq_get m.threads e he, hrel.threads ⟨e, he⟩]
  rfl

/-- `Bridge.Core.Rel`'s `PC` clause from `ChipRel`. -/
theorem rel_pcOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget m.threads e).pc.toNat =
      (Core.slice (coreIn s pin c.val).tPc (8 * e) 8).toNat := by
  show (m.threads[e]!).pc.toNat = _
  rw [tPc_slot s pin c.val e he, vec_get!_eq_get m.threads e he, hrel.threads ⟨e, he⟩]
  rfl

/-- `Bridge.Core.Rel`'s `LINE` clause from `ChipRel`. -/
theorem rel_lineOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget (Machine.cfgView m.cfg).threads e).line =
      (Core.slice (coreIn s pin c.val).tLine (2 * e) 2).toNat := by
  show (Machine.cfgView m.cfg).threads[e]!.line = _
  rw [tLine_slot s pin c.val e he, hrel.cfg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using thread_line_lt s.cont.cfg ⟨e, he⟩)]

/-- `Bridge.Core.Rel`'s `W0C` clause from `ChipRel`. -/
theorem rel_w0cOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget (Machine.cfgView m.cfg).threads e).w0c =
      (Core.slice (coreIn s pin c.val).tW0c (6 * e) 6).toNat := by
  show (Machine.cfgView m.cfg).threads[e]!.w0c = _
  rw [tW0c_slot s pin c.val e he, hrel.cfg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using thread_w0c_lt s.cont.cfg ⟨e, he⟩)]

/-- `Bridge.Core.Rel`'s `W1C` clause from `ChipRel`. -/
theorem rel_w1cOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget (Machine.cfgView m.cfg).threads e).w1c =
      (Core.slice (coreIn s pin c.val).tW1c (6 * e) 6).toNat := by
  show (Machine.cfgView m.cfg).threads[e]!.w1c = _
  rw [tW1c_slot s pin c.val e he, hrel.cfg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using thread_w1c_lt s.cont.cfg ⟨e, he⟩)]

/-- `Bridge.Core.Rel`'s `W0H` clause from `ChipRel`. -/
theorem rel_w0hOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget (Machine.cfgView m.cfg).threads e).w0h =
      (Core.slice (coreIn s pin c.val).tW0h (8 * e) 8).toNat := by
  show (Machine.cfgView m.cfg).threads[e]!.w0h = _
  rw [tW0h_slot s pin c.val e he, hrel.cfg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using thread_w0h_lt s.cont.cfg ⟨e, he⟩)]

/-- `Bridge.Core.Rel`'s `W1H` clause from `ChipRel`. -/
theorem rel_w1hOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    (Machine.Util.vget (Machine.cfgView m.cfg).threads e).w1h =
      (Core.slice (coreIn s pin c.val).tW1h (8 * e) 8).toNat := by
  show (Machine.cfgView m.cfg).threads[e]!.w1h = _
  rw [tW1h_slot s pin c.val e he, hrel.cfg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using thread_w1h_lt s.cont.cfg ⟨e, he⟩)]

/-- The machine's core state at the cut's core with the machine's `IR`. -/
theorem rel_core_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) :
    Machine.Util.vget m.cores (Bridge.Core.coreNat (c.val == 1)) =
      Bridge.Core.absCore (coreIn s pin c.val).rdata (sIr s m c) := by
  rw [coreNat_fin2 c]
  obtain ⟨h1, _, h3, h4, h5, h6, h7⟩ := hrel.cores c
  have hm := hrel.mout c
  have hr : (coreIn s pin c.val).rdata = s.cont.mout[c.val] := by simp [coreIn]
  have hv : Machine.Util.vget m.cores c.val = m.cores[c] := by simp [Machine.Util.vget]
  rw [hv]
  have heta : m.cores[c] = ⟨m.cores[c].xv, m.cores[c].ir, m.cores[c].rv, m.cores[c].fpc,
      m.cores[c].xt, m.cores[c].xl, m.cores[c].rr, m.cores[c].mout⟩ := rfl
  rw [heta]
  simp only [Bridge.Core.absCore, sIr, h1, h3, h4, h5, h6, h7]
  rw [hm, ← hr]

/-- The register-file clause with a `Fin`-indexed machine core. -/
theorem rel_core_sIr' (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) :
    m.cores[c] = Bridge.Core.absCore (coreIn s pin c.val).rdata (sIr s m c) := by
  have hv : Machine.Util.vget m.cores c.val = m.cores[c] := by simp [Machine.Util.vget]
  calc m.cores[c] = Machine.Util.vget m.cores c.val := hv.symm
    _ = Machine.Util.vget m.cores (Bridge.Core.coreNat (c.val == 1)) := by
        rw [coreNat_fin2 c]
    _ = Bridge.Core.absCore (coreIn s pin c.val).rdata (sIr s m c) := rel_core_sIr s m pin c hrel

/-- `Bridge.Core.Rel`'s `RUN` clause from `ChipRel`. -/
theorem rel_run (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) :
    m.ctrl.run = (coreIn s pin c.val).runG := by
  rw [hrel.ctrl.1]
  rfl

/-! ### The thread `CORE` bit: `Bridge.Core.Rel`'s `coreOf` slot -/

/-- The cut's `mine` for core 0 is the complement of the raw `CORE` bit
(`Core.mine false i = ~~~i.tCore`). -/
theorem mine_false_bit (i : Core.Input) (e : Nat) (he : e < 6) :
    Core.bitOf (Core.mine false i) e = !(Core.bitOf i.tCore e) := by
  simp only [Core.mine, Bool.false_eq_true, if_false]
  rw [Bridge.Core.bitOf_eq_getLsbD, Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_not]
  simp [he]

/-- A thread's `CORE` field is one bit. -/
theorem thread_core_lt (c : Machine.Config) (e : Fin 6) :
    (Machine.cfgView c).threads[e]!.core < 2 := by
  rw [show (Machine.cfgView c).threads[e]! = c.thread e.val from by simp [Machine.cfgView]]
  simp only [Machine.Config.thread, Machine.Util.nbits]
  exact Nat.mod_lt _ (by decide)

/-- A one-bit core index: `x = 0` is `x ≠ 1`. -/
theorem beq_zero_of_lt_two (x : Nat) (hx : x < 2) : (x == 0) = !(x == 1) := by
  have h : x = 0 ∨ x = 1 := by omega
  rcases h with rfl | rfl <;> rfl

/-- `Bridge.Core.Rel`'s `CORE` clause from `ChipRel`: for core 1 the cut's `mine` is
`tCore` (the raw `CORE` bit), for core 0 it is its complement, and the machine's
`core == 0`/`== 1` are the same two tests on the one-bit field. -/
theorem rel_coreOf (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (e : Nat) (he : e < 6) :
    ((Machine.Util.vget (Machine.cfgView m.cfg).threads e).core ==
      Bridge.Core.coreNat (c.val == 1)) =
      Core.bitOf (Core.mine (c.val == 1) (coreIn s pin c.val)) e := by
  show ((Machine.cfgView m.cfg).threads[e]!.core == Bridge.Core.coreNat (c.val == 1)) = _
  rw [hrel.cfg]
  have hlt : (Machine.cfgView s.cont.cfg).threads[e]!.core < 2 := thread_core_lt _ ⟨e, he⟩
  rcases c with ⟨n, hn⟩
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · show (((Machine.cfgView s.cont.cfg).threads[e]!).core == 0) =
      Core.bitOf (Core.mine false (coreIn s pin 0)) e
    rw [mine_false_bit _ e he, tCore_bit s pin 0 e he]
    exact beq_zero_of_lt_two _ hlt
  · show (((Machine.cfgView s.cont.cfg).threads[e]!).core == 1) =
      Core.bitOf (Core.mine true (coreIn s pin 1)) e
    rw [show Core.mine true (coreIn s pin 1) = (coreIn s pin 1).tCore from rfl]
    rw [tCore_bit s pin 1 e he]


/-- The remaining core-input wiring: the effective guard vector and the source
vector.  Everything else of `Bridge.Core.Rel` is proved from `ChipRel`/`Inv`. -/
structure CoreInputBus (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (x : Core.State) : Prop where
  guards : ∀ (ln : Nat), ln < 4 → ∀ k : Nat,
    Core.bitOf (Core.guardVec (coreIn s pin c.val).guards (coreIn s pin c.val).gLine
      (BitVec.ofNat 2 ln)) k =
      Machine.guardVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) ln
        (Machine.guardOp k)
  srcs : ∀ k : Nat,
    (Core.slice (Core.srcVec x (coreIn s pin c.val)) (8 * k) 8).toNat =
      Machine.srcVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        x.xl.toNat (Machine.insnField x.ir Machine.Tables.FIELD_imm) (Machine.srcOp k)

/-- `Bridge.Core.Rel` from `ChipRel`, `Inv` and the input bus. -/
theorem rel_of_bus (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : CoreInputBus s m pin c (sIr s m c)) :
    Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (sIr s m c) (coreIn s pin c.val) :=
  { core := rel_core_sIr s m pin c hrel
    guards := hbus.guards
    srcs := hbus.srcs
    ready := fun e he => rel_ready s m pin c hrel e he
    coreOf := fun e he => rel_coreOf s m pin c hrel e he
    lineOf := fun e he => rel_lineOf s m pin c hrel e he
    pcOf := fun e he => rel_pcOf s m pin c hrel e he
    w0cOf := fun e he => rel_w0cOf s m pin c hrel e he
    w1cOf := fun e he => rel_w1cOf s m pin c hrel e he
    w0hOf := fun e he => rel_w0hOf s m pin c hrel e he
    w1hOf := fun e he => rel_w1hOf s m pin c hrel e he
    run := rel_run s m pin c hrel
    rrOk := by
      show (sIr s m c).rr.toNat < 6
      exact hinv.rrLt c }

/-- **`Premises.cores`.**  One cut core step refines one machine core step, field by
field, with `ChipRel`'s weakened `IR` clause (`xv → ir = ir'`).  The machine's `IR`
is fed to the cut as `sIr` (the cut's core with the machine's `IR`): with
`XV = 0` that difference is unobservable (`core_next_congr`), and with `XV = 1` the
weakened `ChipRel` pins `IR` anyway. -/
theorem premise_cores (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c)) :
    ∀ c : Fin 2, CoreRegsRel ((activeStep s pin).cores[c]) ((Machine.step m pin).cores[c]) := by
  intro c
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hR := rel_of_bus s m pin c hrel hinv (hbus c)
  have hact' : (coreIn s pin c.val).resetN = true := hact
  have hfrz : m.dbg.frz = (coreIn s pin c.val).frz := by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hcb : mCoreComb m pin c =
      Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz := by
    simp only [mCoreComb, hfrz, coreNat_fin2 c]
  have hnext : mCoreNext m pin c = Machine.coreNext
      (Bridge.Core.absCore (coreIn s pin c.val).rdata (sIr s m c))
      (Machine.cfgView m.cfg)
      (Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz)
      ((mCoreComb m pin c).fetch.map fun a => Machine.progWord m.pmem[c.val] a)
      (coreIn s pin c.val).frz := by
    simp only [mCoreNext, rel_core_sIr' s m pin c hrel, hcb, hfrz]
  -- the cut's own `IR` is the machine's on `XV = 1` cycles
  have hxvs : (s.cores[c.val]).xv = ((sIr s m c).xv) := rfl
  have hxvir : (s.cores[c.val]).xv = true → (s.cores[c.val]).ir = (sIr s m c).ir := by
    intro hx
    have hthis := (hrel.cores c).2.1 hx
    show (s.cores[c.val]).ir = m.cores[c].ir
    exact hthis.symm
  have hcongr := core_next_congr (c.val == 1) (s.cores[c.val]) (sIr s m c)
    (coreIn s pin c.val) (coreIn s pin c.val).rdata hxvs hxvir rfl rfl rfl rfl rfl
  rw [runStep_cores m pin hq]
  rw [show (Vector.ofFn (fun c : Fin 2 => mCoreNext m pin c))[c] = mCoreNext m pin c from
    vec_get_ofFn' _ c]
  rw [show (activeStep s pin).cores = Vector.ofFn (fun c : Fin 2 =>
      Core.step (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)) from rfl]
  rw [show (Vector.ofFn (fun c : Fin 2 =>
      Core.step (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)))[c] =
      Core.step (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) from vec_get_ofFn' _ c]
  rw [hnext]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Bridge.Core.xv_bridge hR hJGTab hact' _).symm).trans g1
  · intro hx
    have hx' : (Core.next (c.val == 1) (sIr s m c) (coreIn s pin c.val)).xv = true := by
      rw [show (Core.next (c.val == 1) (sIr s m c) (coreIn s pin c.val)).xv =
        (Core.next (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).xv from g1]
      exact hx
    have hld : Core.load (sIr s m c) (coreIn s pin c.val) = true ∨
        (coreIn s pin c.val).frz = true := by
      by_cases hf : (coreIn s pin c.val).frz = true
      · exact Or.inr hf
      · left
        have h := hx'
        simp only [Core.next, hact', Bool.true_and] at h
        simpa [hf] using h
    exact ((Bridge.Core.ir_bridge hR hJGTab hact' _ hld).symm).trans (g2 hx)
  · exact ((Bridge.Core.rv_bridge hR hJGTab hact' _).symm).trans g3
  · exact ((Bridge.Core.fpc_bridge hR hJGTab hact' _).symm).trans g4
  · exact ((Bridge.Core.xt_bridge hR hJGTab hact' _).symm).trans g5
  · exact ((Bridge.Core.xl_bridge hR hJGTab hact' _).symm).trans g6
  · exact ((Bridge.Core.rr_bridge hR hJGTab hact' _).symm).trans g7

/-! ## 6. The `units` field -/

/-! ### Byte-word bound (for the LFSR polynomial) -/

theorem bget_lt (a : ByteArray) (i : Nat) : Machine.Util.bget a i < 256 := by
  simpa [Machine.Util.bget] using (a.get! i).toNat_lt

theorem foldr_bound (a : ByteArray) (base w b : Nat) :
    (List.range w).foldr (fun k acc => acc * 256 + Machine.Util.bget a (base + k)) b <
      (b + 1) * 256 ^ w := by
  induction w generalizing base b with
  | zero => simp
  | succ w ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    have hb := bget_lt a (base + w)
    have h := ih base (b * 256 + Machine.Util.bget a (base + w))
    have hle : b * 256 + Machine.Util.bget a (base + w) + 1 ≤ (b + 1) * 256 := by
      have h1 : (b + 1) * 256 = b * 256 + 256 := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (b * 256 + Machine.Util.bget a (base + w) + 1) * 256 ^ w ≤
        ((b + 1) * 256) * 256 ^ w := Nat.mul_le_mul_right _ hle
    have heq : ((b + 1) * 256) * 256 ^ w = (b + 1) * 256 ^ (w + 1) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm]
    exact Nat.lt_of_lt_of_le h (Nat.le_trans h2 (Nat.le_of_eq heq))

theorem bgetLE_lt (a : ByteArray) (base w : Nat) :
    Machine.Util.bgetLE a base w < 2 ^ (8 * w) := by
  have h := foldr_bound a base w 0
  have h2 : (256 : Nat) ^ w = 2 ^ (8 * w) := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]
  simpa [Machine.Util.bgetLE, h2] using h

/-! ### The unit input relation -/

/-- The machine's unit write groups, group by group.  The five non-accumulator
groups (`flag`, `sh`, `shCfg`, `cnt`, `lf`) are pure `resolveMoves`-vs-strobe
wiring; `acc`/`reg` additionally need the slot order of `accIn.sel`/`rWe`/`rD`
(now correct, §3) and the packed op-code/byte selects. -/
structure UnitInputs (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  /-- The `FLAGS` write in the projected (`% 16`) form: `Machine.unitsNext` keeps
  only `v % 16` (`v % 16` is the set-bit index), the cut's `flagsIndex` is a
  `BitVec 4`.  The exact form is *false* (`MoveFabric.flag_data_witness`); the
  projected form is `MoveFabric.unitInputs_flag_low4`. -/
  flag : (mUnitsIn m pin).flag.map (fun p : Bool × Nat => (p.1, p.2 % 16)) =
    (Bridge.Glue.unitsInOf (glueIn s pin)).flag
  acc : (mUnitsIn m pin).acc = (Bridge.AccB.absIn (accIn s pin)).acc
  reg : (mUnitsIn m pin).reg = (Bridge.AccB.absIn (accIn s pin)).reg
  sh : ∀ k : Fin 2, (mUnitsIn m pin).sh[k] = Bridge.ShifterB.absOp (shIn s pin k.val)
  /-- The `SHk.CFG` write in the projected (`% 32`) form: `Machine.shNext` reads
  `bv 4 v` and `nbit v 4`, the cut's `cfgD` is a `BitVec 5`.  The exact form is
  *false* (`shCfg_data_witness`); the projected form is
  `MoveFabric.unitInputs_shCfg_low5`. -/
  shCfg : ∀ k : Fin 2,
    ((mUnitsIn m pin).shCfg[k]).map (fun v => v % 32) =
      Bridge.ShifterB.absCfg (shIn s pin k.val)
  cnt : ∀ k : Fin 3,
    (mUnitsIn m pin).cnt[k] = Bridge.CounterB.absIn (cntIn s pin k.val)
  lf : ∀ k : Fin 2, (mUnitsIn m pin).lf[k] = Bridge.LfsrB.absIn (lfIn s pin k.val)

/-! ### Congruences: `unitsNext` reads each group independently -/

theorem unitsNext_f_congr (cfg : Machine.Config) (u : Machine.UnitsSt)
    (i1 i2 : Machine.UnitsIn) (f : Bool) (h : i1.flag = i2.flag) :
    (Machine.unitsNext cfg u i1 f).f = (Machine.unitsNext cfg u i2 f).f := by
  simp only [Machine.unitsNext, h]

/-- `nbit` at `k` only reads the low `k+1` bits (`Nat.testBit` and
`Nat.testBit_mod_two_pow`). -/
theorem nbit_testBit (x k : Nat) : Machine.Util.nbit x k = x.testBit k := by
  unfold Machine.Util.nbit
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rfl

/-- `nbit` of a `2^m` modulus is unchanged below `m`. -/
theorem nbit_mod_two_pow (x k m : Nat) (hk : k < m) :
    Machine.Util.nbit (x % 2 ^ m) k = Machine.Util.nbit x k := by
  rw [nbit_testBit, nbit_testBit, Nat.testBit_mod_two_pow]
  simp [hk]

/-- `bv m` of a `2^n` modulus agrees with `bv m` when `m ≤ n`. -/
theorem bv_mod_two_pow (m x n : Nat) (hmn : m ≤ n) :
    Machine.Util.bv m (x % 2 ^ n) = Machine.Util.bv m x := by
  unfold Machine.Util.bv
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 hmn)

/-- `unitsNext.f` is a function of the projected (`% 16`) `FLAGS` write. -/
theorem unitsNext_f_map (cfg : Machine.Config) (u : Machine.UnitsSt) (i : Machine.UnitsIn)
    (f : Bool) :
    (Machine.unitsNext cfg u i f).f =
      (match i.flag.map (fun p : Bool × Nat => (p.1, p.2 % 16)) with
        | some (b, v) => Machine.Util.setBit u.f v b
        | none => u.f) := by
  unfold Machine.unitsNext
  cases i.flag with
  | none => rfl
  | some p => obtain ⟨b, v⟩ := p; rfl

/-- `unitsNext.f` reads only `v % 16` of the `FLAGS` write. -/
theorem unitsNext_f_congr_low (cfg : Machine.Config) (u : Machine.UnitsSt)
    (i1 i2 : Machine.UnitsIn) (f : Bool)
    (h : i1.flag.map (fun p : Bool × Nat => (p.1, p.2 % 16)) =
      i2.flag.map (fun p : Bool × Nat => (p.1, p.2 % 16))) :
    (Machine.unitsNext cfg u i1 f).f = (Machine.unitsNext cfg u i2 f).f := by
  rw [unitsNext_f_map, unitsNext_f_map, h]

/-- `shNext`'s `SHk.CFG` half reads only `v % 32` (`bv 4 v` and `nbit v 4`). -/
theorem shNext_cfg_congr (st : Machine.ShSt) (op : Option (Bool × Nat))
    (c1 c2 : Option Nat) (h : c1.map (fun v => v % 32) = c2.map (fun v => v % 32)) :
    Machine.shNext st op c1 = Machine.shNext st op c2 := by
  unfold Machine.shNext
  cases c1 with
  | none =>
    cases c2 with
    | none => rfl
    | some w => simp at h
  | some v =>
    cases c2 with
    | none => simp at h
    | some w =>
      simp only [Option.map_some, Option.some.injEq] at h
      have hv : v % 32 = w % 32 := h
      have hbv : Machine.Util.bv 4 v = Machine.Util.bv 4 w := by
        have h1 : Machine.Util.bv 4 v = Machine.Util.bv 4 (v % 32) := by
          rw [show (32 : Nat) = 2 ^ 5 from rfl]
          exact (bv_mod_two_pow 4 v 5 (by omega)).symm
        have h2 : Machine.Util.bv 4 w = Machine.Util.bv 4 (w % 32) := by
          rw [show (32 : Nat) = 2 ^ 5 from rfl]
          exact (bv_mod_two_pow 4 w 5 (by omega)).symm
        rw [h1, h2, hv]
      have hnb : Machine.Util.nbit v 4 = Machine.Util.nbit w 4 := by
        have h1 : Machine.Util.nbit v 4 = Machine.Util.nbit (v % 32) 4 := by
          rw [show (32 : Nat) = 2 ^ 5 from rfl]
          exact (nbit_mod_two_pow v 4 5 (by omega)).symm
        have h2 : Machine.Util.nbit w 4 = Machine.Util.nbit (w % 32) 4 := by
          rw [show (32 : Nat) = 2 ^ 5 from rfl]
          exact (nbit_mod_two_pow w 4 5 (by omega)).symm
        rw [h1, h2, hv]
      simp only []
      rw [hbv, hnb]

/-- The cut's `FLAGS` index is a nibble, so the `% 16` projection is the identity
on `unitsInOf`'s flag. -/
theorem unitsInOf_flag_low16 (s : State) (pin : Machine.PinIn) :
    ((Bridge.Glue.unitsInOf (glueIn s pin)).flag).map
      (fun p : Bool × Nat => (p.1, p.2 % 16)) =
      (Bridge.Glue.unitsInOf (glueIn s pin)).flag := by
  unfold Bridge.Glue.unitsInOf
  split
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
    exact Nat.mod_eq_of_lt
      (by simpa using (Metronome.Glue.flagsIndex (glueIn s pin)).isLt)
  · rfl

theorem unitsNext_fp_congr (cfg : Machine.Config) (u : Machine.UnitsSt)
    (i1 i2 : Machine.UnitsIn) (f : Bool) :
    (Machine.unitsNext cfg u i1 f).fp = (Machine.unitsNext cfg u i2 f).fp := by
  simp only [Machine.unitsNext]

theorem unitsNext_acc_congr (cfg : Machine.Config) (u1 u2 : Machine.UnitsSt)
    (i1 i2 : Machine.UnitsIn) (f1 f2 : Bool)
    (ha : u1.a = u2.a) (hz : u1.z = u2.z) (hc : u1.c = u2.c) (hn : u1.n = u2.n)
    (hr : u1.r = u2.r) (hi : i1.acc = i2.acc) (hir : i1.reg = i2.reg) :
    (Machine.unitsNext cfg u1 i1 f1).a = (Machine.unitsNext cfg u2 i2 f2).a ∧
    (Machine.unitsNext cfg u1 i1 f1).z = (Machine.unitsNext cfg u2 i2 f2).z ∧
    (Machine.unitsNext cfg u1 i1 f1).c = (Machine.unitsNext cfg u2 i2 f2).c ∧
    (Machine.unitsNext cfg u1 i1 f1).n = (Machine.unitsNext cfg u2 i2 f2).n ∧
    (Machine.unitsNext cfg u1 i1 f1).r = (Machine.unitsNext cfg u2 i2 f2).r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Machine.unitsNext, ha, hz, hc, hn, hr, hi, hir]

/-! ### `CtrlRegs` from `ChipRel` -/

theorem ctrlRegs_of_rel (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Bridge.Glue.CtrlRegs m s.glue := by
  obtain ⟨hc_run, hc_irqen, _, _, _, hc_inb, hc_inv, hc_invp, hc_outb, hc_outv, hc_db,
    hc_irq⟩ := hrel.ctrl
  obtain ⟨hu_f, hu_fp, _⟩ := hrel.units
  exact
    { run := hc_run.symm
      irqen := hc_irqen.symm
      inb := hc_inb.symm
      inv := hc_inv.symm
      invp := hc_invp.symm
      outb := hc_outb.symm
      outv := hc_outv.symm
      db := hc_db.symm
      irq := hc_irq.symm
      fl := hu_f.symm
      flp := hu_fp.symm }

/-! ### The accumulator's code-7 side condition, from the destination table -/

theorem opCodeOf_ne_seven (d : BitVec 6) : Units.Acc.opCodeOf d ≠ 7 := by
  unfold Units.Acc.opCodeOf
  intro h
  repeat' split at h
  all_goals exact absurd h (by decide)

theorem accIn_opSel_ne_seven (s : State) (pin : Machine.PinIn) (m : Nat) (hm : m < 6) :
    Units.Acc.opSel (accIn s pin) m ≠ 7 := by
  rw [accIn_sel s pin m hm]
  exact opCodeOf_ne_seven _

/-- §6's code-7 side condition: every three-bit group of `sel` is an `opCodeOf`
code (`0..6`), so the winner's code is never 7. -/
theorem acc_hit_ne_seven (s : State) (pin : Machine.PinIn) :
    (accIn s pin).hit = 0 ∨ Bridge.AccB.winnerSel (accIn s pin) ≠ 7 := by
  rcases (sideConds s pin).accHit with h | h | h | h | h | h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 0 (by decide) h]
    exact accIn_opSel_ne_seven s pin 0 (by decide)
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 1 (by decide) h]
    exact accIn_opSel_ne_seven s pin 1 (by decide)
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 2 (by decide) h]
    exact accIn_opSel_ne_seven s pin 2 (by decide)
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 3 (by decide) h]
    exact accIn_opSel_ne_seven s pin 3 (by decide)
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 4 (by decide) h]
    exact accIn_opSel_ne_seven s pin 4 (by decide)
  · refine Or.inr ?_
    rw [Bridge.AccB.winnerSel_eq_slot _ 5 (by decide) h]
    exact accIn_opSel_ne_seven s pin 5 (by decide)

/-! ### Cut-side component steps -/

theorem shAt_active (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    shAt (activeStep s pin) k.val = Units.Shifter.step (shAt s k.val) (shIn s pin k.val) := by
  rcases k with ⟨kv, hk⟩
  have h : kv = 0 ∨ kv = 1 := by omega
  rcases h with rfl | rfl <;> simp [shAt, activeStep]

theorem cntAt_active (s : State) (pin : Machine.PinIn) (k : Fin 3) :
    cntAt (activeStep s pin) k.val = Units.Counter.step (cntAt s k.val) (cntIn s pin k.val) := by
  rcases k with ⟨kv, hk⟩
  have h : kv = 0 ∨ kv = 1 ∨ kv = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp [cntAt, activeStep]

theorem lfAt_active (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    lfAt (activeStep s pin) k.val = Units.Lfsr.step (lfAt s k.val) (lfIn s pin k.val) := by
  rcases k with ⟨kv, hk⟩
  have h : kv = 0 ∨ kv = 1 := by omega
  rcases h with rfl | rfl <;> simp [lfAt, activeStep]

/-! ### The accumulator-field agreement for the actual machine units state -/

theorem agrees_machine_units (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hacc : (mUnitsIn m pin).acc = (Bridge.AccB.absIn (accIn s pin)).acc)
    (hreg : (mUnitsIn m pin).reg = (Bridge.AccB.absIn (accIn s pin)).reg) :
    Bridge.AccB.Agrees (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) m.dbg.frz)
      s.acc (accIn s pin) := by
  obtain ⟨hu_f, hu_fp, hu_a, hu_z, hu_c, hu_n, hu_r, hu_sh, hu_cnt, hu_lf⟩ := hrel.units
  have hstep := Bridge.AccB.abs_step m.cfg s.acc (accIn s pin) hact
    (sideConds s pin).accHit (acc_hit_ne_seven s pin)
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hstep
  have hr : m.units.r = (Bridge.AccB.absUnits s.acc).r := by
    rw [show (Bridge.AccB.absUnits s.acc).r =
      Vector.ofFn (fun k : Fin 4 => Bridge.AccB.rbyte s.acc.r k.val) from rfl]
    apply Vector.ext
    intro k hk
    rw [Vector.getElem_ofFn]
    simp only [Bridge.AccB.rbyte]
    exact hu_r ⟨k, hk⟩
  have hc := unitsNext_acc_congr m.cfg m.units (Bridge.AccB.absUnits s.acc)
    (mUnitsIn m pin) (Bridge.AccB.absIn (accIn s pin)) m.dbg.frz false
    hu_a hu_z hu_c hu_n hr hacc hreg
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hc
  exact ⟨hc1.trans hs1, hc2.trans hs2, hc3.trans hs3, hc4.trans hs4,
    hs5.trans hc5.symm⟩

/-- **`Premises.units`.**  One cut unit cycle refines one machine unit cycle, field
by field; the code-7 side condition is proved (`acc_hit_ne_seven`). -/
theorem premise_units (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hIn : UnitInputs s m pin) :
    UnitsRel (activeStep s pin) (Machine.step m pin).units := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hreset : (glueIn s pin).resetN = true := hact
  have hfrz : m.dbg.frz = (glueIn s pin).frz := by
    rw [hrel.dbg.2.1]; simp [glueIn]
  rw [runStep_units m pin hq, hfrz]
  obtain ⟨hu_f, hu_fp, hu_a, hu_z, hu_c, hu_n, hu_r, hu_sh, hu_cnt, hu_lf⟩ := hrel.units
  have hcr : Bridge.Glue.CtrlRegs m s.glue := ctrlRegs_of_rel s m hrel
  have hA := agrees_machine_units s m pin hrel hact hIn.acc hIn.reg
  rw [hfrz] at hA
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [unitsNext_f_congr_low m.cfg m.units (mUnitsIn m pin)
      (Bridge.Glue.unitsInOf (glueIn s pin)) (glueIn s pin).frz
      (hIn.flag.trans (unitsInOf_flag_low16 s pin).symm)]
    exact Bridge.Glue.flags_f (hwOf s) (glueIn s pin) s.glue m hcr hreset
  · rw [unitsNext_fp_congr m.cfg m.units (mUnitsIn m pin)
      (Bridge.Glue.unitsInOf (glueIn s pin)) (glueIn s pin).frz]
    exact Bridge.Glue.flags_fp (hwOf s) (glueIn s pin) s.glue m hcr hreset
  · show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).a =
      (Units.Acc.step s.acc (accIn s pin)).a
    exact hA1
  · show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).z =
      (Units.Acc.step s.acc (accIn s pin)).z
    exact hA2
  · show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).c =
      (Units.Acc.step s.acc (accIn s pin)).c
    exact hA3
  · show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).n =
      (Units.Acc.step s.acc (accIn s pin)).n
    exact hA4
  · intro k
    have h := congrArg (fun v => v[k]) hA5.symm
    rw [h, vec_get_ofFn']
    show Bridge.AccB.rbyte (Units.Acc.rNext s.acc (accIn s pin)) k.val =
      BitVec.truncate 8 (BitVec.ushiftRight
        (Units.Acc.rNext s.acc (accIn s pin)) (8 * k.val))
    rw [Bridge.AccB.rbyte]
  · intro k
    have hs := Bridge.ShifterB.abs_step (shAt s k.val) (shIn s pin k.val) hact
    rw [shAt_active]
    show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).sh[k] =
      (Bridge.ShifterB.abs (Units.Shifter.step (shAt s k.val) (shIn s pin k.val))
        : Machine.ShSt)
    rw [show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin)
        (glueIn s pin).frz).sh[k] =
        Machine.shNext (m.units.sh[k]) ((mUnitsIn m pin).sh[k])
          ((mUnitsIn m pin).shCfg[k]) from by simp [Machine.unitsNext]]
    have hcfg : ((mUnitsIn m pin).shCfg[k]).map (fun v => v % 32) =
        (Bridge.ShifterB.absCfg (shIn s pin k.val)).map (fun v => v % 32) := by
      rw [hIn.shCfg k]
      unfold Bridge.ShifterB.absCfg
      split
      · show (some (shIn s pin k.val).cfgD.toNat) =
          (some (shIn s pin k.val).cfgD.toNat).map (fun v => v % 32)
        rw [Option.map_some, Option.some.injEq]
        exact (Nat.mod_eq_of_lt (by simpa using (shIn s pin k.val).cfgD.isLt)).symm
      · rfl
    rw [shNext_cfg_congr (m.units.sh[k]) ((mUnitsIn m pin).sh[k])
      ((mUnitsIn m pin).shCfg[k]) (Bridge.ShifterB.absCfg (shIn s pin k.val)) hcfg]
    rw [hu_sh k, hIn.sh k]
    exact hs.symm
  · intro k
    have hs := (Bridge.CounterB.abs_step (cntAt s k.val) (cntIn s pin k.val) hact).symm
    rw [cntAt_active]
    show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).cnt[k] =
      Bridge.CounterB.abs (Units.Counter.step (cntAt s k.val) (cntIn s pin k.val))
    rw [show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin)
        (glueIn s pin).frz).cnt[k] =
        Machine.cntNext (m.units.cnt[k]) ((mUnitsIn m pin).cnt[k])
        from by simp [Machine.unitsNext]]
    rw [hu_cnt k, hIn.cnt k]
    exact hs
  · intro k
    have hs := (Bridge.LfsrB.abs_step (lfAt s k.val) (lfIn s pin k.val) hact).symm
    rw [lfAt_active]
    show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin) (glueIn s pin).frz).lf[k] =
      Bridge.LfsrB.abs (Units.Lfsr.step (lfAt s k.val) (lfIn s pin k.val))
    rw [show (Machine.unitsNext m.cfg m.units (mUnitsIn m pin)
        (glueIn s pin).frz).lf[k] =
        Machine.lfNext (m.units.lf[k]) (m.cfg.poly k.val) ((mUnitsIn m pin).lf[k])
        from by simp [Machine.unitsNext]]
    rw [hu_lf k, hIn.lf k]
    have hpoly : (lfIn s pin k.val).poly.toNat = m.cfg.poly k.val := by
      simp only [lfIn, hrel.cfg, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt]
      exact bgetLE_lt _ _ _
    rw [hpoly] at hs
    exact hs




theorem bitOf_setBit_same {w : Nat} (v : BitVec w) (i : Nat) (b : Bool) (hi : i < w) :
    Core.bitOf (Core.setBit v i b) i = b := by
  cases b
  · simp only [Core.setBit, Bool.false_eq_true, ite_false]
    change Core.bitOf (v &&& ~~~(BitVec.twoPow w i)) i = false
    rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_twoPow]
    simp [hi]
  · simp only [Core.setBit, ite_true]
    change Core.bitOf (v ||| BitVec.twoPow w i) i = true
    rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_or, BitVec.getLsbD_twoPow]
    simp [hi]

theorem bitOf_setBit_ne {w : Nat} (v : BitVec w) (i j : Nat) (b : Bool) (h : j ≠ i) :
    Core.bitOf (Core.setBit v i b) j = Core.bitOf v j := by
  by_cases hj : j < w
  · cases b
    · simp only [Core.setBit, Bool.false_eq_true, ite_false]
      change Core.bitOf (v &&& ~~~(BitVec.twoPow w i)) j = Core.bitOf v j
      rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_and, BitVec.getLsbD_not,
        BitVec.getLsbD_twoPow, Bridge.Core.bitOf_eq_getLsbD]
      simp [hj, Ne.symm h]
    · simp only [Core.setBit, ite_true]
      change Core.bitOf (v ||| BitVec.twoPow w i) j = Core.bitOf v j
      rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_or, BitVec.getLsbD_twoPow,
        Bridge.Core.bitOf_eq_getLsbD]
      simp [hj, Ne.symm h]
  · have hw : w ≤ j := Nat.le_of_not_lt hj
    rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_of_ge _ _ hw,
      Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_of_ge _ _ hw]

theorem getLsbD_lowMask {w : Nat} (n k : Nat) (hk : k < w) :
    (Core.lowMask w n).getLsbD k = decide (k < n) := by
  show (~~~((BitVec.allOnes w) <<< n)).getLsbD k = decide (k < n)
  rw [BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  have h : k - n < w := by omega
  simp [hk, h]

theorem bitOf_lowMask_lt {w : Nat} (v : BitVec w) (n k : Nat) (hk : k < w) (hn : k < n) :
    Core.bitOf (v &&& Core.lowMask w n) k = Core.bitOf v k := by
  rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_and, getLsbD_lowMask n k hk,
    Bridge.Core.bitOf_eq_getLsbD]
  simp [hn]

theorem bitOf_lowMask_ge {w : Nat} (v : BitVec w) (n k : Nat) (hk : k < w) (hn : n ≤ k) :
    Core.bitOf (v &&& Core.lowMask w n) k = false := by
  rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_and, getLsbD_lowMask n k hk]
  simp [Nat.not_lt.mpr hn]

/-- The effective guard vector, bit by bit: bit 0 is `TRUE`, bits 27..31 are the
line bundle `g_line`, other bits below 62 are the global slot, 62/63 are cleared. -/
theorem guardVec_bit (g : BitVec 64) (gl : BitVec 20) (ln : BitVec 2) (k : Nat) (hk : k < 64) :
    Core.bitOf (Core.guardVec g gl ln) k =
      (if k = 0 then true
       else if 27 ≤ k ∧ k ≤ 31 then Core.bitOf (Core.lineSlot gl ln) (k - 27)
       else if k < 62 then Core.bitOf g k else false) := by
  simp only [Core.guardVec]
  by_cases h62 : k < 62
  · rw [bitOf_lowMask_lt _ 62 k (by omega) h62]
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos rfl, bitOf_setBit_ne _ 31 0 _ (by decide), bitOf_setBit_ne _ 30 0 _ (by decide),
        bitOf_setBit_ne _ 29 0 _ (by decide), bitOf_setBit_ne _ 28 0 _ (by decide),
        bitOf_setBit_ne _ 27 0 _ (by decide)]
      exact bitOf_setBit_same _ 0 true (by decide)
    · rw [if_neg h0]
      by_cases h2731 : 27 ≤ k ∧ k ≤ 31
      · rw [if_pos h2731]
        have hkc : k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
        rcases hkc with rfl | rfl | rfl | rfl | rfl
        · rw [bitOf_setBit_ne _ 31 27 _ (by decide), bitOf_setBit_ne _ 30 27 _ (by decide),
            bitOf_setBit_ne _ 29 27 _ (by decide), bitOf_setBit_ne _ 28 27 _ (by decide),
            bitOf_setBit_same _ 27 _ (by decide)]
        · rw [bitOf_setBit_ne _ 31 28 _ (by decide), bitOf_setBit_ne _ 30 28 _ (by decide),
            bitOf_setBit_ne _ 29 28 _ (by decide), bitOf_setBit_same _ 28 _ (by decide)]
        · rw [bitOf_setBit_ne _ 31 29 _ (by decide), bitOf_setBit_ne _ 30 29 _ (by decide),
            bitOf_setBit_same _ 29 _ (by decide)]
        · rw [bitOf_setBit_ne _ 31 30 _ (by decide), bitOf_setBit_same _ 30 _ (by decide)]
        · rw [bitOf_setBit_same _ 31 _ (by decide)]
      · rw [if_neg h2731, if_pos h62]
        rw [bitOf_setBit_ne _ 31 k _ (by omega), bitOf_setBit_ne _ 30 k _ (by omega),
          bitOf_setBit_ne _ 29 k _ (by omega), bitOf_setBit_ne _ 28 k _ (by omega),
          bitOf_setBit_ne _ 27 k _ (by omega), bitOf_setBit_ne _ 0 k _ (by omega)]
  · have h62' : 62 ≤ k := Nat.le_of_not_lt h62
    rw [if_neg (by omega : ¬ (k = 0)), if_neg (by omega : ¬ (27 ≤ k ∧ k ≤ 31)),
      if_neg h62, bitOf_lowMask_ge _ 62 k (by omega) h62']


open Metronome

theorem guardV_global (h : Bridge.Glue.GuardTable) (e : Bridge.Glue.Env) (k : Nat)
    (hk : k < 64) (h27 : k ≠ 27) (h28 : k ≠ 28) (h29 : k ≠ 29) (h30 : k ≠ 30)
    (h31 : k ≠ 31) :
    Bridge.Glue.guardV e k = Glue.guardAt k (Bridge.Glue.guardsOf e) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bridge.Glue.guard_slot_0 h e
  · exact Bridge.Glue.guard_slot_1 h e
  · exact Bridge.Glue.guard_slot_2 h e
  · exact Bridge.Glue.guard_slot_3 h e
  · exact Bridge.Glue.guard_slot_4 h e
  · exact Bridge.Glue.guard_slot_5 h e
  · exact Bridge.Glue.guard_slot_6 h e
  · exact Bridge.Glue.guard_slot_7 h e
  · exact Bridge.Glue.guard_slot_8 h e
  · exact Bridge.Glue.guard_slot_9 h e
  · exact Bridge.Glue.guard_slot_10 h e
  · exact Bridge.Glue.guard_slot_11 h e
  · exact Bridge.Glue.guard_slot_12 h e
  · exact Bridge.Glue.guard_slot_13 h e
  · exact Bridge.Glue.guard_slot_14 h e
  · exact Bridge.Glue.guard_slot_15 h e
  · exact Bridge.Glue.guard_slot_16 h e
  · exact Bridge.Glue.guard_slot_17 h e
  · exact Bridge.Glue.guard_slot_18 h e
  · exact Bridge.Glue.guard_slot_19 h e
  · exact Bridge.Glue.guard_slot_20 h e
  · exact Bridge.Glue.guard_slot_21 h e
  · exact Bridge.Glue.guard_slot_22 h e
  · exact Bridge.Glue.guard_slot_23 h e
  · exact Bridge.Glue.guard_slot_24 h e
  · exact Bridge.Glue.guard_slot_25 h e
  · exact Bridge.Glue.guard_slot_26 h e
  · exact absurd rfl h27
  · exact absurd rfl h28
  · exact absurd rfl h29
  · exact absurd rfl h30
  · exact absurd rfl h31
  · exact Bridge.Glue.guard_slot_32 h e
  · exact Bridge.Glue.guard_slot_33 h e
  · exact Bridge.Glue.guard_slot_34 h e
  · exact Bridge.Glue.guard_slot_35 h e
  · exact Bridge.Glue.guard_slot_36 h e
  · exact Bridge.Glue.guard_slot_37 h e
  · exact Bridge.Glue.guard_slot_38 h e
  · exact Bridge.Glue.guard_slot_39 h e
  · exact Bridge.Glue.guard_slot_40 h e
  · exact Bridge.Glue.guard_slot_41 h e
  · exact Bridge.Glue.guard_slot_42 h e
  · exact Bridge.Glue.guard_slot_43 h e
  · exact Bridge.Glue.guard_slot_44 h e
  · exact Bridge.Glue.guard_slot_45 h e
  · exact Bridge.Glue.guard_slot_46 h e
  · exact Bridge.Glue.guard_slot_47 h e
  · exact Bridge.Glue.guard_slot_48 h e
  · exact Bridge.Glue.guard_slot_49 h e
  · exact Bridge.Glue.guard_slot_50 h e
  · exact Bridge.Glue.guard_slot_51 h e
  · exact Bridge.Glue.guard_slot_52 h e
  · exact Bridge.Glue.guard_slot_53 h e
  · exact Bridge.Glue.guard_slot_54 h e
  · exact Bridge.Glue.guard_slot_55 h e
  · exact Bridge.Glue.guard_slot_56 h e
  · exact Bridge.Glue.guard_slot_57 h e
  · exact Bridge.Glue.guard_slot_58 h e
  · exact Bridge.Glue.guard_slot_59 h e
  · exact Bridge.Glue.guard_slot_60 h e
  · exact Bridge.Glue.guard_slot_61 h e
  · exact Bridge.Glue.guard_slot_62 h e
  · exact Bridge.Glue.guard_slot_63 h e

theorem srcV_global (h : Bridge.Glue.SrcTable) (e : Bridge.Glue.Env) (k : Nat)
    (hk : k < 64) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    Bridge.Glue.srcV e k = (Glue.srcAt k (Bridge.Glue.sourcesOf e)).toNat := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bridge.Glue.src_slot_0 h e
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact Bridge.Glue.src_slot_4 h e
  · exact Bridge.Glue.src_slot_5 h e
  · exact Bridge.Glue.src_slot_6 h e
  · exact Bridge.Glue.src_slot_7 h e
  · exact Bridge.Glue.src_slot_8 h e
  · exact Bridge.Glue.src_slot_9 h e
  · exact Bridge.Glue.src_slot_10 h e
  · exact Bridge.Glue.src_slot_11 h e
  · exact Bridge.Glue.src_slot_12 h e
  · exact Bridge.Glue.src_slot_13 h e
  · exact Bridge.Glue.src_slot_14 h e
  · exact Bridge.Glue.src_slot_15 h e
  · exact Bridge.Glue.src_slot_16 h e
  · exact Bridge.Glue.src_slot_17 h e
  · exact Bridge.Glue.src_slot_18 h e
  · exact Bridge.Glue.src_slot_19 h e
  · exact Bridge.Glue.src_slot_20 h e
  · exact Bridge.Glue.src_slot_21 h e
  · exact Bridge.Glue.src_slot_22 h e
  · exact Bridge.Glue.src_slot_23 h e
  · exact Bridge.Glue.src_slot_24 h e
  · exact Bridge.Glue.src_slot_25 h e
  · exact Bridge.Glue.src_slot_26 h e
  · exact Bridge.Glue.src_slot_27 h e
  · exact Bridge.Glue.src_slot_28 h e
  · exact Bridge.Glue.src_slot_29 h e
  · exact Bridge.Glue.src_slot_30 h e
  · exact Bridge.Glue.src_slot_31 h e
  · exact Bridge.Glue.src_slot_32 h e
  · exact Bridge.Glue.src_slot_33 h e
  · exact Bridge.Glue.src_slot_34 h e
  · exact Bridge.Glue.src_slot_35 h e
  · exact Bridge.Glue.src_slot_36 h e
  · exact Bridge.Glue.src_slot_37 h e
  · exact Bridge.Glue.src_slot_38 h e
  · exact Bridge.Glue.src_slot_39 h e
  · exact Bridge.Glue.src_slot_40 h e
  · exact Bridge.Glue.src_slot_41 h e
  · exact Bridge.Glue.src_slot_42 h e
  · exact Bridge.Glue.src_slot_43 h e
  · exact Bridge.Glue.src_slot_44 h e
  · exact Bridge.Glue.src_slot_45 h e
  · exact Bridge.Glue.src_slot_46 h e
  · exact Bridge.Glue.src_slot_47 h e
  · exact Bridge.Glue.src_slot_48 h e
  · exact Bridge.Glue.src_slot_49 h e
  · exact Bridge.Glue.src_slot_50 h e
  · exact Bridge.Glue.src_slot_51 h e
  · exact Bridge.Glue.src_slot_52 h e
  · exact Bridge.Glue.src_slot_53 h e
  · exact Bridge.Glue.src_slot_54 h e
  · exact Bridge.Glue.src_slot_55 h e
  · exact Bridge.Glue.src_slot_56 h e
  · exact Bridge.Glue.src_slot_57 h e
  · exact Bridge.Glue.src_slot_58 h e
  · exact Bridge.Glue.src_slot_59 h e
  · exact Bridge.Glue.src_slot_60 h e
  · exact Bridge.Glue.src_slot_61 h e
  · exact Bridge.Glue.src_slot_62 h e
  · exact Bridge.Glue.src_slot_63 h e


end Metronome.ChipCut.Discharge
