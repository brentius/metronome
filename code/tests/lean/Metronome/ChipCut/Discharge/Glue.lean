/-
# ChipCut: the `Glue` premises (`sync`, `ctrl`, `out`, `oen`)

This file discharges the four `Premises` fields that belong to the glue/output
group (`CHIPCUT_NOTES.md` §3.4.1, fields 1, 10, 15, 16):

* `sync`  — `SyncRel` after one active cycle (`SpiPins.step` against
  `Machine.syncNext`), proved unconditionally from `ChipRel.sync`;
* `ctrl`  — `CtrlRel`: the nine control/mailbox registers through
  `Bridge.Glue.ctrl_bridge` (with `CtrlWr`/`ErrTerms`/`CtrlRegs` proved here),
  the sticky `CONFLICT`/`MEMHAZ` bits through `Bridge.Moves.ctrl_conflict_bridge`
  / `ctrl_memhaz_bridge`, and `CWOVR` through a general overrun lemma that
  replaces the frozen/issue-gated `Bridge.CfgWrite.overrun_bridge`.  The five
  *input-level* wiring facts the machine's inline `runStep` record still needs
  (the picked `HOST.OUT` word, the `HOST.IN` read test, the two sticky events
  and the queue drop event) are named in `ctrl_open_move_fabric`; see the notes
  file;
* `out`, `oen` — the `OUT`/`OEN` registers through `Bridge.Glue.out_bridge`,
  with `CvRange` proved from the machine's two-bit configuration decode and the
  cut's packed `OutCfg` identified with `Bridge.Glue.outCfgOf`.

The machine's per-cycle component inputs are built inline in
`Machine.runStep`; §1 re-derives the projections used by the premises (the
missing pieces `CHIPCUT_NOTES.md` §3.4 names).
-/

import Metronome.ChipCut.Proof

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. Projections of `Machine.runStep`

`Machine.runStep` has one `let` chain and no named component inputs.  The
definitions below repeat the relevant prefix of that chain verbatim so the
premises can be stated against the machine's *inputs* (and so the wiring
obligation can be named), and the projections in this section are `rfl`. -/

/-- The machine's data-RAM arbiter decision of the cycle. -/
def machineServed (m : Machine.State) (pin : Machine.PinIn) : Nat :=
  let frozen := m.dbg.frz
  let cv := Machine.cfgView m.cfg
  let modes : Vector Nat 2 := Vector.ofFn fun k => Machine.streamMode cv.streams[k] k.val m.dbg
  let sreq (k : Fin 2) := Machine.streamReq modes[k] m.streams[k]
  Machine.arbiter (sreq 0) (sreq 1) (Machine.p0Req m.p0) (Machine.hostReq m.host) frozen

/-- The host write the machine issues in the cycle (`hostNext`'s second
component). -/
def machineHw (m : Machine.State) (pin : Machine.PinIn) : Option Machine.HostWr :=
  (Machine.hostNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
    (machineServed m pin == 4)).2

/-- The machine's control-register inputs of the cycle, projected out of
`Machine.runStep`'s inline record. -/
def ctrlInTrue (m : Machine.State) (pin : Machine.PinIn) : Machine.CtrlIn :=
  let frozen := m.dbg.frz
  let cv := Machine.cfgView m.cfg
  let p := Machine.pinView m.sync m.dbg
  let cbs : Vector Machine.CoreComb 2 := Vector.ofFn fun c => Machine.coreComb m cv p c.val frozen
  let allMoves := cbs[0].moves ++ cbs[1].moves
  let (ws, conflict) := Machine.resolveMoves allMoves
  let hostInRead := allMoves.any fun mv => match Machine.srcOp mv.src with
    | .hostIn => true
    | _ => false
  let pdHaz := !m.p0.rdy && allMoves.any fun mv => match Machine.srcOp mv.src with
    | .pD => true
    | _ => false
  let served := machineServed m pin
  let (host', hw) := Machine.hostNext m cv p (served == 4)
  let pmv : Option Machine.P0Move := ws.findSome? fun mv => match Machine.dstOp mv.dst with
    | .pAl => some ⟨0, mv.v⟩
    | .pAh => some ⟨1, mv.v⟩
    | .pW => some ⟨2, mv.v⟩
    | .pR => some ⟨3, mv.v⟩
    | _ => none
  let (p0', p0haz) := Machine.p0Next m.p0 pmv (served == 3) (m.ramOwner == 3)
    m.ramOut.toNat m.ramLane.toNat frozen
  let cwm : Option Machine.CwMove := ws.findSome? fun mv => match Machine.dstOp mv.dst with
    | .cwAl => some ⟨0, mv.v⟩
    | .cwAh => some ⟨1, mv.v⟩
    | .cwD => some ⟨2, mv.v⟩
    | _ => none
  let window := !(Machine.Util.bit m.rqh 0 && Machine.Util.bit m.rqh 1)
  let hwIsCfg := match hw with
    | some w => Machine.Config.isCfgAddr w.addr
    | none => false
  let hostCfg := if hwIsCfg then hw.map fun w => (w.addr, w.v) else none
  let cwo := Machine.cwNext m.cw hostCfg cwm window frozen
  let hostOut := ws.findSome? fun mv => match Machine.dstOp mv.dst with
    | .hostOut => some mv.v
    | _ => none
  { hostOut, hostInRead, conflict, memhaz := pdHaz || p0haz, cwovr := cwo.ovr }

/-- The machine's `ctrl` record of the cycle is `ctrlNext` on `ctrlInTrue`. -/
theorem runStep_ctrl (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.ctrl =
      Machine.ctrlNext m (machineHw m pin) (ctrlInTrue m pin) m.dbg.frz := rfl

/-- The machine's synchroniser input of the cycle. -/
theorem runStep_sync (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.sync = Machine.syncNext m.sync pin := rfl

/-- The machine's `OUT` register of the cycle. -/
theorem runStep_out (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.out =
      (Machine.outNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) m.dbg.frz).1 := rfl

/-- The machine's `OEN` register of the cycle. -/
theorem runStep_oen (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.runStep m pin).1.oen =
      (Machine.outNext m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) m.dbg.frz).2 := rfl

/-- Under the active-cycle reset sample, the machine takes the `runStep` branch. -/
theorem machine_step_active (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) :
    Machine.step m pin = (Machine.runStep m pin).1 := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  simp [Machine.step, Machine.stepObs, hq]

/-- `runRst` gives both the pin's `rst_n` and the cut's `rst_q`. -/
theorem runRst_facts {s : State} {pin : Machine.PinIn} (h : runRst s pin = true) :
    pin.rstn = true ∧ s.rst.rstQ = true := by
  have hc : (s.rst.rstQ && pin.rstn) = true := h
  exact ⟨(Bool.and_eq_true_iff.mp hc).2, (Bool.and_eq_true_iff.mp hc).1⟩

/-! ## 2. The pin view: the cut's synchroniser words are the machine's bytes

`{ui_in, uio_in}` packs into `s1` (`State.lean:209`, `project.v` 60-66): the
high byte is `ui_in`, the low byte `uio_in`.  These lemmas turn `ChipRel.sync`
into the machine's `SyncSt`, and hence identify the two `pinView`s the output
registers and the glue read. -/

theorem append_hi (a b : BitVec 8) :
    BitVec.truncate 8 (BitVec.ushiftRight (a ++ b) 8) = a := by
  simp only [BitVec.ushiftRight_eq, BitVec.truncate_eq_setWidth]
  bv_decide

theorem append_lo (a b : BitVec 8) : BitVec.truncate 8 (a ++ b) = b := by
  simp only [BitVec.truncate_eq_setWidth]
  bv_decide

/-- The cut's packed synchroniser words are the machine's two-byte state. -/
theorem sync_abs {a : SpiPins.Sync} {b : Machine.SyncSt} (h : SyncRel a b) :
    ({ ui1 := BitVec.truncate 8 (BitVec.ushiftRight a.s1 8)
       ui2 := BitVec.truncate 8 (BitVec.ushiftRight a.s2 8)
       uip := BitVec.truncate 8 (BitVec.ushiftRight a.sp 8)
       uio1 := BitVec.truncate 8 a.s1
       uio2 := BitVec.truncate 8 a.s2
       uiop := BitVec.truncate 8 a.sp } : Machine.SyncSt) = b := by
  obtain ⟨h1, h2, h3⟩ := h
  cases b
  simp only [Machine.SyncSt.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [h1, h2, h3]
  all_goals first
    | exact append_hi _ _
    | exact append_lo _ _

/-- The cut's debug registers are the machine's debug block. -/
theorem dbg_abs {s : State} {d : Machine.DbgSt} (h : DbgRel s d) :
    ({ freeze := s.freeze.freeze, frz := s.freeze.frz, frzd := s.freeze.frzd,
       men := s.dbgDigest.men, misr := s.dbgDigest.misr, cen := s.dbgCtrl.cen,
       rpl := s.dbgCtrl.replay, emask := s.dbgCtrl.emask, dc := s.dbgCtrl.dc,
       rlv := s.dbgCtrl.rlv, rlvp := s.dbgCtrl.rlvPrev } : Machine.DbgSt) = d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  cases d
  simp only [Machine.DbgSt.mk.injEq]
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm,
    h9.symm, h10.symm, h11.symm⟩

/-- The pin view of the cut's synchroniser and debug state is the machine's. -/
theorem pinView_abs (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Machine.pinView (absChip s).sync (absChip s).dbg = Machine.pinView m.sync m.dbg := by
  rw [show (absChip s).sync = m.sync from sync_abs hrel.sync,
    show (absChip s).dbg = m.dbg from dbg_abs hrel.dbg]

theorem protoPins_lt (ui uio : BitVec 8) : Machine.Util.protoPins ui uio < 2 ^ 13 := by
  unfold Machine.Util.protoPins
  have h1 := ui.isLt
  have h2 := uio.isLt
  omega

/-- The pin view's level fits in thirteen bits (the bridge's `Env.hlvl`). -/
theorem pinView_lvl_lt (sy : Machine.SyncSt) (d : Machine.DbgSt) :
    (Machine.pinView sy d).lvl < 2 ^ 13 := by
  have hraw : Machine.Util.protoPins sy.ui2 sy.uio2 < 2 ^ 13 := protoPins_lt _ _
  have hm : (if d.rpl then d.emask.toNat else 0) < 2 ^ 13 := by
    have := d.emask.isLt
    split <;> omega
  have hk : (2 ^ 13 - 1 - (if d.rpl then d.emask.toNat else 0)) < 2 ^ 13 := by
    have := d.emask.isLt
    split <;> omega
  have hr : d.rlv.toNat < 2 ^ 13 := d.rlv.isLt
  have hnin : Machine.Tables.N_IN_PINS = 13 := by decide
  show ((Machine.Util.protoPins sy.ui2 sy.uio2 &&&
      (2 ^ Machine.Tables.N_IN_PINS - 1 - (if d.rpl then d.emask.toNat else 0))) |||
      (d.rlv.toNat &&& (if d.rpl then d.emask.toNat else 0))) < 2 ^ 13
  rw [hnin]
  exact Nat.or_lt_two_pow (Nat.and_lt_two_pow _ hk) (Nat.and_lt_two_pow _ hm)

/-! ## 3. The host write and the `CTRL.STICKY` byte

The machine issues the host write `hwOf s` (`hostNext`'s second component), and
`hwByte` decodes it.  `STICKY` is a one-byte register of the `CTRL` block, so a
located `STICKY` write is byte 0 and `hwByte`'s byte index is the RTL's
`c_wr_stk` strobe.  The register map is checked by compiled evaluation
(`decide`) of `Machine.Tables.hostBlocks`; no `native_decide`. -/

/-- The machine's host write is the cut's `hwOf`. -/
theorem machineHw_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) : machineHw m pin = hwOf s := by
  have hc : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
    HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
  have hwr := hrel.host.base.wr
  have had := hrel.host.base.addr
  have hwd := hrel.host.base.wdata
  rw [hc] at hwr had hwd
  simp only [machineHw, Machine.hostNext, hwOf]
  rw [← hwr, ← had]
  by_cases hw : s.hostCmd.wr = true
  · simp only [hw, if_true]
    rw [hwd hw]
  · simp [hw]

/-- `hwByte` of the machine's `hwOf`, with the cut's byte-strobe test. -/
theorem hwByte_hwOf (s : State) (blk : String) (inst : Nat) (reg : String) :
    Machine.Util.hwByte (hwOf s) blk inst reg =
      (if hwIsSome s blk inst reg then some s.hostCmd.wdata.toNat else none) := by
  unfold Machine.Util.hwByte hwIsSome hwOf
  by_cases hw : s.hostCmd.wr = true
  · rw [if_pos hw]
    simp only [Machine.Util.hwAt]
    split
    · rename_i l hl
      by_cases ht : (l.blk == blk && l.inst == inst && l.reg == reg) = true
      · simp [ht]
      · simp [ht]
    · simp
  · have hwr : s.hostCmd.wr = false := by simpa using hw
    simp [hwOf, hwr, hwIsSome, Machine.Util.hwAt]

/-- The `CTRL` block's register map (`Machine.Tables.hostBlocks`). -/
def ctrlRegs : Array (Nat × String × Nat × String) :=
  #[(0x00, "RUN", 1, "RW"), (0x01, "STICKY", 1, "W1C"), (0x02, "IRQEN", 1, "RW"),
    (0x03, "DOORBELL", 1, "W"), (0x04, "HOSTIN", 1, "RW"), (0x05, "HOSTOUT", 1, "R"),
    (0x06, "HOSTSTAT", 1, "RW"), (0x07, "ID", 1, "R"), (0x08, "ERRSUM", 1, "R")]

/-- The block table's `CTRL` row has exactly this register map (compiled
evaluation of the host map). -/
theorem hostBlocks_ctrl :
    (Machine.Tables.hostBlocks.toList.all (fun (name, _base, _stride0, _inst, regs) =>
      !(name == "CTRL") || (regs.toList == ctrlRegs.toList))) = true := by decide

/-- Every `STICKY` entry of the `CTRL` map is a one-byte register at byte offset
1 (compiled evaluation of the host map). -/
theorem ctrlRegs_sticky :
    (ctrlRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "STICKY") || (ro == 1 && bytes == 1))) = true := by decide

theorem ite_some {α : Type} {c : Prop} [Decidable c] {o : Option α} {l : α} {P : Prop}
    (h : (if c then o else none) = some l) (ho : o = some l → P) : P := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact ho h
  · rw [if_neg hc] at h
    exact absurd h (by simp)

theorem hostLocate_eq (a : Nat) :
    Machine.hostLocate a =
      (Machine.Tables.hostBlocks.findSome? fun (name, base, stride0, inst, regs) =>
        let stride := if stride0 == 0 then regs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else stride0
        if base ≤ a && a < base + stride * inst then
          let i := (a - base) / stride
          let off := (a - base) % stride
          regs.findSome? fun (ro, rn, bytes, acc) =>
            if ro ≤ off && off < ro + bytes then some ⟨name, i, rn, off - ro, acc⟩ else none
        else none) := rfl

theorem findSome_blk (regs : Array (Nat × String × Nat × String)) (name : String)
    (i off : Nat) (l : Machine.HostLoc)
    (h : regs.findSome? (fun (ro, rn, bytes, acc) =>
      (if ro ≤ off && off < ro + bytes then
        some (⟨name, i, rn, off - ro, acc⟩ : Machine.HostLoc) else none)) = some l) :
    l.blk = name := by
  obtain ⟨ys, r, zs, -, hgr, -⟩ := Array.findSome?_eq_some_iff.mp h
  simp only at hgr
  split at hgr
  · simp only [Option.some.injEq] at hgr
    rw [← hgr]
  · simp at hgr

theorem findSome_byte (regs : Array (Nat × String × Nat × String)) (name : String) (i off : Nat)
    (l : Machine.HostLoc)
    (h : regs.findSome? (fun (ro, rn, bytes, acc) =>
      (if ro ≤ off && off < ro + bytes then
        some (⟨name, i, rn, off - ro, acc⟩ : Machine.HostLoc) else none)) = some l) :
    ∃ ro rn bytes acc, (ro, rn, bytes, acc) ∈ regs.toList ∧ ro ≤ off ∧ off < ro + bytes ∧
      l.byte = off - ro ∧ l.reg = rn := by
  obtain ⟨ys, r, zs, hpush, hgr, -⟩ := Array.findSome?_eq_some_iff.mp h
  have hrmem : r ∈ regs.toList := by
    have h' : r ∈ (ys.push r ++ zs).toList := by simp
    rwa [← hpush] at h'
  simp only at hgr
  split at hgr
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq] at hgr
    exact ⟨r.1, r.2.1, r.2.2.1, r.2.2.2, hrmem, hc.1, hc.2, by rw [← hgr], by rw [← hgr]⟩
  · simp at hgr

theorem hostLoc_blk (a : Nat) (name : String) (base stride0 inst : Nat)
    (regs : Array (Nat × String × Nat × String)) (l : Machine.HostLoc)
    (h : (let stride := if stride0 == 0 then regs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else stride0
          if base ≤ a && a < base + stride * inst then
            let i := (a - base) / stride
            let off := (a - base) % stride
            regs.findSome? fun (ro, rn, bytes, acc) =>
              if ro ≤ off && off < ro + bytes then some ⟨name, i, rn, off - ro, acc⟩ else none
          else none) = some l) : l.blk = name := by
  dsimp only at h
  refine ite_some h ?_
  intro h2
  exact findSome_blk regs name _ _ l h2

/-- A located `CTRL.STICKY` byte is byte 0 (the register is one byte wide). -/
theorem hostLocate_ctrl_sticky_byte (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "CTRL") (hi : l.inst = 0)
    (hr : l.reg = "STICKY") : l.byte = 0 := by
  rw [hostLocate_eq] at h
  obtain ⟨ys, blk, zs, hpush, hfa, -⟩ := Array.findSome?_eq_some_iff.mp h
  obtain ⟨name, base, stride0, inst, regs⟩ := blk
  have hmem : (name, base, stride0, inst, regs) ∈ Machine.Tables.hostBlocks.toList := by
    have h' : (name, base, stride0, inst, regs) ∈
        (ys.push (name, base, stride0, inst, regs) ++ zs).toList := by simp
    rwa [← hpush] at h'
  have hbn : name = "CTRL" := by
    have h' := hostLoc_blk a name base stride0 inst regs l hfa
    exact h'.symm.trans hb
  have hregs : regs = ctrlRegs := by
    have h' := List.all_eq_true.mp hostBlocks_ctrl (name, base, stride0, inst, regs) hmem
    rw [hbn] at h'
    simpa using h'
  subst hregs
  dsimp only at hfa
  refine ite_some hfa ?_
  intro hfind
  obtain ⟨ro, rn, bytes, acc, hrmem, hle, hlt, hbyte, hreg⟩ :=
    findSome_byte ctrlRegs name ((a - base) / (if stride0 == 0 then
      ctrlRegs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else stride0))
      ((a - base) % (if stride0 == 0 then
        ctrlRegs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else stride0)) l hfind
  have hsticky := List.all_eq_true.mp ctrlRegs_sticky (ro, rn, bytes, acc) hrmem
  simp only at hsticky
  rw [← hreg, hr] at hsticky
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hsticky
  obtain ⟨hro, hby⟩ := hsticky
  subst hro
  subst hby
  rw [hbyte]
  omega

/-- The `hwAt` of the machine's `hwOf`, when it locates a register: the block,
instance and register tests hold and the byte value is the write data. -/
theorem hwAt_some_facts {hw : Option Machine.HostWr} {blk : String} {inst : Nat} {reg : String}
    {j v : Nat} (h : Machine.Util.hwAt hw blk inst reg = some (j, v)) :
    ∃ (w : Machine.HostWr) (l : Machine.HostLoc), hw = some w ∧ w.loc = some l ∧
      l.byte = j ∧ w.v = v ∧ l.blk = blk ∧ l.inst = inst ∧ l.reg = reg := by
  unfold Machine.Util.hwAt at h
  cases hw with
  | none => simp at h
  | some w =>
    cases hl : w.loc with
    | none => simp [hl] at h
    | some l =>
      by_cases ht : (l.blk == blk && l.inst == inst && l.reg == reg) = true
      · simp only [hl, ht, if_true, Option.some.injEq, Prod.mk.injEq] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        exact ⟨w, l, rfl, hl, h.1, h.2, ht.1.1, ht.1.2, ht.2⟩
      · simp [hl, ht] at h

/-- A located `CTRL.STICKY` write's byte index is 0 and its value is the host
write data. -/
theorem hwAt_sticky (s : State) (v j : Nat)
    (h : Machine.Util.hwAt (hwOf s) "CTRL" 0 "STICKY" = some (j, v)) :
    j = 0 ∧ v = s.hostCmd.wdata.toNat := by
  obtain ⟨w, l, hw, hl, hbyte, hv, hblk, hinst, hreg⟩ := hwAt_some_facts h
  unfold hwOf at hw
  by_cases hwr : s.hostCmd.wr = true
  · rw [if_pos hwr] at hw
    obtain rfl : w = ⟨s.hostCmd.addr.toNat, s.hostCmd.wdata.toNat,
      Machine.hostLocate s.hostCmd.addr.toNat⟩ := Option.some.inj hw.symm
    simp only at hl
    constructor
    · rw [← hbyte]
      exact hostLocate_ctrl_sticky_byte s.hostCmd.addr.toNat l hl hblk hinst hreg
    · rw [← hv]
  · rw [if_neg hwr] at hw
    exact absurd hw (by simp)

/-- The machine's `STICKY` bit is the cut's `stickyClear` strobe. -/
theorem sticky_nbit (s : State) (k : Nat) :
    Machine.Util.nbit ((Machine.Util.hwByte (hwOf s) "CTRL" 0 "STICKY").getD 0) k =
      stickyClear s k := by
  rcases h : Machine.Util.hwAt (hwOf s) "CTRL" 0 "STICKY" with _ | ⟨j, v⟩
  · have hv : Machine.Util.hwByte (hwOf s) "CTRL" 0 "STICKY" = none := by
      unfold Machine.Util.hwByte
      rw [h]
      rfl
    rw [hv]
    simp only [Option.getD_none]
    rw [stickyClear, h]
    simp [Machine.Util.nbit]
  · have hv : Machine.Util.hwByte (hwOf s) "CTRL" 0 "STICKY" = some v := by
      unfold Machine.Util.hwByte
      rw [h]
      rfl
    rw [hv]
    simp only [Option.getD_some]
    obtain ⟨hj, -⟩ := hwAt_sticky s v j h
    subst hj
    rw [stickyClear, h]
    simp

/-- `CoreQueue.bitAt` is the machine's `nbit`. -/
theorem bitAt_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    CoreQueue.bitAt x i = Machine.Util.nbit x.toNat i := by
  unfold CoreQueue.bitAt Machine.Util.nbit
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, beq_iff_eq, ne_eq, BitVec.toNat_eq]
  rw [show (BitVec.toNat (0 : BitVec 1)) = 0 from rfl]
  rw [show (BitVec.truncate 1 (BitVec.ushiftRight x i)).toNat = (x.toNat >>> i) % 2 from by
    rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      show BitVec.ushiftRight x i = (x >>> i) from rfl, BitVec.toNat_ushiftRight]]
  rw [Nat.shiftRight_eq_div_pow]
  have := Nat.mod_lt (x.toNat / 2 ^ i) (by decide : 0 < 2)
  omega

/-- The cut's `CWOVR` clear leaf is the machine's `STICKY` bit 2. -/
theorem hostClear_eq (s : State) (pin : Machine.PinIn) :
    CoreQueue.hostClear (cqIn s pin) = stickyClear s 2 := by
  unfold CoreQueue.hostClear cqIn
  by_cases hcs : stickyClear s 2 = true
  · rw [hcs]
    simp only [Bool.true_and]
    rcases h : Machine.Util.hwAt (hwOf s) "CTRL" 0 "STICKY" with _ | ⟨j, v⟩
    · rw [stickyClear, h] at hcs
      simp at hcs
    · obtain ⟨hj, hv⟩ := hwAt_sticky s v j h
      subst hj
      subst hv
      rw [bitAt_eq_nbit]
      -- nbit wdata 2 = true from stickyClear
      rw [stickyClear, h] at hcs
      simp only [beq_self_eq_true, Bool.true_and] at hcs
      exact hcs
  · rw [show stickyClear s 2 = false from by simpa using hcs]
    rfl

/-! ## 4. The control block

`Bridge.Glue.ctrl_bridge` gives the nine control/mailbox registers; the three
sticky fields are `Bridge.Moves.ctrl_conflict_bridge`/`ctrl_memhaz_bridge` and
the `CWOVR` step below.  The machine's *inputs* to the block come from the cycle's
move fabric and from the pointer hazard; those five input equalities are named
in `ctrl_open_move_fabric` (see `DISCHARGE_GLUE_NOTES.md`). -/

/-- Bit `i` of `packBools n f` as the cut's `bitAt` (item `0` is the low bit). -/
theorem gl_bitAt_packBools (n : Nat) (f : Nat → Bool) (i : Nat) :
    Glue.bitAt (packBools n f) i = (decide (i < n) && f i) := by
  rw [Bridge.Glue.bitAt_eq_nbit, ← Bridge.Glue.bit_eq_nbit]
  exact packBools_getLsbD n f i

theorem any6_packBools (f : Nat → Bool) :
    Glue.any6 (packBools 6 f) = (f 0 || f 1 || f 2 || f 3 || f 4 || f 5) := by
  unfold Glue.any6
  rw [gl_bitAt_packBools 6 f 0, gl_bitAt_packBools 6 f 1, gl_bitAt_packBools 6 f 2,
    gl_bitAt_packBools 6 f 3, gl_bitAt_packBools 6 f 4, gl_bitAt_packBools 6 f 5]
  simp

theorem any4_packBools (f : Nat → Bool) :
    Glue.any4 (packBools 4 f) = (f 0 || f 1 || f 2 || f 3) := by
  unfold Glue.any4
  rw [gl_bitAt_packBools 4 f 0, gl_bitAt_packBools 4 f 1, gl_bitAt_packBools 4 f 2,
    gl_bitAt_packBools 4 f 3]
  simp

theorem any2_packBools (f : Nat → Bool) :
    Glue.any2 (packBools 2 f) = (f 0 || f 1) := by
  unfold Glue.any2
  rw [gl_bitAt_packBools 2 f 0, gl_bitAt_packBools 2 f 1]
  simp

/-- The list of a six-entry vector. -/
theorem vector_toList_six {α : Type} (v : Vector α 6) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5]] := by
  have h' : v = Vector.ofFn (fun i : Fin 6 => v[i]) := by
    apply Vector.ext
    intro i h
    simp
  rw [h', Vector.toList_ofFn]
  simp [List.ofFn_succ]

theorem vector_any_six {α : Type} (v : Vector α 6) (g : α → Bool) :
    v.toList.any g = (g v[0] || g v[1] || g v[2] || g v[3] || g v[4] || g v[5]) := by
  rw [vector_toList_six]
  simp [List.any_cons, Bool.or_assoc]

/-- Four-entry vectors (the lines). -/
theorem vector_toList_four {α : Type} (v : Vector α 4) :
    v.toList = [v[0], v[1], v[2], v[3]] := by
  have h' : v = Vector.ofFn (fun i : Fin 4 => v[i]) := by
    apply Vector.ext
    intro i h
    simp
  rw [h', Vector.toList_ofFn]
  simp [List.ofFn_succ]

theorem vector_any_four {α : Type} (v : Vector α 4) (g : α → Bool) :
    v.toList.any g = (g v[0] || g v[1] || g v[2] || g v[3]) := by
  rw [vector_toList_four]
  simp [List.any_cons, Bool.or_assoc]

/-- Two-entry vectors (the streams). -/
theorem vector_toList_two {α : Type} (v : Vector α 2) :
    v.toList = [v[0], v[1]] := by
  have h' : v = Vector.ofFn (fun i : Fin 2 => v[i]) := by
    apply Vector.ext
    intro i h
    simp
  rw [h', Vector.toList_ofFn]
  simp [List.ofFn_succ]

theorem vector_any_two {α : Type} (v : Vector α 2) (g : α → Bool) :
    v.toList.any g = (g v[0] || g v[1]) := by
  rw [vector_toList_two]
  simp [List.any_cons, Bool.or_assoc]

/-- The cut's `ERR` leaves are the machine's §9 error terms. -/
theorem errTerms (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m) :
    Bridge.Glue.ErrTerms m (glueIn s pin) := by
  obtain ⟨-, -, hconf, hmem, hcwovr, -, -, -, -, -, -, -⟩ := hrel.ctrl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.conflict = m.ctrl.conflict
    exact hconf.symm
  · show s.memhaz = m.ctrl.memhaz
    exact hmem.symm
  · show s.cq.overrun = m.ctrl.cwovr
    exact hcwovr.symm
  · show Glue.any6 (packBools 6 fun t => (threadAt s t).late) =
      m.threads.toList.any (fun t => t.late)
    rw [any6_packBools, vector_any_six]
    have e0 : m.threads[0] = Bridge.Thread.absState (threadAt s 0) := hrel.threads 0
    have e1 : m.threads[1] = Bridge.Thread.absState (threadAt s 1) := hrel.threads 1
    have e2 : m.threads[2] = Bridge.Thread.absState (threadAt s 2) := hrel.threads 2
    have e3 : m.threads[3] = Bridge.Thread.absState (threadAt s 3) := hrel.threads 3
    have e4 : m.threads[4] = Bridge.Thread.absState (threadAt s 4) := hrel.threads 4
    have e5 : m.threads[5] = Bridge.Thread.absState (threadAt s 5) := hrel.threads 5
    rw [e0, e1, e2, e3, e4, e5]
    rfl
  · show Glue.any6 (packBools 6 fun t => (threadAt s t).ovr) =
      m.threads.toList.any (fun t => t.ovr)
    rw [any6_packBools, vector_any_six]
    have e0 : m.threads[0] = Bridge.Thread.absState (threadAt s 0) := hrel.threads 0
    have e1 : m.threads[1] = Bridge.Thread.absState (threadAt s 1) := hrel.threads 1
    have e2 : m.threads[2] = Bridge.Thread.absState (threadAt s 2) := hrel.threads 2
    have e3 : m.threads[3] = Bridge.Thread.absState (threadAt s 3) := hrel.threads 3
    have e4 : m.threads[4] = Bridge.Thread.absState (threadAt s 4) := hrel.threads 4
    have e5 : m.threads[5] = Bridge.Thread.absState (threadAt s 5) := hrel.threads 5
    rw [e0, e1, e2, e3, e4, e5]
    rfl
  · show Glue.any4 (packBools 4 fun l => (lineAt s l).tapmiss) =
      m.lines.toList.any (fun l => l.tapmiss)
    rw [any4_packBools, vector_any_four]
    have e0 : m.lines[0] = Bridge.Line.absSt (lineAt s 0) := hrel.lines 0
    have e1 : m.lines[1] = Bridge.Line.absSt (lineAt s 1) := hrel.lines 1
    have e2 : m.lines[2] = Bridge.Line.absSt (lineAt s 2) := hrel.lines 2
    have e3 : m.lines[3] = Bridge.Line.absSt (lineAt s 3) := hrel.lines 3
    rw [e0, e1, e2, e3]
    rfl
  · show Glue.any2 (packBools 2 fun k => (streamAt s k).starved) =
      m.streams.toList.any (fun k => k.starved)
    rw [any2_packBools, vector_any_two]
    obtain ⟨-, -, -, -, -, -, -, -, -, h0, -⟩ := hrel.streams 0
    obtain ⟨-, -, -, -, -, -, -, -, -, h1, -⟩ := hrel.streams 1
    congr 1

/-- The cut's glue registers hold the machine's control and flag registers. -/
theorem ctrlRegsRel (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Bridge.Glue.CtrlRegs m s.glue := by
  obtain ⟨h1, h2, -, -, -, h3, h4, h5, h6, h7, h8, h9⟩ := hrel.ctrl
  obtain ⟨hf, hfp, -, -, -, -, -, -, -, -⟩ := hrel.units
  exact
    { run := h1.symm
      irqen := h2.symm
      inb := h3.symm
      inv := h4.symm
      invp := h5.symm
      outb := h6.symm
      outv := h7.symm
      db := h8.symm
      irq := h9.symm
      fl := hf.symm
      flp := hfp.symm }

/-- The `CTRL` host-write bytes are the cut's strobes. -/
theorem ctrlWr (s : State) (pin : Machine.PinIn) :
    Bridge.Glue.CtrlWr (hwOf s) (glueIn s pin) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Machine.Util.hwByte (hwOf s) "CTRL" 0 "RUN" =
      (if hwIsSome s "CTRL" 0 "RUN" then some (hwData s).toNat else none)
    simpa [hwData] using hwByte_hwOf s "CTRL" 0 "RUN"
  · show Machine.Util.hwByte (hwOf s) "CTRL" 0 "IRQEN" =
      (if hwIsSome s "CTRL" 0 "IRQEN" then some (hwData s).toNat else none)
    simpa [hwData] using hwByte_hwOf s "CTRL" 0 "IRQEN"
  · show Machine.Util.hwByte (hwOf s) "CTRL" 0 "DOORBELL" =
      (if hwIsSome s "CTRL" 0 "DOORBELL" then some (hwData s).toNat else none)
    simpa [hwData] using hwByte_hwOf s "CTRL" 0 "DOORBELL"
  · show Machine.Util.hwByte (hwOf s) "CTRL" 0 "HOSTIN" =
      (if hwIsSome s "CTRL" 0 "HOSTIN" then some (hwData s).toNat else none)
    simpa [hwData] using hwByte_hwOf s "CTRL" 0 "HOSTIN"
  · show Machine.Util.hwByte (hwOf s) "CTRL" 0 "HOSTSTAT" =
      (if hwIsSome s "CTRL" 0 "HOSTSTAT" then some (hwData s).toNat else none)
    simpa [hwData] using hwByte_hwOf s "CTRL" 0 "HOSTSTAT"

/-- The machine's `ctrl` record of the active cycle, with the cut's host write. -/
theorem machine_ctrl_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.step m pin).ctrl =
      Machine.ctrlNext m (hwOf s) (ctrlInTrue m pin) s.freeze.frz := by
  obtain ⟨-, hfrz, -, -, -, -, -, -, -, -, -⟩ := hrel.dbg
  rw [machine_step_active s m pin hrel hact, runStep_ctrl,
    machineHw_eq s m pin hrel hinv, hfrz]

/-- The nine non-sticky control registers depend on the input record only
through the host mailbox fields. -/
theorem ctrlNext_host_congr (m : Machine.State) (hw : Option Machine.HostWr)
    (c1 c2 : Machine.CtrlIn) (frz : Bool)
    (hout : c1.hostOut = c2.hostOut) (hin : c1.hostInRead = c2.hostInRead) :
    (Machine.ctrlNext m hw c1 frz).run = (Machine.ctrlNext m hw c2 frz).run ∧
    (Machine.ctrlNext m hw c1 frz).irqen = (Machine.ctrlNext m hw c2 frz).irqen ∧
    (Machine.ctrlNext m hw c1 frz).inb = (Machine.ctrlNext m hw c2 frz).inb ∧
    (Machine.ctrlNext m hw c1 frz).inv = (Machine.ctrlNext m hw c2 frz).inv ∧
    (Machine.ctrlNext m hw c1 frz).invp = (Machine.ctrlNext m hw c2 frz).invp ∧
    (Machine.ctrlNext m hw c1 frz).outb = (Machine.ctrlNext m hw c2 frz).outb ∧
    (Machine.ctrlNext m hw c1 frz).outv = (Machine.ctrlNext m hw c2 frz).outv ∧
    (Machine.ctrlNext m hw c1 frz).db = (Machine.ctrlNext m hw c2 frz).db ∧
    (Machine.ctrlNext m hw c1 frz).irq = (Machine.ctrlNext m hw c2 frz).irq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Machine.ctrlNext, hout, hin]

/-- `CWOVR` after the cycle: the machine's sticky bit with the cut's queue drop
event, against the queue cut's overrun step.  Unlike
`Bridge.CfgWrite.overrun_bridge` this needs no frozen/grant side condition: the
queue's `drain` and the machine's `drains` agree on all four branches, because the
arbiter's `coreIssue` carries exactly the `!HH`/`!BWP`/no-host-write gates of
`Machine.cwNext`.  Here the agreement is taken as the input fact `hci`. -/
theorem cwovr_step (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hci : (ctrlInTrue m pin).cwovr =
      (CoreQueue.writeData (cqIn s pin) && !CoreQueue.accept s.cq (cqIn s pin))) :
    (Machine.ctrlNext m (hwOf s) (ctrlInTrue m pin) s.freeze.frz).cwovr =
      (CoreQueue.step s.cq (cqIn s pin)).overrun := by
  unfold Machine.ctrlNext
  dsimp only
  obtain ⟨-, -, -, -, hcwovr, -, -, -, -, -, -, -⟩ := hrel.ctrl
  rw [sticky_nbit s 2, hcwovr, hci]
  show ((s.cq.overrun && !stickyClear s 2) ||
      (CoreQueue.writeData (cqIn s pin) && !CoreQueue.accept s.cq (cqIn s pin))) = _
  dsimp only [CoreQueue.step]
  rw [hostClear_eq s pin, show (cqIn s pin).resetN = true from hact, if_pos rfl]
  exact Bool.or_comm _ _

/-- The input-level wiring facts of the control block.  Each says that one leaf
of the machine's inline `ctrlInTrue` record is the cut's same-cycle fabric value:

* `hostOut`/`hostInRead`: the `HOST.OUT` pick and the `HOST.IN` read test (the
  move fabric, as for the `cores`/`units` premises);
* `conflict`/`memhaz`: the two sticky-error events (move fabric plus the pointer
  hazard of the `p0` premise);
* `cwovr`: the queue drop event of the `cw` premise.

They are not functions of the current registers alone, so they cannot be
derived from `ChipRel`; see `DISCHARGE_GLUE_NOTES.md`.  The carried hypothesis of
`premise_ctrl` is the abbreviation `ctrl_open_move_fabric`. -/
structure CtrlMoveFabric (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  hostOut : (ctrlInTrue m pin).hostOut =
    (Bridge.Glue.ctrlInOf (glueIn s pin)).hostOut
  hostInRead : (ctrlInTrue m pin).hostInRead =
    (Bridge.Glue.ctrlInOf (glueIn s pin)).hostInRead
  conflict : (ctrlInTrue m pin).conflict =
    Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s)
  memhaz : (ctrlInTrue m pin).memhaz =
    Moves.memhazEvent (mvEn s pin) (mvSrc s pin) (Mem.haz s.p0 (memIn s pin)) s.p0.rdy
  cwovr : (ctrlInTrue m pin).cwovr =
    (CoreQueue.writeData (cqIn s pin) && !CoreQueue.accept s.cq (cqIn s pin))

/-- The carried open hypothesis of `ctrl`: this cycle's move-fabric / pointer
hazard wiring (see `CtrlMoveFabric`). -/
abbrev ctrl_open_move_fabric := CtrlMoveFabric

/-- **`ctrl`**: the control registers, mailbox and sticky errors after one active
cycle, through `ctrl_bridge`, the two `Moves` sticky bridges and `cwovr_step`.
The move-fabric input facts are the named `ctrl_open_move_fabric` hypothesis. -/
theorem premise_ctrl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hopen : ctrl_open_move_fabric s m pin) :
    CtrlRel (activeStep s pin) (Machine.step m pin).ctrl := by
  have hB : Bridge.Glue.CtrlRegs (Bridge.Glue.ctrlStep (hwOf s) (glueIn s pin) m)
      (Glue.step s.glue (glueIn s pin)) :=
    Bridge.Glue.ctrl_bridge (hwOf s) (glueIn s pin) s.glue m
      (ctrlWr s pin) (errTerms s m pin hrel) (ctrlRegsRel s m hrel) hact
  have hcongr := ctrlNext_host_congr m (hwOf s) (ctrlInTrue m pin)
    (Bridge.Glue.ctrlInOf (glueIn s pin)) s.freeze.frz hopen.hostOut hopen.hostInRead
  obtain ⟨h_run, h_irqen, h_inb, h_inv, h_invp, h_outb, h_outv, h_db, h_irq⟩ := hcongr
  obtain ⟨-, -, hconf, hmem, -, -, -, -, -, -, -, -⟩ := hrel.ctrl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_run]
    exact hB.run.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_irqen]
    exact hB.irqen.symm
  · have h := Bridge.Moves.ctrl_conflict_bridge m (hwOf s) (ctrlInTrue m pin)
      s.freeze.frz ((Machine.Util.hwByte (hwOf s) "CTRL" 0 "STICKY").getD 0) rfl
      s.conflict (Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s))
      (stickyClear s 0) hconf hopen.conflict (sticky_nbit s 0)
    rw [machine_ctrl_eq s m pin hrel hinv hact]
    simpa [activeStep, hact] using h
  · have h := Bridge.Moves.ctrl_memhaz_bridge m (hwOf s) (ctrlInTrue m pin)
      s.freeze.frz ((Machine.Util.hwByte (hwOf s) "CTRL" 0 "STICKY").getD 0) rfl
      s.memhaz (Moves.memhazEvent (mvEn s pin) (mvSrc s pin)
        (Mem.haz s.p0 (memIn s pin)) s.p0.rdy)
      (stickyClear s 1) hmem hopen.memhaz (sticky_nbit s 1)
    rw [machine_ctrl_eq s m pin hrel hinv hact]
    simpa [activeStep, hact] using h
  · rw [machine_ctrl_eq s m pin hrel hinv hact]
    exact cwovr_step s m pin hrel hact hopen.cwovr
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_inb]
    exact hB.inb.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_inv]
    exact hB.inv.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_invp]
    exact hB.invp.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_outb]
    exact hB.outb.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_outv]
    exact hB.outv.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_db]
    exact hB.db.symm
  · rw [machine_ctrl_eq s m pin hrel hinv hact, h_irq]
    exact hB.irq.symm

/-! ## 5. The output registers (`out`, `oen`)

`Bridge.Glue.out_bridge` states the machine's `OUT`/`OEN` registers as `packBits`
of the per-pin `Glue.outNext`/`oeNext` values, with `Bridge.Glue.outCfgOf` the
cut's per-pin configuration.  `CvRange` is proved from the machine's two-bit
`BIND`/`SEL` decode, and the cut's packed `outCfgOf` is identified with the
bridge's field by field. -/

/-- The bridge's environment for the machine's output registers. -/
def outEnv (m : Machine.State) : Bridge.Glue.Env :=
  { ms := m
    cv := Machine.cfgView m.cfg
    p := Machine.pinView m.sync m.dbg
    l := 0
    imm := 0
    hlvl := pinView_lvl_lt m.sync m.dbg }

theorem vget_cfgView_outs_lt (c : Machine.Config) (o : Nat) (h : o < 14) :
    Machine.Util.vget (Machine.cfgView c).outs o = c.out o := by
  simp [Machine.Util.vget, Machine.cfgView, h]

theorem vget_cfgView_outs_ge (c : Machine.Config) (o : Nat) (h : ¬ o < 14) :
    Machine.Util.vget (Machine.cfgView c).outs o = default := by
  simp [Machine.Util.vget, Machine.cfgView, h]

theorem cfgView_out_line (c : Machine.Config) (o : Nat) :
    (Machine.Util.vget (Machine.cfgView c).outs o).line < 4 := by
  by_cases h : o < 14
  · rw [vget_cfgView_outs_lt c o h]
    simp only [Machine.Config.out]
    exact Nat.mod_lt _ (by decide)
  · rw [vget_cfgView_outs_ge c o h]
    show (default : Machine.OutCfg).line < 4
    decide

theorem cfgView_out_live (c : Machine.Config) (o : Nat) :
    (Machine.Util.vget (Machine.cfgView c).outs o).live < 4 := by
  by_cases h : o < 14
  · rw [vget_cfgView_outs_lt c o h]
    simp only [Machine.Config.out]
    exact Nat.mod_lt _ (by decide)
  · rw [vget_cfgView_outs_ge c o h]
    show (default : Machine.OutCfg).live < 4
    decide

theorem cfgView_out_sel0 (c : Machine.Config) (o : Nat) :
    (Machine.Util.vget (Machine.cfgView c).outs o).sel0 < 4 := by
  by_cases h : o < 14
  · rw [vget_cfgView_outs_lt c o h]
    simp only [Machine.Config.out]
    exact Nat.mod_lt _ (by decide)
  · rw [vget_cfgView_outs_ge c o h]
    show (default : Machine.OutCfg).sel0 < 4
    decide

theorem cfgView_out_sel1 (c : Machine.Config) (o : Nat) :
    (Machine.Util.vget (Machine.cfgView c).outs o).sel1 < 4 := by
  by_cases h : o < 14
  · rw [vget_cfgView_outs_lt c o h]
    simp only [Machine.Config.out]
    exact Nat.mod_lt _ (by decide)
  · rw [vget_cfgView_outs_ge c o h]
    show (default : Machine.OutCfg).sel1 < 4
    decide

theorem cfgView_out_sel2 (c : Machine.Config) (o : Nat) :
    (Machine.Util.vget (Machine.cfgView c).outs o).sel2 < 4 := by
  by_cases h : o < 14
  · rw [vget_cfgView_outs_lt c o h]
    simp only [Machine.Config.out]
    exact Nat.mod_lt _ (by decide)
  · rw [vget_cfgView_outs_ge c o h]
    show (default : Machine.OutCfg).sel2 < 4
    decide

/-- The machine's decoded output configuration is in the bridge's `CvRange`. -/
theorem cvRange (m : Machine.State) : Bridge.Glue.CvRange (outEnv m) :=
  { line := fun o => cfgView_out_line m.cfg o
    sel0 := fun o => cfgView_out_sel0 m.cfg o
    sel1 := fun o => cfgView_out_sel1 m.cfg o
    sel2 := fun o => cfgView_out_sel2 m.cfg o }

/-! ### Packing identities -/

theorem comm_eq (f : Nat → BitVec 4) :
    Bridge.Glue.commPack (f 0) (f 1) (f 2) (f 3) = packNs 4 4 f := by
  simp only [Bridge.Glue.commPack, packNs, BitVec.cast_eq]
  bv_decide

theorem seg_eq (g : Nat → BitVec 2) :
    Bridge.Glue.segPack (g 0) (g 1) (g 2) (g 3) = packNs 2 4 g := by
  simp only [Bridge.Glue.segPack, packNs, BitVec.cast_eq]
  bv_decide

theorem pack4_eq (f : Nat → Bool) :
    Bridge.Glue.pack4b (f 3) (f 2) (f 1) (f 0) = packBools 4 f := by
  simp only [Bridge.Glue.pack4b, packBools, BitVec.cast_eq]
  bv_decide

theorem bind_eq (line : Nat) (hl : line < 4) (bd : Bool) (live : Nat) (hv : live < 4) :
    Bridge.Glue.bindPack (Machine.Util.bv 2 line) bd (Machine.Util.nbit live 0)
      (Machine.Util.nbit live 1) =
      BitVec.ofNat 8 (line + 4 * (if bd then 1 else 0) + 8 * live) := by
  rcases (by omega : line = 0 ∨ line = 1 ∨ line = 2 ∨ line = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : live = 0 ∨ live = 1 ∨ live = 2 ∨ live = 3) with rfl | rfl | rfl | rfl <;>
    cases bd <;>
    simp only [Bridge.Glue.bindPack, Bridge.Glue.bitVec1, Machine.Util.bv, Machine.Util.nbit] <;>
    decide

theorem sel_eq (a b c : Nat) (ha : a < 4) (hb : b < 4) (hc : c < 4) :
    Bridge.Glue.selPack (Machine.Util.bv 2 a) (Machine.Util.bv 2 b) (Machine.Util.bv 2 c) =
      BitVec.ofNat 8 (a + 4 * b + 16 * c) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Bridge.Glue.selPack, Machine.Util.bv] <;>
    decide

theorem getElem!_of_lt {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) :
    v[i]! = v[i] := by
  simp [h]

/-- The bridge's per-pin output configuration is the cut's packed one. -/
theorem outCfg_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (o : Nat) :
    Bridge.Glue.outCfgOf (outEnv m) o = outCfgOf s o := by
  have hoc : Bridge.Glue.ocOf (outEnv m) o = (Machine.cfgView s.cont.cfg).outs[o]! := by
    simp [Bridge.Glue.ocOf, outEnv, Machine.Util.vget, hrel.cfg]
  have hcomm : ∀ l : Nat, l < 4 →
      (Machine.Util.vget m.lines l).committed = (lineAt s l).committed := by
    intro l hl
    rw [Machine.Util.vget, getElem!_of_lt _ l hl]
    exact congrArg Machine.LineSt.committed (hrel.lines ⟨l, hl⟩)
  have hseg : ∀ l : Nat, l < 4 → Machine.seg (Machine.Util.vget m.lines l) =
      (Line.seg (lineAt s l)).toNat := by
    intro l hl
    rw [Bridge.Line.seg_test (lineAt s l)]
    congr 1
    rw [Machine.Util.vget, getElem!_of_lt _ l hl]
    exact hrel.lines ⟨l, hl⟩
  unfold Bridge.Glue.outCfgOf outCfgOf
  simp only [hoc]
  simp only [outEnv]
  simp only [Glue.OutCfg.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bind_eq _ (cfgView_out_line s.cont.cfg o) _ _
      (cfgView_out_live s.cont.cfg o)
  · exact sel_eq _ _ _ (cfgView_out_sel0 s.cont.cfg o) (cfgView_out_sel1 s.cont.cfg o)
      (cfgView_out_sel2 s.cont.cfg o)
  · rfl
  · rfl
  · rw [hcomm 0 (by decide), hcomm 1 (by decide), hcomm 2 (by decide), hcomm 3 (by decide)]
    exact comm_eq (fun l => (lineAt s l).committed)
  · rw [← pinView_abs s m hrel]
    simp only [hrel.cfg]
    exact pack4_eq (fun l =>
      (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pina)
  · rw [← pinView_abs s m hrel]
    simp only [hrel.cfg]
    exact pack4_eq (fun l =>
      (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pinb)
  · rw [show Machine.Util.bv 2 (Machine.seg (Machine.Util.vget m.lines 0)) =
        Line.seg (lineAt s 0) from by rw [hseg 0 (by decide), Bridge.Glue.bv_toNat],
      show Machine.Util.bv 2 (Machine.seg (Machine.Util.vget m.lines 1)) =
        Line.seg (lineAt s 1) from by rw [hseg 1 (by decide), Bridge.Glue.bv_toNat],
      show Machine.Util.bv 2 (Machine.seg (Machine.Util.vget m.lines 2)) =
        Line.seg (lineAt s 2) from by rw [hseg 2 (by decide), Bridge.Glue.bv_toNat],
      show Machine.Util.bv 2 (Machine.seg (Machine.Util.vget m.lines 3)) =
        Line.seg (lineAt s 3) from by rw [hseg 3 (by decide), Bridge.Glue.bv_toNat]]
    exact seg_eq (fun l => Line.seg (lineAt s l))

/-! ## 6. The premises -/

/-- **`sync`**: the sixteen synchroniser bits after one active cycle are the
machine's two-byte `SyncSt` (`project.v` 60-66, `SpiPins.step` against
`Machine.syncNext`). -/
theorem premise_sync (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    SyncRel (activeStep s pin).sync (Machine.step m pin).sync := by
  obtain ⟨h1, h2, h3⟩ := hrel.sync
  rw [machine_step_active s m pin hrel hact, runStep_sync]
  refine ⟨?_, ?_, ?_⟩
  · show (if (spiIn s pin).resetN then SpiPins.raw (spiIn s pin) else 0) = pin.ui ++ pin.uio
    rw [show (spiIn s pin).resetN = true from hact, if_pos rfl]
    rfl
  · show (if (spiIn s pin).resetN then s.sync.s1 else 0) = m.sync.ui1 ++ m.sync.uio1
    rw [show (spiIn s pin).resetN = true from hact, if_pos rfl]
    exact h1
  · show (if (spiIn s pin).resetN then s.sync.s2 else 0) = m.sync.ui2 ++ m.sync.uio2
    rw [show (spiIn s pin).resetN = true from hact, if_pos rfl]
    exact h2

/-- The cycle's per-pin output values: the cut's `Glue.outNext` on its packed
configuration, at the machine's pin. -/
theorem out_list_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (hact : runRst s pin = true) :
    ((List.range Machine.Tables.N_OUT_PINS).map (fun o =>
        Glue.outNext (Bridge.Glue.outCfgOf (outEnv m) o) (Machine.Util.bit m.out o)
          true m.dbg.frz)) =
      ((List.range 14).map (fun o =>
        Glue.outNext (outCfgOf s o) (Machine.Util.bit s.outPins o)
          (runRst s pin) s.freeze.frz)) := by
  obtain ⟨-, hfrz, -, -, -, -, -, -, -, -, -⟩ := hrel.dbg
  rw [show Machine.Tables.N_OUT_PINS = 14 from rfl]
  apply List.map_congr_left
  intro o ho
  rw [outCfg_eq s m pin hrel o, hrel.out, hact, hfrz]

/-- The cycle's per-pin output-enable values. -/
theorem oen_list_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (hact : runRst s pin = true) :
    ((List.range Machine.Tables.N_OE_PINS).map (fun o =>
        Glue.oeNext (Bridge.Glue.outCfgOf (outEnv m) o) (Machine.Util.bit m.oen o)
          true m.dbg.frz)) =
      ((List.range 8).map (fun o =>
        Glue.oeNext (outCfgOf s o) (Machine.Util.bit s.oenPins o)
          (runRst s pin) s.freeze.frz)) := by
  obtain ⟨-, hfrz, -, -, -, -, -, -, -, -, -⟩ := hrel.dbg
  rw [show Machine.Tables.N_OE_PINS = 8 from rfl]
  apply List.map_congr_left
  intro o ho
  rw [outCfg_eq s m pin hrel o, hrel.oen, hact, hfrz]

/-- **`out`**: the machine's `OUT` register is the cut's (`Bridge.Glue.out_bridge`). -/
theorem premise_out (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.step m pin).out = (activeStep s pin).outPins := by
  have hb := (Bridge.Glue.out_bridge (outEnv m) (cvRange m) m.dbg.frz).1
  simp only [outEnv] at hb
  rw [machine_step_active s m pin hrel hact, runStep_out, hb]
  show Machine.Util.bv 14 (Machine.Util.packBits ((List.range Machine.Tables.N_OUT_PINS).map
      (fun o => Glue.outNext (Bridge.Glue.outCfgOf (outEnv m) o) (Machine.Util.bit m.out o)
        true m.dbg.frz))) = outNextPins s pin
  rw [out_list_eq s m pin hrel hact]
  unfold outNextPins
  rfl

/-- **`oen`**: the machine's `OEN` register is the cut's. -/
theorem premise_oen (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.step m pin).oen = (activeStep s pin).oenPins := by
  have hb := (Bridge.Glue.out_bridge (outEnv m) (cvRange m) m.dbg.frz).2
  simp only [outEnv] at hb
  rw [machine_step_active s m pin hrel hact, runStep_oen, hb]
  show Machine.Util.bv 8 (Machine.Util.packBits ((List.range Machine.Tables.N_OE_PINS).map
      (fun o => Glue.oeNext (Bridge.Glue.outCfgOf (outEnv m) o) (Machine.Util.bit m.oen o)
        true m.dbg.frz))) = oenNextPins s pin
  rw [oen_list_eq s m pin hrel hact]
  unfold oenNextPins
  rfl

end Metronome.ChipCut.Discharge
