import Metronome.ChipCut.Discharge.LineThread

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-- Local copy: the cut's two host-link cuts agree on their shared registers. -/
theorem linkRel_cmd' {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    Bridge.Host.LinkRel s.hostCmd m := by
  have hagree : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
    HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
  rw [← hagree]
  exact hrel.host.base

/-- Local copy: the machine's host write of the cycle is the cut's `hwOf`. -/
theorem ltHw_eq' {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    ltHw m = hwOf s := by
  have hl := linkRel_cmd' hrel hinv
  simp only [ltHw, hwOf]
  rw [← hl.wr, ← hl.addr]
  by_cases hw : s.hostCmd.wr = true
  · rw [if_pos hw, if_pos hw, hl.wdata hw]
  · rw [if_neg hw, if_neg hw]

/-- Local copy: the value of a located host write byte is the write data byte. -/
theorem hwAt_val' (s : State) (blk : String) (inst : Nat) (reg : String) (j v : Nat)
    (h : Machine.Util.hwAt (hwOf s) blk inst reg = some (j, v)) :
    v = s.hostCmd.wdata.toNat := by
  cases hw : s.hostCmd.wr
  · simp [hwOf, hw, Machine.Util.hwAt] at h
  · simp only [hwOf, hw, if_pos rfl] at h
    unfold Machine.Util.hwAt at h
    cases hl : Machine.hostLocate s.hostCmd.addr.toNat with
    | none => simp [hl] at h
    | some loc =>
      rw [hl] at h
      simp only [if_true] at h
      by_cases hc : (loc.blk == blk && loc.inst == inst && loc.reg == reg) = true
      · rw [if_pos hc] at h
        have h2 := congrArg Prod.snd (Option.some.inj h)
        exact h2.symm
      · rw [if_neg hc] at h
        exact absurd h (by simp)

/-! ### `hPhase`: the `LRT.PHASE` two-byte decode -/

/-- The host map's `PHASE` registers are two bytes wide (finite table check). -/
theorem phase_bytes_all :
    (Machine.Tables.hostBlocks.toList.all (fun (_, _, _, _, regs) =>
      regs.toList.all (fun (_, rn, bytes, _) => rn != "PHASE" || bytes == 2))) = true := by
  decide

/-- Any `PHASE` entry of the host map's register lists is two bytes wide. -/
theorem phase_two {blk : String} {base stride inst : Nat}
    {regs : Array (Nat × String × Nat × String)}
    (hmem : (blk, base, stride, inst, regs) ∈ Machine.Tables.hostBlocks)
    {ro : Nat} {rn : String} {bytes : Nat} {acc : String}
    (hreg : (ro, rn, bytes, acc) ∈ regs) (hrn : rn = "PHASE") : bytes = 2 := by
  have h1 : ((blk, base, stride, inst, regs) : String × Nat × Nat × Nat ×
      Array (Nat × String × Nat × String)).2.2.2.2.toList.all
      (fun (_, rn, bytes, _) => rn != "PHASE" || bytes == 2) = true :=
    (List.all_eq_true.mp phase_bytes_all) _ (Array.mem_toList_iff.mpr hmem)
  have h2 := (List.all_eq_true.mp h1) _ (Array.mem_toList_iff.mpr hreg)
  simpa [hrn] using h2

/-- An `if` returning `some x` splits into its two branches. -/
theorem ite_some {α : Type} {c : Prop} [Decidable c] {a b : Option α} {x : α}
    (h : (if c then a else b) = some x) : (c ∧ a = some x) ∨ (¬c ∧ b = some x) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

/-- **The `LRT.PHASE` byte index is below 2.** -/
theorem hostLocate_phase_byte {a : Nat} {l : Machine.HostLoc}
    (h : Machine.hostLocate a = some l) (hreg : l.reg = "PHASE") : l.byte < 2 := by
  unfold Machine.hostLocate at h
  obtain ⟨block, hmem, hf⟩ := Array.exists_of_findSome?_eq_some h
  obtain ⟨blk, base, stride0, inst, regs⟩ := block
  simp only at hf
  rcases ite_some hf with ⟨hf0, hf0'⟩ | ⟨-, hf0'⟩
  · obtain ⟨ent, hregmem, hf1⟩ := Array.exists_of_findSome?_eq_some hf0'
    obtain ⟨ro, rn, bytes, acc⟩ := ent
    rcases ite_some hf1 with ⟨hro, hf1'⟩ | ⟨-, hf1'⟩
    · obtain hl := Option.some.inj hf1'
      have hrn : rn = "PHASE" := by
        rw [← hl] at hreg
        exact hreg
      have hbytes : bytes = 2 := phase_two hmem hregmem hrn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hro
      obtain ⟨h1, h2⟩ := hro
      rw [← hl]
      simp only []
      omega
    · exact absurd hf1' (by simp)
  · exact absurd hf0' (by simp)

/-- A located host write byte: `hwAt`'s byte index and address come from
`hostLocate` of the command address. -/
theorem hwAt_loc {s : State} {blk : String} {inst : Nat} {reg : String} {j v : Nat}
    (h : Machine.Util.hwAt (hwOf s) blk inst reg = some (j, v)) :
    ∃ l : Machine.HostLoc, Machine.hostLocate s.hostCmd.addr.toNat = some l ∧
      l.blk = blk ∧ l.inst = inst ∧ l.reg = reg ∧ l.byte = j := by
  cases hwr : s.hostCmd.wr
  · simp [hwOf, hwr, Machine.Util.hwAt] at h
  · simp only [hwOf, hwr, if_true] at h
    cases hl : Machine.hostLocate s.hostCmd.addr.toNat with
    | none => simp [Machine.Util.hwAt, hl] at h
    | some loc =>
      simp only [Machine.Util.hwAt, hl] at h
      by_cases hc : (loc.blk == blk && loc.inst == inst && loc.reg == reg) = true
      · rw [if_pos hc] at h
        have hinj := Option.some.inj h
        have hb : loc.byte = j := congrArg Prod.fst hinj
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨loc, rfl, hc.1.1, hc.1.2, hc.2, hb⟩
      · rw [if_neg hc] at h
        exact absurd h (by simp)

/-- The packed `phWe` decodes a located byte below 2 back to itself. -/
theorem phase_pack_any {o : Option (Nat × Nat)} {d : Nat}
    (h : ∀ j v, o = some (j, v) → j < 2 ∧ v = d) :
    o =
      (if Metronome.Line.bitAt 0
          ((if byteStrobe o 1 then (1 : BitVec 1) else 0) ++
           (if byteStrobe o 0 then (1 : BitVec 1) else 0)) then
        some (0, d)
      else if Metronome.Line.bitAt 1
          ((if byteStrobe o 1 then (1 : BitVec 1) else 0) ++
           (if byteStrobe o 0 then (1 : BitVec 1) else 0)) then
        some (1, d)
      else none) := by
  cases o with
  | none => simp [byteStrobe, Metronome.Line.bitAt, Machine.Util.nbit]
  | some pv =>
    obtain ⟨j, v⟩ := pv
    obtain ⟨hj, hv⟩ := h j v rfl
    subst hv
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;>
      simp [byteStrobe, Metronome.Line.bitAt, Machine.Util.nbit]

/-- **`WireAgree.hPhase`.** -/
theorem wire_hPhase (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hPhase = (Bridge.Line.absIn (lineIn s pin l.val)).hPhase := by
  intro l
  simp only [ltLineIn, Bridge.Line.absIn, lineIn, ltHw_eq' hrel hinv]
  refine phase_pack_any (fun j v ho => ?_)
  obtain ⟨loc, hl, -, -, hreg, hbyte⟩ := hwAt_loc ho
  exact ⟨by rw [← hbyte]; exact hostLocate_phase_byte hl hreg,
    hwAt_val' s "LRT" l.val "PHASE" j v ho⟩

end Metronome.ChipCut.Discharge
