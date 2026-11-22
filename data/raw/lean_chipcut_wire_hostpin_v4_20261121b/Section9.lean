import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-! ### The `LRT.PHASE` byte width -/

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

/-- **The `LRT.PHASE` byte index is below 2.**  `hostLocate`'s `findSome?` over
the block table is unrolled with `ite_some`, so no case split on a symbolic
`hostLocate` is needed. -/
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

/-! ### `hPhase` is false: the `phWe` packing puts byte 0 in bit 1 -/

/-- The concrete state: a completed host write of byte `0x5A` to
`LRT[0].PHASE` byte 0 (address `0x2410`). -/
def hPhaseState (cont : Contents) : State :=
  { resetState cont with
    hostCmd := { HostCmd.resetState with wr := true, addr := 0x2410, wdata := 0x5A }
    hostRead := { HostRead.resetState with wr := true, addr := 0x2410, wdata := 0x5A } }

/-- The machine side of the `PHASE` write decode: byte 0, data `0x5A`. -/
theorem hPhase_mach (cont : Contents) (pin : Machine.PinIn) :
    Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE" = some (0, 0x5A) := by
  show Machine.Util.hwAt
    (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE"
      = some (0, (0x5A : Nat))
  decide

/-- The cut side of the same write: `lineIn`'s `phWe` packs the byte-0 strobe
into **bit 1** (`a ++ b` puts `a` high), so `absIn` reads it as byte 1. -/
theorem hPhase_cut (cont : Contents) (pin : Machine.PinIn) :
    (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase = some (1, 0x5A) := by
  have hpw : (lineIn (hPhaseState cont) pin 0).phWe = (2 : BitVec 2) := by
    show ((if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          0 then (1 : BitVec 1) else 0) ++
        (if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          1 then (1 : BitVec 1) else 0)) = (2 : BitVec 2)
    decide
  have hd : (lineIn (hPhaseState cont) pin 0).hD = 0x5A := rfl
  simp only [Bridge.Line.absIn, hpw, hd]
  decide

/-- **`WireAgree.hPhase` is false.**  The two sides of the field disagree on a
plain `LRT[0].PHASE` byte-0 write: `ChipCut/Wire.lean`'s `phWe` is
`(byte-0 strobe) ++ (byte-1 strobe)`, i.e. the byte-0 strobe lands in bit 1,
while the cut's own `Line.phF` and `Bridge.Line.absIn` read bit 0 as byte 0.
`ltHw_eq` reduces the field's left side to the machine side below, so no
`WireAgree` holds for a related machine on such a cycle. -/
theorem hPhase_false (cont : Contents) (pin : Machine.PinIn) :
    ¬ ((Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE") =
        (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase) := by
  intro h
  rw [hPhase_mach cont pin, hPhase_cut cont pin] at h
  exact absurd h (by decide)

end Metronome.ChipCut.Discharge
