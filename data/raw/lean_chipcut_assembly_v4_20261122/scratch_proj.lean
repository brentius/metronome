import Metronome.ChipCut.Discharge.LineThread

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Metronome.ChipCut.Discharge

open Metronome

theorem nbit_testBit (x k : Nat) : Machine.Util.nbit x k = x.testBit k := by
  unfold Machine.Util.nbit
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rfl

theorem nbit_mod8 (x k : Nat) (hk : k < 3) :
    Machine.Util.nbit (x % 8) k = Machine.Util.nbit x k := by
  rw [nbit_testBit, nbit_testBit]
  rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]
  simp [hk]

theorem bv4_mod16 (x : Nat) : Machine.Util.bv 4 (x % 16) = Machine.Util.bv 4 x := by
  unfold Machine.Util.bv
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

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

/-- Projections of a literal `LineIn` (the four non-data fields are unchanged by
the truncation). -/
theorem lineIn_mk_sym (a : Option Machine.SymWrite) (b : Option Nat) (c : Option (Nat × Nat))
    (d : Option Nat) (e : Bool) : (⟨a, b, c, d, e⟩ : Machine.LineIn).sym = a := rfl

theorem lineIn_mk_ctl (a : Option Machine.SymWrite) (b : Option Nat) (c : Option (Nat × Nat))
    (d : Option Nat) (e : Bool) : (⟨a, b, c, d, e⟩ : Machine.LineIn).ctlMove = b := rfl

theorem lineNext_trunc (c : Machine.LineCfg) (st : Machine.LineSt) (cb : Machine.LineComb)
    (p : Machine.PinView) (f : Bool) (i : Machine.LineIn) :
    Machine.lineNext c st cb p i f =
      Machine.lineNext c st cb p
        { i with sym := i.sym.map (fun w => { w with v := w.v % 16 }),
                 ctlMove := i.ctlMove.map (fun v => v % 8) } f := by
  obtain ⟨sy, ct, ph, hc, ht⟩ := i
  show Machine.lineNext c st cb p ⟨sy, ct, ph, hc, ht⟩ f =
    Machine.lineNext c st cb p ⟨sy.map (fun w => { w with v := w.v % 16 }),
      ct.map (fun v => v % 8), ph, hc, ht⟩ f
  unfold Machine.lineNext
  rw [lineIn_mk_sym, lineIn_mk_ctl, lineIn_mk_sym, lineIn_mk_ctl]
  rw [stagedNext_mod16]
  rw [ctlTriple_mod8]

end Metronome.ChipCut.Discharge
