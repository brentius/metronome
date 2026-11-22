import Metronome.ChipCut.Discharge.Glue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-- The `DBG` block's register map. -/
def dbgRegs : Array (Nat × String × Nat × String) :=
  #[(0x00, "DBG", 1, "RW"), (0x01, "MCTL", 1, "RW"), (0x02, "ECTL", 1, "RW"),
    (0x04, "MISR", 4, "R"), (0x08, "EMASK", 2, "RW"), (0x0A, "ACC", 1, "R"),
    (0x0B, "AFLG", 1, "R"), (0x0C, "FLAGS", 2, "R"), (0x0E, "CST", 2, "R"),
    (0x10, "FPC", 2, "R"), (0x12, "RLV", 2, "RW")]

/-- The block table's `DBG` row (compiled evaluation of the host map). -/
theorem hostBlocks_dbg :
    (Machine.Tables.hostBlocks.toList.all (fun b =>
      !(b.1 == "DBG") || b == ("DBG", 0x2460, 0x20, 1, dbgRegs))) = true := by decide

theorem dbgRegs_emask :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "EMASK") || (ro == 8 && bytes == 2))) = true := by decide

theorem dbgRegs_ectl :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "ECTL") || (ro == 2 && bytes == 1))) = true := by decide

theorem dbgRegs_mctl :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "MCTL") || (ro == 1 && bytes == 1))) = true := by decide

theorem dbgRegs_rlv :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "RLV") || (ro == 18 && bytes == 2))) = true := by decide

/-- A `DBG`-located address's offset within the block and its register lane. -/
theorem hostLocate_dbg_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") :
    ∃ ro rn bytes acc, (ro, rn, bytes, acc) ∈ dbgRegs.toList ∧ rn = l.reg ∧
      a = 0x2460 + ro + l.byte ∧ l.byte < bytes := by
  rw [hostLocate_eq] at h
  obtain ⟨ys, blk, zs, hpush, hfa, -⟩ := Array.findSome?_eq_some_iff.mp h
  obtain ⟨name, base, stride0, inst, regs⟩ := blk
  have hmem : (name, base, stride0, inst, regs) ∈ Machine.Tables.hostBlocks.toList := by
    have h' : (name, base, stride0, inst, regs) ∈
        (ys.push (name, base, stride0, inst, regs) ++ zs).toList := by simp
    rwa [← hpush] at h'
  have hbn : name = "DBG" := by
    have h' := hostLoc_blk a name base stride0 inst regs l hfa
    exact h'.symm.trans hb
  have hball := List.all_eq_true.mp hostBlocks_dbg (name, base, stride0, inst, regs) hmem
  rw [hbn] at hball
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hball
  have heq : ("DBG", base, stride0, inst, regs) = ("DBG", 0x2460, 0x20, 1, dbgRegs) := hball
  have hbase : base = 0x2460 := congrArg (fun x => x.2.1) heq
  have hstride : stride0 = 0x20 := congrArg (fun x => x.2.2.1) heq
  have hinst : inst = 1 := congrArg (fun x => x.2.2.2.1) heq
  have hregs : regs = dbgRegs := congrArg (fun x => x.2.2.2.2) heq
  subst hbase
  subst hstride
  subst hinst
  subst hregs
  dsimp only at hfa
  have hstr : (if (0x20 == 0) = true then
      dbgRegs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else 0x20) = 0x20 := by decide
  rw [hstr] at hfa
  by_cases hc : (0x2460 ≤ a && a < 0x2460 + 0x20 * 1) = true
  · rw [if_pos hc] at hfa
    have hcs := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcs
    obtain ⟨hle, hlt⟩ := hcs
    obtain ⟨ro, rn, bytes, acc, hrmem, hoffle, hofflt, hbyte, hreg⟩ :=
      findSome_byte dbgRegs name ((a - 0x2460) / 0x20) ((a - 0x2460) % 0x20) l hfa
    refine ⟨ro, rn, bytes, acc, hrmem, hreg.symm, ?_, ?_⟩
    · omega
    · omega
  · rw [if_neg hc] at hfa
    simp at hfa

end Metronome.ChipCut.Discharge.DbgMapWire
