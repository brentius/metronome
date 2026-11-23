/-
# ChipCut premise discharge: host decode and pin vectors (W3)

This file closes the host-decode and pin-vector wiring hypotheses left open by
the five per-field discharge files:

* `LineThread.WireAgree` fields `pinAgree`, `pinLvl`, `pinPrev`, `beat`,
  `hPhase`, `hCtl`, `hTapmissClr`, `hPC`, `hStat`, and the `hcfg` argument of
  `premise_lines`;
* `StreamDbg.DbgWire`'s host `DBG`-window byte decode (`hdbg`) and the
  single-drain exclusivity of the two-byte `EMASK`/`RLV` registers (`hESC`,
  `hRSC`) (`StreamWire.hostctl` is a separate task; see the notes §2.3);
* `MemHostCfg`'s three named facts `hostReq_open_strobe`, `host_open_quiet`,
  `host_open_regVal`.

Each deliverable is a theorem whose statement is verbatim the named hypothesis
(quantified over `(s, m, pin)` with only `hrel : ChipRel s m`, `hinv : Inv s`,
`hact : runRst s pin = true`), or a one-line adapter to it where the field is a
two-sided wiring equality of the cut's and the machine's records.  Two fields
carry one extra hypothesis each, both *named* and not fields of the other side:
the reachable-state invariant `HostPinInv s` (proved at reset and preserved by
`step`) and the SCK-spacing pin-timing premise `host_sck_spacing s pin`.

See `WIRE_HOSTPIN_NOTES.md` for the per-field status.

No `sorry`, no `native_decide`.
-/

import Metronome.ChipCut.Discharge.LineThread
import Metronome.ChipCut.Discharge.StreamDbg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. Bit plumbing -/

/-- A `Nat` below `2 ^ k` has bit `k` clear. -/
theorem nbit_of_lt {x k : Nat} (h : x < 2 ^ k) : Machine.Util.nbit x k = false := by
  simp [Machine.Util.nbit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/-- Appending bit vectors: the value is a shift and an addition (the low part is
below `2 ^ width`). -/
theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm]
  exact (Nat.two_pow_add_eq_or_of_lt y.isLt x.toNat).symm

/-- A truncation's value is the low bits. -/
theorem toNat_trunc {w v : Nat} (x : BitVec w) :
    (BitVec.truncate v x).toNat = x.toNat % 2 ^ v := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

/-- An unsigned shift right's value. -/
theorem toNat_ushr {w : Nat} (x : BitVec w) (i : Nat) :
    (BitVec.ushiftRight x i).toNat = x.toNat / 2 ^ i := by
  rw [Metronome.Bridge.Line.ushiftRight_eq_shift, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- The cut's `sel` of the zero-padded 13-bit pin vector is the machine's `nbit`. -/
theorem sel_pad13 (v : BitVec 13) (k : Nat) :
    Metronome.Line.sel k ((0 : BitVec 3) ++ v) = Machine.Util.nbit v.toNat k := by
  rw [Bridge.Line.sel16_eq_nbit]
  congr 1
  rw [toNat_append']
  simp

/-- The 16-bit level vector of the cut is `{3'd0, 13 pins}`. -/
theorem lvlVec_eq (s : State) : lvlVec s = (0 : BitVec 3) ++ pinLvl s := rfl

/-- The 16-bit rising-edge vector of the cut. -/
theorem riseVec_eq (s : State) :
    riseVec s = (0 : BitVec 3) ++ (pinLvl s &&& ~~~pinPrev s) := rfl

/-- The 16-bit falling-edge vector of the cut. -/
theorem fallVec_eq (s : State) :
    fallVec s = (0 : BitVec 3) ++ (~~~pinLvl s &&& pinPrev s) := rfl

/-! ## 2. The pin levels: `pinLvl`, `pinPrev` -/

/-- The machine's `protoPins` of the synchroniser word is the cut's `pinVec`
value: `P8..P12` are `s2[15:11]`, `P0..P7` are `s2[7:0]`. -/
theorem protoPins_pinVec (x : BitVec 16) :
    Machine.Util.protoPins (BitVec.truncate 8 (BitVec.ushiftRight x 8))
        (BitVec.truncate 8 x) = (Metronome.Debug.Pins.pinVec x).toNat := by
  have hui : (BitVec.truncate 8 (BitVec.ushiftRight x 8)).toNat = x.toNat / 256 % 256 := by
    rw [toNat_trunc, toNat_ushr]
  have huio : (BitVec.truncate 8 x).toNat = x.toNat % 256 := by
    rw [toNat_trunc]
  have hpv : (Metronome.Debug.Pins.pinVec x).toNat
      = (BitVec.truncate 5 (BitVec.ushiftRight x 11)).toNat * 256
        + (BitVec.truncate 8 x).toNat := by
    unfold Metronome.Debug.Pins.pinVec Metronome.Debug.slice
    rw [toNat_append', show (2 : Nat) ^ 8 = 256 from by decide]
    rfl
  have h5 : (BitVec.truncate 5 (BitVec.ushiftRight x 11)).toNat = x.toNat / 2048 % 32 := by
    rw [toNat_trunc, toNat_ushr]
  unfold Machine.Util.protoPins
  rw [hui, huio, hpv, h5]
  have hdiv : x.toNat / 256 % 256 / 8 = x.toNat / 2048 % 32 := by omega
  rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 3 = 8 from by decide]
  omega

/-- `Machine.pinView`'s level is the cut's `pinLvl` (`ChipRel` fixes the
synchroniser words and the replay registers). -/
theorem pinLvl_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (Machine.pinView m.sync m.dbg).lvl = (pinAbs s).lvl := by
  rw [← sync_eq hrel, ← dbg_eq hrel]
  simp only [Machine.pinView, pinAbs, absChip, protoPins_pinVec, Bridge.Debug.level_toNat,
    Machine.Tables.N_IN_PINS]
  rfl

/-- `Machine.pinView`'s previous level is the cut's `pinPrev`. -/
theorem pinPrev_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (Machine.pinView m.sync m.dbg).prev = (pinAbs s).prev := by
  rw [← sync_eq hrel, ← dbg_eq hrel]
  simp only [Machine.pinView, pinAbs, absChip, protoPins_pinVec, Bridge.Debug.previous_toNat,
    Machine.Tables.N_IN_PINS]
  rfl

/-- **`WireAgree.pinLvl`.** -/
theorem wire_pinLvl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.pinView m.sync m.dbg).lvl = (pinAbs s).lvl :=
  pinLvl_eq hrel

/-- **`WireAgree.pinPrev`.** -/
theorem wire_pinPrev (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.pinView m.sync m.dbg).prev = (pinAbs s).prev :=
  pinPrev_eq hrel

/-! ## 3. `pinAgree` -/

/-- **`WireAgree.pinAgree`.**  The cut's free `lvl`/`rise`/`fall` vectors are
the machine's §2 vectors of the synchronised pins. -/
theorem wire_pinAgree (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, Bridge.Line.PinAgree (pinAbs s) (lineIn s pin l.val) := by
  intro l
  have hlvlb : (pinAbs s).lvl = (pinLvl s).toNat := rfl
  have hprevb : (pinAbs s).prev = (pinPrev s).toNat := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [Bridge.Line.PinAbs.view, Machine.PinView.pin, Machine.Tables.N_IN_PINS]
    rw [hlvlb, show (lineIn s pin l.val).lvl = lvlVec s from rfl, lvlVec_eq, sel_pad13]
    by_cases hk : k < 13
    · simp [hk]
    · have hlt : (pinLvl s).toNat < 2 ^ k :=
        Nat.lt_of_lt_of_le (pinLvl s).isLt (Nat.pow_le_pow_right (by decide) (by omega))
      simp [hk, nbit_of_lt hlt]
  · intro k
    simp only [Bridge.Line.PinAbs.view, Machine.PinView.rise, Machine.Tables.N_IN_PINS]
    rw [hlvlb, hprevb, show (lineIn s pin l.val).rise = riseVec s from rfl, riseVec_eq,
      sel_pad13, Bridge.Debug.nbit_and_not]
    by_cases hk : k < 13 <;> simp [hk]
  · intro k
    simp only [Bridge.Line.PinAbs.view, Machine.PinView.fall, Machine.Tables.N_IN_PINS]
    rw [hlvlb, hprevb, show (lineIn s pin l.val).fall = fallVec s from rfl, fallVec_eq,
      sel_pad13, Bridge.Debug.nbit_not_and]
    by_cases hk : k < 13 <;> simp [hk]

/-! ## 4. The host write of the cycle -/

/-- The cut's two host-link cuts agree on their shared registers
(`Inv.hostAgrees`). -/
theorem linkRel_cmd {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    Bridge.Host.LinkRel s.hostCmd m := by
  have hagree : s.hostRead.toHostCmd s.hostCmd.cmd = s.hostCmd :=
    HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees
  rw [← hagree]
  exact hrel.host.base

/-- The machine's host write of the cycle is the cut's `hwOf` (§9). -/
theorem ltHw_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    ltHw m = hwOf s := by
  have hl := linkRel_cmd hrel hinv
  simp only [ltHw, hwOf]
  rw [← hl.wr, ← hl.addr]
  by_cases hw : s.hostCmd.wr = true
  · rw [if_pos hw, if_pos hw, hl.wdata hw]
  · rw [if_neg hw, if_neg hw]

/-- The value of a located host write byte is the write data byte. -/
theorem hwAt_val (s : State) (blk : String) (inst : Nat) (reg : String) (j v : Nat)
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

/-- A one-byte host write read through `hwByte` is `some` exactly under its
`hwAt` locator test, with the write data byte. -/
theorem hwByte_eq (s : State) (blk : String) (inst : Nat) (reg : String) :
    Machine.Util.hwByte (hwOf s) blk inst reg =
      (if (Machine.Util.hwAt (hwOf s) blk inst reg).isSome then
        some s.hostCmd.wdata.toNat else none) := by
  unfold Machine.Util.hwByte
  cases h : Machine.Util.hwAt (hwOf s) blk inst reg with
  | none => simp
  | some pv =>
    obtain ⟨j, v⟩ := pv
    rw [show v = s.hostCmd.wdata.toNat from hwAt_val s blk inst reg j v h]
    simp

/-- **`WireAgree.hCtl`.**  The machine's `LRT.CTL` byte write is the cut's
`absIn` byte write. -/
theorem wire_hCtl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hCtl = (Bridge.Line.absIn (lineIn s pin l.val)).hCtl := by
  intro l
  simp only [ltLineIn, Bridge.Line.absIn, lineIn, hwIsSome, hwData, ltHw_eq hrel hinv,
    hwByte_eq]
  rfl

/-- **`WireAgree.hPC`.**  The machine's `TRT.PC` byte write is the cut's. -/
theorem wire_hPC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).hPC =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hPC := by
  intro t
  simp only [ltThreadIn, Bridge.Thread.absInput, threadIn, hwIsSome, hwData,
    ltHw_eq hrel hinv, hwByte_eq]
  rfl

/-- **`WireAgree.hStat`.**  The machine's `TRT.STAT` byte write is the cut's. -/
theorem wire_hStat (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).hStat =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hStat := by
  intro t
  simp only [ltThreadIn, Bridge.Thread.absInput, threadIn, hwIsSome, hwData,
    ltHw_eq hrel hinv, hwByte_eq]
  rfl

/-- **`WireAgree.hTapmissClr`.**  The machine's `LRT.STAT` clear bit is the
cut's. -/
theorem wire_hTapmissClr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hTapmissClr =
      (Bridge.Line.absIn (lineIn s pin l.val)).hTapmissClr := by
  intro l
  simp only [ltLineIn, Bridge.Line.absIn, lineIn, hwIsSome, hwData, ltHw_eq hrel hinv,
    hwByte_eq]
  by_cases h : (Machine.Util.hwAt (hwOf s) "LRT" l.val "STAT").isSome
  · simp only [h, if_true, Option.getD_some, Bool.true_and]
    exact (Bridge.Line.bitAt_eq_nbit s.hostCmd.wdata 0).symm
  · simp [h, Machine.Util.nbit]

/-! ## 5. The `LRT.PHASE` two-byte decode: `hPhase`

`Bridge.Line.absIn` reads byte `0`/`1` of `LRT.PHASE` from bits `0`/`1` of the
packed strobe word, while the machine's `ltLineIn.hPhase` is the located byte
index `l.byte`.  The cut's `phWe` packs `{byte-1 strobe, byte-0 strobe}`
(`ChipCut/Wire.lean`, RTL `project.v` 520), so bit `0` is byte 0; the only
remaining fact is the host map's own geometry — `LRT.PHASE` is a two-byte
register, so a located write to it has `l.byte < 2`.  (An earlier revision of
`phWe` had the two strobes swapped; the witness of that defect is kept in the
notes as historical evidence, §2.1.) -/

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
theorem hpw_ite_some {α : Type} {c : Prop} [Decidable c] {a b : Option α} {x : α}
    (h : (if c then a else b) = some x) : (c ∧ a = some x) ∨ (¬c ∧ b = some x) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

/-- **The `LRT.PHASE` byte index is below 2.**  `hostLocate`'s `findSome?` over
the block table is unrolled with `hpw_ite_some`, so no case split on a symbolic
`hostLocate` is needed. -/
theorem hostLocate_phase_byte {a : Nat} {l : Machine.HostLoc}
    (h : Machine.hostLocate a = some l) (hreg : l.reg = "PHASE") : l.byte < 2 := by
  unfold Machine.hostLocate at h
  obtain ⟨block, hmem, hf⟩ := Array.exists_of_findSome?_eq_some h
  obtain ⟨blk, base, stride0, inst, regs⟩ := block
  simp only at hf
  rcases hpw_ite_some hf with ⟨hf0, hf0'⟩ | ⟨-, hf0'⟩
  · obtain ⟨ent, hregmem, hf1⟩ := Array.exists_of_findSome?_eq_some hf0'
    obtain ⟨ro, rn, bytes, acc⟩ := ent
    rcases hpw_ite_some hf1 with ⟨hro, hf1'⟩ | ⟨-, hf1'⟩
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

/-- A located host write byte: `hwAt`'s byte index comes from `hostLocate` of
the command address. -/
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

/-- The packed `phWe` decodes a located byte below `2` back to itself. -/
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

/-- **`WireAgree.hPhase`.**  The machine's two-byte `LRT.PHASE` write decode is
the cut's packed byte-strobe decode. -/
theorem wire_hPhase (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hPhase = (Bridge.Line.absIn (lineIn s pin l.val)).hPhase := by
  intro l
  simp only [ltLineIn, Bridge.Line.absIn, lineIn, ltHw_eq hrel hinv]
  refine phase_pack_any (fun j v ho => ?_)
  obtain ⟨loc, hl, -, -, hreg, hbyte⟩ := hwAt_loc ho
  exact ⟨by rw [← hbyte]; exact hostLocate_phase_byte hl hreg,
    hwAt_val s "LRT" l.val "PHASE" j v ho⟩

/-! ## 6. The `DBG` window: byte decode and single-drain exclusivity

The host map is a concrete table.  The facts needed here are all *concrete*
address look-ups (`by decide`) plus bit-vector arithmetic on `dbgOff`; no
general geometry lemma is required. -/

/-- `hostLocate` at `DBG.EMASK` byte 0 (`0x2468`). -/
theorem hostLocate_emask0 :
    (Machine.hostLocate 0x2468).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "EMASK", (0 : Nat)) := by decide

/-- `hostLocate` at `DBG.EMASK` byte 1 (`0x2469`). -/
theorem hostLocate_emask1 :
    (Machine.hostLocate 0x2469).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "EMASK", (1 : Nat)) := by decide

/-- `hostLocate` at `DBG.RLV` byte 0 (`0x2472`). -/
theorem hostLocate_rlv0 :
    (Machine.hostLocate 0x2472).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "RLV", (0 : Nat)) := by decide

/-- `hostLocate` at `DBG.RLV` byte 1 (`0x2473`). -/
theorem hostLocate_rlv1 :
    (Machine.hostLocate 0x2473).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "RLV", (1 : Nat)) := by decide

/-- A `hostDbg` write reads the window offset through a 32-bit comparison. -/
theorem hostDbg_setWidth {w : Bool} {a : BitVec 16} {D : Nat}
    (h : Strobes.hostDbg w (dbgOff a) D = true) :
    BitVec.setWidth 32 (dbgOff a) = BitVec.ofNat 32 D := by
  unfold Strobes.hostDbg at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- A host write at `DBG.EMASK` byte 0 is at `0x2468`. -/
theorem hostDbg_addr8 {w : Bool} {a : BitVec 16}
    (h : Strobes.hostDbg w (dbgOff a) 8 = true) : a = 0x2468 := by
  have hh := hostDbg_setWidth h
  unfold dbgOff at hh
  bv_decide

/-- A host write at `DBG.EMASK` byte 1 is at `0x2469`. -/
theorem hostDbg_addr9 {w : Bool} {a : BitVec 16}
    (h : Strobes.hostDbg w (dbgOff a) 9 = true) : a = 0x2469 := by
  have hh := hostDbg_setWidth h
  unfold dbgOff at hh
  bv_decide

/-- A host write at `DBG.RLV` byte 0 is at `0x2472`. -/
theorem hostDbg_addr18 {w : Bool} {a : BitVec 16}
    (h : Strobes.hostDbg w (dbgOff a) 18 = true) : a = 0x2472 := by
  have hh := hostDbg_setWidth h
  unfold dbgOff at hh
  bv_decide

/-- A host write at `DBG.RLV` byte 1 is at `0x2473`. -/
theorem hostDbg_addr19 {w : Bool} {a : BitVec 16}
    (h : Strobes.hostDbg w (dbgOff a) 19 = true) : a = 0x2473 := by
  have hh := hostDbg_setWidth h
  unfold dbgOff at hh
  bv_decide

/-- The located fields extracted from a `hostLocate` tuple equality. -/
theorem hostLocate_fields {a : Nat} {blk : String} {inst : Nat} {reg : String} {b : Nat}
    (hmap : (Machine.hostLocate a).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some (blk, inst, reg, b)) :
    ∃ l : Machine.HostLoc, Machine.hostLocate a = some l ∧ l.blk = blk ∧ l.inst = inst ∧
      l.reg = reg ∧ l.byte = b := by
  obtain ⟨l, hl, hf⟩ := Option.map_eq_some_iff.mp hmap
  exact ⟨l, hl, by simpa using congrArg (·.1) hf, by simpa using congrArg (·.2.1) hf,
    by simpa using congrArg (·.2.2.1) hf, by simpa using congrArg (·.2.2.2) hf⟩

/-- A `hwAt` hit at the located register, with the write data byte. -/
theorem hwAt_of_loc {s : State} {a : Nat} {blk : String} {inst b : Nat} {reg : String}
    (hwr : s.hostCmd.wr = true) (hmap : (Machine.hostLocate a).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some (blk, inst, reg, b))
    (ha : s.hostCmd.addr.toNat = a) :
    Machine.Util.hwAt (hwOf s) blk inst reg = some (b, s.hostCmd.wdata.toNat) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hmap
  simp only [hwOf, hwr, if_pos rfl, ha, hl, Machine.Util.hwAt, hb, hi, hr, hby]
  simp [hb, hi, hr, hby]

/-- A host write located at `DBG.EMASK` byte 0 is the `EMASK` strobe. -/
theorem hwIsSome_emask0 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2468) : hwIsSome s "DBG" 0 "EMASK" = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "EMASK", (0 : Nat)) := by
    rw [ha]
    exact hostLocate_emask0
  have hw := hwAt_of_loc hwr hmap rfl
  unfold hwIsSome
  rw [hw]
  rfl

/-- A host write located at `DBG.EMASK` byte 0 sets the byte-0 strobe (the cut's
`hEm0` after the orchestrator's 2026-11-22 Wire.lean fix, project.v 662). -/
theorem byteStrobe_emask0 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2468) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "EMASK", (0 : Nat)) := by
    rw [ha]
    exact hostLocate_emask0
  have hw := hwAt_of_loc hwr hmap rfl
  unfold byteStrobe
  rw [hw]
  rfl

/-- A host write located at `DBG.RLV` byte 0 sets the byte-0 strobe (`hRlv0`,
project.v 664). -/
theorem byteStrobe_rlv0 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2472) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "RLV", (0 : Nat)) := by
    rw [ha]
    exact hostLocate_rlv0
  have hw := hwAt_of_loc hwr hmap rfl
  unfold byteStrobe
  rw [hw]
  rfl

/-- A host write located at `DBG.EMASK` byte 1 sets the byte-1 strobe. -/
theorem byteStrobe_emask1 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2469) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "EMASK", (1 : Nat)) := by
    rw [ha]
    exact hostLocate_emask1
  have hw := hwAt_of_loc hwr hmap rfl
  unfold byteStrobe
  rw [hw]
  rfl

/-- A host write located at `DBG.RLV` byte 0 is the `RLV` strobe. -/
theorem hwIsSome_rlv0 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2472) : hwIsSome s "DBG" 0 "RLV" = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "RLV", (0 : Nat)) := by
    rw [ha]
    exact hostLocate_rlv0
  have hw := hwAt_of_loc hwr hmap rfl
  unfold hwIsSome
  rw [hw]
  rfl

/-- A host write located at `DBG.RLV` byte 1 sets the byte-1 strobe. -/
theorem byteStrobe_rlv1 (s : State) (hwr : s.hostCmd.wr = true)
    (ha : s.hostCmd.addr = 0x2473) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = true := by
  have hmap : (Machine.hostLocate s.hostCmd.addr.toNat).map
      (fun l => (l.blk, l.inst, l.reg, l.byte)) = some ("DBG", 0, "RLV", (1 : Nat)) := by
    rw [ha]
    exact hostLocate_rlv1
  have hw := hwAt_of_loc hwr hmap rfl
  unfold byteStrobe
  rw [hw]
  rfl

/-- A host write at `DBG.EMASK` byte 0 sets the `EMASK` strobe. -/
theorem emask0_of_host8 (s : State)
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 8 = true) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true := by
  have hwr : s.hostCmd.wr = true := by
    unfold Strobes.hostDbg hwDbg at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  exact byteStrobe_emask0 s hwr (hostDbg_addr8 h)

/-- A host write at `DBG.EMASK` byte 1 sets the byte-1 strobe. -/
theorem emask1_of_host9 (s : State)
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 9 = true) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = true := by
  have hwr : s.hostCmd.wr = true := by
    unfold Strobes.hostDbg hwDbg at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  exact byteStrobe_emask1 s hwr (hostDbg_addr9 h)

/-- A host write at `DBG.RLV` byte 0 sets the `RLV` strobe. -/
theorem rlv0_of_host18 (s : State)
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 18 = true) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true := by
  have hwr : s.hostCmd.wr = true := by
    unfold Strobes.hostDbg hwDbg at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  exact byteStrobe_rlv0 s hwr (hostDbg_addr18 h)

/-- A host write at `DBG.RLV` byte 1 sets the byte-1 strobe. -/
theorem rlv1_of_host19 (s : State)
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 19 = true) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = true := by
  have hwr : s.hostCmd.wr = true := by
    unfold Strobes.hostDbg hwDbg at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  exact byteStrobe_rlv1 s hwr (hostDbg_addr19 h)

/-- **`DbgWire.hdbg`.**  The machine's host `DBG` byte (`FREEZE`/`FRZ`/`FRZD`
write) is the cut's `DBG`-window byte decode. -/
theorem dbgWire_hdbg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Machine.Util.hwByte (machHw m) "DBG" 0 "DBG" =
      (if (freezeIn s pin).dbgWrite then some (freezeIn s pin).data.toNat else none) := by
  have hhw : machHw m = hwOf s := by
    simp only [machHw]
    rw [hostNext_hw]
    exact ltHw_eq hrel hinv
  simp only [hhw, freezeIn, hwIsSome, hwData, hwByte_eq]
  rfl

/-- **`DbgWire.hESC`.**  A two-byte `EMASK` register cannot receive both bytes
from drains in one cycle: the drain addresses one byte. -/
theorem dbgWire_hESC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrEm0 && !(dbgCtrlIn s pin).hEm0 &&
      (dbgCtrlIn s pin).dWrEm1 && !(dbgCtrlIn s pin).hEm1) = false := by
  rw [Bool.eq_false_iff]
  intro hcon
  unfold dbgCtrlIn at hcon
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcon
  obtain ⟨⟨⟨hd0, hne0⟩, hd1⟩, hne1⟩ := hcon
  simp only [Bool.not_eq_true] at hne0 hne1
  unfold Strobes.dbgByteWrite at hd0 hd1
  have hdrain0 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8) = true := by
    cases hb : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 8 with
    | true =>
      rw [emask0_of_host8 s hb] at hne0
      exact absurd hne0 (by decide)
    | false =>
      rw [hb, Bool.false_or, Bool.and_eq_true] at hd0
      exact hd0.2
  have hdrain1 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9) = true := by
    cases hb : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 9 with
    | true =>
      rw [emask1_of_host9 s hb] at hne1
      exact absurd hne1 (by decide)
    | false =>
      rw [hb, Bool.false_or, Bool.and_eq_true] at hd1
      exact hd1.2
  have e1 : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 8 := beq_iff_eq.mp hdrain0
  have e2 : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 9 := beq_iff_eq.mp hdrain1
  have hbad : (BitVec.ofNat 32 8) = BitVec.ofNat 32 9 := by rw [← e1, e2]
  exact absurd hbad (by decide)

/-- **`DbgWire.hRSC`.**  The same single-drain exclusivity for `RLV`. -/
theorem dbgWire_hRSC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrRlv0 && !(dbgCtrlIn s pin).hRlv0 &&
      (dbgCtrlIn s pin).dWrRlv1 && !(dbgCtrlIn s pin).hRlv1) = false := by
  rw [Bool.eq_false_iff]
  intro hcon
  unfold dbgCtrlIn at hcon
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcon
  obtain ⟨⟨⟨hd0, hne0⟩, hd1⟩, hne1⟩ := hcon
  simp only [Bool.not_eq_true] at hne0 hne1
  unfold Strobes.dbgByteWrite at hd0 hd1
  have hdrain0 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18) = true := by
    cases hb : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 18 with
    | true =>
      rw [rlv0_of_host18 s hb] at hne0
      exact absurd hne0 (by decide)
    | false =>
      rw [hb, Bool.false_or, Bool.and_eq_true] at hd0
      exact hd0.2
  have hdrain1 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19) = true := by
    cases hb : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 19 with
    | true =>
      rw [rlv1_of_host19 s hb] at hne1
      exact absurd hne1 (by decide)
    | false =>
      rw [hb, Bool.false_or, Bool.and_eq_true] at hd1
      exact hd1.2
  have e1 : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 18 := beq_iff_eq.mp hdrain0
  have e2 : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 19 := beq_iff_eq.mp hdrain1
  have hbad : (BitVec.ofNat 32 18) = BitVec.ofNat 32 19 := by rw [← e1, e2]
  exact absurd hbad (by decide)

/-! ## 7. Host-link strobe exclusivity and quietness

`hostReq_open_strobe` and the `wr` half of `host_open_quiet` are one-cycle
pulse properties of the command machine.  They are stated under a new
reachable-state invariant `HostPinInv`, proved here to hold at reset and be
preserved by `step`:

* `wr` and `rd` are the outputs of `wrNext`/`rdNext`, which require `!isRd` and
  `isRd` respectively, so they are never both up;
* `wr` and `rd` are both set only by a completing byte, which clears `bitc`, so
  a strobe is never up while `bitc = 7` — the fact `host_open_quiet`'s `wr`
  conjunct needs (`completing` requires `bitc = 7`).

The `ack` conjunct of `host_open_quiet` is *not* a state invariant: it is the
SCK-spacing pin-timing premise `host_sck_spacing` of §7.1 below. -/

/-- Reachable-state facts about the host command machine that the strobe and
quietness fields need. -/
structure HostPinInv (s : State) : Prop where
  /-- the two strobes are never up together. -/
  wrRd : ¬(s.hostCmd.wr = true ∧ s.hostCmd.rd = true)
  /-- a write strobe is never up with a full bit counter. -/
  wrBitc : s.hostCmd.wr = true → s.hostCmd.bitc = 0
  /-- a read strobe is never up with a full bit counter. -/
  rdBitc : s.hostCmd.rd = true → s.hostCmd.bitc = 0

/-- The right conjunct of a true `&&`. -/
theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases hb : b with
  | false => rw [hb] at h; simp at h
  | true => rfl

/-- `HostCmd.step` never raises both strobes. -/
theorem step_wr_rd_excl (s : HostCmd.State) (i : HostCmd.Input) :
    ¬((HostCmd.step s i).wr = true ∧ (HostCmd.step s i).rd = true) := by
  rintro ⟨h1, h2⟩
  have hw : (!s.isRd) = true := and_right h1
  have hd : s.isRd = true := and_right h2
  rw [hd] at hw
  exact absurd hw (by decide)

/-- A write strobe is set only by a completing byte. -/
theorem wrNext_completing (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.wrNext s i = true) : HostCmd.completing s i = true := by
  by_cases hc : HostCmd.completing s i = true
  · exact hc
  · have hc' : HostCmd.completing s i = false := by
      cases hv : HostCmd.completing s i <;> simp_all
    unfold HostCmd.wrNext at h
    rw [hc'] at h
    simp at h

/-- A read strobe is set only by a completing byte. -/
theorem rdNext_completing (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.rdNext s i = true) : HostCmd.completing s i = true := by
  by_cases hc : HostCmd.completing s i = true
  · exact hc
  · have hc' : HostCmd.completing s i = false := by
      cases hv : HostCmd.completing s i <;> simp_all
    unfold HostCmd.rdNext at h
    rw [hc'] at h
    simp at h

/-- A completing byte clears the bit counter. -/
theorem bitcNext_completing (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = true) : HostCmd.bitcNext s i = 0 := by
  have hsr : HostCmd.sr i = true := by
    unfold HostCmd.completing at h
    by_cases hs : HostCmd.sr i = true
    · exact hs
    · have hs' : HostCmd.sr i = false := by
        cases hv : HostCmd.sr i <;> simp_all
      rw [hs'] at h
      simp at h
  have hb : (s.bitc == 7) = true := by
    have h2 := h
    unfold HostCmd.completing at h2
    rw [hsr] at h2
    simpa using h2
  have hb7 : s.bitc = 7 := by simpa using hb
  by_cases h1 : i.resetN = true <;> by_cases h2 : i.csN = true <;>
    simp [HostCmd.bitcNext, hsr, hb7, h1, h2]

/-- The invariant is preserved by one cycle (active or reset). -/
theorem hostPinInv_step (s : State) (pin : Machine.PinIn) (h : HostPinInv s) :
    HostPinInv (step s pin) := by
  unfold step
  by_cases hr : runRst s pin = true
  · rw [if_pos hr]
    refine ⟨?_, ?_, ?_⟩
    · show ¬(((HostCmd.step s.hostCmd (hostCmdIn s pin)).wr = true) ∧
          ((HostCmd.step s.hostCmd (hostCmdIn s pin)).rd = true))
      exact step_wr_rd_excl s.hostCmd (hostCmdIn s pin)
    · intro hw
      exact bitcNext_completing _ _ (wrNext_completing _ _ hw)
    · intro hd
      exact bitcNext_completing _ _ (rdNext_completing _ _ hd)
  · rw [if_neg hr]
    exact ⟨by simp [resetChip, resetState, HostCmd.resetState],
      by simp [resetChip, resetState, HostCmd.resetState],
      by simp [resetChip, resetState, HostCmd.resetState]⟩

/-- The invariant holds at reset. -/
theorem hostPinInv_reset (cont : Contents) : HostPinInv (resetState cont) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [resetState, HostCmd.resetState]

/-- **`hostReq_open_strobe`.**  The host link never has both strobes up. -/
theorem hostReq_open_strobe (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) :
    ¬(s.hostCmd.wr = true ∧ s.hostCmd.rd = true) :=
  hpinv.wrRd

/-- The `wr` conjunct of `host_open_quiet`: in a completing cycle the host link
has no write strobe up. -/
theorem quiet_wr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) :
    HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
      (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false := by
  intro h
  have hbit : (s.hostCmd.bitc == 7) = true := by
    have h2 := h
    unfold HostCmd.completing at h2
    rw [Bool.and_eq_true] at h2
    have hb : ((s.hostRead.toHostCmd s.hostCmd.cmd).bitc == 7) = true := h2.2
    rw [show (s.hostRead.toHostCmd s.hostCmd.cmd).bitc = s.hostRead.bitc from rfl] at hb
    rw [hinv.hostAgrees.bitc_eq] at hb
    exact hb
  by_cases hw : s.hostCmd.wr = true
  · have h0 := hpinv.wrBitc hw
    rw [h0] at hbit
    exact absurd hbit (by decide)
  · have hwf : s.hostCmd.wr = false := by
      cases hv : s.hostCmd.wr <;> simp_all
    have hwr : (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false := by
      rw [show (s.hostRead.toHostCmd s.hostCmd.cmd).wr = s.hostRead.wr from rfl,
        hinv.hostAgrees.wr_eq]
      exact hwf
    exact hwr

/-! ### 7.1 The SCK-spacing pin-timing premise -/

/-- The pin-timing premise of `host_open_quiet` (§7.1): a byte-completing `SR`
edge never coincides with a host acknowledgement (a data-RAM landing or a
pending register-read acknowledgement).

This is a no-coincidence condition, STRONGER than the `SCK ≤ clk/16` rate limit
alone (corrected 2026-11-22 after the second independent review).  `SPEC_V2` §9
bounds `SCK` at `clk/16`, so byte completions are at least 128 clock cycles
apart.  The register-read acknowledgement `rack` is a one-cycle pulse two cycles
after the completing edge that issued the read, so normal SPI timing keeps it
clear of the next completion.  The data-RAM landing, however, depends on
arbitration: streams S0/S1 and P0 can delay the host's RAM service, and a grant
one cycle before a completing edge puts the landing on that edge and violates
this premise.  The RTL gives no unconditional host service bound; SPEC §9's
12-cycle RAM service budget (sufficient for a timely read) is what a program must
respect, and it implies this premise.  It is a waveform/arbitration fact, not a
state invariant: a `clk/2`-rate `SCK` would satisfy every `ChipRel`/`Inv` state
while breaking the coincidence. -/
def host_sck_spacing (s : State) (pin : Machine.PinIn) : Prop :=
  HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
    s.hostRead.rack = false ∧ hostLand s = false

/-- **`host_open_quiet`.**  In a completing cycle the host link has no write
strobe, no `rack` and no RAM landing (`HostCmd.ackBit` is their `||`); the `wr`
half is `quiet_wr` (state invariant), the acknowledgement half is the named
pin-timing premise `host_sck_spacing`. -/
theorem host_open_quiet (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) (hspacing : host_sck_spacing s pin) :
    HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
      (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false ∧
        HostCmd.ackBit (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = false := by
  intro h
  refine ⟨quiet_wr s m pin hrel hinv hact hpinv h, ?_⟩
  obtain ⟨hrack, hland⟩ := hspacing h
  unfold HostCmd.ackBit
  rw [show (s.hostRead.toHostCmd s.hostCmd.cmd).rack = s.hostRead.rack from rfl,
    show (hostReadIn s pin).toHostCmd.hland = hostLand s from rfl, hrack, hland]
  rfl

/-! ## 8. The register-read value: the `hostRead` congruence

`host_open_regVal` is `Bridge.Host.regVal (absChip s) cv = Bridge.Host.regVal m cv`,
i.e. the machine's register decode on the related states.  `regVal` is the
`.inl` value of `Machine.hostRead`, so the obligation is a congruence of
`hostRead` under `ChipRel`.

Proved here: the whole record/vector equalities `ctrl_eq` (all twelve control
registers), the five unit registers `hostRead` reads, the whole line and thread
vectors (`absChip_lines_eq`, `absChip_threads_eq`), and the core/stream
projections it reads (`XT`, `XV`, `RV`, `FPC`, `POS`, `BIDX`, `STARVED`, the
last through a `Vector.toList.any` congruence because whole stream vectors are
not equal — `BufRel` guards `WB`/`NV`).  `hostRead_eq` then closes the 30-arm
decode, and `host_open_regVal` is its one-line consequence. -/

/-- The whole control record is the cut's (`CtrlRel`). -/
theorem ctrl_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl = m.ctrl := by
  have h := hrel.ctrl
  simp only [CtrlRel] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [absChip]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11, ← h12]

/-- The units' `A` register agrees (`UnitsRel`). -/
theorem absChip_units_a {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.a = m.units.a := by
  obtain ⟨_, _, h, _, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `Z` flag agrees. -/
theorem absChip_units_z {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.z = m.units.z := by
  obtain ⟨_, _, _, h, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `C` flag agrees. -/
theorem absChip_units_c {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.c = m.units.c := by
  obtain ⟨_, _, _, _, h, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `N` flag agrees. -/
theorem absChip_units_n {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.n = m.units.n := by
  obtain ⟨_, _, _, _, _, h, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `F` register agrees. -/
theorem absChip_units_f {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.f = m.units.f := by
  obtain ⟨h, _, _, _, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The machine's line vector is the cut's (`ChipRel.lines`). -/
theorem absChip_lines_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).lines = m.lines := by
  apply Vector.ext
  intro k hk
  have hl := (hrel.lines ⟨k, hk⟩).symm
  simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
  have hlk : lineAt s k = s.lines[k] := by
    simpa using lineAt_fin s ⟨k, hk⟩
  rw [hlk] at hl
  exact hl

/-- The machine's thread vector is the cut's (`ChipRel.threads`). -/
theorem absChip_threads_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).threads = m.threads := by
  apply Vector.ext
  intro k hk
  have hl := (hrel.threads ⟨k, hk⟩).symm
  simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
  have hlk : threadAt s k = s.threads[k] := by
    simpa using threadAt_fin s ⟨k, hk⟩
  rw [hlk] at hl
  exact hl

/-- The selected stream at a `Fin` index is the vector entry. -/
theorem hpw_streamAt_fin (s : State) (k : Fin 2) : streamAt s k.val = s.streams[k] := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- A valid `vget` is the vector entry. -/
theorem vget_eq' {a : Type} {n : Nat} [Inhabited a] (v : Vector a n) {i : Nat} (h : i < n) :
    Machine.Util.vget v i = v[i]'h := by
  simp [Machine.Util.vget, h]

/-- An out-of-range `vget` is the default. -/
theorem vget_default {a : Type} {n : Nat} [Inhabited a] (v : Vector a n) {i : Nat}
    (h : ¬ i < n) : Machine.Util.vget v i = default := by
  simp [Machine.Util.vget, h]

/-- The machine's line vector is the cut's (`ChipRel.lines`). -/
theorem vget_lines {s : State} {m : Machine.State} (hrel : ChipRel s m) (i : Nat) :
    Machine.Util.vget (absChip s).lines i = Machine.Util.vget m.lines i := by
  have hvec : (absChip s).lines = m.lines := by
    apply Vector.ext
    intro k hk
    have hl := (hrel.lines ⟨k, hk⟩).symm
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
    have hlk : lineAt s k = s.lines[k] := by
      simpa using lineAt_fin s ⟨k, hk⟩
    rw [hlk] at hl
    exact hl
  rw [hvec]

/-- The machine's thread vector is the cut's (`ChipRel.threads`). -/
theorem hpw_vget_threads {s : State} {m : Machine.State} (hrel : ChipRel s m) (i : Nat) :
    Machine.Util.vget (absChip s).threads i = Machine.Util.vget m.threads i := by
  have hvec : (absChip s).threads = m.threads := by
    apply Vector.ext
    intro k hk
    have hl := (hrel.threads ⟨k, hk⟩).symm
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
    have hlk : threadAt s k = s.threads[k] := by
      simpa using threadAt_fin s ⟨k, hk⟩
    rw [hlk] at hl
    exact hl
  rw [hvec]

/-- The core executing-thread register agrees. -/
theorem vget_cores_xt {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).cores k).xt = (Machine.Util.vget m.cores k).xt := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hc := hrel.cores ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.Core.absCore] at *
    exact hc.2.2.2.2.1.symm
  · rw [vget_default _ h, vget_default _ h]

/-- The core execute-valid flag agrees. -/
theorem vget_cores_xv {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).cores k).xv = (Machine.Util.vget m.cores k).xv := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hc := hrel.cores ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.Core.absCore] at *
    exact hc.1.symm
  · rw [vget_default _ h, vget_default _ h]

/-- The core run-valid flag agrees. -/
theorem vget_cores_rv {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).cores k).rv = (Machine.Util.vget m.cores k).rv := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hc := hrel.cores ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.Core.absCore] at *
    exact hc.2.2.1.symm
  · rw [vget_default _ h, vget_default _ h]

/-- The core fetch-PC register agrees. -/
theorem vget_cores_fpc {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).cores k).fpc = (Machine.Util.vget m.cores k).fpc := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hc := hrel.cores ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.Core.absCore] at *
    exact hc.2.2.2.1.symm
  · rw [vget_default _ h, vget_default _ h]

/-- The stream position agrees. -/
theorem vget_streams_pos {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).streams k).pos = (Machine.Util.vget m.streams k).pos := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hs := hrel.streams ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.StreamB.abs] at hs ⊢
    have hsk : streamAt s k = s.streams[k] := by
      simpa using hpw_streamAt_fin s ⟨k, h⟩
    rw [hsk] at hs
    exact hs.1
  · rw [vget_default _ h, vget_default _ h]

/-- The stream bit index agrees. -/
theorem vget_streams_bidx {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).streams k).bidx = (Machine.Util.vget m.streams k).bidx := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hs := hrel.streams ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.StreamB.abs] at hs ⊢
    have hsk : streamAt s k = s.streams[k] := by
      simpa using hpw_streamAt_fin s ⟨k, h⟩
    rw [hsk] at hs
    exact hs.2.1
  · rw [vget_default _ h, vget_default _ h]

/-- The stream starved flag agrees. -/
theorem vget_streams_starved {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Nat) :
    (Machine.Util.vget (absChip s).streams k).starved =
      (Machine.Util.vget m.streams k).starved := by
  by_cases h : k < 2
  · rw [vget_eq' _ h, vget_eq' _ h]
    have hs := hrel.streams ⟨k, h⟩
    simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn, Bridge.StreamB.abs] at hs ⊢
    have hsk : streamAt s k = s.streams[k] := by
      simpa using hpw_streamAt_fin s ⟨k, h⟩
    rw [hsk] at hs
    exact hs.2.2.2.2.2.2.2.2.2.1
  · rw [vget_default _ h, vget_default _ h]

/-- `List.any` over a two-element list. -/
theorem list_any_len_two {α : Type} (l : List α) (h : l.length = 2) (p : α → Bool) :
    l.any p = (p l[0] || p l[1]) := by
  match l with
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => simp
  | a :: b :: c :: rest => simp at h

/-- `List.any` over a two-element `Vector`. -/
theorem toList_any_two {α : Type} (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p v[0] || p v[1]) := by
  have hlen : v.toList.length = 2 := Vector.length_toList
  rw [list_any_len_two v.toList hlen p]
  have h0 : v.toList[0]'(by rw [hlen]; omega) = v[0] := Vector.getElem_toList _
  have h1 : v.toList[1]'(by rw [hlen]; omega) = v[1] := Vector.getElem_toList _
  rw [h0, h1]

/-- `List.any` over a two-element `Vector`, in `vget` form. -/
theorem vget_toList_any_two {α : Type} [Inhabited α] (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p (Machine.Util.vget v 0) || p (Machine.Util.vget v 1)) := by
  rw [toList_any_two, vget_eq' _ (by decide : 0 < 2), vget_eq' _ (by decide : 1 < 2)]

/-- The `ERRSUM` arm's stream `starved` scan (pointwise; the whole stream
vectors are not equal because `BufRel` guards `WB`/`NV`). -/
theorem streams_any_starved {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).streams.toList.any (fun x => x.starved) =
      m.streams.toList.any (fun x => x.starved) := by
  rw [vget_toList_any_two, vget_toList_any_two, vget_streams_starved hrel 0,
    vget_streams_starved hrel 1]

/-- **`Machine.hostRead` is a `ChipRel` congruence.**  Every arm of the register
decode reads only `ChipRel` projections (the whole `ctrl` and unit records, the
whole `dbg` record, the whole line/thread vectors, the core and stream
projections), so the two decodes agree. -/
theorem hostRead_eq (s : State) (m : Machine.State) (hrel : ChipRel s m)
    (cv : Machine.CfgView) (a : Nat) :
    Machine.hostRead (absChip s) cv a = Machine.hostRead m cv a := by
  unfold Machine.hostRead
  by_cases hd : (Machine.Tables.DATA_BASE ≤ a && a <
      Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) = true
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]
    split
    · rfl
    · split <;> simp_all only [ctrl_eq hrel, absChip_units_a hrel, absChip_units_z hrel,
        absChip_units_c hrel, absChip_units_n hrel, absChip_units_f hrel, dbg_eq hrel,
        absChip_lines_eq hrel, absChip_threads_eq hrel, streams_any_starved hrel,
        vget_lines hrel, hpw_vget_threads hrel, vget_cores_xt hrel, vget_cores_xv hrel,
        vget_cores_rv hrel, vget_cores_fpc hrel, vget_streams_pos hrel,
        vget_streams_bidx hrel, vget_streams_starved hrel]

/-- **`host_open_regVal` from a `hostRead` congruence.**  The register-read value
is the `.inl` value of `Machine.hostRead`, so a congruence of `hostRead` under
`ChipRel` (with the two `cfgView`s identified) gives the field. -/
theorem host_open_regVal_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hread : ∀ (cv : Machine.CfgView) (a : Nat),
      Machine.hostRead (absChip s) cv a = Machine.hostRead m cv a) :
    Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg) := by
  have hcfgv : Machine.cfgView m.cfg = Machine.cfgView s.cont.cfg := by rw [hrel.cfg]
  have haddr : (absChip s).host.addr = m.host.addr := by
    rw [show (absChip s).host.addr = s.hostCmd.addr from rfl, (linkRel_cmd hrel hinv).addr]
  unfold Bridge.Host.regVal
  simp only [hcfgv, haddr, hread]

/-- **`host_open_regVal`.**  The machine's register-read value is the cut's
`regVal` input (the `hostRead` congruence at the related address). -/
theorem host_open_regVal (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg) :=
  host_open_regVal_of s m pin hrel hinv hact (fun cv a => hostRead_eq s m hrel cv a)

/-! ## 9. The line configuration decode/encode round trip, `hcfg` and `beat`

`hcfg` is `(cfgView m.cfg).lines[l] = absCfg (lineCfgOf ((cfgView …).lines[l]))`;
the round trip needs only the bit widths the decode itself guarantees.  `beat`
then follows from `Bridge.Line.beat_bridge`. -/

theorem hpw_bget_lt (a : ByteArray) (i : Nat) : Machine.Util.bget a i < 256 := by
  unfold Machine.Util.bget
  simpa using UInt8.toNat_lt (a.get! i)

theorem foldr_lt (a : ByteArray) (base : Nat) (l : List Nat) :
    (l.foldr (fun k acc => acc * 256 + Machine.Util.bget a (base + k)) 0) < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have ih' : xs.foldr (fun k acc => acc * 256 + Machine.Util.bget a (base + k)) 0
        ≤ 256 ^ xs.length - 1 := by omega
    have hb : Machine.Util.bget a (base + x) ≤ 255 := by have := hpw_bget_lt a (base + x); omega
    have hA : 1 ≤ 256 ^ xs.length := Nat.one_le_pow _ _ (by decide)
    omega

theorem hpw_bgetLE_lt (a : ByteArray) (base w : Nat) :
    Machine.Util.bgetLE a base w < 256 ^ w := by
  unfold Machine.Util.bgetLE
  simpa using foldr_lt a base (List.range w)

theorem cfgLE_two_lt (c : Machine.Config) (a : Nat) : Machine.Util.cfgLE c a 2 < 65536 := by
  unfold Machine.Util.cfgLE
  have := hpw_bgetLE_lt c.img (a - Machine.Tables.LINE_BASE) 2
  simpa using this

theorem cfgLE_four_lt (c : Machine.Config) (a : Nat) :
    Machine.Util.cfgLE c a 4 < 4294967296 := by
  unfold Machine.Util.cfgLE
  have := hpw_bgetLE_lt c.img (a - Machine.Tables.LINE_BASE) 4
  simpa using this

theorem nbits04 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Machine.Util.nbits (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)) 0 4 = p := by
  unfold Machine.Util.nbits
  cases b1 <;> cases b2 <;> simp only [Bool.false_eq_true, if_true, if_false,
    Nat.shiftRight_zero, show (2 : Nat) ^ 4 = 16 from by decide] <;> omega

theorem nbits42 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Machine.Util.nbits (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)) 4 2 = q := by
  unfold Machine.Util.nbits
  cases b1 <;> cases b2 <;> simp only [Bool.false_eq_true, if_true, if_false,
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 4 = 16 from by decide,
    show (2 : Nat) ^ 2 = 4 from by decide] <;> omega

theorem nbit6 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Machine.Util.nbit (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)) 6 = b1 := by
  unfold Machine.Util.nbit
  cases b1 <;> cases b2 <;>
    simp only [Bool.false_eq_true, if_true, if_false, beq_iff_eq, beq_eq_false_iff_ne,
      Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 6 = 64 from by decide] <;> omega

theorem nbit7 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Machine.Util.nbit (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)) 7 = b2 := by
  unfold Machine.Util.nbit
  cases b1 <;> cases b2 <;>
    simp only [Bool.false_eq_true, if_true, if_false, beq_iff_eq, beq_eq_false_iff_ne,
      Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 7 = 128 from by decide] <;> omega

theorem packE_lt (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0) < 256 := by
  cases b1 <;> cases b2 <;> simp only [Bool.false_eq_true, if_true, if_false] <;> omega

theorem packE_toNat (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    (BitVec.ofNat 8 (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0))).toNat
      = (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (packE_lt p q hp hq b1 b2)]

theorem slice04 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    (Metronome.Line.slice 0 4 (BitVec.ofNat 8
      (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)))).toNat = p := by
  have hE := packE_toNat p q hp hq b1 b2
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr, Nat.pow_zero, Nat.div_one]
  exact nbits04 p q hp hq b1 b2

theorem slice42 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    (Metronome.Line.slice 4 2 (BitVec.ofNat 8
      (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0)))).toNat = q := by
  have hE := packE_toNat p q hp hq b1 b2
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr]
  simpa [Machine.Util.nbits, Nat.shiftRight_eq_div_pow] using nbits42 p q hp hq b1 b2

theorem bitAt6 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Metronome.Line.bitAt 6 (BitVec.ofNat 8
      (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0))) = b1 := by
  have hE := packE_toNat p q hp hq b1 b2
  rw [Bridge.Line.bitAt_eq_nbit, hE]
  exact nbit6 p q hp hq b1 b2

theorem bitAt7 (p q : Nat) (hp : p < 16) (hq : q < 4) (b1 b2 : Bool) :
    Metronome.Line.bitAt 7 (BitVec.ofNat 8
      (p + 16*q + (if b1 then 64 else 0) + (if b2 then 128 else 0))) = b2 := by
  have hE := packE_toNat p q hp hq b1 b2
  rw [Bridge.Line.bitAt_eq_nbit, hE]
  exact nbit7 p q hp hq b1 b2

theorem ofNat16_val (x : Nat) (h : x < 65536) : (BitVec.ofNat 16 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat32_val (x : Nat) (h : x < 4294967296) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat2_val (x : Nat) (h : x < 4) : (BitVec.ofNat 2 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem nbits44 (p q : Nat) (hp : p < 16) (hq : q < 16) :
    Machine.Util.nbits (p + 16*q) 4 4 = q := by
  unfold Machine.Util.nbits
  simp only [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 4 = 16 from by decide]
  omega

theorem slice04p (p q : Nat) (hp : p < 16) (hq : q < 16) :
    (Metronome.Line.slice 0 4 (BitVec.ofNat 8 (p + 16*q))).toNat = p := by
  have hE : (BitVec.ofNat 8 (p + 16*q)).toNat = (p + 16*q) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr, Nat.pow_zero, Nat.div_one,
    Machine.Util.nbits, Nat.shiftRight_zero, show (2 : Nat) ^ 4 = 16 from by decide]
  omega

theorem slice44 (p q : Nat) (hp : p < 16) (hq : q < 16) :
    (Metronome.Line.slice 4 4 (BitVec.ofNat 8 (p + 16*q))).toNat = q := by
  have hE : (BitVec.ofNat 8 (p + 16*q)).toNat = (p + 16*q) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr]
  simpa [Machine.Util.nbits, Nat.shiftRight_eq_div_pow] using nbits44 p q hp hq

theorem hold_lt (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0) < 256 := by
  cases b <;> cases c <;> simp only [Bool.false_eq_true, if_true, if_false] <;> omega

theorem hold_toNat (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    (BitVec.ofNat 8 (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0))).toNat
      = (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hold_lt p t hp ht b c)]

theorem holdPin (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    (Metronome.Line.slice 0 4 (BitVec.ofNat 8
      (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0)))).toNat = p := by
  have hE := hold_toNat p t hp ht b c
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr, Nat.pow_zero, Nat.div_one,
    Machine.Util.nbits, Nat.shiftRight_zero, show (2 : Nat) ^ 4 = 16 from by decide]
  cases b <;> cases c <;> simp only [Bool.false_eq_true, if_true, if_false] <;> omega

theorem holdLvl (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    Metronome.Line.bitAt 4 (BitVec.ofNat 8
      (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0))) = b := by
  have hE := hold_toNat p t hp ht b c
  rw [Bridge.Line.bitAt_eq_nbit, hE]
  unfold Machine.Util.nbit
  cases b <;> cases c <;>
    simp only [Bool.false_eq_true, if_true, if_false, beq_iff_eq, beq_eq_false_iff_ne,
      Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 4 = 16 from by decide] <;> omega

theorem holdTap (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    (Metronome.Line.slice 5 2 (BitVec.ofNat 8
      (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0)))).toNat = t := by
  have hE := hold_toNat p t hp ht b c
  simp only [Metronome.Line.slice, hE, toNat_trunc, toNat_ushr, Nat.pow_zero, Nat.div_one,
    Machine.Util.nbits, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 5 = 32 from by decide, show (2 : Nat) ^ 2 = 4 from by decide]
  cases b <;> cases c <;> simp only [Bool.false_eq_true, if_true, if_false] <;> omega

theorem holdHen (p t : Nat) (hp : p < 16) (ht : t < 4) (b c : Bool) :
    Metronome.Line.bitAt 7 (BitVec.ofNat 8
      (p + 16 * (if b then 1 else 0) + 32 * t + (if c then 128 else 0))) = c := by
  have hE := hold_toNat p t hp ht b c
  rw [Bridge.Line.bitAt_eq_nbit, hE]
  unfold Machine.Util.nbit
  cases b <;> cases c <;>
    simp only [Bool.false_eq_true, if_true, if_false, beq_iff_eq, beq_eq_false_iff_ne,
      Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 7 = 128 from by decide] <;> omega

/-- **The line configuration decode/encode round trip.** -/
theorem absCfg_lineCfgOf (lc : Machine.LineCfg)
    (hinc : lc.inc < 65536) (hmod : lc.mod < 65536) (ht0 : lc.t0 < 65536)
    (ht1 : lc.t1 < 65536) (ht2 : lc.t2 < 65536) (hpre : lc.pre < 65536)
    (hwlo : lc.wlo < 65536) (hwhi : lc.whi < 65536)
    (hePin : lc.edgePin < 16) (hePol : lc.edgePol < 4)
    (ht0Pin : lc.t0Pin < 16) (ht0Pol : lc.t0Pol < 4) (hsnap : lc.snap < 4)
    (hpina : lc.pina < 16) (hpinb : lc.pinb < 16)
    (hlut0 : lc.lut0 < 4294967296) (hlut1 : lc.lut1 < 4294967296)
    (hhpin : lc.hpin < 16) (hhtap : lc.htap < 4) :
    Bridge.Line.absCfg (lineCfgOf lc) = lc := by
  obtain ⟨inc, mod, t0, t1, t2, pre, wlo, whi, edgePin, edgePol, wen, follow, t0Pin, t0Pol,
    t0src, snap, pina, pinb, lut0, lut1, hpin, hlvl, htap, hen⟩ := lc
  simp only at *
  simp only [Bridge.Line.absCfg, lineCfgOf, Metronome.Line.Config.edgePin,
    Metronome.Line.Config.edgePol, Metronome.Line.Config.wen, Metronome.Line.Config.follow,
    Metronome.Line.Config.t0Pin, Metronome.Line.Config.t0Pol, Metronome.Line.Config.t0src,
    Metronome.Line.Config.pinaSel, Metronome.Line.Config.pinbSel, Metronome.Line.Config.hpin,
    Metronome.Line.Config.hlvl, Metronome.Line.Config.htap, Metronome.Line.Config.hen]
  rw [Machine.LineCfg.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact ofNat16_val inc hinc
  · exact ofNat16_val mod hmod
  · exact ofNat16_val t0 ht0
  · exact ofNat16_val t1 ht1
  · exact ofNat16_val t2 ht2
  · exact ofNat16_val pre hpre
  · exact ofNat16_val wlo hwlo
  · exact ofNat16_val whi hwhi
  · exact slice04 edgePin edgePol hePin hePol wen follow
  · exact slice42 edgePin edgePol hePin hePol wen follow
  · exact bitAt6 edgePin edgePol hePin hePol wen follow
  · exact bitAt7 edgePin edgePol hePin hePol wen follow
  · simpa using slice04 t0Pin t0Pol ht0Pin ht0Pol t0src false
  · simpa using slice42 t0Pin t0Pol ht0Pin ht0Pol t0src false
  · simpa using bitAt6 t0Pin t0Pol ht0Pin ht0Pol t0src false
  · exact ofNat2_val snap hsnap
  · simpa using slice04p pina pinb hpina hpinb
  · exact slice44 pina pinb hpina hpinb
  · exact ofNat32_val lut0 hlut0
  · exact ofNat32_val lut1 hlut1
  · exact holdPin hpin htap hhpin hhtap hlvl hen
  · exact holdLvl hpin htap hhpin hhtap hlvl hen
  · exact holdTap hpin htap hhpin hhtap hlvl hen
  · exact holdHen hpin htap hhpin hhtap hlvl hen

/-- The decode bounds of the line configuration. -/
theorem line_cfg_bounds (c : Machine.Config) (l : Fin 4) :
    ((Machine.cfgView c).lines[l]).inc < 65536 ∧
      ((Machine.cfgView c).lines[l]).mod < 65536 ∧
      ((Machine.cfgView c).lines[l]).t0 < 65536 ∧
      ((Machine.cfgView c).lines[l]).t1 < 65536 ∧
      ((Machine.cfgView c).lines[l]).t2 < 65536 ∧
      ((Machine.cfgView c).lines[l]).pre < 65536 ∧
      ((Machine.cfgView c).lines[l]).wlo < 65536 ∧
      ((Machine.cfgView c).lines[l]).whi < 65536 ∧
      ((Machine.cfgView c).lines[l]).edgePin < 16 ∧
      ((Machine.cfgView c).lines[l]).edgePol < 4 ∧
      ((Machine.cfgView c).lines[l]).t0Pin < 16 ∧
      ((Machine.cfgView c).lines[l]).t0Pol < 4 ∧
      ((Machine.cfgView c).lines[l]).snap < 4 ∧
      ((Machine.cfgView c).lines[l]).pina < 16 ∧
      ((Machine.cfgView c).lines[l]).pinb < 16 ∧
      ((Machine.cfgView c).lines[l]).lut0 < 4294967296 ∧
      ((Machine.cfgView c).lines[l]).lut1 < 4294967296 ∧
      ((Machine.cfgView c).lines[l]).hpin < 16 ∧
      ((Machine.cfgView c).lines[l]).htap < 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Machine.cfgView, Fin.getElem_fin, Vector.getElem_ofFn, Machine.Config.line,
      Machine.Util.cfgLE]
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact cfgLE_two_lt c _
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact cfgLE_four_lt c _
  · exact cfgLE_four_lt c _
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)

/-- **`premise_lines`' `hcfg`.**  The machine's decoded line configuration is the
cut's window packed back, for the decode's own bit widths. -/
theorem hcfg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4,
      (Machine.cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l.val) := by
  intro l
  have hcf : Machine.cfgView m.cfg = Machine.cfgView s.cont.cfg := by rw [hrel.cfg]
  have hbang : (Machine.cfgView s.cont.cfg).lines[l.val]! =
      (Machine.cfgView s.cont.cfg).lines[l] := getElem!_eq_get _ l.isLt
  show (Machine.cfgView m.cfg).lines[l] = Bridge.Line.absCfg
    (lineCfgOf ((Machine.cfgView s.cont.cfg).lines[l.val]!))
  rw [hcf, hbang]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ :=
    line_cfg_bounds s.cont.cfg l
  exact (absCfg_lineCfgOf _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19).symm

/-- A thread's configured line index is `LINE`'s two bits. -/
theorem hpw_thread_line_lt (c : Machine.Config) (t : Nat) : (c.thread t).line < 4 := by
  simp only [Machine.Config.thread]
  exact Nat.mod_lt _ (by decide)

/-- **`WireAgree.beat`.**  The thread's line `BEAT` is the machine's
`lineComb … .beat` (`Bridge.Line.beat_bridge` under `hcfg` and `pinAgree`). -/
theorem wire_beat (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).beat =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).beat := by
  intro t
  let L := ((Machine.cfgView s.cont.cfg).threads[t.val]!).line
  have hl4 : L < 4 := by
    have h := hpw_thread_line_lt s.cont.cfg t.val
    have h2 : ((Machine.cfgView s.cont.cfg).threads[t.val]!).line < 4 := by
      simpa [Machine.cfgView, Fin.getElem_fin, Vector.getElem_ofFn] using h
    exact h2
  have hinner : (Machine.Util.vget (Machine.cfgView m.cfg).threads t.val).line = L := by
    have h2 : (Machine.Util.vget (Machine.cfgView m.cfg).threads t.val).line =
        ((Machine.cfgView s.cont.cfg).threads[t.val]!).line := by
      rw [hrel.cfg]
      rfl
    rw [h2]
  have hcfg' : (Machine.cfgView m.cfg).lines[L]'hl4 =
      Bridge.Line.absCfg (lineCfg s L) :=
    hcfg s m pin hrel hinv hact (Fin.mk L hl4)
  have hline : m.lines[L]'hl4 = Bridge.Line.absSt (lineAt s L) := by
    simpa using hrel.lines (Fin.mk L hl4)
  simp only [ltThreadIn, Bridge.Thread.absInput, threadIn]
  rw [hinner, vget_eq (v := ltLcs m) hl4]
  simp only [ltLcs, Fin.getElem_fin, Vector.getElem_ofFn]
  have hpc := lineComb_pin_congr ((Machine.cfgView m.cfg).lines[L]'hl4)
    (m.lines[L]'hl4) (Machine.pinView m.sync m.dbg) (pinAbs s).view m.dbg.frz
    (pinLvl_eq hrel) (pinPrev_eq hrel)
  rw [hpc, hline, hcfg']
  have hfrz : m.dbg.frz = s.freeze.frz := by rw [(dbg_eq hrel).symm]; rfl
  rw [hfrz]
  exact Bridge.Line.beat_bridge (lineAt s L) (lineIn s pin L) _ rfl (pinAbs s)
    (wire_pinAgree s m pin hrel hinv hact (Fin.mk L hl4))

end Metronome.ChipCut.Discharge
