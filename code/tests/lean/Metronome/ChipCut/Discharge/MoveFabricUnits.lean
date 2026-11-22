/-
# ChipCut discharge: the counter, LFSR and shifter unit-input fields

This file closes three of the remaining `UnitInputs` fields of
`Metronome/ChipCut/Discharge/CoreUnits.lean` against the machine's move fabric,
building on `Metronome/ChipCut/Discharge/MoveFabric.lean` (`pickScan_mWs`, the
global payload table `DstPayloadTable` and its worked instance `unitInputs_reg`).

Each of `CNTk`, `LFk` and `SHk` is **one write group with several destination
codes** (`Moves.dgTable`): `CNTk` holds `CNTk.LO/HI/DEC` (codes `24+k`, `27+k`,
`30+k`), `LFk` holds `LFk.ST/B0..B3` (codes `33+k`, `35+4k … 38+4k`) and `SHk`
holds `SHk.LD/SH` (codes `18+k`, `20+k`).  The cut reads one `gw` group word and
decodes the *port* from the word's destination code (`Strobes.counterSel` /
`lfsrSel` / `shifterSel`), so each field is one `pickScan_mWs` instance whose `Q`
is that port decode; no data projection is needed (the cut keeps the whole data
byte, unlike `UnitInputs.flag`).

## The one new hypothesis: `DstPortTable`

`DstPayloadTable` decides *which write group* a code belongs to
(`dgTable d == famG f = famIn f (dstOp d)`), which is all `reg`/`flag`-style
fields need (`Q` constant, resp. supplied as `hPQ`).  A port decode additionally
needs *which port* a code is, i.e. the code→constructor map inside one group —
and that is **not** determined by the group: group `8+k` holds both `SHk.LD` and
`SHk.SH`.  `DstKindTable` constrains only `NULL`/`L.SYM`/`T.STOP`/other, and the
kernel cannot reduce `Machine.Util.dstOfName` on the table's parsed names
(`String.splitOnAux` is `@[irreducible]` in Lean 4.35.0 core), so the map cannot
be proved here — exactly the situation of `unitInputs_flag_low4`'s `hPQ`, which is
also an assumed code-level table.  `DstPortTable` states the map at the ten codes
these three fields use; `decode_check_ports.lean` in the evidence directory
checks it by compiled evaluation (like `decode_check_payload.lean`).

## `UnitInputs.sh`: the `SHk.CFG` gate (fixed in round 2)

`shIn.we` is the `SHk` group word's own `we` — RTL `project.v` 396 passes
`.we(w[14])` of that word, and the units cut / README top-wiring row agree
(`we == g_sh[k].w[14]`).  `SHk.CFG` is a *different* write group (`dgTable 22+k =
10+k ≠ 8+k = dgTable 18+k`, `dg_shCfg_ne`) carried by `shCfg`/`cfgWe`, so the two
moves compose independently, exactly as `Machine.shNext` takes an `op` and a
`cfg`.  `Wire.lean`'s `shIn.we` briefly carried an extra `&& !strobe 22+k` gate;
that made this field refutable (a cycle winning both groups gave `none` on the
cut and `some` on the machine, with the shifter state diverging too), which is
what the round‑1 report of this task showed; the gate has been removed and
`unitInputs_sh` is now the field verbatim.

No `sorry`, no `native_decide`.
-/
import Metronome.ChipCut.Discharge.MoveFabric

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.MoveFabric

open Metronome

/-! ## 1. Group words: the strobe and group equality -/

/-- The strobe `OPG(G, D)` is the picked group word's `we` and destination test. -/
theorem strobe_eq (s : State) (pin : Machine.PinIn) (D : BitVec 6) :
    strobe s pin D = ((gw s pin D).we && ((gw s pin D).dst == D)) := by
  simp only [strobe, gw]
  exact Strobes.opg_eq_pick _ _ _ _ _ _

/-- Two destination codes in one write group read the same picked word. -/
theorem gw_congr (s : State) (pin : Machine.PinIn) {D₁ D₂ : BitVec 6}
    (h : Moves.dgTable D₁ = Moves.dgTable D₂) : gw s pin D₁ = gw s pin D₂ := by
  simp only [gw, h]

/-- `CNTk.HI`'s code is in `CNTk.LO`'s write group. -/
theorem dg_cntHi (k : Nat) (hk : k < 3) :
    Moves.dgTable (BitVec.ofNat 6 (27 + k)) = Moves.dgTable (BitVec.ofNat 6 (24 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- `CNTk.DEC`'s code is in `CNTk.LO`'s write group. -/
theorem dg_cntDec (k : Nat) (hk : k < 3) :
    Moves.dgTable (BitVec.ofNat 6 (30 + k)) = Moves.dgTable (BitVec.ofNat 6 (24 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- `LFk.B0`'s code is in `LFk.ST`'s write group. -/
theorem dg_lfB0 (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (35 + 4 * k)) = Moves.dgTable (BitVec.ofNat 6 (33 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem dg_lfB1 (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (36 + 4 * k)) = Moves.dgTable (BitVec.ofNat 6 (33 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem dg_lfB2 (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (37 + 4 * k)) = Moves.dgTable (BitVec.ofNat 6 (33 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem dg_lfB3 (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (38 + 4 * k)) = Moves.dgTable (BitVec.ofNat 6 (33 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- `SHk.SH`'s code is in `SHk.LD`'s write group. -/
theorem dg_shSh (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (20 + k)) = Moves.dgTable (BitVec.ofNat 6 (18 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- **`SHk.CFG` is a different write group** (`10+k ≠ 8+k`), so a cycle may win
both the `SHk` data word and the `SHk.CFG` word; they compose through separate
records (`sh`/`shCfg`), as the RTL and `Machine.shNext` both do. -/
theorem dg_shCfg_ne (k : Nat) (hk : k < 2) :
    Moves.dgTable (BitVec.ofNat 6 (22 + k)) ≠ Moves.dgTable (BitVec.ofNat 6 (18 + k)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-! ## 2. The destination codes of each write group -/

theorem cnt_codes_all (k : Nat) (hk : k < 3) :
    (List.range 64).all (fun d =>
      !(Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k)) ||
        (d == 24 + k || d == 27 + k || d == 30 + k)) = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- A code of `CNTk`'s write group is `24+k`, `27+k` or `30+k`. -/
theorem cnt_codes (k : Nat) (hk : k < 3) (d : Nat) (hd : d < 64)
    (h : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k)) = true) :
    d = 24 + k ∨ d = 27 + k ∨ d = 30 + k := by
  have hall := List.all_eq_true.1 (cnt_codes_all k hk) d (by simpa [List.mem_range] using hd)
  have hall' : (!(Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k))) = true ∨
      (d == 24 + k || d == 27 + k || d == 30 + k) = true := by simpa using hall
  rcases hall' with h' | h'
  · rw [h] at h'
    exact absurd h' (by decide)
  · simp only [Bool.or_eq_true, beq_iff_eq] at h'
    rcases h' with (h' | h') | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

theorem lf_codes_all (k : Nat) (hk : k < 2) :
    (List.range 64).all (fun d =>
      !(Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k)) ||
        (d == 33 + k || d == 35 + 4 * k || d == 36 + 4 * k || d == 37 + 4 * k ||
          d == 38 + 4 * k)) = true := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- A code of `LFk`'s write group is `33+k` or one of the four `Bb` codes. -/
theorem lf_codes (k : Nat) (hk : k < 2) (d : Nat) (hd : d < 64)
    (h : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k)) = true) :
    d = 33 + k ∨ d = 35 + 4 * k ∨ d = 36 + 4 * k ∨ d = 37 + 4 * k ∨ d = 38 + 4 * k := by
  have hall := List.all_eq_true.1 (lf_codes_all k hk) d (by simpa [List.mem_range] using hd)
  have hall' : (!(Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k))) = true ∨
      (d == 33 + k || d == 35 + 4 * k || d == 36 + 4 * k || d == 37 + 4 * k ||
        d == 38 + 4 * k) = true := by simpa using hall
  rcases hall' with h' | h'
  · rw [h] at h'
    exact absurd h' (by decide)
  · simp only [Bool.or_eq_true, beq_iff_eq] at h'
    rcases h' with (((h' | h') | h') | h') | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

theorem sh_codes_all (k : Nat) (hk : k < 2) :
    (List.range 64).all (fun d =>
      !(Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k)) ||
        (d == 18 + k || d == 20 + k)) = true := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- A code of `SHk`'s data write group is `18+k` (`LD`) or `20+k` (`SH`). -/
theorem sh_codes (k : Nat) (hk : k < 2) (d : Nat) (hd : d < 64)
    (h : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k)) = true) :
    d = 18 + k ∨ d = 20 + k := by
  have hall := List.all_eq_true.1 (sh_codes_all k hk) d (by simpa [List.mem_range] using hd)
  have hall' : (!(Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k))) = true ∨
      (d == 18 + k || d == 20 + k) = true := by simpa using hall
  rcases hall' with h' | h'
  · rw [h] at h'
    exact absurd h' (by decide)
  · simp only [Bool.or_eq_true, beq_iff_eq] at h'
    rcases h' with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

/-! ## 3. The code-level port table -/

/-- **The code-level destination-port table.**  For the ten destination codes the
three unit fields read, the machine's decoder carries the port the cut's code
names.  `DstPayloadTable` fixes only the *group* of each code; a group holds
several ports (`SHk` = `LD`/`SH`, `CNTk` = `LO`/`HI`/`DEC`, `LFk` = `ST`/`B0..B3`),
so the port map is a separate table.  Checked by compiled evaluation in
`decode_check_ports.lean` (the kernel cannot reduce `dstOfName`'s `splitOn`). -/
structure DstPortTable : Prop where
  /-- `18+k` is `SHk.LD`. -/
  shLd : ∀ k, k < 2 → Machine.dstOp (18 + k) = .shLd k
  /-- `20+k` is `SHk.SH`. -/
  shSh : ∀ k, k < 2 → Machine.dstOp (20 + k) = .shSh k
  /-- `24+k` is `CNTk.LO`. -/
  cntLo : ∀ k, k < 3 → Machine.dstOp (24 + k) = .cntLo k
  /-- `27+k` is `CNTk.HI`. -/
  cntHi : ∀ k, k < 3 → Machine.dstOp (27 + k) = .cntHi k
  /-- `30+k` is `CNTk.DEC`. -/
  cntDec : ∀ k, k < 3 → Machine.dstOp (30 + k) = .cntDec k
  /-- `33+k` is `LFk.ST`. -/
  lfSt : ∀ k, k < 2 → Machine.dstOp (33 + k) = .lfSt k
  /-- `35+4k` is `LFk.B0`. -/
  lfB0 : ∀ k, k < 2 → Machine.dstOp (35 + 4 * k) = .lfB k 0
  /-- `36+4k` is `LFk.B1`. -/
  lfB1 : ∀ k, k < 2 → Machine.dstOp (36 + 4 * k) = .lfB k 1
  /-- `37+4k` is `LFk.B2`. -/
  lfB2 : ∀ k, k < 2 → Machine.dstOp (37 + 4 * k) = .lfB k 2
  /-- `38+4k` is `LFk.B3`. -/
  lfB3 : ∀ k, k < 2 → Machine.dstOp (38 + 4 * k) = .lfB k 3

/-! ## 4. The unit records on an explicit structure literal

The cut's records are structure literals whose fields are the group strobes.  The
lemmas below unfold the bridge's `absIn`/`absOp` on such a literal (a pure
`rfl`), so the strobe→word rewriting happens on the plain `Bool` fields and never
under an `if`'s `Decidable` instance (where `rw` is pathologically slow). -/

theorem cnt_absIn_fields (resetN we : Bool) (sel : BitVec 2) (d : BitVec 8) :
    Bridge.CounterB.absIn ⟨resetN, we, sel, d⟩ =
      (if !we then (none : Option (Nat × Nat))
        else if sel = 0 then some (0, d.toNat)
        else if sel = 1 then some (1, d.toNat)
        else some (2, d.toNat)) := rfl

theorem lf_absIn_fields (resetN we : Bool) (sel : BitVec 3) (d : BitVec 8)
    (poly : BitVec 32) :
    Bridge.LfsrB.absIn ⟨resetN, we, sel, d, poly⟩ =
      (if !we then (none : Option (Option Nat × Nat))
        else if sel = 0 then some (none, d.toNat)
        else if sel = 1 then some (some 0, d.toNat)
        else if sel = 2 then some (some 1, d.toNat)
        else if sel = 3 then some (some 2, d.toNat)
        else if sel = 4 then some (some 3, d.toNat)
        else none) := rfl

theorem sh_absOp_fields (resetN we sel : Bool) (d : BitVec 8) (cfgWe : Bool)
    (cfgD : BitVec 5) :
    Bridge.ShifterB.absOp ⟨resetN, we, sel, d, cfgWe, cfgD⟩ =
      (if !we then (none : Option (Bool × Nat)) else some (!sel, d.toNat)) := rfl

/-! ## 5. The cut-side port decode, word by word

Each lemma is a pure `Bool` computation: the cut's record is the picked word's
`we`/`dst`/`data` and the group's `OPG` strobes, and the port is the priority mux
of `Strobes.counterSel` / `lfsrSel` / `shifterSel`. -/

/-- The counter port decode over one group's three codes. -/
theorem cnt_word (w : Bool) (dst : BitVec 6) (dat : BitVec 8) (c₀ c₁ c₂ : BitVec 6) :
    (if !((w && (dst == c₀)) || (w && (dst == c₁)) || (w && (dst == c₂))) then
        (none : Option (Nat × Nat))
      else if Metronome.Units.Counter.selOf (w && (dst == c₀)) (w && (dst == c₁)) = 0 then
        some (0, dat.toNat)
      else if Metronome.Units.Counter.selOf (w && (dst == c₀)) (w && (dst == c₁)) = 1 then
        some (1, dat.toNat)
      else some (2, dat.toNat))
      = (if w then
          (if dst == c₀ then (some 0 : Option Nat)
            else if dst == c₁ then some 1 else if dst == c₂ then some 2 else none) |>.map
            (fun a => (a, dat.toNat))
        else none) := by
  cases hw : w <;> cases h₀ : (dst == c₀) <;> cases h₁ : (dst == c₁) <;>
    cases h₂ : (dst == c₂) <;> simp [Metronome.Units.Counter.selOf]

/-- The LFSR port decode over one group's `ST` and `B0..B2` codes (the fourth `B`
code is the mux's fallback, `sel = 4`). -/
theorem lf_word (w : Bool) (dst : BitVec 6) (dat : BitVec 8) (c₀ c₁ c₂ c₃ : BitVec 6) :
    (if !w then (none : Option (Option Nat × Nat))
      else if Metronome.Units.Lfsr.selOf (w && (dst == c₀)) (w && (dst == c₁))
          (w && (dst == c₂)) (w && (dst == c₃)) = 0 then some (none, dat.toNat)
      else if Metronome.Units.Lfsr.selOf (w && (dst == c₀)) (w && (dst == c₁))
          (w && (dst == c₂)) (w && (dst == c₃)) = 1 then some (some 0, dat.toNat)
      else if Metronome.Units.Lfsr.selOf (w && (dst == c₀)) (w && (dst == c₁))
          (w && (dst == c₂)) (w && (dst == c₃)) = 2 then some (some 1, dat.toNat)
      else if Metronome.Units.Lfsr.selOf (w && (dst == c₀)) (w && (dst == c₁))
          (w && (dst == c₂)) (w && (dst == c₃)) = 3 then some (some 2, dat.toNat)
      else if Metronome.Units.Lfsr.selOf (w && (dst == c₀)) (w && (dst == c₁))
          (w && (dst == c₂)) (w && (dst == c₃)) = 4 then some (some 3, dat.toNat)
      else none)
      = (if w then
          (if dst == c₀ then (some none : Option (Option Nat))
            else if dst == c₁ then some (some 0)
            else if dst == c₂ then some (some 1)
            else if dst == c₃ then some (some 2) else some (some 3)) |>.map
            (fun a => (a, dat.toNat))
        else none) := by
  cases hw : w <;> cases h₀ : (dst == c₀) <;> cases h₁ : (dst == c₁) <;>
    cases h₂ : (dst == c₂) <;> cases h₃ : (dst == c₃) <;>
    simp [Metronome.Units.Lfsr.selOf]

/-- The shifter data port decode: `LD` (code `18+k`) is `true`, `SH` (code `20+k`)
is `false`.  The record is **not** gated by `SHk.CFG` (RTL `project.v` 396 passes
the group word's own `w[14]`; see the header note). -/
theorem sh_word (w : Bool) (dst : BitVec 6) (dat : BitVec 8) (c : BitVec 6) :
    (if !w then (none : Option (Bool × Nat))
      else some (!(Metronome.Strobes.shifterSel (w && (dst == c)) == 1), dat.toNat))
      = (if w then (some (!(dst == c)) : Option Bool) |>.map (fun a => (a, dat.toNat))
        else none) := by
  cases hw : w <;> cases hd : (dst == c) <;>
    simp [Metronome.Strobes.shifterSel]

/-! ## 6. The cut records in terms of one group word -/

/-- The cut's counter record: one group pick, the port from the word's code. -/
theorem cnt_absIn (s : State) (pin : Machine.PinIn) (k : Nat) (hk : k < 3) :
    Bridge.CounterB.absIn (cntIn s pin k) =
      (if (gw s pin (BitVec.ofNat 6 (24 + k))).we then
        (if (gw s pin (BitVec.ofNat 6 (24 + k))).dst == BitVec.ofNat 6 (24 + k) then
            (some 0 : Option Nat)
          else if (gw s pin (BitVec.ofNat 6 (24 + k))).dst == BitVec.ofNat 6 (27 + k) then some 1
          else if (gw s pin (BitVec.ofNat 6 (24 + k))).dst == BitVec.ofNat 6 (30 + k) then some 2
          else none) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (24 + k))).data.toNat))
        else none) := by
  have h₁ : gw s pin (BitVec.ofNat 6 (27 + k)) = gw s pin (BitVec.ofNat 6 (24 + k)) :=
    gw_congr s pin (dg_cntHi k hk)
  have h₂ : gw s pin (BitVec.ofNat 6 (30 + k)) = gw s pin (BitVec.ofNat 6 (24 + k)) :=
    gw_congr s pin (dg_cntDec k hk)
  have hrec : cntIn s pin k =
      ⟨runRst s pin,
        (gw s pin (BitVec.ofNat 6 (24 + k))).we && ((gw s pin (BitVec.ofNat 6 (24 + k))).dst ==
            BitVec.ofNat 6 (24 + k)) ||
          (gw s pin (BitVec.ofNat 6 (24 + k))).we && ((gw s pin (BitVec.ofNat 6 (24 + k))).dst ==
            BitVec.ofNat 6 (27 + k)) ||
          (gw s pin (BitVec.ofNat 6 (24 + k))).we && ((gw s pin (BitVec.ofNat 6 (24 + k))).dst ==
            BitVec.ofNat 6 (30 + k)),
        Metronome.Units.Counter.selOf
          ((gw s pin (BitVec.ofNat 6 (24 + k))).we && ((gw s pin (BitVec.ofNat 6 (24 + k))).dst ==
            BitVec.ofNat 6 (24 + k)))
          ((gw s pin (BitVec.ofNat 6 (24 + k))).we && ((gw s pin (BitVec.ofNat 6 (24 + k))).dst ==
            BitVec.ofNat 6 (27 + k))),
        (gw s pin (BitVec.ofNat 6 (24 + k))).data⟩ := by
    simp only [cntIn, strobe_eq, h₁, h₂, Metronome.Strobes.counterSel]
  rw [hrec, cnt_absIn_fields]
  exact cnt_word _ _ _ _ _ _

/-- The cut's LFSR record: one group pick, the port from the word's code. -/
theorem lf_absIn (s : State) (pin : Machine.PinIn) (k : Nat) (hk : k < 2) :
    Bridge.LfsrB.absIn (lfIn s pin k) =
      (if (gw s pin (BitVec.ofNat 6 (33 + k))).we then
        (if (gw s pin (BitVec.ofNat 6 (33 + k))).dst == BitVec.ofNat 6 (33 + k) then
            (some none : Option (Option Nat))
          else if (gw s pin (BitVec.ofNat 6 (33 + k))).dst == BitVec.ofNat 6 (35 + 4 * k) then
            some (some 0)
          else if (gw s pin (BitVec.ofNat 6 (33 + k))).dst == BitVec.ofNat 6 (36 + 4 * k) then
            some (some 1)
          else if (gw s pin (BitVec.ofNat 6 (33 + k))).dst == BitVec.ofNat 6 (37 + 4 * k) then
            some (some 2)
          else some (some 3)) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (33 + k))).data.toNat))
        else none) := by
  have h₁ : gw s pin (BitVec.ofNat 6 (35 + 4 * k)) = gw s pin (BitVec.ofNat 6 (33 + k)) :=
    gw_congr s pin (dg_lfB0 k hk)
  have h₂ : gw s pin (BitVec.ofNat 6 (36 + 4 * k)) = gw s pin (BitVec.ofNat 6 (33 + k)) :=
    gw_congr s pin (dg_lfB1 k hk)
  have h₃ : gw s pin (BitVec.ofNat 6 (37 + 4 * k)) = gw s pin (BitVec.ofNat 6 (33 + k)) :=
    gw_congr s pin (dg_lfB2 k hk)
  have hrec : lfIn s pin k =
      ⟨runRst s pin,
        (gw s pin (BitVec.ofNat 6 (33 + k))).we,
        Metronome.Units.Lfsr.selOf
          ((gw s pin (BitVec.ofNat 6 (33 + k))).we && ((gw s pin (BitVec.ofNat 6 (33 + k))).dst ==
            BitVec.ofNat 6 (33 + k)))
          ((gw s pin (BitVec.ofNat 6 (33 + k))).we && ((gw s pin (BitVec.ofNat 6 (33 + k))).dst ==
            BitVec.ofNat 6 (35 + 4 * k)))
          ((gw s pin (BitVec.ofNat 6 (33 + k))).we && ((gw s pin (BitVec.ofNat 6 (33 + k))).dst ==
            BitVec.ofNat 6 (36 + 4 * k)))
          ((gw s pin (BitVec.ofNat 6 (33 + k))).we && ((gw s pin (BitVec.ofNat 6 (33 + k))).dst ==
            BitVec.ofNat 6 (37 + 4 * k))),
        (gw s pin (BitVec.ofNat 6 (33 + k))).data,
        BitVec.ofNat 32 (s.cont.cfg.poly k)⟩ := by
    simp only [lfIn, strobe_eq, h₁, h₂, h₃, Metronome.Strobes.lfsrSel]
  rw [hrec, lf_absIn_fields]
  exact lf_word _ _ _ _ _ _ _

/-- The cut's shifter data record: one group pick, the port from the word's code,
and **no** `SHk.CFG` gate (`shIn.we` is the `SHk` group word's own `we`). -/
theorem sh_absOp (s : State) (pin : Machine.PinIn) (k : Nat) (hk : k < 2) :
    Bridge.ShifterB.absOp (shIn s pin k) =
      (if (gw s pin (BitVec.ofNat 6 (18 + k))).we then
        (some (!((gw s pin (BitVec.ofNat 6 (18 + k))).dst ==
            BitVec.ofNat 6 (20 + k))) : Option Bool) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (18 + k))).data.toNat))
        else none) := by
  have h₁ : gw s pin (BitVec.ofNat 6 (20 + k)) = gw s pin (BitVec.ofNat 6 (18 + k)) :=
    gw_congr s pin (dg_shSh k hk)
  have hrec : shIn s pin k =
      ⟨runRst s pin,
        (gw s pin (BitVec.ofNat 6 (18 + k))).we,
        Metronome.Strobes.shifterSel
            ((gw s pin (BitVec.ofNat 6 (18 + k))).we && ((gw s pin (BitVec.ofNat 6 (18 + k))).dst ==
              BitVec.ofNat 6 (20 + k))) == 1,
        (gw s pin (BitVec.ofNat 6 (18 + k))).data,
        strobe s pin (BitVec.ofNat 6 (22 + k)),
        BitVec.truncate 5 (gw s pin (BitVec.ofNat 6 (22 + k))).data⟩ := by
    simp only [shIn, strobe_eq, h₁]
  rw [hrec, sh_absOp_fields]
  exact sh_word _ _ _ _

/-! ## 7. The `hPQ` table of each family, from `DstPayloadTable` and `DstPortTable` -/

/-- `hPQ` for the `CNTk` group. -/
theorem cnt_hPQ (hT : DstPayloadTable) (hP : DstPortTable) (k : Nat) (hk : k < 3) :
    ∀ d, d < 64 →
      (match Machine.dstOp d with
        | .cntLo j => if j == k then some (0 : Nat) else none
        | .cntHi j => if j == k then some 1 else none
        | .cntDec j => if j == k then some 2 else none
        | _ => none)
      = (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k)) then
          (if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (24 + k) then some 0
            else if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (27 + k) then some 1
            else if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (30 + k) then some 2 else none)
          else none) := by
  intro d hd
  have hp := hT.payload (.cnt k) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k)) = true
  · have hfam : famIn (.cnt k) (Machine.dstOp d) = true := by rw [← hp]; exact hg
    rw [hp, hfam, if_pos rfl]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      rcases cnt_codes _ (by omega) d hd hg with rfl | rfl | rfl <;>
      simp [hP.cntLo 0 (by omega), hP.cntHi 0 (by omega), hP.cntDec 0 (by omega),
        hP.cntLo 1 (by omega), hP.cntHi 1 (by omega), hP.cntDec 1 (by omega),
        hP.cntLo 2 (by omega), hP.cntHi 2 (by omega), hP.cntDec 2 (by omega)]
  · have hgf : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.cnt k)) = false := by
      simpa using hg
    have hfam : famIn (.cnt k) (Machine.dstOp d) = false := by rw [← hp]; exact hgf
    rw [hp, hfam]
    simp only [Bool.false_eq_true, if_false]
    cases h : Machine.dstOp d <;> simp_all [famIn]

/-- `hPQ` for the `LFk` group. -/
theorem lf_hPQ (hT : DstPayloadTable) (hP : DstPortTable) (k : Nat) (hk : k < 2) :
    ∀ d, d < 64 →
      (match Machine.dstOp d with
        | .lfSt j => if j == k then some (none : Option Nat) else none
        | .lfB j b => if j == k then some (some b) else none
        | _ => none)
      = (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k)) then
          (if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (33 + k) then some none
            else if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (35 + 4 * k) then some (some 0)
            else if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (36 + 4 * k) then some (some 1)
            else if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (37 + 4 * k) then some (some 2)
            else some (some 3))
          else none) := by
  intro d hd
  have hp := hT.payload (.lf k) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k)) = true
  · have hfam : famIn (.lf k) (Machine.dstOp d) = true := by rw [← hp]; exact hg
    rw [hp, hfam, if_pos rfl]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      rcases lf_codes _ (by omega) d hd hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [hP.lfSt 0 (by omega), hP.lfB0 0 (by omega), hP.lfB1 0 (by omega),
        hP.lfB2 0 (by omega), hP.lfB3 0 (by omega), hP.lfSt 1 (by omega),
        hP.lfB0 1 (by omega), hP.lfB1 1 (by omega), hP.lfB2 1 (by omega),
        hP.lfB3 1 (by omega)]
  · have hgf : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.lf k)) = false := by
      simpa using hg
    have hfam : famIn (.lf k) (Machine.dstOp d) = false := by rw [← hp]; exact hgf
    rw [hp, hfam]
    simp only [Bool.false_eq_true, if_false]
    cases h : Machine.dstOp d <;> simp_all [famIn]

/-- `hPQ` for the `SHk` data group (the port decode here is the gate-free one:
`SHk.CFG` is a separate write group carried by `shCfg`, not a gate on this
record). -/
theorem sh_hPQ (hT : DstPayloadTable) (hP : DstPortTable) (k : Nat) (hk : k < 2) :
    ∀ d, d < 64 →
      (match Machine.dstOp d with
        | .shLd j => if j == k then some true else none
        | .shSh j => if j == k then some false else none
        | _ => none)
      = (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k)) then
          (some (!(BitVec.ofNat 6 d == BitVec.ofNat 6 (20 + k))) : Option Bool)
          else none) := by
  intro d hd
  have hp := hT.payload (.sh k) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k)) = true
  · have hfam : famIn (.sh k) (Machine.dstOp d) = true := by rw [← hp]; exact hg
    rw [hp, hfam, if_pos rfl]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      rcases sh_codes _ (by omega) d hd hg with rfl | rfl <;>
      simp [hP.shLd 0 (by omega), hP.shSh 0 (by omega), hP.shLd 1 (by omega),
        hP.shSh 1 (by omega)]
  · have hgf : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.sh k)) = false := by
      simpa using hg
    have hfam : famIn (.sh k) (Machine.dstOp d) = false := by rw [← hp]; exact hgf
    rw [hp, hfam]
    simp only [Bool.false_eq_true, if_false]
    cases h : Machine.dstOp d <;> simp_all [famIn]

/-! ## 8. The machine-side records -/

/-- The machine's counter record is the `CNTk` group pick. -/
theorem cnt_machine (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable)
    (k : Fin 3) :
    (mUnitsIn m pin).cnt[k] =
      (if (gw s pin (BitVec.ofNat 6 (24 + k.val))).we then
        (if (gw s pin (BitVec.ofNat 6 (24 + k.val))).dst == BitVec.ofNat 6 (24 + k.val) then
            (some 0 : Option Nat)
          else if (gw s pin (BitVec.ofNat 6 (24 + k.val))).dst ==
            BitVec.ofNat 6 (27 + k.val) then some 1
          else if (gw s pin (BitVec.ofNat 6 (24 + k.val))).dst ==
            BitVec.ofNat 6 (30 + k.val) then some 2
          else none) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (24 + k.val))).data.toNat))
        else none) := by
  have hk : k.val < 3 := k.isLt
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (fun o => match o with
      | .cntLo j => if j == k.val then some (0 : Nat) else none
      | .cntHi j => if j == k.val then some 1 else none
      | .cntDec j => if j == k.val then some 2 else none
      | _ => none)
    (fun dst => if dst == BitVec.ofNat 6 (24 + k.val) then some 0
      else if dst == BitVec.ofNat 6 (27 + k.val) then some 1
      else if dst == BitVec.ofNat 6 (30 + k.val) then some 2 else none)
    (fun v => v) (famG (.cnt k.val))
    (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2
    (cnt_hPQ hT hP k.val hk)
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with
        | .cntLo j => if j == k.val then some (0, mv.v) else none
        | .cntHi j => if j == k.val then some (1, mv.v) else none
        | .cntDec j => if j == k.val then some (2, mv.v) else none
        | _ => none)
      = ((match Machine.dstOp mv.dst with
        | .cntLo j => if j == k.val then some (0 : Nat) else none
        | .cntHi j => if j == k.val then some 1 else none
        | .cntDec j => if j == k.val then some 2 else none
        | _ => none).map (fun a => (a, mv.v))) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> simp
  rw [show (mUnitsIn m pin).cnt[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .cntLo j => if j == k.val then some (0, mv.v) else none
      | .cntHi j => if j == k.val then some (1, mv.v) else none
      | .cntDec j => if j == k.val then some (2, mv.v) else none
      | _ => none) from by
    show (Vector.ofFn (fun i : Fin 3 => (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .cntLo j => if j == i.val then some (0, mv.v) else none
      | .cntHi j => if j == i.val then some (1, mv.v) else none
      | .cntDec j => if j == i.val then some (2, mv.v) else none
      | _ => none))).get k = _
    exact vec_get_ofFn' _ k,
    findSome?_congr (fun mv => hpt mv), hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.cnt k.val)))
        (mvDst s pin) (mvDat s pin) = gw s pin (BitVec.ofNat 6 (24 + k.val)) from rfl]

/-- The machine's LFSR record is the `LFk` group pick. -/
theorem lf_machine (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable)
    (k : Fin 2) :
    (mUnitsIn m pin).lf[k] =
      (if (gw s pin (BitVec.ofNat 6 (33 + k.val))).we then
        (if (gw s pin (BitVec.ofNat 6 (33 + k.val))).dst == BitVec.ofNat 6 (33 + k.val) then
            (some none : Option (Option Nat))
          else if (gw s pin (BitVec.ofNat 6 (33 + k.val))).dst ==
            BitVec.ofNat 6 (35 + 4 * k.val) then some (some 0)
          else if (gw s pin (BitVec.ofNat 6 (33 + k.val))).dst ==
            BitVec.ofNat 6 (36 + 4 * k.val) then some (some 1)
          else if (gw s pin (BitVec.ofNat 6 (33 + k.val))).dst ==
            BitVec.ofNat 6 (37 + 4 * k.val) then some (some 2)
          else some (some 3)) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (33 + k.val))).data.toNat))
        else none) := by
  have hk : k.val < 2 := k.isLt
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (fun o => match o with
      | .lfSt j => if j == k.val then some (none : Option Nat) else none
      | .lfB j b => if j == k.val then some (some b) else none
      | _ => none)
    (fun dst => if dst == BitVec.ofNat 6 (33 + k.val) then some none
      else if dst == BitVec.ofNat 6 (35 + 4 * k.val) then some (some 0)
      else if dst == BitVec.ofNat 6 (36 + 4 * k.val) then some (some 1)
      else if dst == BitVec.ofNat 6 (37 + 4 * k.val) then some (some 2)
      else some (some 3))
    (fun v => v) (famG (.lf k.val))
    (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2
    (lf_hPQ hT hP k.val hk)
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with
        | .lfSt j => if j == k.val then some (none, mv.v) else none
        | .lfB j b => if j == k.val then some (some b, mv.v) else none
        | _ => none)
      = ((match Machine.dstOp mv.dst with
        | .lfSt j => if j == k.val then some (none : Option Nat) else none
        | .lfB j b => if j == k.val then some (some b) else none
        | _ => none).map (fun a => (a, mv.v))) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> simp
  rw [show (mUnitsIn m pin).lf[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .lfSt j => if j == k.val then some (none, mv.v) else none
      | .lfB j b => if j == k.val then some (some b, mv.v) else none
      | _ => none) from by
    show (Vector.ofFn (fun i : Fin 2 => (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .lfSt j => if j == i.val then some (none, mv.v) else none
      | .lfB j b => if j == i.val then some (some b, mv.v) else none
      | _ => none))).get k = _
    exact vec_get_ofFn' _ k,
    findSome?_congr (fun mv => hpt mv), hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.lf k.val)))
        (mvDst s pin) (mvDat s pin) = gw s pin (BitVec.ofNat 6 (33 + k.val)) from rfl]

/-- The machine's shifter data record is the `SHk` group pick (the `SHk.CFG` move
is the separate `shCfg` record, matching `Machine.shNext`'s two options). -/
theorem sh_machine (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable)
    (k : Fin 2) :
    (mUnitsIn m pin).sh[k] =
      (if (gw s pin (BitVec.ofNat 6 (18 + k.val))).we then
        (some (!((gw s pin (BitVec.ofNat 6 (18 + k.val))).dst ==
            BitVec.ofNat 6 (20 + k.val))) : Option Bool) |>.map
          (fun a => (a, (gw s pin (BitVec.ofNat 6 (18 + k.val))).data.toNat))
        else none) := by
  have hk : k.val < 2 := k.isLt
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (fun o => match o with
      | .shLd j => if j == k.val then some true else none
      | .shSh j => if j == k.val then some false else none
      | _ => none)
    (fun dst => some (!(dst == BitVec.ofNat 6 (20 + k.val))))
    (fun v => v) (famG (.sh k.val))
    (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2
    (sh_hPQ hT hP k.val hk)
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with
        | .shLd j => if j == k.val then some (true, mv.v) else none
        | .shSh j => if j == k.val then some (false, mv.v) else none
        | _ => none)
      = ((match Machine.dstOp mv.dst with
        | .shLd j => if j == k.val then some true else none
        | .shSh j => if j == k.val then some false else none
        | _ => none).map (fun a => (a, mv.v))) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> simp
  rw [show (mUnitsIn m pin).sh[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .shLd j => if j == k.val then some (true, mv.v) else none
      | .shSh j => if j == k.val then some (false, mv.v) else none
      | _ => none) from by
    show (Vector.ofFn (fun i : Fin 2 => (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .shLd j => if j == i.val then some (true, mv.v) else none
      | .shSh j => if j == i.val then some (false, mv.v) else none
      | _ => none))).get k = _
    exact vec_get_ofFn' _ k,
    findSome?_congr (fun mv => hpt mv), hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.sh k.val)))
        (mvDst s pin) (mvDat s pin) = gw s pin (BitVec.ofNat 6 (18 + k.val)) from rfl]

/-! ## 9. The three fields -/

/-- **`UnitInputs.cnt`** — the counter record is the `CNTk` group pick, statement
verbatim. -/
theorem unitInputs_cnt (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable) :
    ∀ k : Fin 3, (mUnitsIn m pin).cnt[k] = Bridge.CounterB.absIn (cntIn s pin k.val) := by
  intro k
  rw [cnt_machine s m pin hrel hinv hJGTab hbus hgrp hkind hT hP k,
    cnt_absIn s pin k.val k.isLt]

/-- **`UnitInputs.lf`** — the LFSR record is the `LFk` group pick, statement
verbatim. -/
theorem unitInputs_lf (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable) :
    ∀ k : Fin 2, (mUnitsIn m pin).lf[k] = Bridge.LfsrB.absIn (lfIn s pin k.val) := by
  intro k
  rw [lf_machine s m pin hrel hinv hJGTab hbus hgrp hkind hT hP k,
    lf_absIn s pin k.val k.isLt]

/-- **`UnitInputs.sh`** — the shifter data record is the `SHk` group pick,
statement verbatim.  No gate: `shIn.we` is the `SHk` group word's own `we` (RTL
`project.v` 396 `.we(w[14])`, README units top wiring `we == g_sh[k].w[14]`), and
the `SHk.CFG` move is a *different* write group carried by `shCfg`/`cfgWe`.

Historical note (ChipCut wiring fix, round 2): `Wire.lean`'s `shIn.we` used to be
`(gw 18+k).we && !strobe 22+k`.  That gate is not in the RTL; with it this field
was refutable — on a cycle where the `SHk` word fires **and** the `SHk.CFG` strobe
fires (`dg_shCfg_ne`: `10+k ≠ 8+k`, so the arbiter does not exclude it) the cut's
record was `none` while `mUnitsIn.sh[k]` was `some`.  The gate has been removed in
`Wire.lean`, and the equality now holds outright. -/
theorem unitInputs_sh (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hP : DstPortTable) :
    ∀ k : Fin 2, (mUnitsIn m pin).sh[k] = Bridge.ShifterB.absOp (shIn s pin k.val) := by
  intro k
  rw [sh_machine s m pin hrel hinv hJGTab hbus hgrp hkind hT hP k,
    sh_absOp s pin k.val k.isLt]

end Metronome.ChipCut.Discharge.MoveFabric
