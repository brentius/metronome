import Metronome.Machine
import Metronome.Line

/-!
# Bridge: the line cut (`Metronome.Line`) refines `Machine.Line`

`Metronome.Line` is the per-cut independent statement of SPEC_V2 §3 (§3.1
configuration and state, §3.2 beat generator, §3.2a hold, §3.3 follower mode and
edge-sourced tap 0, §3.4 taps/`FIRED`/`TAPMISS`, §3.5 capture and snapshot,
§3.6 output symbol and commit), §12.1 (`LIVE`/`PINA`/`PINB`) and §12.3 (freeze),
plus the precedence note of `md2_line.v` (generator, then a move to `Lk.CTL`,
then a host write).  `line_check.py` proves that the elaborated `md2_line`
registers implement it, one register at a time.

`Metronome.Machine` is the whole-chip executable specification written from
SPEC_V2 alone.  Its line component is `Machine.lineComb` (the combinational
values of cycle `t`) and `Machine.lineNext` (the register values of `t+1`).

This file proves that the cut's one-cycle transition *is* the machine's line
transition under an explicit abstraction map, so the RTL line step and the
machine line step agree wherever the abstraction holds.  Every theorem is over
symbolic state and input; no `sorry`, no `native_decide`.

## Abstraction map

* `absCfg` maps the cut's 32-byte window view (`Line.Config`, decoded bit fields)
  to the machine's `Machine.LineCfg`.  A 16-bit field is carried as
  `BitVec.toNat`, a byte as its `Config.*` field's `toNat`, so all machine
  comparisons are the cut's `BitVec` comparisons read through `BitVec.le_def` /
  `BitVec.lt_def`.
* `absSt` copies the fifteen state fields one for one.
* `absIn` builds the machine's `Machine.LineIn` from the cut's per-cycle inputs:
  a symbol write is `some ⟨op, data⟩` with the cut's `symOp` recoded to the
  machine's `L.SYM = 1 / L.DBIT = 2 / L.XOR = 3`; a `Lk.CTL` move is
  `some ctlD`; a host `PHASE` byte is `some (0, hD)` / `some (1, hD)`; host
  `CTL` is `some hD`; `hTapmissClr` is `hStatWe && hD[0]`.
* `PinAbs`/`PinAgree` are the §2 pin view: the cut samples `lvl`, `rise` and
  `fall` as free vectors, the machine derives them from `lvl` and `prev`.  The
  side condition is exactly that the cut's three vectors are the machine's
  level and edge vectors.

## Side conditions

* `PinAgree` (above): the cut's `lvl`/`rise`/`fall` are §2 vectors.
* `hcfg : lc = absCfg i.cfg`: the machine's decoded line configuration is the
  cut's window view.  (The decode from the configuration byte image is
  `Machine.Config.line`; the cut's byte-slice wiring is `line_check.py`'s.)
* `hiM : iM = absIn i`: the machine's line inputs are `absIn` of the cut's.

## Readings carried over from the cut

The cut's `sym_op = 3` fallback is unreachable from the elaborated decode; both
models treat it as `L.XOR` (the machine's `op = 3`; the cut's `0` is recoded to
the machine's `1`), so the bridge maps it there.  A frozen follower cycle
clears `SC` in both models (§3.3).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 1024

namespace Metronome.Bridge.Line

open Metronome.Machine Metronome.Machine.Util

/-! ## Bit plumbing: the cut's `bitAt`/`sel` are the machine's `nbit` -/

/-- A field bit is `(x >>> i) % 2 == 1` in the machine. -/
theorem nbit_eq_testBit (x i : Nat) : nbit x i = Nat.testBit x i := by
  rw [nbit, Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

/-- The machine's `bit` is its `nbit` of the cut's `toNat`. -/
theorem bit_eq_nbit {n : Nat} (x : BitVec n) (i : Nat) : bit x i = nbit x.toNat i := by
  rw [nbit_eq_testBit]
  rfl

/-- A one-bit truncation is nonzero exactly when bit 0 is set. -/
theorem bne_zero_one_bit (z : BitVec 1) : (z != 0) = z.getLsbD 0 := by
  bv_decide

/-- The cut's `bitAt` is the machine's `nbit`. -/
theorem ushiftRight_eq_shift {n : Nat} (v : BitVec n) (k : Nat) :
    BitVec.ushiftRight v k = (v >>> k) := rfl

theorem ushiftRight_getLsbD {n : Nat} (v : BitVec n) (k : Nat) :
    (BitVec.ushiftRight v k).getLsbD 0 = v.getLsbD k := by
  rw [ushiftRight_eq_shift, BitVec.getLsbD_ushiftRight, Nat.add_zero]

theorem setWidth_one_getLsbD {n : Nat} (y : BitVec n) :
    (BitVec.setWidth 1 y).getLsbD 0 = y.getLsbD 0 := by
  rw [BitVec.getLsbD_setWidth]
  simp

theorem bitAt_eq_nbit {n : Nat} (v : BitVec n) (k : Nat) :
    Metronome.Line.bitAt k v = nbit v.toNat k := by
  simp only [Metronome.Line.bitAt, BitVec.truncate_eq_setWidth]
  rw [bne_zero_one_bit, setWidth_one_getLsbD, ushiftRight_getLsbD]
  exact bit_eq_nbit v k

/-- `x &&& 1 != 0` is bit 0, for a 16-bit bus. -/
theorem and_one_bne_zero_16 (y : BitVec 16) : (y &&& 1 != 0) = y.getLsbD 0 := by
  bv_decide

theorem and_one_bne_zero_3 (y : BitVec 3) : (y &&& 1 != 0) = y.getLsbD 0 := by
  bv_decide

theorem and_one_bne_zero_32 (y : BitVec 32) : (y &&& 1 != 0) = y.getLsbD 0 := by
  bv_decide

/-- The cut's `sel` (16-bit bus) is the machine's `nbit`. -/
theorem sel16_eq_nbit (v : BitVec 16) (k : Nat) :
    Metronome.Line.sel k v = nbit v.toNat k := by
  have h := and_one_bne_zero_16 (BitVec.ushiftRight v k)
  simp only [Metronome.Line.sel] at h ⊢
  rw [h, ushiftRight_getLsbD]
  exact bit_eq_nbit v k

/-- The cut's `sel` (3-bit tap bus) is the machine's `nbit`. -/
theorem sel3_eq_nbit (v : BitVec 3) (k : Nat) :
    Metronome.Line.sel k v = nbit v.toNat k := by
  have h := and_one_bne_zero_3 (BitVec.ushiftRight v k)
  simp only [Metronome.Line.sel] at h ⊢
  rw [h, ushiftRight_getLsbD]
  exact bit_eq_nbit v k

/-- The cut's `sel` (32-bit LUT) is the machine's `nbit`. -/
theorem sel32_eq_nbit (v : BitVec 32) (k : Nat) :
    Metronome.Line.sel k v = nbit v.toNat k := by
  have h := and_one_bne_zero_32 (BitVec.ushiftRight v k)
  simp only [Metronome.Line.sel] at h ⊢
  rw [h, ushiftRight_getLsbD]
  exact bit_eq_nbit v k

/-- The window slice's `toNat` is the machine's `nbits`. -/
theorem slice_toNat {n : Nat} (s w : Nat) (v : BitVec n) :
    (Metronome.Line.slice s w v).toNat = nbits v.toNat s w := by
  simp [Metronome.Line.slice, nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

/-- The machine's `bv` of a cut field's `toNat` is the field. -/
theorem bv_toNat {n : Nat} (x : BitVec n) : bv n x.toNat = x := by
  simp [bv]

/-- A `BitVec` equality at `toNat` is a `Nat` equality. -/
theorem beq_toNat {n : Nat} (a b : BitVec n) : (a == b) = true ↔ a.toNat = b.toNat := by
  rw [beq_iff_eq, BitVec.toNat_eq]

/-- `nbit x 0` is the low bit. -/
theorem nbit_zero (x : Nat) : nbit x 0 = (x % 2 == 1) := by
  simp [nbit, Nat.shiftRight_zero]

/-- A `BitVec` is zero exactly when its value is zero. -/
theorem toNat_eq_zero {n : Nat} {x : BitVec n} (h : x.toNat = 0) : x = 0 :=
  BitVec.eq_of_toNat_eq (by rw [h]; rfl)

theorem toNat_ne_zero {n : Nat} {x : BitVec n} (h : x ≠ 0) : x.toNat ≠ 0 := by
  intro h0
  exact h (toNat_eq_zero h0)

/-- A `BitVec` inequality is the `Nat` inequality. -/
theorem bv_le_iff {n : Nat} {a b : BitVec n} : (a ≤ b) = (a.toNat ≤ b.toNat) := by
  exact propext BitVec.le_def

/-- `b2n` is the 0/1 indicator. -/
theorem b2n_eq (b : Bool) : b2n b = if b then 1 else 0 := by cases b <;> rfl

/-- Three bits pack to `4*b2 + 2*b1 + b0`. -/
theorem pack3_toNat (b2 b1 b0 : Bool) :
    (Metronome.Line.pack3 b2 b1 b0).toNat = 4 * b2n b2 + 2 * b2n b1 + b2n b0 := by
  cases b2 <;> cases b1 <;> cases b0 <;> decide

/-- Four bits pack to `8*b3 + 4*b2 + 2*b1 + b0`. -/
theorem pack4_toNat (b3 b2 b1 b0 : Bool) :
    (Metronome.Line.pack4 b3 b2 b1 b0).toNat = 8 * b2n b3 + 4 * b2n b2 + 2 * b2n b1 + b2n b0 := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> decide

/-- A three-bit bus repacks to `pack3` of its bits. -/
theorem pack3_bits' (v : BitVec 3) :
    Metronome.Line.pack3 (bit v 2) (bit v 1) (bit v 0) = v := by
  simp only [Metronome.Line.pack3, bit, b2n]
  bv_decide

/-- A four-bit bus repacks to `pack4` of its bits. -/
theorem pack4_bits' (v : BitVec 4) :
    Metronome.Line.pack4 (bit v 3) (bit v 2) (bit v 1) (bit v 0) = v := by
  simp only [Metronome.Line.pack4, bit, b2n]
  bv_decide

/-- Bit `k < 3` of `pack3` is the corresponding bit. -/
theorem pack3_bit (b2 b1 b0 : Bool) (k : Nat) (hk : k < 3) :
    bit (Metronome.Line.pack3 b2 b1 b0) k =
      (if k = 0 then b0 else if k = 1 then b1 else b2) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
    cases b2 <;> cases b1 <;> cases b0 <;> decide

/-- `packBits [a, b, c]` is `pack3 c b a`. -/
theorem packBits3_as_pack3 (a b c : Bool) :
    bv 3 (packBits [a, b, c]) = Metronome.Line.pack3 c b a := by
  cases a <;> cases b <;> cases c <;> decide

/-- Bitwise or of two 3-bit buses is `pack3` of the or-ed bits. -/
theorem or3_as_pack3 (x y : BitVec 3) :
    x ||| y = Metronome.Line.pack3 (bit x 2 || bit y 2) (bit x 1 || bit y 1)
      (bit x 0 || bit y 0) := by
  simp only [Metronome.Line.pack3, bit, b2n]
  bv_decide

/-- A `nbit` of `b2n b * 2 + b2n c` at bit 1 recovers `b`. -/
theorem nbit_two_mul_add (b c : Bool) : nbit (b2n b * 2 + b2n c) 1 = b := by
  cases b <;> cases c <;> decide

/-- `Vector.ofFn` at a literal index. -/
theorem vec3_get0 (f : Fin 3 → Bool) : (Vector.ofFn f)[0]! = f 0 := by simp
theorem vec3_get1 (f : Fin 3 → Bool) : (Vector.ofFn f)[1]! = f 1 := by simp
theorem vec3_get2 (f : Fin 3 → Bool) : (Vector.ofFn f)[2]! = f 2 := by simp

/-! ## Abstraction map -/

/-- The cut's window view as the machine's decoded line configuration. -/
def absCfg (c : Metronome.Line.Config) : Machine.LineCfg :=
  { inc := c.inc.toNat
    mod := c.mod.toNat
    t0 := c.t0.toNat
    t1 := c.t1.toNat
    t2 := c.t2.toNat
    pre := c.pre.toNat
    wlo := c.wlo.toNat
    whi := c.whi.toNat
    edgePin := c.edgePin.toNat
    edgePol := c.edgePol.toNat
    wen := c.wen
    follow := c.follow
    t0Pin := c.t0Pin.toNat
    t0Pol := c.t0Pol.toNat
    t0src := c.t0src
    snap := c.snap.toNat
    pina := c.pinaSel.toNat
    pinb := c.pinbSel.toNat
    lut0 := c.lut0.toNat
    lut1 := c.lut1.toNat
    hpin := c.hpin.toNat
    hlvl := c.hlvl
    htap := c.htap.toNat
    hen := c.hen }

/-- The cut's line state is the machine's, field for field. -/
def absSt (s : Metronome.Line.State) : Machine.LineSt :=
  { ph := s.ph, run := s.run, arm := s.arm, ren := s.ren, held := s.held,
    first := s.first, sc := s.sc, sp := s.sp, fired := s.fired, w := s.w, sn := s.sn,
    rem := s.rem, staged := s.staged, committed := s.committed, tapmiss := s.tapmiss }

/-- The cut's symbol operation recoded to the machine's `L.SYM = 1`,
`L.DBIT = 2`, `L.XOR = 3`.  The cut's `3` is the RTL `case` default (XOR) and is
unreachable from the elaborated decode; it maps to `L.XOR`. -/
def absSymOp (op : BitVec 2) : Nat :=
  if op == (0 : BitVec 2) then 1 else if op == (1 : BitVec 2) then 2 else 3

/-- The cut's per-cycle inputs as the machine's `LineIn`. -/
def absIn (i : Metronome.Line.Input) : Machine.LineIn :=
  { sym := if i.symWe then some ⟨absSymOp i.symOp, i.symD.toNat⟩ else none
    ctlMove := if i.ctlWe then some i.ctlD.toNat else none
    hPhase := if Metronome.Line.bitAt 0 i.phWe then some (0, i.hD.toNat)
      else if Metronome.Line.bitAt 1 i.phWe then some (1, i.hD.toNat) else none
    hCtl := if i.hCtlWe then some i.hD.toNat else none
    hTapmissClr := i.hStatWe && Metronome.Line.bitAt 0 i.hD }

/-- A §2 pin view abstracted from the cut's free pin vectors. -/
structure PinAbs where
  /-- `PIN[12:0]`. -/
  lvl : Nat
  /-- The previous cycle's level `sp`. -/
  prev : Nat

/-- The machine pin view of a `PinAbs` (the host pins are not part of a line). -/
def PinAbs.view (a : PinAbs) : Machine.PinView :=
  { lvl := a.lvl, prev := a.prev, sck := false, csn := false, mosi := false,
    sckRise := false }

/-- The cut's free `lvl`/`rise`/`fall` vectors are the machine's §2 vectors. -/
structure PinAgree (a : PinAbs) (i : Metronome.Line.Input) : Prop where
  pin : ∀ k, a.view.pin k = Metronome.Line.sel k i.lvl
  rise : ∀ k, a.view.rise k = Metronome.Line.sel k i.rise
  fall : ∀ k, a.view.fall k = Metronome.Line.sel k i.fall

/-- A `BitVec 2` is one of its four values. -/
theorem bv2_cases (x : BitVec 2) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have h : x.toNat < 4 := x.isLt
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3) with h0 | h1 | h2 | h3
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h0]))
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h1])))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h2]))))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by simp [h3]))))

/-- The polarity-selected edge is the machine's `edgeSel`. -/
theorem esel_eq (a : PinAbs) (i : Metronome.Line.Input) (h : PinAgree a i)
    {pin : BitVec 4} {pol : BitVec 2} :
    Metronome.Line.esel pin pol i.rise i.fall = a.view.edgeSel pin.toNat pol.toNat := by
  rcases bv2_cases pol with rfl | rfl | rfl | rfl
  · simp [Metronome.Line.esel, Machine.PinView.edgeSel]
  · simp [Metronome.Line.esel, Machine.PinView.edgeSel, h.rise]
  · simp [Metronome.Line.esel, Machine.PinView.edgeSel, h.fall]
  · simp [Metronome.Line.esel, Machine.PinView.edgeSel, h.rise, h.fall]

/-! ## Combinational values of the cycle -/

/-- The machine's line configuration fields read through `absCfg`. -/
theorem absCfg_inc (c : Metronome.Line.Config) : (absCfg c).inc = c.inc.toNat := rfl
theorem absCfg_mod (c : Metronome.Line.Config) : (absCfg c).mod = c.mod.toNat := rfl
theorem absCfg_t0 (c : Metronome.Line.Config) : (absCfg c).t0 = c.t0.toNat := rfl
theorem absCfg_t1 (c : Metronome.Line.Config) : (absCfg c).t1 = c.t1.toNat := rfl
theorem absCfg_t2 (c : Metronome.Line.Config) : (absCfg c).t2 = c.t2.toNat := rfl
theorem absCfg_pre (c : Metronome.Line.Config) : (absCfg c).pre = c.pre.toNat := rfl
theorem absCfg_wlo (c : Metronome.Line.Config) : (absCfg c).wlo = c.wlo.toNat := rfl
theorem absCfg_whi (c : Metronome.Line.Config) : (absCfg c).whi = c.whi.toNat := rfl
theorem absCfg_snap (c : Metronome.Line.Config) : (absCfg c).snap = c.snap.toNat := rfl
theorem absCfg_htap (c : Metronome.Line.Config) : (absCfg c).htap = c.htap.toNat := rfl
theorem absCfg_edgePin (c : Metronome.Line.Config) : (absCfg c).edgePin = c.edgePin.toNat := rfl
theorem absCfg_edgePol (c : Metronome.Line.Config) : (absCfg c).edgePol = c.edgePol.toNat := rfl
theorem absCfg_t0Pin (c : Metronome.Line.Config) : (absCfg c).t0Pin = c.t0Pin.toNat := rfl
theorem absCfg_t0Pol (c : Metronome.Line.Config) : (absCfg c).t0Pol = c.t0Pol.toNat := rfl
theorem absCfg_pina (c : Metronome.Line.Config) : (absCfg c).pina = c.pinaSel.toNat := rfl
theorem absCfg_pinb (c : Metronome.Line.Config) : (absCfg c).pinb = c.pinbSel.toNat := rfl
theorem absCfg_hpin (c : Metronome.Line.Config) : (absCfg c).hpin = c.hpin.toNat := rfl

theorem absCfg_hen (c : Metronome.Line.Config) : (absCfg c).hen = c.hen := rfl
theorem absCfg_hlvl (c : Metronome.Line.Config) : (absCfg c).hlvl = c.hlvl := rfl
theorem absCfg_lut0 (c : Metronome.Line.Config) : (absCfg c).lut0 = c.lut0.toNat := rfl
theorem absCfg_lut1 (c : Metronome.Line.Config) : (absCfg c).lut1 = c.lut1.toNat := rfl
theorem absCfg_t0src (c : Metronome.Line.Config) : (absCfg c).t0src = c.t0src := rfl
theorem absCfg_wen (c : Metronome.Line.Config) : (absCfg c).wen = c.wen := rfl
theorem absCfg_follow (c : Metronome.Line.Config) : (absCfg c).follow = c.follow := rfl

/-- `decide (a ≤ b)` is the `Nat` comparison of the values. -/
theorem bv_le_decide {n : Nat} (a b : BitVec n) :
    decide (a ≤ b) = decide (a.toNat ≤ b.toNat) := by
  by_cases h : a ≤ b
  · have h2 : a.toNat ≤ b.toNat := BitVec.le_def.1 h
    simp [h, h2]
  · have h2 : ¬(a.toNat ≤ b.toNat) := fun hh => h (BitVec.le_def.2 hh)
    simp [h, h2]

/-- `decide (a ≥ b)` is the `Nat` comparison of the values. -/
theorem bv_ge_decide {n : Nat} (a b : BitVec n) :
    decide (a ≥ b) = decide (a.toNat ≥ b.toNat) := by
  by_cases h : a ≥ b
  · have h2 : a.toNat ≥ b.toNat := BitVec.le_def.1 h
    simp [h, h2]
  · have h2 : ¬(a.toNat ≥ b.toNat) := fun hh => h (BitVec.le_def.2 hh)
    simp [h, h2]

/-- The boundary edge `§3.2` agrees. -/
theorem edge_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).edge = Metronome.Line.edge s i := by
  subst hcfg
  show (!i.frz && a.view.edgeSel (absCfg i.cfg).edgePin (absCfg i.cfg).edgePol) =
    Metronome.Line.edge s i
  rw [absCfg_edgePin, absCfg_edgePol]
  simp only [Metronome.Line.edge, esel_eq a i hpin, Bool.and_comm]

/-- The edge-sourced tap 0 `§3.3` agrees. -/
theorem e0_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).e0 = Metronome.Line.e0 s i := by
  subst hcfg
  show (!i.frz && a.view.edgeSel (absCfg i.cfg).t0Pin (absCfg i.cfg).t0Pol) =
    Metronome.Line.e0 s i
  rw [absCfg_t0Pin, absCfg_t0Pol]
  simp only [Metronome.Line.e0, esel_eq a i hpin, Bool.and_comm]

/-- The accepted-edge window `§3.2` agrees. -/
theorem inwin_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).inwin = Metronome.Line.inwin s i := by
  subst hcfg
  show (if (absCfg i.cfg).wlo ≤ (absCfg i.cfg).whi then
      ((absCfg i.cfg).wlo ≤ (absSt s).ph.toNat && (absSt s).ph.toNat ≤ (absCfg i.cfg).whi)
    else ((absSt s).ph.toNat ≥ (absCfg i.cfg).wlo || (absSt s).ph.toNat ≤ (absCfg i.cfg).whi)) =
    Metronome.Line.inwin s i
  rw [absCfg_wlo, absCfg_whi]
  simp only [Metronome.Line.inwin, absSt]
  by_cases hw : i.cfg.wlo.toNat ≤ i.cfg.whi.toNat
  · rw [if_pos hw, if_pos (by rw [bv_le_decide]; simp [hw])]
    by_cases h1 : i.cfg.wlo.toNat ≤ s.ph.toNat <;> by_cases h2 : s.ph.toNat ≤ i.cfg.whi.toNat <;>
      simp [h1, h2, bv_le_decide]
  · rw [if_neg hw, if_neg (by rw [bv_le_decide]; simp [hw])]
    by_cases h1 : i.cfg.wlo.toNat ≤ s.ph.toNat <;> by_cases h2 : s.ph.toNat ≤ i.cfg.whi.toNat <;>
      simp [h1, h2, bv_le_decide, ge_iff_le]

/-- `start` agrees. -/
theorem start_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).start = Metronome.Line.start s i := by
  subst hcfg
  show ((Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).edge &&
      (absSt s).arm && !(absSt s).run) = Metronome.Line.start s i
  rw [edge_bridge s i (absCfg i.cfg) rfl a hpin]
  rfl

/-- `accept` agrees. -/
theorem accept_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).accept = Metronome.Line.accept s i := by
  subst hcfg
  show ((Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).edge &&
      (absSt s).run && (absSt s).ren &&
      (!(absCfg i.cfg).wen ||
        (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).inwin)) =
    Metronome.Line.accept s i
  rw [edge_bridge s i (absCfg i.cfg) rfl a hpin]
  rw [inwin_bridge s i (absCfg i.cfg) rfl a hpin]
  rfl

/-! ## The phase sum, the boundary and the hold -/

/-- A 16-bit bus sliced at 0 is itself. -/
theorem slice16_self (v : BitVec 16) : Metronome.Line.slice 0 16 v = v := by
  apply BitVec.eq_of_toNat_eq
  rw [slice_toNat]
  simp [nbits, Nat.mod_eq_of_lt v.isLt]

/-- The 17-bit zero extension has the same value. -/
theorem concat17_toNat (v : BitVec 16) : ((0 : BitVec 1) ++ v).toNat = v.toNat := by
  rw [BitVec.toNat_append]
  simp

/-- The 17-bit phase sum `PH + INC`. -/
theorem sum17_toNat (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.sum17 s i).toNat = s.ph.toNat + i.cfg.inc.toNat := by
  simp only [Metronome.Line.sum17, slice16_self]
  rw [BitVec.toNat_add, concat17_toNat, concat17_toNat]
  have hp : s.ph.toNat < 65536 := s.ph.isLt
  have hi : i.cfg.inc.toNat < 65536 := i.cfg.inc.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

/-- `over` in terms of the `Nat` sum. -/
theorem over_eq_decide (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Metronome.Line.over s i =
      decide (s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat) := by
  have hb : ((0 : BitVec 1) ++ Metronome.Line.slice 0 16 i.cfg.mod).toNat = i.cfg.mod.toNat := by
    rw [concat17_toNat, slice16_self]
  show decide (Metronome.Line.sum17 s i ≥
      ((0 : BitVec 1) ++ Metronome.Line.slice 0 16 i.cfg.mod)) =
    decide (s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, ge_iff_le, BitVec.le_def, sum17_toNat, hb]

/-- `over` (`N >= MOD`) agrees. -/
theorem over_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).over = Metronome.Line.over s i := by
  subst hcfg
  rw [over_eq_decide]
  show decide ((absSt s).ph.toNat + (absCfg i.cfg).inc ≥ (absCfg i.cfg).mod) = _
  rw [absCfg_inc, absCfg_mod, absSt]

/-! ## Readings carried over: two witnessed differences in the *signals*

The cut's `hold` signal includes the freeze gate (`runa = RUN && !frz`), while
`Machine.LineComb.hold` does not.  The two therefore differ in a frozen cycle
with `RUN = 1` and a hold-worthy pin; no state equation is affected because
`HELD'` and `adv` are freeze-gated in both models.  `hold_frozen_cut` and
`hold_frozen_machine` are the witness pair.

The cut's `sym_op = 3` is the elaborated decode's unused code and both models
read it as `L.XOR`; `absSymOp_three` and `staged_op3_is_xor` record it. -/

/-- The cut's `hold` is low in a frozen cycle (§12.3's `runa`). -/
theorem hold_frozen_cut (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (h : i.frz = true) : Metronome.Line.hold s i = false := by
  simp [Metronome.Line.hold, Metronome.Line.runa, h]

/-- The machine's combinational `hold` can stay high in the same frozen cycle. -/
theorem hold_frozen_machine :
    (Machine.lineComb
      { inc := 4, mod := 8, t0 := 4, t1 := 0, t2 := 0, pre := 0, wlo := 0, whi := 0,
        edgePin := 0, edgePol := 0, wen := false, follow := false, t0Pin := 0, t0Pol := 0,
        t0src := false, snap := 0, pina := 0, pinb := 0, lut0 := 0, lut1 := 0,
        hpin := 0, hlvl := true, htap := 0, hen := true }
      { ph := 0, run := true, arm := false, ren := false, held := false, first := false,
        sc := false, sp := false, fired := 0, w := 0, sn := 0, rem := false, staged := 0,
        committed := 0, tapmiss := false }
      { lvl := 0, prev := 0, sck := false, csn := false, mosi := false,
        sckRise := false } true).hold = true := by decide

/-- The cut's `sym_op = 3` recodes to the machine's `L.XOR`. -/
theorem absSymOp_three : absSymOp 3 = 3 := by decide

/-- The cut's `sym_op = 3` stages the XOR, as the elaborated `case` default does. -/
theorem staged_op3_is_xor (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (hw : i.symWe = true) (h3 : i.symOp = 3) :
    Metronome.Line.stagedNext s i = s.staged ^^^ i.symD := by
  simp [Metronome.Line.stagedNext, hw, h3]

/-! ## Plumbing for the register equations

The register equations compare `BitVec` values with the machine's `Nat` fields and
with `bv`, `setBit` and `setByte`.  The lemmas below are the whole interface:
`toNat` of a small `bv`, the `Nat` value of a window slice, `setByte` at byte 0
and byte 1, `bitAt = bit`, the pack order of `pack4`, the three-bit case split
and the `BitVec 2`/`Nat` equality of a 2-bit field against a literal. -/

theorem two_pow_2 : (2 : Nat) ^ 2 = 4 := by decide
theorem two_pow_3 : (2 : Nat) ^ 3 = 8 := by decide
theorem two_pow_4 : (2 : Nat) ^ 4 = 16 := by decide
theorem two_pow_8 : (2 : Nat) ^ 8 = 256 := by decide
theorem two_pow_16 : (2 : Nat) ^ 16 = 65536 := by decide
theorem two_pow_17 : (2 : Nat) ^ 17 = 131072 := by decide

/-- `bv n x` at a value in range is `x`. -/
theorem toNat_bv_of_lt {n x : Nat} (h : x < 2 ^ n) : (bv n x).toNat = x := by
  simp [bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_bv2 {x : Nat} (h : x < 4) : (bv 2 x).toNat = x :=
  toNat_bv_of_lt (by rw [two_pow_2]; exact h)

theorem toNat_bv3 {x : Nat} (h : x < 8) : (bv 3 x).toNat = x :=
  toNat_bv_of_lt (by rw [two_pow_3]; exact h)

theorem toNat_bv4 {x : Nat} (h : x < 16) : (bv 4 x).toNat = x :=
  toNat_bv_of_lt (by rw [two_pow_4]; exact h)

theorem toNat_bv16 {x : Nat} (h : x < 65536) : (bv 16 x).toNat = x :=
  toNat_bv_of_lt (by rw [two_pow_16]; exact h)

/-- Byte 1 (bits 15:8) of a 16-bit word, as a `Nat`. -/
theorem slice8_8_toNat (p : BitVec 16) :
    (Metronome.Line.slice 8 8 p).toNat = p.toNat / 256 := by
  rw [slice_toNat]
  simp only [nbits, Nat.mul_zero, Nat.shiftRight_zero, Nat.pow_zero, two_pow_8]
  rw [Nat.shiftRight_eq_div_pow, two_pow_8]
  have h : p.toNat / 256 < 256 := by
    have := p.isLt
    omega
  rw [Nat.mod_eq_of_lt h]

/-- Byte 0 (bits 7:0) of a 16-bit word, as a `Nat`. -/
theorem slice0_8_toNat (p : BitVec 16) :
    (Metronome.Line.slice 0 8 p).toNat = p.toNat % 256 := by
  rw [slice_toNat]
  simp only [nbits, Nat.mul_zero, Nat.shiftRight_zero, Nat.pow_zero, two_pow_8]

/-- Two bytes concatenate to `hi * 256 + lo`. -/
theorem concat8_toNat (a b : BitVec 8) : (a ++ b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq, two_pow_8]

theorem setByte0_16 (p : BitVec 16) (b : BitVec 8) :
    setByte p 0 b.toNat = Metronome.Line.slice 8 8 p ++ b := by
  apply BitVec.eq_of_toNat_eq
  rw [concat8_toNat, slice8_8_toNat, setByte]
  simp only [bv, BitVec.toNat_ofNat, nbits, Nat.mul_zero, Nat.shiftRight_zero, Nat.pow_zero,
    Nat.sub_zero, Nat.one_mul, Nat.mul_one, two_pow_8, two_pow_16]
  rw [Nat.mod_eq_of_lt b.isLt]
  have hsplit : p.toNat / 256 * 256 + p.toNat % 256 = p.toNat := by
    have := Nat.div_add_mod p.toNat 256
    omega
  rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]
  omega

theorem setByte1_16 (p : BitVec 16) (b : BitVec 8) :
    setByte p 1 b.toNat = b ++ Metronome.Line.slice 0 8 p := by
  apply BitVec.eq_of_toNat_eq
  rw [concat8_toNat, slice0_8_toNat, setByte]
  simp only [bv, BitVec.toNat_ofNat, nbits, Nat.mul_zero, Nat.shiftRight_zero, Nat.pow_zero,
    Nat.one_mul, Nat.mul_one, two_pow_8, two_pow_16]
  rw [Nat.mod_eq_of_lt b.isLt]
  have hsplit : p.toNat / 256 * 256 + p.toNat % 256 = p.toNat := by
    have := Nat.div_add_mod p.toNat 256
    omega
  rw [Nat.mod_eq_of_lt (by have := p.isLt; omega)]
  omega

/-- The cut's `bitAt` is the machine's `bit`. -/
theorem bitAt_eq_bit {n : Nat} (v : BitVec n) (k : Nat) :
    Metronome.Line.bitAt k v = bit v k := by
  simp only [Metronome.Line.bitAt, BitVec.truncate_eq_setWidth]
  rw [bne_zero_one_bit, setWidth_one_getLsbD, ushiftRight_getLsbD]
  rfl

/-- Bit `k < 4` of `pack4` is the corresponding argument. -/
theorem pack4_bit (b3 b2 b1 b0 : Bool) (k : Nat) (hk : k < 4) :
    bit (Metronome.Line.pack4 b3 b2 b1 b0) k =
      (if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else b3) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> decide

/-- A `BitVec 3` is one of its eight values. -/
theorem bv3_cases (x : BitVec 3) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by
  have h : x.toNat < 8 := x.isLt
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨
      x.toNat = 4 ∨ x.toNat = 5 ∨ x.toNat = 6 ∨ x.toNat = 7) with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h0]))
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h1])))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h2]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h3])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h4]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (BitVec.eq_of_toNat_eq (by simp [h5])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (BitVec.eq_of_toNat_eq (by simp [h6]))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (BitVec.eq_of_toNat_eq (by simp [h7]))))))))

/-- A 2-bit field equals a literal exactly when its value does. -/
theorem beq_ofNat_two (x : BitVec 2) (n : Nat) (hn : n < 4) :
    (x == bv 2 n) = (x.toNat == n) := by
  rcases bv2_cases x with rfl | rfl | rfl | rfl <;>
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
      decide

/-- The cut's `!= 3` is the machine's `Nat` `!= 3`. -/
theorem ne_three_two (x : BitVec 2) : (x != 3) = (x.toNat != 3) := by
  rcases bv2_cases x with rfl | rfl | rfl | rfl <;> decide

/-- `x != 0` for a 3-bit bus is the disjunction of its three bits. -/
theorem bv3_ne_zero (x : BitVec 3) :
    (x != 0) = (x.getLsbD 0 || x.getLsbD 1 || x.getLsbD 2) := by
  bv_decide

/-- `(List.range 3).map f` is `[f 0, f 1, f 2]`. -/
theorem range_three_map (f : Nat → Bool) :
    (List.range 3).map f = [f 0, f 1, f 2] := by
  simp [List.range_succ]

/-- `any` over `List.range 3` is the disjunction of the three values. -/
theorem range_three_any (f : Nat → Bool) :
    (List.range 3).any f = (f 0 || f 1 || f 2) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
    simp [List.range_succ, h0, h1, h2]

/-! ## `lineComb` field unfoldings and tap-vector accesses

`lineComb` is a `let`-chain, so each field reduces definitionally; these
`rfl` lemmas name the reduced form.  The tap vectors are `Vector.ofFn` values,
so element `k` is read with `vec3_get`. -/

theorem vec3_get (f : Fin 3 → Bool) (k : Nat) (hk : k < 3) :
    (Vector.ofFn f)[k]! = f ⟨k, hk⟩ := by
  simp [Vector.getElem?_ofFn, hk]

theorem lineComb_n (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).n = st.ph.toNat + lc.inc := rfl

theorem lineComb_over (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) :
    (Machine.lineComb lc st p f).over = decide (st.ph.toNat + lc.inc ≥ lc.mod) := rfl

theorem lineComb_nx (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).nx =
      (if st.ph.toNat + lc.inc ≥ lc.mod then st.ph.toNat + lc.inc - lc.mod
        else st.ph.toNat + lc.inc) % 65536 := rfl

theorem lineComb_hold (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).hold =
      (lc.hen && (st.run && !(Machine.lineComb lc st p f).accept &&
        (lc.hen && lc.htap != 3 && Machine.tapEnabled lc lc.htap &&
          Machine.Util.isPhaseTap lc lc.htap) &&
        Machine.phaseCross lc st.ph.toNat (st.ph.toNat + lc.inc)
          ((Machine.lineComb lc st p f).nx) true lc.htap) &&
        (p.pin lc.hpin != lc.hlvl)) := rfl

theorem lineComb_adv (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).adv =
      (!f && st.run && !(Machine.lineComb lc st p f).accept &&
        !(Machine.lineComb lc st p f).hold) := rfl

theorem lineComb_wrap (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).wrap =
      ((Machine.lineComb lc st p f).adv && (Machine.lineComb lc st p f).over) := rfl

theorem lineComb_beat (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).beat =
      (if lc.follow then (Machine.lineComb lc st p f).accept
      else (Machine.lineComb lc st p f).wrap) := rfl

theorem lineComb_en0 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).en[0]! = Machine.tapEnabled lc 0 := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_en1 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).en[1]! = Machine.tapEnabled lc 1 := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_en2 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).en[2]! = Machine.tapEnabled lc 2 := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cross0 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cross[0]! =
      ((Machine.lineComb lc st p f).en[0]! &&
        (if Machine.Util.isPhaseTap lc 0 then
          Machine.phaseCross lc st.ph.toNat (st.ph.toNat + lc.inc)
            ((Machine.lineComb lc st p f).nx) (Machine.lineComb lc st p f).adv 0
        else st.run && (Machine.lineComb lc st p f).e0)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cross1 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cross[1]! =
      ((Machine.lineComb lc st p f).en[1]! &&
        (if Machine.Util.isPhaseTap lc 1 then
          Machine.phaseCross lc st.ph.toNat (st.ph.toNat + lc.inc)
            ((Machine.lineComb lc st p f).nx) (Machine.lineComb lc st p f).adv 1
        else st.run && (Machine.lineComb lc st p f).e0)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cross2 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cross[2]! =
      ((Machine.lineComb lc st p f).en[2]! &&
        (if Machine.Util.isPhaseTap lc 2 then
          Machine.phaseCross lc st.ph.toNat (st.ph.toNat + lc.inc)
            ((Machine.lineComb lc st p f).nx) (Machine.lineComb lc st p f).adv 2
        else st.run && (Machine.lineComb lc st p f).e0)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_next0 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).next[0]! =
      ((Machine.lineComb lc st p f).cross[0]! && (Machine.lineComb lc st p f).beat &&
        (if Machine.Util.isPhaseTap lc 0 then
          ((Machine.lineComb lc st p f).over && Machine.Util.tapT lc 0 ≤
            (Machine.lineComb lc st p f).nx) else true)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_next1 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).next[1]! =
      ((Machine.lineComb lc st p f).cross[1]! && (Machine.lineComb lc st p f).beat &&
        (if Machine.Util.isPhaseTap lc 1 then
          ((Machine.lineComb lc st p f).over && Machine.Util.tapT lc 1 ≤
            (Machine.lineComb lc st p f).nx) else true)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_next2 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).next[2]! =
      ((Machine.lineComb lc st p f).cross[2]! && (Machine.lineComb lc st p f).beat &&
        (if Machine.Util.isPhaseTap lc 2 then
          ((Machine.lineComb lc st p f).over && Machine.Util.tapT lc 2 ≤
            (Machine.lineComb lc st p f).nx) else true)) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cur0 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cur[0]! =
      ((Machine.lineComb lc st p f).cross[0]! && !(Machine.lineComb lc st p f).next[0]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cur1 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cur[1]! =
      ((Machine.lineComb lc st p f).cross[1]! && !(Machine.lineComb lc st p f).next[1]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_cur2 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).cur[2]! =
      ((Machine.lineComb lc st p f).cross[2]! && !(Machine.lineComb lc st p f).next[2]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_tap0 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).tap[0]! =
      (((Machine.lineComb lc st p f).cur[0]! && !bit st.fired 0) ||
        (Machine.lineComb lc st p f).next[0]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_tap1 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).tap[1]! =
      (((Machine.lineComb lc st p f).cur[1]! && !bit st.fired 1) ||
        (Machine.lineComb lc st p f).next[1]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

theorem lineComb_tap2 (lc : Machine.LineCfg) (st : Machine.LineSt) (p : Machine.PinView)
    (f : Bool) : (Machine.lineComb lc st p f).tap[2]! =
      (((Machine.lineComb lc st p f).cur[2]! && !bit st.fired 2) ||
        (Machine.lineComb lc st p f).next[2]!) := by
  simp only [Machine.lineComb, vec3_get]
  rfl

/-! ## Phase sum, `nx` and the crossing predicate -/

theorem bv_lt_decide {n : Nat} (a b : BitVec n) :
    decide (a < b) = decide (a.toNat < b.toNat) := by
  by_cases h : a < b
  · have h2 : a.toNat < b.toNat := BitVec.lt_def.1 h
    simp [h, h2]
  · have h2 : ¬ a.toNat < b.toNat := fun hh => h (BitVec.lt_def.2 hh)
    simp [h, h2]

theorem decide_bv16_lt (a : BitVec 16) (t : Nat) (ht : t < 65536) :
    decide (a < bv 16 t) = decide (a.toNat < t) := by
  rw [bv_lt_decide, toNat_bv16 ht]

theorem decide_bv16_le (t : Nat) (x : BitVec 16) (ht : t < 65536) :
    decide (bv 16 t ≤ x) = decide (t ≤ x.toNat) := by
  rw [bv_le_decide, toNat_bv16 ht]

/-- `over` as the machine's `Nat` comparison. -/
theorem over_iff (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Metronome.Line.over s i = true ↔ s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat := by
  rw [over_eq_decide]
  exact decide_eq_true_iff

theorem mod_two_pow_add_sub {b a : Nat} (hb : b ≤ a) (ha : a < 131072) :
    (131072 - b + a) % 131072 = a - b := by
  have h1 : 131072 - b + a = 131072 + (a - b) := by omega
  rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The 17-bit wrapped difference has the `Nat` value `N - MOD` when `over`. -/
theorem nxw_toNat (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (hover : Metronome.Line.over s i = true) :
    (Metronome.Line.nxw s i).toNat = s.ph.toNat + i.cfg.inc.toNat - i.cfg.mod.toNat := by
  have hs : (Metronome.Line.sum17 s i).toNat = s.ph.toNat + i.cfg.inc.toNat :=
    sum17_toNat s i
  have hm : ((0 : BitVec 1) ++ Metronome.Line.slice 0 16 i.cfg.mod).toNat =
      i.cfg.mod.toNat := concat17_toNat i.cfg.mod
  have hge : i.cfg.mod.toNat ≤ s.ph.toNat + i.cfg.inc.toNat := (over_iff s i).1 hover
  simp only [Metronome.Line.nxw]
  rw [BitVec.toNat_sub, hs, hm, two_pow_17]
  exact mod_two_pow_add_sub hge (by
    have := (Metronome.Line.sum17 s i).isLt
    rw [hs] at this
    omega)

/-- The cut's `nx` value is the machine's `nx`. -/
theorem nx_toNat (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.nx s i).toNat =
      (if s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat
        then s.ph.toNat + i.cfg.inc.toNat - i.cfg.mod.toNat
        else s.ph.toNat + i.cfg.inc.toNat) % 65536 := by
  rw [Metronome.Line.nx]
  by_cases ho : Metronome.Line.over s i = true
  · have hge := (over_iff s i).1 ho
    rw [if_pos ho, if_pos hge, slice_toNat, nxw_toNat s i ho]
    simp only [nbits, Nat.shiftRight_zero, two_pow_16]
  · have hge : ¬ (s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat) := by
      intro h
      exact ho ((over_iff s i).2 h)
    rw [if_neg ho, if_neg hge, slice_toNat, sum17_toNat]
    simp only [nbits, Nat.shiftRight_zero, two_pow_16]

theorem nx_machine (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).nx = (Metronome.Line.nx s i).toNat := by
  subst hcfg
  rw [nx_toNat, lineComb_nx, absCfg_inc, absCfg_mod]
  rfl

/-- `crossing` at a `Nat` tap is the machine's `phaseCross` conditional. -/
theorem crossing_eq (s : Metronome.Line.State) (i : Metronome.Line.Input) (t : Nat)
    (ht : t < 65536) :
    Metronome.Line.crossing (bv 16 t) s.ph (Metronome.Line.nx s i) (Metronome.Line.over s i) =
      (if s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat
        then (t > s.ph.toNat || t ≤ (Metronome.Line.nx s i).toNat)
        else (s.ph.toNat < t && t ≤ (Metronome.Line.nx s i).toNat)) := by
  rw [Metronome.Line.crossing]
  by_cases ho : Metronome.Line.over s i = true
  · have hge := (over_iff s i).1 ho
    rw [if_pos ho, if_pos hge, decide_bv16_lt s.ph t ht,
      decide_bv16_le t (Metronome.Line.nx s i) ht]
  · have hge : ¬ (s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat) := by
      intro h
      exact ho ((over_iff s i).2 h)
    rw [if_neg ho, if_neg hge, decide_bv16_lt s.ph t ht,
      decide_bv16_le t (Metronome.Line.nx s i) ht]


theorem neZero_two (x : BitVec 2) : (x != 0) = (x.toNat != 0) := by
  rcases bv2_cases x with rfl | rfl | rfl | rfl <;> decide

theorem tapEnabled_zero (i : Metronome.Line.Input) :
    Machine.tapEnabled (absCfg i.cfg) 0 =
      (if i.cfg.t0src then (i.cfg.t0Pol != 0) else (i.cfg.t0 < i.cfg.mod)) := by
  by_cases h : i.cfg.t0src
  · simp [Machine.tapEnabled, Machine.Util.tapT, absCfg, h]
    exact (neZero_two _).symm
  · simp [Machine.tapEnabled, Machine.Util.tapT, absCfg, h]
    exact BitVec.lt_def.symm

theorem tapEnabled_one (i : Metronome.Line.Input) :
    Machine.tapEnabled (absCfg i.cfg) 1 = (decide (i.cfg.t1 < i.cfg.mod) : Bool) := by
  simp [Machine.tapEnabled, Machine.Util.tapT, absCfg]
  exact BitVec.lt_def.symm

theorem tapEnabled_two (i : Metronome.Line.Input) :
    Machine.tapEnabled (absCfg i.cfg) 2 = (decide (i.cfg.t2 < i.cfg.mod) : Bool) := by
  simp [Machine.tapEnabled, Machine.Util.tapT, absCfg]
  exact BitVec.lt_def.symm

theorem isPhaseTap_zero (i : Metronome.Line.Input) :
    Machine.Util.isPhaseTap (absCfg i.cfg) 0 = !i.cfg.t0src := by
  simp [Machine.Util.isPhaseTap, absCfg]

theorem isPhaseTap_one (i : Metronome.Line.Input) :
    Machine.Util.isPhaseTap (absCfg i.cfg) 1 = true := by
  simp [Machine.Util.isPhaseTap]

theorem isPhaseTap_two (i : Metronome.Line.Input) :
    Machine.Util.isPhaseTap (absCfg i.cfg) 2 = true := by
  simp [Machine.Util.isPhaseTap]

theorem tapT_zero (i : Metronome.Line.Input) :
    Machine.Util.tapT (absCfg i.cfg) 0 = i.cfg.t0.toNat := by
  simp [Machine.Util.tapT, absCfg]

theorem tapT_one (i : Metronome.Line.Input) :
    Machine.Util.tapT (absCfg i.cfg) 1 = i.cfg.t1.toNat := by
  simp [Machine.Util.tapT, absCfg]

theorem tapT_two (i : Metronome.Line.Input) :
    Machine.Util.tapT (absCfg i.cfg) 2 = i.cfg.t2.toNat := by
  simp [Machine.Util.tapT, absCfg]

theorem htap_cases (i : Metronome.Line.Input) :
    i.cfg.htap = 0 ∨ i.cfg.htap = 1 ∨ i.cfg.htap = 2 ∨ i.cfg.htap = 3 := by
  have h4 := i.cfg.htap.isLt
  rcases (by omega : i.cfg.htap.toNat = 0 ∨ i.cfg.htap.toNat = 1 ∨
    i.cfg.htap.toNat = 2 ∨ i.cfg.htap.toNat = 3) with h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h])))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))))

theorem holdTap_bridge (i : Metronome.Line.Input) :
    Machine.Util.tapT (absCfg i.cfg) (absCfg i.cfg).htap =
      (Metronome.Line.holdTap i).toNat := by
  rcases htap_cases i with h | h | h | h <;>
    simp [Machine.Util.tapT, Metronome.Line.holdTap, absCfg, h]

theorem holdOk_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    ((absCfg i.cfg).hen && ((absCfg i.cfg).htap != 3) &&
      Machine.tapEnabled (absCfg i.cfg) (absCfg i.cfg).htap &&
      Machine.Util.isPhaseTap (absCfg i.cfg) (absCfg i.cfg).htap)
    = ((absCfg i.cfg).hen && Metronome.Line.holdTok s i) := by
  rcases htap_cases i with h | h | h | h
  · by_cases hsrc : i.cfg.t0src
    · simp [Metronome.Line.holdTok, Machine.tapEnabled, Machine.Util.isPhaseTap,
        Machine.Util.tapT, absCfg, h, hsrc]
    · simp [Metronome.Line.holdTok, Machine.tapEnabled, Machine.Util.isPhaseTap,
        Machine.Util.tapT, absCfg, h, hsrc]
      simp only [Metronome.Line.tlt0]
      rw [bv_lt_decide]
  · simp [Metronome.Line.holdTok, Machine.tapEnabled, Machine.Util.isPhaseTap,
      Machine.Util.tapT, absCfg, h]
    simp only [Metronome.Line.tlt1]
    rw [bv_lt_decide]
  · simp [Metronome.Line.holdTok, Machine.tapEnabled, Machine.Util.isPhaseTap,
      Machine.Util.tapT, absCfg, h]
    simp only [Metronome.Line.tlt2]
    rw [bv_lt_decide]
  · simp [Metronome.Line.holdTok, absCfg, h]

theorem phaseCross_true (s : Metronome.Line.State) (i : Metronome.Line.Input) (k : Nat) :
    Machine.phaseCross (absCfg i.cfg) s.ph.toNat (s.ph.toNat + i.cfg.inc.toNat)
      (Metronome.Line.nx s i).toNat true k =
      (if s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat then
        (Machine.Util.tapT (absCfg i.cfg) k > s.ph.toNat ||
          Machine.Util.tapT (absCfg i.cfg) k ≤ (Metronome.Line.nx s i).toNat)
      else (s.ph.toNat < Machine.Util.tapT (absCfg i.cfg) k &&
        Machine.Util.tapT (absCfg i.cfg) k ≤ (Metronome.Line.nx s i).toNat)) := by
  simp only [Machine.phaseCross, Bool.true_and, absCfg_mod]
  rfl

theorem phaseCross_holdTap (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Machine.phaseCross (absCfg i.cfg) s.ph.toNat (s.ph.toNat + i.cfg.inc.toNat)
      (Metronome.Line.nx s i).toNat true (absCfg i.cfg).htap =
      Metronome.Line.crossing (Metronome.Line.holdTap i) s.ph (Metronome.Line.nx s i)
        (Metronome.Line.over s i) := by
  rw [phaseCross_true, holdTap_bridge, ← bv_toNat (Metronome.Line.holdTap i),
    crossing_eq s i (Metronome.Line.holdTap i).toNat (Metronome.Line.holdTap i).isLt]
  simp only [toNat_bv16 (Metronome.Line.holdTap i).isLt]

/-! ## Hold, advance, wrap and beat

The combinational `hold` is the one signal where the two models genuinely differ:
the cut gates it with `RUN && !frz` (`runa`), the machine does not.  `hold_bridge`
therefore carries `frz = false`; `adv`, `wrap` and `beat` are bridged
*unconditionally* because `adv` is freeze-gated in both models. -/

theorem hold_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i)
    (hfrz : i.frz = false) :
    (Machine.lineComb lc (absSt s) a.view i.frz).hold = Metronome.Line.hold s i := by
  subst hcfg
  rw [lineComb_hold, Metronome.Line.hold, holdOk_bridge s i,
    accept_bridge s i (absCfg i.cfg) rfl a hpin]
  rw [nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [absSt, absCfg_inc]
  rw [phaseCross_holdTap]
  have hpin' : a.view.pin (absCfg i.cfg).hpin =
      Metronome.Line.sel (Metronome.Line.Config.hpin i.cfg).toNat i.lvl := by
    rw [absCfg_hpin]
    exact hpin.pin _
  rw [hpin', absCfg_hen, absCfg_hlvl]
  simp only [Metronome.Line.runa, hfrz, Bool.not_false, Bool.and_true]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.and_self]

theorem adv_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).adv = Metronome.Line.adv s i := by
  subst hcfg
  rw [lineComb_adv, Metronome.Line.adv]
  by_cases hf : i.frz = false
  · rw [hold_bridge s i (absCfg i.cfg) rfl a hpin hf,
      accept_bridge s i (absCfg i.cfg) rfl a hpin]
    simp only [Metronome.Line.runa, absSt, hf, Bool.not_false, Bool.true_and]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.true_and]
  · have hft : i.frz = true := by
      cases hh : i.frz
      · exact absurd hh hf
      · rfl
    simp only [Metronome.Line.runa, hft, Bool.not_true, Bool.false_and, Bool.and_false]

theorem wrap_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).wrap = Metronome.Line.wrap s i := by
  subst hcfg
  rw [lineComb_wrap, Metronome.Line.wrap, adv_bridge s i (absCfg i.cfg) rfl a hpin,
    over_bridge s i (absCfg i.cfg) rfl a hpin]

theorem beat_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).beat = Metronome.Line.beat s i := by
  subst hcfg
  rw [lineComb_beat, Metronome.Line.beat, absCfg_follow]
  by_cases hf : i.cfg.follow = true
  · simp [hf, accept_bridge s i (absCfg i.cfg) rfl a hpin]
  · have hf' : i.cfg.follow = false := by
      cases hh : i.cfg.follow
      · rfl
      · exact absurd hh hf
    simp [hf', wrap_bridge s i (absCfg i.cfg) rfl a hpin]

/-! ## Taps: `cross`, `next`, `cur`, `tap` -/

/-- The edge-sourced tap-0 enable does not lose the edge: a zero polarity makes
`e0` false, so `(T0EDGE.polarity != 0) && e0 = e0`. -/
theorem bne_zero_and_e0 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    ((i.cfg.t0Pol != 0) && (s.run && Metronome.Line.e0 s i)) =
      (s.run && Metronome.Line.e0 s i) := by
  rcases bv2_cases i.cfg.t0Pol with h | h | h | h <;>
    simp [Metronome.Line.e0, Metronome.Line.esel, h]

/-- `cross_0`: the edge-sourced tap 0 when `T0SRC`, else the phase crossing. -/
theorem cross0_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cross[0]! = Metronome.Line.cross0 s i := by
  subst hcfg
  rw [lineComb_cross0, lineComb_en0, Metronome.Line.cross0]
  by_cases hsrc : i.cfg.t0src = true
  · rw [isPhaseTap_zero, hsrc, tapEnabled_zero]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, hsrc, ite_true]
    rw [e0_bridge s i (absCfg i.cfg) rfl a hpin]
    simp only [absSt]
    rw [bne_zero_and_e0]
  · have hsrc' : i.cfg.t0src = false := by
      cases hh : i.cfg.t0src
      · rfl
      · exact absurd hh hsrc
    rw [isPhaseTap_zero, hsrc', tapEnabled_zero, Metronome.Line.tapCross0,
      Metronome.Line.tlt0, adv_bridge s i (absCfg i.cfg) rfl a hpin]
    simp only [hsrc', Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [Machine.phaseCross, absCfg_mod, tapT_zero,
      nx_machine s i (absCfg i.cfg) rfl a hpin]
    simp only [absSt, absCfg_inc]
    rw [Metronome.Line.crossing, ← bv_toNat i.cfg.t0]
    by_cases hP : s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat
    · have ho : Metronome.Line.over s i = true := (over_iff s i).2 hP
      simp only [hP, ite_true, ho]
      simp only [toNat_bv16 i.cfg.t0.isLt,
        decide_bv16_lt s.ph i.cfg.t0.toNat i.cfg.t0.isLt,
        decide_bv16_le i.cfg.t0.toNat (Metronome.Line.nx s i) i.cfg.t0.isLt]
      simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
    · have ho : ¬ (Metronome.Line.over s i = true) := fun h => hP ((over_iff s i).1 h)
      simp only [hP, ite_false, ho, ite_false, Bool.false_eq_true]
      simp only [toNat_bv16 i.cfg.t0.isLt,
        decide_bv16_lt s.ph i.cfg.t0.toNat i.cfg.t0.isLt,
        decide_bv16_le i.cfg.t0.toNat (Metronome.Line.nx s i) i.cfg.t0.isLt]
      simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem cross1_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cross[1]! = Metronome.Line.tapCross1 s i := by
  subst hcfg
  rw [lineComb_cross1, lineComb_en1, tapEnabled_one, isPhaseTap_one,
    Metronome.Line.tapCross1, Metronome.Line.tlt1,
    adv_bridge s i (absCfg i.cfg) rfl a hpin]
  rw [Machine.phaseCross, absCfg_mod, tapT_one,
    nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [absSt, absCfg_inc, ite_true]
  rw [Metronome.Line.crossing, ← bv_toNat i.cfg.t1]
  by_cases hP : s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat
  · have ho : Metronome.Line.over s i = true := (over_iff s i).2 hP
    simp only [hP, ite_true, ho]
    simp only [toNat_bv16 i.cfg.t1.isLt,
      decide_bv16_lt s.ph i.cfg.t1.toNat i.cfg.t1.isLt,
      decide_bv16_le i.cfg.t1.toNat (Metronome.Line.nx s i) i.cfg.t1.isLt]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · have ho : ¬ (Metronome.Line.over s i = true) := fun h => hP ((over_iff s i).1 h)
    simp only [hP, ite_false, ho, ite_false, Bool.false_eq_true]
    simp only [toNat_bv16 i.cfg.t1.isLt,
      decide_bv16_lt s.ph i.cfg.t1.toNat i.cfg.t1.isLt,
      decide_bv16_le i.cfg.t1.toNat (Metronome.Line.nx s i) i.cfg.t1.isLt]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem cross2_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cross[2]! = Metronome.Line.tapCross2 s i := by
  subst hcfg
  rw [lineComb_cross2, lineComb_en2, tapEnabled_two, isPhaseTap_two,
    Metronome.Line.tapCross2, Metronome.Line.tlt2,
    adv_bridge s i (absCfg i.cfg) rfl a hpin]
  rw [Machine.phaseCross, absCfg_mod, tapT_two,
    nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [absSt, absCfg_inc, ite_true]
  rw [Metronome.Line.crossing, ← bv_toNat i.cfg.t2]
  by_cases hP : s.ph.toNat + i.cfg.inc.toNat ≥ i.cfg.mod.toNat
  · have ho : Metronome.Line.over s i = true := (over_iff s i).2 hP
    simp only [hP, ite_true, ho]
    simp only [toNat_bv16 i.cfg.t2.isLt,
      decide_bv16_lt s.ph i.cfg.t2.toNat i.cfg.t2.isLt,
      decide_bv16_le i.cfg.t2.toNat (Metronome.Line.nx s i) i.cfg.t2.isLt]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · have ho : ¬ (Metronome.Line.over s i = true) := fun h => hP ((over_iff s i).1 h)
    simp only [hP, ite_false, ho, ite_false, Bool.false_eq_true]
    simp only [toNat_bv16 i.cfg.t2.isLt,
      decide_bv16_lt s.ph i.cfg.t2.toNat i.cfg.t2.isLt,
      decide_bv16_le i.cfg.t2.toNat (Metronome.Line.nx s i) i.cfg.t2.isLt]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

/-- `next_0`: a boundary's tap-0 event belongs to the next beat. -/
theorem next0_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).next[0]! = Metronome.Line.next0 s i := by
  subst hcfg
  rw [lineComb_next0, cross0_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.next0]
  by_cases hsrc : i.cfg.t0src = true
  · rw [isPhaseTap_zero, hsrc, Metronome.Line.cross0]
    simp only [hsrc, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [beat_bridge s i (absCfg i.cfg) rfl a hpin]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.true_and,
      Bool.and_true]
  · have hsrc' : i.cfg.t0src = false := by
      cases hh : i.cfg.t0src
      · rfl
      · exact absurd hh hsrc
    rw [isPhaseTap_zero, hsrc', Metronome.Line.cross0, tapT_zero,
      Metronome.Line.tapCross0, beat_bridge s i (absCfg i.cfg) rfl a hpin,
      over_bridge s i (absCfg i.cfg) rfl a hpin,
      nx_machine s i (absCfg i.cfg) rfl a hpin]
    simp only [hsrc', ite_false, Bool.not_false, bv_le_decide, ite_true,
      Bool.false_eq_true]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.true_and,
      Bool.and_true]

theorem next1_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).next[1]! = Metronome.Line.next1 s i := by
  subst hcfg
  rw [lineComb_next1, cross1_bridge s i (absCfg i.cfg) rfl a hpin, isPhaseTap_one,
    tapT_one, Metronome.Line.next1,
    beat_bridge s i (absCfg i.cfg) rfl a hpin,
    over_bridge s i (absCfg i.cfg) rfl a hpin,
    nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [ite_true, bv_le_decide]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.true_and]

theorem next2_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).next[2]! = Metronome.Line.next2 s i := by
  subst hcfg
  rw [lineComb_next2, cross2_bridge s i (absCfg i.cfg) rfl a hpin, isPhaseTap_two,
    tapT_two, Metronome.Line.next2,
    beat_bridge s i (absCfg i.cfg) rfl a hpin,
    over_bridge s i (absCfg i.cfg) rfl a hpin,
    nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [ite_true, bv_le_decide]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Bool.true_and]

theorem cur0_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cur[0]! = Metronome.Line.cur0 s i := by
  subst hcfg
  rw [lineComb_cur0, cross0_bridge s i (absCfg i.cfg) rfl a hpin,
    next0_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.cur0]

theorem cur1_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cur[1]! = Metronome.Line.cur1 s i := by
  subst hcfg
  rw [lineComb_cur1, cross1_bridge s i (absCfg i.cfg) rfl a hpin,
    next1_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.cur1]

theorem cur2_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).cur[2]! = Metronome.Line.cur2 s i := by
  subst hcfg
  rw [lineComb_cur2, cross2_bridge s i (absCfg i.cfg) rfl a hpin,
    next2_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.cur2]

theorem tap0_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).tap[0]! = Metronome.Line.tap0 s i := by
  subst hcfg
  rw [lineComb_tap0, cur0_bridge s i (absCfg i.cfg) rfl a hpin,
    next0_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap0,
    bitAt_eq_bit s.fired 0]
  simp only [absSt]

theorem tap1_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).tap[1]! = Metronome.Line.tap1 s i := by
  subst hcfg
  rw [lineComb_tap1, cur1_bridge s i (absCfg i.cfg) rfl a hpin,
    next1_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap1,
    bitAt_eq_bit s.fired 1]
  simp only [absSt]

theorem tap2_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb lc (absSt s) a.view i.frz).tap[2]! = Metronome.Line.tap2 s i := by
  subst hcfg
  rw [lineComb_tap2, cur2_bridge s i (absCfg i.cfg) rfl a hpin,
    next2_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap2,
    bitAt_eq_bit s.fired 2]
  simp only [absSt]


theorem pack3_get0 (b2 b1 b0 : Bool) :
    (Metronome.Line.pack3 b2 b1 b0).getLsbD 0 = b0 := by
  show bit (Metronome.Line.pack3 b2 b1 b0) 0 = b0
  rw [pack3_bit _ _ _ 0 (by omega)]
  simp

theorem pack3_get1 (b2 b1 b0 : Bool) :
    (Metronome.Line.pack3 b2 b1 b0).getLsbD 1 = b1 := by
  show bit (Metronome.Line.pack3 b2 b1 b0) 1 = b1
  rw [pack3_bit _ _ _ 1 (by omega)]
  simp

theorem pack3_get2 (b2 b1 b0 : Bool) :
    (Metronome.Line.pack3 b2 b1 b0).getLsbD 2 = b2 := by
  show bit (Metronome.Line.pack3 b2 b1 b0) 2 = b2
  rw [pack3_bit _ _ _ 2 (by omega)]
  simp

theorem missBits_disj (a b c d : BitVec 3) :
    ((a &&& ~~~b) &&& ~~~c &&& d != 0) =
      ((a.getLsbD 0 && !b.getLsbD 0 && !c.getLsbD 0 && d.getLsbD 0) ||
       (a.getLsbD 1 && !b.getLsbD 1 && !c.getLsbD 1 && d.getLsbD 1) ||
       (a.getLsbD 2 && !b.getLsbD 2 && !c.getLsbD 2 && d.getLsbD 2)) := by
  bv_decide

theorem enBit0 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.enBits s i).getLsbD 0 =
      (if i.cfg.t0src then (i.cfg.t0Pol != 0) else decide (i.cfg.t0 < i.cfg.mod)) := by
  rw [Metronome.Line.enBits, pack3_get0]
  simp [Metronome.Line.tlt0]

theorem enBit1 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.enBits s i).getLsbD 1 = decide (i.cfg.t1 < i.cfg.mod) := by
  rw [Metronome.Line.enBits, pack3_get1]
  simp [Metronome.Line.tlt1]

theorem enBit2 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.enBits s i).getLsbD 2 = decide (i.cfg.t2 < i.cfg.mod) := by
  rw [Metronome.Line.enBits, pack3_get2]
  simp [Metronome.Line.tlt2]

theorem curBit0 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.curBits s i).getLsbD 0 = Metronome.Line.cur0 s i := by
  rw [Metronome.Line.curBits, pack3_get0]

theorem curBit1 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.curBits s i).getLsbD 1 = Metronome.Line.cur1 s i := by
  rw [Metronome.Line.curBits, pack3_get1]

theorem curBit2 (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.curBits s i).getLsbD 2 = Metronome.Line.cur2 s i := by
  rw [Metronome.Line.curBits, pack3_get2]

theorem missBits_expand (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.missBits s i != 0) =
      (((Metronome.Line.enBits s i).getLsbD 0 && !s.fired.getLsbD 0 &&
          !(Metronome.Line.curBits s i).getLsbD 0 && !(i.cfg.t0src && s.first)) ||
       ((Metronome.Line.enBits s i).getLsbD 1 && !s.fired.getLsbD 1 &&
          !(Metronome.Line.curBits s i).getLsbD 1) ||
       ((Metronome.Line.enBits s i).getLsbD 2 && !s.fired.getLsbD 2 &&
          !(Metronome.Line.curBits s i).getLsbD 2)) := by
  rw [Metronome.Line.missBits, missBits_disj, Metronome.Line.missOk,
    pack3_get0, pack3_get1, pack3_get2]
  simp only [Bool.and_true]



theorem setBit_pack4_0 (b3 b2 b1 b0 v : Bool) :
    setBit (Metronome.Line.pack4 b3 b2 b1 b0) 0 v = Metronome.Line.pack4 b3 b2 b1 v := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> cases v <;> decide

theorem setBit_pack4_1 (b3 b2 b1 b0 v : Bool) :
    setBit (Metronome.Line.pack4 b3 b2 b1 b0) 1 v = Metronome.Line.pack4 b3 b2 v b0 := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> cases v <;> decide

theorem setBit_pack4_2 (b3 b2 b1 b0 v : Bool) :
    setBit (Metronome.Line.pack4 b3 b2 b1 b0) 2 v = Metronome.Line.pack4 b3 v b1 b0 := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> cases v <;> decide

theorem setBit_pack4_3 (b3 b2 b1 b0 v : Bool) :
    setBit (Metronome.Line.pack4 b3 b2 b1 b0) 3 v = Metronome.Line.pack4 v b2 b1 b0 := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> cases v <;> decide

theorem pack4_bit0 (b3 b2 b1 b0 : Bool) :
    bit (Metronome.Line.pack4 b3 b2 b1 b0) 0 = b0 := by
  rw [pack4_bit _ _ _ _ 0 (by omega)]
  simp

theorem pack4_bit1 (b3 b2 b1 b0 : Bool) :
    bit (Metronome.Line.pack4 b3 b2 b1 b0) 1 = b1 := by
  rw [pack4_bit _ _ _ _ 1 (by omega)]
  simp

theorem pack4_bit2 (b3 b2 b1 b0 : Bool) :
    bit (Metronome.Line.pack4 b3 b2 b1 b0) 2 = b2 := by
  rw [pack4_bit _ _ _ _ 2 (by omega)]
  simp

theorem pack4_bit3 (b3 b2 b1 b0 : Bool) :
    bit (Metronome.Line.pack4 b3 b2 b1 b0) 3 = b3 := by
  rw [pack4_bit _ _ _ _ 3 (by omega)]
  simp

theorem capture_test (w : BitVec 4) (t0 t1 t2 pa pb : Bool) :
    (let w1 := if t0 then setBit w 0 pa else w
     let w2 := if t1 then setBit (setBit w1 1 pa) 3 pb else w1
     if t2 then setBit w2 2 pa else w2) =
      Metronome.Line.pack4 (if t1 then pb else bit w 3) (if t2 then pa else bit w 2)
        (if t1 then pa else bit w 1) (if t0 then pa else bit w 0) := by
  rw [← pack4_bits' w]
  by_cases h0 : t0 <;> by_cases h1 : t1 <;> by_cases h2 : t2 <;>
    simp [h0, h1, h2, setBit_pack4_0, setBit_pack4_1, setBit_pack4_2, setBit_pack4_3,
      pack4_bit0, pack4_bit1, pack4_bit2, pack4_bit3]



theorem two_pow_1 : (2 : Nat) ^ 1 = 2 := by decide

theorem slice1_3_toNat (v : BitVec 4) :
    (Metronome.Line.slice 1 3 v).toNat = v.toNat / 2 := by
  rw [slice_toNat]
  simp only [nbits, Nat.shiftRight_zero, two_pow_3]
  rw [Nat.shiftRight_eq_div_pow, two_pow_1]
  have h : v.toNat / 2 < 8 := by
    have := v.isLt
    omega
  rw [Nat.mod_eq_of_lt h]

theorem slice0_1_toNat (v : BitVec 4) :
    (Metronome.Line.slice 0 1 v).toNat = v.toNat % 2 := by
  rw [slice_toNat]
  simp only [nbits, Nat.mul_zero, Nat.shiftRight_zero, two_pow_1]

theorem dbit_test (staged d : BitVec 4) :
    Metronome.Line.slice 1 3 staged ++ Metronome.Line.slice 0 1 d =
      bv 4 ((staged.toNat / 2) * 2 + d.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (by
      rw [slice0_1_toNat]; exact Nat.mod_lt _ (by omega)),
    Nat.shiftLeft_eq, slice1_3_toNat, slice0_1_toNat, two_pow_1]
  rw [toNat_bv4 (by
    have := staged.isLt
    omega)]

theorem absSymOp0 : absSymOp 0 = 1 := by decide
theorem absSymOp1 : absSymOp 1 = 2 := by decide
theorem absSymOp2 : absSymOp 2 = 3 := by decide

theorem stagedNext_test (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Machine.stagedNext (absSt s) (absIn i).sym = Metronome.Line.stagedNext s i := by
  rw [Metronome.Line.stagedNext, absIn]
  by_cases hw : i.symWe = true
  · simp only [hw, if_true]
    rcases bv2_cases i.symOp with h | h | h | h
    · rw [h, absSymOp0]
      simp [Machine.stagedNext, absSt, bv_toNat]
    · rw [h, absSymOp1]
      simp [Machine.stagedNext, absSt, dbit_test]
    · rw [h, absSymOp2]
      simp [Machine.stagedNext, absSt, bv_toNat]
    · rw [h, absSymOp_three]
      simp [Machine.stagedNext, absSt, bv_toNat]
  · simp only [hw, if_false]
    simp [Machine.stagedNext, absSt]



theorem run_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).run =
      Metronome.Line.runF s i := by
  simp only [Machine.lineNext, absIn, Metronome.Line.runF, Metronome.Line.runC]
  rw [start_bridge s i (absCfg i.cfg) rfl a hpin]
  by_cases hc : i.ctlWe = true <;> by_cases hh : i.hCtlWe = true <;>
    simp [hc, hh, bitAt_eq_nbit, absSt]

theorem arm_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).arm =
      Metronome.Line.armF s i := by
  simp only [Machine.lineNext, absIn, Metronome.Line.armF, Metronome.Line.armC]
  rw [start_bridge s i (absCfg i.cfg) rfl a hpin]
  by_cases hc : i.ctlWe = true <;> by_cases hh : i.hCtlWe = true <;>
    simp [hc, hh, bitAt_eq_nbit, absSt]

theorem ren_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).ren =
      Metronome.Line.renF s i := by
  simp only [Machine.lineNext, absIn, Metronome.Line.renF, Metronome.Line.renC]
  by_cases hc : i.ctlWe = true <;> by_cases hh : i.hCtlWe = true <;>
    simp [hc, hh, bitAt_eq_nbit, absSt]



theorem slice4_self (v : BitVec 4) : Metronome.Line.slice 0 4 v = v := by
  apply BitVec.eq_of_toNat_eq
  rw [slice_toNat]
  simp [nbits, two_pow_4, Nat.mod_eq_of_lt v.isLt]

theorem concat1_4_toNat (b : BitVec 1) (x : BitVec 4) :
    (b ++ x).toNat = b.toNat * 16 + x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq, two_pow_4]

theorem concat1_1_toNat (a b : BitVec 1) : (a ++ b).toNat = a.toNat * 2 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem cap_toNat (s : Metronome.Line.State) :
    (Metronome.Line.cap s).toNat = b2n (absSt s).rem * 16 + (absSt s).sn.toNat := by
  rw [Metronome.Line.cap, concat1_4_toNat, slice4_self]
  have h : (if s.rem then (1 : BitVec 1) else 0).toNat = b2n s.rem := by
    rw [b2n_eq]
    cases s.rem <;> rfl
  rw [h]
  rfl

theorem bit1_if (b : Bool) : (if b then (1 : BitVec 1) else 0).toNat = b2n b := by
  rw [b2n_eq]
  cases b <;> rfl

theorem inSym_toNat (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.inSym s i).toNat = Machine.inSym (absCfg i.cfg) (absSt s) := by
  rw [Metronome.Line.inSym, concat1_1_toNat, cap_toNat s,
    Machine.inSym, sel32_eq_nbit, sel32_eq_nbit, bit1_if, bit1_if,
    absCfg_lut0, absCfg_lut1]

theorem rem_test (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Metronome.Line.sel (Metronome.Line.cap s).toNat i.cfg.lut1 =
      nbit (Machine.inSym (absCfg i.cfg) (absSt s)) 1 := by
  rw [sel32_eq_nbit, Machine.inSym, cap_toNat s, absCfg_lut0, absCfg_lut1]
  rw [nbit_two_mul_add]



theorem pina_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    a.view.pin (absCfg i.cfg).pina = Metronome.Line.pina i := by
  rw [absCfg_pina]
  exact hpin.pin _

theorem pinb_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    a.view.pin (absCfg i.cfg).pinb = Metronome.Line.pinb i := by
  rw [absCfg_pinb]
  exact hpin.pin _

theorem w_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).w =
      Metronome.Line.wNext s i := by
  simp only [Machine.lineNext]
  rw [tap0_bridge s i (absCfg i.cfg) rfl a hpin,
    tap1_bridge s i (absCfg i.cfg) rfl a hpin,
    tap2_bridge s i (absCfg i.cfg) rfl a hpin,
    pina_test s i a hpin, pinb_test s i a hpin]
  simp only [absSt]
  rw [Metronome.Line.wNext, bitAt_eq_bit, bitAt_eq_bit, bitAt_eq_bit, bitAt_eq_bit]
  exact capture_test s.w (Metronome.Line.tap0 s i) (Metronome.Line.tap1 s i)
    (Metronome.Line.tap2 s i) (Metronome.Line.pina i) (Metronome.Line.pinb i)



theorem phC_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    Metronome.Line.phC s i =
      bv 16 (if (Metronome.Line.start s i || Metronome.Line.accept s i) then
          i.cfg.pre.toNat
        else if Metronome.Line.adv s i then (Metronome.Line.nx s i).toNat else s.ph.toNat) := by
  rw [Metronome.Line.phC]
  by_cases h : (Metronome.Line.start s i || Metronome.Line.accept s i) = true
  · rw [if_pos h, if_pos h]
    exact (bv_toNat i.cfg.pre).symm
  · rw [if_neg h, if_neg h]
    by_cases hadv : Metronome.Line.adv s i = true
    · rw [if_pos hadv, if_pos hadv]
      exact (bv_toNat (Metronome.Line.nx s i)).symm
    · rw [if_neg hadv, if_neg hadv]
      exact (bv_toNat s.ph).symm

theorem phF_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (ph0 : Nat)
    (h : (if (Metronome.Line.start s i || Metronome.Line.accept s i) then i.cfg.pre.toNat
        else if Metronome.Line.adv s i then (Metronome.Line.nx s i).toNat else s.ph.toNat) = ph0) :
    Metronome.Line.phF s i =
      (match (absIn i).hPhase with
       | some (k, v) => setByte (bv 16 ph0) k v
       | none => bv 16 ph0) := by
  rw [Metronome.Line.phF, phC_bridge s i, h]
  by_cases h0 : Metronome.Line.bitAt 0 i.phWe = true
  · rw [if_pos h0, absIn]
    simp only [h0, if_true]
    rw [← setByte0_16 (bv 16 ph0) i.hD]
  · by_cases h1 : Metronome.Line.bitAt 1 i.phWe = true
    · rw [if_neg h0, if_pos h1, absIn]
      simp only [h0, h1, if_true, if_false, Bool.false_eq_true]
      rw [← setByte1_16 (bv 16 ph0) i.hD]
    · rw [if_neg h0, if_neg h1, absIn]
      simp only [h0, h1, if_false, Bool.false_eq_true]

theorem ph_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).ph =
      Metronome.Line.phF s i := by
  simp only [Machine.lineNext]
  rw [start_bridge s i (absCfg i.cfg) rfl a hpin,
    accept_bridge s i (absCfg i.cfg) rfl a hpin,
    adv_bridge s i (absCfg i.cfg) rfl a hpin,
    nx_machine s i (absCfg i.cfg) rfl a hpin]
  simp only [absCfg_pre, absSt]
  rw [phF_bridge s i _ rfl]
  rfl

theorem held_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).held =
      (if i.frz = true then s.held else Metronome.Line.hold s i) := by
  simp only [Machine.lineNext]
  by_cases hf : i.frz = false
  · rw [if_neg (by simp [hf]), hold_bridge s i (absCfg i.cfg) rfl a hpin hf]
    simp [hf]
  · have hft : i.frz = true := by
      cases hh : i.frz
      · exact absurd hh hf
      · rfl
    rw [if_pos hft]
    simp [hft, absSt]



theorem beat_st (s : Metronome.Line.State) (i : Metronome.Line.Input) (st : Machine.LineSt)
    (hst : absSt s = st) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb (absCfg i.cfg) st a.view i.frz).beat = Metronome.Line.beat s i := by
  subst st
  exact beat_bridge s i (absCfg i.cfg) rfl a hpin

theorem start_st (s : Metronome.Line.State) (i : Metronome.Line.Input) (st : Machine.LineSt)
    (hst : absSt s = st) (a : PinAbs) (hpin : PinAgree a i) :
    (Machine.lineComb (absCfg i.cfg) st a.view i.frz).start = Metronome.Line.start s i := by
  subst st
  exact start_bridge s i (absCfg i.cfg) rfl a hpin

theorem stagedNext_st2 (s : Metronome.Line.State) (i : Metronome.Line.Input) (st : Machine.LineSt)
    (hst : absSt s = st) :
    Machine.stagedNext st
      (if i.symWe = true then some { op := absSymOp i.symOp, v := i.symD.toNat } else none) =
      Metronome.Line.stagedNext s i := by
  subst st
  exact stagedNext_test s i

theorem committed_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).committed =
      Metronome.Line.committedNext s i := by
  rw [Metronome.Line.committedNext, Metronome.Line.starting,
    Metronome.Line.runF, Metronome.Line.runC]
  simp only [Machine.lineNext, absIn]
  generalize hst : absSt s = st
  rw [beat_st s i st hst a hpin, start_st s i st hst a hpin, stagedNext_st2 s i st hst]
  subst st
  by_cases hc : i.ctlWe = true <;> by_cases hh : i.hCtlWe = true <;>
    simp [hc, hh, bitAt_eq_nbit, absSt]



theorem miss_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    ((List.range 3).any fun k =>
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).en[k]! &&
      !(absSt s).fired.getLsbD k &&
      !(Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).cur[k]! &&
      !(k == 0 && (absCfg i.cfg).t0src && (absSt s).first)) =
      (Metronome.Line.missBits s i != 0) := by
  rw [range_three_any, Metronome.Bridge.Line.missBits_expand,
    Metronome.Bridge.Line.cur0_bridge s i (absCfg i.cfg) rfl a hpin,
    Metronome.Bridge.Line.cur1_bridge s i (absCfg i.cfg) rfl a hpin,
    Metronome.Bridge.Line.cur2_bridge s i (absCfg i.cfg) rfl a hpin,
    lineComb_en0, lineComb_en1, lineComb_en2,
    Metronome.Bridge.Line.tapEnabled_zero, Metronome.Bridge.Line.tapEnabled_one,
    Metronome.Bridge.Line.tapEnabled_two,
    Metronome.Bridge.Line.enBit0, Metronome.Bridge.Line.enBit1,
    Metronome.Bridge.Line.enBit2, Metronome.Bridge.Line.curBit0,
    Metronome.Bridge.Line.curBit1, Metronome.Bridge.Line.curBit2]
  simp only [absSt, absCfg_t0src]
  simp



theorem seg_test (s : Metronome.Line.State) :
    (Metronome.Line.seg s).toNat = Machine.seg (absSt s) := by
  rw [Metronome.Line.seg, Machine.seg, absSt]
  rcases bv3_cases s.fired with h | h | h | h | h | h | h | h <;> rw [h]
  all_goals
    (simp only [Metronome.Machine.Util.popcount]; decide)



theorem tapmiss_test (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).tapmiss =
      (Metronome.Line.missEv s i ||
        (s.tapmiss && !(i.hStatWe && Metronome.Line.bitAt 0 i.hD))) := by
  rw [Metronome.Line.missEv]
  simp only [Machine.lineNext, absIn]
  simp only [Metronome.Machine.Util.bit]
  rw [beat_bridge s i (absCfg i.cfg) rfl a hpin,
    miss_test s i a hpin]
  simp only [absSt, bitAt_eq_bit, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm,
    Bool.not_and, Bool.or_comm, Bool.or_assoc]

/-! ## `FIRST`, `FIRED` and the snapshot dot product

`lineNext` binds its `FIRST`/`FIRED` pair as one `let (fired', first') := ...`;
the projections `Prod.fst`/`Prod.snd` of that tuple are distributed over the
`if` by `prod_fst_ite`/`prod_snd_ite`.  `starting_st` names the machine's start
condition (the `.run` field equation of `run_test` read through `absSt`).  The
three register equations then follow from the per-field bridges above. -/

theorem prod_snd_ite {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).snd = if c then x.snd else y.snd := by
  by_cases h : c <;> simp [h]

theorem prod_fst_ite {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).fst = if c then x.fst else y.fst := by
  by_cases h : c <;> simp [h]

/-- Bitwise or of a bus with a packed triple, as the three branch bits. -/
theorem or3_bits (f : BitVec 3) (x y z : Bool) :
    Metronome.Line.pack3 (bit f 2 || x) (bit f 1 || y) (bit f 0 || z) =
      (f ||| Metronome.Line.pack3 x y z) := by
  rw [or3_as_pack3, pack3_bit _ _ _ 0 (by omega), pack3_bit _ _ _ 1 (by omega),
    pack3_bit _ _ _ 2 (by omega)]
  simp

/-- `sel k` of `pack3` is the packed bit `k < 3` (`SNAP`/`TAP` dot product). -/
theorem sel_pack3 (b2 b1 b0 : Bool) (k : Nat) (hk : k < 3) :
    Metronome.Line.sel k (Metronome.Line.pack3 b2 b1 b0) =
      (if k = 0 then b0 else if k = 1 then b1 else b2) := by
  rw [sel3_eq_nbit, ← bit_eq_nbit]
  exact pack3_bit b2 b1 b0 k hk

theorem absSt_ph (s : Metronome.Line.State) : (absSt s).ph = s.ph := rfl

theorem absSt_fired (s : Metronome.Line.State) : (absSt s).fired = s.fired := rfl

/-- The machine start condition `run' && !RUN` is the cut's `starting`. -/
theorem starting_st (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    ((Machine.lineNext (absCfg i.cfg) (absSt s)
        (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).run
      && !(absSt s).run) = Metronome.Line.starting s i := by
  rw [run_test s i a hpin]
  rfl

/-- `FIRST' = starting || (FIRST && !BEAT)` (§3.4, D28). -/
theorem first_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).first =
      (Metronome.Line.starting s i || (s.first && !Metronome.Line.beat s i)) := by
  rw [Metronome.Line.starting, Metronome.Line.runF, Metronome.Line.runC,
    Metronome.Line.beat]
  simp only [Machine.lineNext]
  rw [prod_snd_ite, prod_snd_ite,
    beat_bridge s i (absCfg i.cfg) rfl a hpin,
    start_bridge s i (absCfg i.cfg) rfl a hpin]
  by_cases hc : i.ctlWe = true <;> by_cases hh : i.hCtlWe = true <;>
    by_cases hb : i.cfg.follow = true <;>
    simp [hc, hh, hb, absIn, bitAt_eq_nbit, absSt, Metronome.Line.beat,
      Bool.and_comm, Bool.or_comm]

/-- `FIRED'` (§3.4): `startBits` on a start, `nextBits` on a beat, otherwise
`FIRED || curBits`. -/
theorem fired_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).fired =
      (if Metronome.Line.starting s i then Metronome.Line.startBits s i
        else Metronome.Line.firedNext s i) := by
  rw [Metronome.Line.startBits, Metronome.Line.firedNext,
    Metronome.Line.nextBits, Metronome.Line.curBits]
  simp only [Machine.lineNext]
  have hstart := starting_st s i a hpin
  simp only [Machine.lineNext] at hstart
  rw [prod_fst_ite, prod_fst_ite, hstart]
  simp only [start_bridge s i (absCfg i.cfg) rfl a hpin,
    accept_bridge s i (absCfg i.cfg) rfl a hpin,
    adv_bridge s i (absCfg i.cfg) rfl a hpin,
    nx_machine s i (absCfg i.cfg) rfl a hpin, absCfg_pre, absSt_ph]
  simp only [phF_bridge s i _ rfl]
  simp only [range_three_map, packBits3_as_pack3, tapEnabled_zero, tapEnabled_one,
    tapEnabled_two, isPhaseTap_zero, isPhaseTap_one, isPhaseTap_two, tapT_zero,
    tapT_one, tapT_two]
  rw [bv_le_decide i.cfg.t0 _, bv_le_decide i.cfg.t1 _, bv_le_decide i.cfg.t2 _]
  rw [next0_bridge s i (absCfg i.cfg) rfl a hpin,
    next1_bridge s i (absCfg i.cfg) rfl a hpin,
    next2_bridge s i (absCfg i.cfg) rfl a hpin,
    cur0_bridge s i (absCfg i.cfg) rfl a hpin,
    cur1_bridge s i (absCfg i.cfg) rfl a hpin,
    cur2_bridge s i (absCfg i.cfg) rfl a hpin,
    absSt_fired, beat_bridge s i (absCfg i.cfg) rfl a hpin]
  rw [or3_bits]
  by_cases hsrc : i.cfg.t0src = true <;>
    by_cases hpw0 : Metronome.Line.bitAt 0 i.phWe = true <;>
    by_cases hpw1 : Metronome.Line.bitAt 1 i.phWe = true <;>
    simp [hsrc, hpw0, hpw1, absIn, Metronome.Line.tlt0, Metronome.Line.tlt1,
      Metronome.Line.tlt2, setByte0_16, setByte1_16, Bool.and_comm, Bool.or_comm,
      Bool.true_and]

/-- The `SNAP`/`TAP` dot product (§3.5): `SNAP == 3 ? BEAT : TAP[SNAP]`. -/
theorem snap_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (if (absCfg i.cfg).snap == 3 then
        (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).beat
      else (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[(absCfg i.cfg).snap]!) =
      Metronome.Line.snap s i := by
  rw [Metronome.Line.snap, absCfg_snap]
  rcases bv2_cases i.cfg.snap with h | h | h | h
  · rw [h]
    show (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[0]! =
      Metronome.Line.sel 0 (Metronome.Line.tap s i)
    rw [tap0_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap,
      sel_pack3 _ _ _ 0 (by decide)]
    rfl
  · rw [h]
    show (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[1]! =
      Metronome.Line.sel 1 (Metronome.Line.tap s i)
    rw [tap1_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap,
      sel_pack3 _ _ _ 1 (by decide)]
    rfl
  · rw [h]
    show (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[2]! =
      Metronome.Line.sel 2 (Metronome.Line.tap s i)
    rw [tap2_bridge s i (absCfg i.cfg) rfl a hpin, Metronome.Line.tap,
      sel_pack3 _ _ _ 2 (by decide)]
    rfl
  · rw [h]
    show (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).beat =
      Metronome.Line.beat s i
    rw [beat_bridge s i (absCfg i.cfg) rfl a hpin]

/-! ## The line step

`step_bridge` assembles the per-register lemmas.  Its three field hypotheses
(`hfirst`, `hfired`, `hsnap`) are the theorems `first_bridge`, `fired_bridge` and
`snap_bridge`; `step_bridge'` is the same statement with those hypotheses
discharged, so the line transition is bridged with only `hcfg`, `PinAgree` and
`hreset`. -/


theorem sc_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).sc =
      Metronome.Line.scNext s i := by
  simp only [Machine.lineNext, absCfg_follow, Metronome.Line.scNext]
  rw [beat_bridge s i (absCfg i.cfg) rfl a hpin,
    accept_bridge s i (absCfg i.cfg) rfl a hpin]
  by_cases hf : i.cfg.follow = true <;> simp [hf, absSt]

theorem sp_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).sp =
      Metronome.Line.spNext s i := by
  simp only [Machine.lineNext, absCfg_follow, Metronome.Line.spNext]
  rw [beat_bridge s i (absCfg i.cfg) rfl a hpin,
    wrap_bridge s i (absCfg i.cfg) rfl a hpin]
  by_cases hf : i.cfg.follow = true <;> simp [hf, absSt]

theorem w_inline_st (s : Metronome.Line.State) (i : Metronome.Line.Input) (st : Machine.LineSt)
    (hst : absSt s = st) (a : PinAbs) (hpin : PinAgree a i) :
    (let pa := a.view.pin (absCfg i.cfg).pina
     let pb := a.view.pin (absCfg i.cfg).pinb
     let w0 := st.w
     let w1 := if (Machine.lineComb (absCfg i.cfg) st a.view i.frz).tap[0]! then setBit w0 0 pa else w0
     let w2 := if (Machine.lineComb (absCfg i.cfg) st a.view i.frz).tap[1]! then
         setBit (setBit w1 1 pa) 3 pb else w1
     if (Machine.lineComb (absCfg i.cfg) st a.view i.frz).tap[2]! then setBit w2 2 pa else w2) =
      Metronome.Line.wNext s i := by
  subst st
  exact w_test s i a hpin

theorem sn_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i)
    (hsnap : (if (absCfg i.cfg).snap == 3 then
        (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).beat
      else (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[(absCfg i.cfg).snap]!) =
        Metronome.Line.snap s i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).sn =
      (if Metronome.Line.snap s i then Metronome.Line.wNext s i else s.sn) := by
  simp only [Machine.lineNext]
  rw [hsnap]
  generalize hst : absSt s = st
  rw [w_inline_st s i st hst a hpin]
  subst st
  simp only [absSt]

theorem rem_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i)
    (hsnap : (if (absCfg i.cfg).snap == 3 then
        (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).beat
      else (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz).tap[(absCfg i.cfg).snap]!) =
        Metronome.Line.snap s i) :
    (Machine.lineNext (absCfg i.cfg) (absSt s)
      (Machine.lineComb (absCfg i.cfg) (absSt s) a.view i.frz) a.view (absIn i) i.frz).rem =
      (if Metronome.Line.snap s i then Metronome.Line.sel (Metronome.Line.cap s).toNat i.cfg.lut1
        else s.rem) := by
  simp only [Machine.lineNext]
  rw [hsnap]
  by_cases hs : Metronome.Line.snap s i = true
  · rw [if_pos hs, if_pos hs, rem_test s i]
  · rw [if_neg hs, if_neg hs]
    simp only [absSt]

theorem lineSt_eq_of_fields (x y : Machine.LineSt)
    (hph : x.ph = y.ph) (hrun : x.run = y.run) (harm : x.arm = y.arm)
    (hren : x.ren = y.ren) (hheld : x.held = y.held) (hfirst : x.first = y.first)
    (hsc : x.sc = y.sc) (hsp : x.sp = y.sp) (hfired : x.fired = y.fired)
    (hw : x.w = y.w) (hsn : x.sn = y.sn) (hrem : x.rem = y.rem)
    (hstaged : x.staged = y.staged) (hcommitted : x.committed = y.committed)
    (htapmiss : x.tapmiss = y.tapmiss) : x = y := by
  cases x
  cases y
  simp_all

theorem step_bridge (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i)
    (hreset : i.resetN = true)
    (hfirst : (Machine.lineNext lc (absSt s)
        (Machine.lineComb lc (absSt s) a.view i.frz) a.view (absIn i) i.frz).first =
      (Metronome.Line.starting s i || (s.first && !Metronome.Line.beat s i)))
    (hfired : (Machine.lineNext lc (absSt s)
        (Machine.lineComb lc (absSt s) a.view i.frz) a.view (absIn i) i.frz).fired =
      (if Metronome.Line.starting s i then Metronome.Line.startBits s i
        else Metronome.Line.firedNext s i))
    (hsnap : (if (absCfg i.cfg).snap == 3 then
        (Machine.lineComb lc (absSt s) a.view i.frz).beat
      else (Machine.lineComb lc (absSt s) a.view i.frz).tap[(absCfg i.cfg).snap]!) =
        Metronome.Line.snap s i) :
    absSt (Metronome.Line.step s i) =
      Machine.lineNext lc (absSt s) (Machine.lineComb lc (absSt s) a.view i.frz) a.view
        (absIn i) i.frz := by
  subst hcfg
  rw [Metronome.Line.step]
  simp only [hreset, ite_true, absSt]
  refine lineSt_eq_of_fields _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case _ =>
    exact (ph_bridge s i a hpin).symm
  case _ =>
    exact (run_test s i a hpin).symm
  case _ =>
    exact (arm_test s i a hpin).symm
  case _ =>
    exact (ren_test s i a hpin).symm
  case _ =>
    exact (held_bridge s i a hpin).symm
  case _ =>
    exact hfirst.symm
  case _ =>
    exact (sc_bridge s i a hpin).symm
  case _ =>
    exact (sp_bridge s i a hpin).symm
  case _ =>
    exact hfired.symm
  case _ =>
    exact (w_test s i a hpin).symm
  case _ =>
    exact (sn_bridge s i a hpin hsnap).symm
  case _ =>
    exact (rem_bridge s i a hpin hsnap).symm
  case _ =>
    exact (stagedNext_test s i).symm
  case _ =>
    exact (committed_test s i a hpin).symm
  case _ =>
    exact (tapmiss_test s i a hpin).symm

/-- `step_bridge` without the three field hypotheses: `FIRST`, `FIRED` and the
snapshot dot product are now proved field equations. -/
theorem step_bridge' (s : Metronome.Line.State) (i : Metronome.Line.Input)
    (lc : Machine.LineCfg) (hcfg : lc = absCfg i.cfg) (a : PinAbs) (hpin : PinAgree a i)
    (hreset : i.resetN = true) :
    absSt (Metronome.Line.step s i) =
      Machine.lineNext lc (absSt s) (Machine.lineComb lc (absSt s) a.view i.frz) a.view
        (absIn i) i.frz := by
  subst hcfg
  exact step_bridge s i (absCfg i.cfg) rfl a hpin hreset
    (first_bridge s i a hpin) (fired_bridge s i a hpin) (snap_bridge s i a hpin)

theorem cap_out (s : Metronome.Line.State) :
    (Metronome.Line.cap s).toNat = b2n (absSt s).rem * 16 + (absSt s).sn.toNat :=
  cap_toNat s

theorem in_sym_out (s : Metronome.Line.State) (i : Metronome.Line.Input) :
    (Metronome.Line.inSym s i).toNat = Machine.inSym (absCfg i.cfg) (absSt s) :=
  inSym_toNat s i

theorem pina_out (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    a.view.pin (absCfg i.cfg).pina = Metronome.Line.pina i :=
  pina_test s i a hpin

theorem pinb_out (s : Metronome.Line.State) (i : Metronome.Line.Input) (a : PinAbs)
    (hpin : PinAgree a i) :
    a.view.pin (absCfg i.cfg).pinb = Metronome.Line.pinb i :=
  pinb_test s i a hpin

theorem seg_out (s : Metronome.Line.State) :
    (Metronome.Line.seg s).toNat = Machine.seg (absSt s) :=
  seg_test s

end Metronome.Bridge.Line
