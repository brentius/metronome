/-
# ChipCut: the RTL configuration mask (`CFG_MASK`) and the latch-bank wiring

This file supplies the three facts the `ChipCut` latch-bank relation needs from
the RTL:

1. **The real mask.** `src/md2_map.vh` (`CFG_MASK`, 3840 bits) gives one mask
   byte per configuration-window offset; `md2_cfg_cells` instantiates a latch on
   exactly the set bits and ties the others to zero.  `cfgMaskList` is that table
   (generated, see `data/raw/lean_chipcut_bank_v4_20261122/gen_bank_mask.py`);
   `cfgMask_partial`/`cfgMaskList_length` tie it back to the RTL inventory
   (480 bytes, 56 partially latched bytes, 2112 latch bits = `CFG_LATCH_BITS`).
2. **Masked configuration decoding.**  Every bit `cfgView` (and `Config.poly`)
   reads is a latched bit, so masking the byte image with `CFG_MASK` does not
   change the decoded configuration: `cfgView_maskImg` / `cfgMask_poly` /
   `cfgView_of_masked`.
3. **The bank view.**  The configuration the RTL decodes from the latch bank's
   outputs is `cfgView` of the machine's image (`cfgView_bankImg`), given the
   latch-image relation.

`MaskedZero` is the power-on/reset condition this makes necessary: the RTL
latches reset to zero, so the machine's configuration image must be cleared in
its implemented bits at reset (see `WIRE_BANK_NOTES.md` §4).
-/

import Metronome

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut.Discharge.BankWire

open Metronome

/-! ## 1. The RTL mask table

`CFG_MASK` is `src/md2_map.vh:121`; bit `8a+b` is "byte `a`, bit `b` has a
latch".  Byte `a` of the window (`0x2000 + a`) is `CFG_MASK[8a +: 8]`, i.e. the
least significant byte is offset 0.  The table is generated from the RTL file by
`gen_bank_mask.py`; the theorems below are the Lean-side checks against the
independently stated inventory (480 bytes, `CFG_LATCH_BITS = 2112`, and the 56
partially latched bytes with their values). -/

/-- `CFG_MASK` bytes, offset `k` of the configuration window
(`CFG_MASK[8k +: 8]`).  Generated from `src/md2_map.vh`. -/
def cfgMaskList : List (BitVec 8) :=
  [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x03, 0xFF, 0x07, 0xFF, 0x0F, 0xFF, 0x0F, 0x00, 0x03, 0xFF, 0x07, 0xFF, 0x0F, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- The published latch inventory: `CFG_LATCH_BITS` = 2112. -/
def cfgLatchBits : Nat := 2112

/-- Mask byte of window offset `k` (0 outside the window). -/
def cfgMaskB (k : Nat) : BitVec 8 := cfgMaskList.getD k 0

/-- Mask byte of window offset `k`, as the byte the latch bank's readers see. -/
def cfgMaskNat (k : Nat) : Nat := (cfgMaskB k).toNat

/-- The elaborated `MASK` parameter of `md2_cfg_cells`. -/
def cfgMaskFin : Fin Bank.BYTES → BitVec 8 := fun k => cfgMaskB k.val

theorem cfgMaskList_length : cfgMaskList.length = Bank.BYTES := by decide

theorem cfgSize_eq : Machine.Util.cfgSize = Bank.BYTES := by decide

/-- The 56 partially latched bytes of `CFG_MASK`, with their values: this is
the RTL inventory `CFG_VALID_*`/`CFG_LATCH_BITS` re-derived from the table. -/
theorem cfgMask_partial :
    List.filter (fun p => p.2 != 0 && p.2 != 0xFF)
        ((List.zipIdx cfgMaskList).map (fun p => (p.2, p.1))) =
      [(17, 0x7F), (19, 0x03), (49, 0x7F), (51, 0x03), (81, 0x7F), (83, 0x03),
       (113, 0x7F), (115, 0x03), (129, 0x3F), (130, 0x3F), (137, 0x3F),
       (138, 0x3F), (145, 0x3F), (146, 0x3F), (153, 0x3F), (154, 0x3F),
       (161, 0x3F), (162, 0x3F), (169, 0x3F), (170, 0x3F), (208, 0x03),
       (210, 0x07), (212, 0x0F), (214, 0x0F), (216, 0x03), (218, 0x07),
       (220, 0x0F), (222, 0x0F), (256, 0x1F), (257, 0x3F), (272, 0x1F),
       (273, 0x3F), (288, 0x1F), (289, 0x3F), (304, 0x1F), (305, 0x3F),
       (320, 0x1F), (321, 0x3F), (336, 0x1F), (337, 0x3F), (352, 0x1F),
       (353, 0x3F), (368, 0x1F), (369, 0x3F), (384, 0x1F), (385, 0x3F),
       (400, 0x1F), (401, 0x3F), (416, 0x1F), (417, 0x3F), (432, 0x1F),
       (433, 0x3F), (448, 0x1F), (449, 0x3F), (464, 0x1F), (465, 0x3F)] := by
  decide

/-- The number of latches the table selects is `CFG_LATCH_BITS`. -/
theorem cfgMask_latchBits :
    cfgMaskList.foldl (fun acc b => acc + ((List.range 8).foldl
      (fun a i => a + (if b.getLsbD i then 1 else 0)) 0)) 0 = cfgLatchBits := by
  decide

theorem cfgMaskB_lt (k : Nat) : cfgMaskNat k < 256 := (cfgMaskB k).isLt

/-- `cfgMaskB` at an in-window index is the table entry. -/
theorem cfgMaskB_eq {k : Nat} (h : k < Bank.BYTES) :
    cfgMaskB k = cfgMaskList[k]'(by rw [cfgMaskList_length]; exact h) := by
  simp only [cfgMaskB]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [cfgMaskList_length]; exact h)]
  rfl

/-! ### The per-block mask patterns

`cfgMaskList` is block-uniform: four LINE blocks of 32 bytes, six THREAD blocks
of 8, two LFSR blocks of 8, two STREAM blocks of 8, and fourteen OUT blocks of
16.  The `*MaskAt` theorems are the `decide` links from the flat table to those
patterns, so the field lemmas below can be stated for a symbolic instance
index. -/

/-- One LINE block's mask bytes (offsets `0x00 .. 0x1F`). -/
def lineMaskP : List (BitVec 8) :=
  [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00]

/-- One THREAD block's mask bytes. -/
def threadMaskP : List (BitVec 8) :=
  [0xFF, 0x3F, 0x3F, 0xFF, 0xFF, 0x00, 0x00, 0x00]

/-- One LFSR block's mask bytes. -/
def lfsrMaskP : List (BitVec 8) := [0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00]

/-- One STREAM block's mask bytes. -/
def streamMaskP : List (BitVec 8) := [0x03, 0xFF, 0x07, 0xFF, 0x0F, 0xFF, 0x0F, 0x00]

/-- One OUT block's mask bytes for `o < 8` (the `OE` latches exist). -/
def outMaskP : List (BitVec 8) :=
  [0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
   0x00, 0x00, 0x00]

/-- One OUT block's mask bytes for `o ≥ 8` (`OUT[8..13].OE` has no latch). -/
def outMaskP8 : List (BitVec 8) :=
  [0x1F, 0x3F, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00]

theorem lineMaskAt (l : Fin 4) (o : Fin 32) :
    cfgMaskB (0x20 * l.val + o.val) = lineMaskP.getD o.val 0 := by
  revert l o; decide

theorem threadMaskAt (t : Fin 6) (o : Fin 8) :
    cfgMaskB (0x80 + 0x8 * t.val + o.val) = threadMaskP.getD o.val 0 := by
  revert t o; decide

theorem lfsrMaskAt (k : Fin 2) (o : Fin 8) :
    cfgMaskB (0xC0 + 0x8 * k.val + o.val) = lfsrMaskP.getD o.val 0 := by
  revert k o; decide

theorem streamMaskAt (k : Fin 2) (o : Fin 8) :
    cfgMaskB (0xD0 + 0x8 * k.val + o.val) = streamMaskP.getD o.val 0 := by
  revert k o; decide

theorem outMaskAt (o : Fin 14) (j : Fin 16) (h : o.val < 8) :
    cfgMaskB (0x100 + 0x10 * o.val + j.val) = outMaskP.getD j.val 0 := by
  revert o j h; decide

theorem outMaskAt8 (o : Fin 14) (j : Fin 16) (h : 8 ≤ o.val) :
    cfgMaskB (0x100 + 0x10 * o.val + j.val) = outMaskP8.getD j.val 0 := by
  revert o j h; decide

open Machine.Util Machine.Tables

/-- Byte image presented by the enabled latch outputs. -/
def maskImg (c : Machine.Config) : Machine.Config :=
  ⟨⟨Array.ofFn fun k : Fin Bank.BYTES =>
    UInt8.ofNat (BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k).toNat⟩⟩

/-- Relate a configuration supplied to the decoder to the masked image. -/
def MaskedImage (d c : Machine.Config) : Prop :=
  ∀ k : Fin Bank.BYTES,
    bget d.img k.val = bget c.img k.val &&& cfgMaskNat k.val

private theorem bget_lt (a : ByteArray) (k : Nat) : bget a k < 256 :=
  (a.get! k).toBitVec.isLt

private theorem bget_ofFn (f : Fin Bank.BYTES → UInt8) (k : Fin Bank.BYTES) :
    bget ⟨Array.ofFn f⟩ k.val = (f k).toNat := by
  simp [bget, ByteArray.get!, getElem!_pos, k.isLt]

theorem maskImg_masked (c : Machine.Config) : MaskedImage (maskImg c) c := by
  intro k
  rw [maskImg, bget_ofFn]
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bget_lt c.img k.val)]
  rfl

private theorem cfgLE2 (c : Machine.Config) (a : Nat) :
    cfgLE c a 2 = bget c.img (a - LINE_BASE + 1) * 256 + bget c.img (a - LINE_BASE) := by
  simp only [cfgLE, bgetLE, show List.range 2 = [0, 1] by rfl,
    List.foldr_cons, List.foldr_nil, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

private theorem cfgLE4 (c : Machine.Config) (a : Nat) :
    cfgLE c a 4 =
      ((bget c.img (a - LINE_BASE + 3) * 256 + bget c.img (a - LINE_BASE + 2)) * 256 +
        bget c.img (a - LINE_BASE + 1)) * 256 + bget c.img (a - LINE_BASE) := by
  simp only [cfgLE, bgetLE, show List.range 4 = [0, 1, 2, 3] by rfl,
    List.foldr_cons, List.foldr_nil, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

private theorem fullByte (a : ByteArray) (k : Nat) :
    bget a k &&& 255 = bget a k := by
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) (bget_lt a k)

private theorem cfgByte_rel (c : Machine.Config) (b j : Nat) :
    cfgByte c (LINE_BASE + b + j) = bget c.img (b + j) := by
  simp [cfgByte, Nat.add_assoc]

private theorem cfgLE2_rel (c : Machine.Config) (b j : Nat) :
    cfgLE c (LINE_BASE + b + j) 2 =
      bget c.img (b + (j + 1)) * 256 + bget c.img (b + j) := by
  simp [cfgLE2, Nat.add_assoc]

private theorem cfgLE4_rel (c : Machine.Config) (b j : Nat) :
    cfgLE c (LINE_BASE + b + j) 4 =
      ((bget c.img (b + (j + 3)) * 256 + bget c.img (b + (j + 2))) * 256 +
        bget c.img (b + (j + 1))) * 256 + bget c.img (b + j) := by
  simp [cfgLE4, Nat.add_assoc]

private theorem maskedBlock {d c : Machine.Config} {b n : Nat}
    (h : MaskedImage d c) (pattern : List (BitVec 8))
    (hm : ∀ j : Fin n, cfgMaskB (b + j.val) = pattern.getD j.val 0)
    (hb : b + n ≤ Bank.BYTES) (j : Nat) (hj : j < n) :
    bget d.img (b + j) = bget c.img (b + j) &&& (pattern.getD j 0).toNat := by
  have he := h ⟨b + j, by omega⟩
  change bget d.img (b + j) = bget c.img (b + j) &&& (cfgMaskB (b + j)).toNat at he
  rw [hm ⟨j, hj⟩] at he
  exact he

local macro "solveDecoder" : tactic =>
  `(tactic| first | rfl | (
    congr 1 <;> first | rfl | (
      simp only [nbits, nbit, Nat.shiftRight_eq_div_pow,
        show ∀ x : Nat, x &&& 3 = x % 4 from fun x => Nat.and_two_pow_sub_one_eq_mod x 2,
        show ∀ x : Nat, x &&& 7 = x % 8 from fun x => Nat.and_two_pow_sub_one_eq_mod x 3,
        show ∀ x : Nat, x &&& 15 = x % 16 from fun x => Nat.and_two_pow_sub_one_eq_mod x 4,
        show ∀ x : Nat, x &&& 31 = x % 32 from fun x => Nat.and_two_pow_sub_one_eq_mod x 5,
        show ∀ x : Nat, x &&& 63 = x % 64 from fun x => Nat.and_two_pow_sub_one_eq_mod x 6,
        show ∀ x : Nat, x &&& 127 = x % 128 from fun x => Nat.and_two_pow_sub_one_eq_mod x 7]
      first | omega | congr 1 <;> omega)))

private theorem line_masked {d c : Machine.Config} (h : MaskedImage d c) (i : Fin 4) :
    Machine.Config.line d i.val = Machine.Config.line c i.val := by
  let b := 32 * i.val
  have hbase : LINE_BASE + STRIDE_LINE * i.val = LINE_BASE + b := by
    rfl
  have hb := maskedBlock h (b := b) (n := 32) lineMaskP
    (fun j => lineMaskAt i j) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
  unfold Machine.Config.line
  rw [hbase]
  simp (disch := decide) only [LINE_INC, LINE_MOD, LINE_T0, LINE_T1, LINE_T2,
    LINE_PRE, LINE_WLO, LINE_WHI, LINE_EDGE, LINE_T0EDGE, LINE_PINS, LINE_SNAP, LINE_LUT0, LINE_LUT1, LINE_HOLD,
    cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, lineMaskP, Fin.val_mk,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Option.getD, BitVec.reduceToNat, fullByte]
  all_goals solveDecoder

private theorem thread_masked {d c : Machine.Config} (h : MaskedImage d c) (i : Fin 6) :
    Machine.Config.thread d i.val = Machine.Config.thread c i.val := by
  let b := 0x80 + 8 * i.val
  have hbase : THREAD_BASE + STRIDE_THREAD * i.val = LINE_BASE + b := by
    simp [b, THREAD_BASE, STRIDE_THREAD, LINE_BASE]
    omega
  have hb := maskedBlock h (b := b) (n := 8) threadMaskP
    (fun j => threadMaskAt i j) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
  unfold Machine.Config.thread
  rw [hbase]
  simp (disch := decide) only [THREAD_CFG, THREAD_W0C, THREAD_W1C, THREAD_W0H, THREAD_W1H,
    cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, threadMaskP, Fin.val_mk,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Option.getD, BitVec.reduceToNat, fullByte]
  all_goals solveDecoder

private theorem maskedWord (hi lo w : Nat) (h : 8 ≤ w) :
    nbits ((hi &&& (2 ^ (w - 8) - 1)) * 256 + lo) 0 w =
      nbits (hi * 256 + lo) 0 w := by
  simp only [nbits, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod]
  have hw : 2 ^ w = 2 ^ (w - 8) * 256 := by
    simpa only [show w - 8 + 8 = w by omega] using (Nat.pow_add 2 (w - 8) 8)
  rw [hw, ← Nat.mul_mod_mul_right 256 hi (2 ^ (w - 8)), Nat.mod_add_mod]

private theorem streamModeBit (x i : Nat) (h : i < 2) :
    nbit (x &&& 3) i = nbit x i := by
  have he : ((x % 4) >>> i) % 2 = (x >>> i) % 2 := by
    simp only [Nat.shiftRight_eq_div_pow]
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> omega
  rw [show x &&& 3 = x % 4 from Nat.and_two_pow_sub_one_eq_mod x 2]
  exact congrArg (fun y : Nat => y == 1) he

private theorem stream_masked {d c : Machine.Config} (h : MaskedImage d c) (i : Fin 2) :
    Machine.Config.stream d i.val = Machine.Config.stream c i.val := by
  let b := 0xD0 + 8 * i.val
  have hbase : STREAM_BASE + STRIDE_STREAM * i.val = LINE_BASE + b := by
    simp [b, STREAM_BASE, STRIDE_STREAM, LINE_BASE]
    omega
  have hb := maskedBlock h (b := b) (n := 8) streamMaskP
    (fun j => streamMaskAt i j) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
  unfold Machine.Config.stream
  rw [hbase]
  simp (disch := decide) only [STREAM_MODE, STREAM_START, STREAM_LEN, STREAM_MARK, STREAM_ADDR_BITS, STREAM_LEN_BITS,
    cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, streamMaskP, Fin.val_mk,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Option.getD, BitVec.reduceToNat, fullByte]
  have start (hi lo : Nat) :
      nbits ((hi &&& 7) * 256 + lo) 0 11 = nbits (hi * 256 + lo) 0 11 :=
    maskedWord hi lo 11 (by decide)
  have len (hi lo : Nat) :
      nbits ((hi &&& 15) * 256 + lo) 0 12 = nbits (hi * 256 + lo) 0 12 :=
    maskedWord hi lo 12 (by decide)
  rw [streamModeBit (bget c.img (b + 0)) 0 (by decide),
    streamModeBit (bget c.img (b + 0)) 1 (by decide),
    start (bget c.img (b + 2)) (bget c.img (b + 1)),
    len (bget c.img (b + 4)) (bget c.img (b + 3)),
    len (bget c.img (b + 6)) (bget c.img (b + 5))]

private theorem out_masked {d c : Machine.Config} (h : MaskedImage d c) (i : Fin 14) :
    Machine.Config.out d i.val = Machine.Config.out c i.val := by
  let b := 0x100 + 16 * i.val
  have hbase : OUT_BASE + STRIDE_OUT * i.val = LINE_BASE + b := by
    simp [b, OUT_BASE, STRIDE_OUT, LINE_BASE]
    omega
  by_cases hlo : i.val < 8
  · have hb := maskedBlock h (b := b) (n := 16) outMaskP
      (fun j => outMaskAt i j hlo) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
    unfold Machine.Config.out
    rw [hbase]
    simp (disch := decide) only [OUT_BIND, OUT_SEL, OUT_LUT, OUT_OE, N_OE_PINS,
      cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, outMaskP, Fin.val_mk,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
      Option.getD, BitVec.reduceToNat, fullByte, hlo, if_pos]
    all_goals solveDecoder
  · have hb := maskedBlock h (b := b) (n := 16) outMaskP8
      (fun j => outMaskAt8 i j (by omega)) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
    unfold Machine.Config.out
    rw [hbase]
    simp (disch := decide) only [OUT_BIND, OUT_SEL, OUT_LUT, OUT_OE, N_OE_PINS,
      cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, outMaskP8, Fin.val_mk,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
      Option.getD, BitVec.reduceToNat, fullByte, hlo, if_neg]
    all_goals solveDecoder

private theorem poly_masked {d c : Machine.Config} (h : MaskedImage d c) (i : Fin 2) :
    Machine.Config.poly d i.val = Machine.Config.poly c i.val := by
  let b := 0xC0 + 8 * i.val
  have hbase : LFSR_BASE + STRIDE_LFSR * i.val = LINE_BASE + b := by
    simp [b, LFSR_BASE, STRIDE_LFSR, LINE_BASE]
    omega
  have hb := maskedBlock h (b := b) (n := 8) lfsrMaskP
    (fun j => lfsrMaskAt i j) (by dsimp [b, Bank.BYTES]; have := i.isLt; omega)
  unfold Machine.Config.poly
  rw [hbase]
  simp (disch := decide) only [LFSR_POLY,
    cfgByte_rel, cfgLE2_rel, cfgLE4_rel, hb, lfsrMaskP, Fin.val_mk,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Option.getD, BitVec.reduceToNat, fullByte]

theorem cfgView_of_masked {d c : Machine.Config} (h : MaskedImage d c) :
    Machine.cfgView d = Machine.cfgView c := by
  unfold Machine.cfgView
  rw [show (fun i : Fin 4 => d.line i.val) = (fun i => c.line i.val) from funext (line_masked h),
    show (fun i : Fin 6 => d.thread i.val) = (fun i => c.thread i.val) from funext (thread_masked h),
    show (fun i : Fin 14 => d.out i.val) = (fun i => c.out i.val) from funext (out_masked h),
    show (fun i : Fin 2 => d.stream i.val) = (fun i => c.stream i.val) from funext (stream_masked h)]

theorem cfgView_maskImg (c : Machine.Config) :
    Machine.cfgView (maskImg c) = Machine.cfgView c :=
  cfgView_of_masked (maskImg_masked c)

theorem cfgMask_poly (c : Machine.Config) (i : Fin 2) :
    (maskImg c).poly i.val = c.poly i.val :=
  poly_masked (maskImg_masked c) i

/-- Reset latches can represent exactly the images with zero implemented bits. -/
def MaskedZero (c : Machine.Config) : Prop :=
  ∀ k : Fin Bank.BYTES,
    BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k = 0

theorem maskedZero_zero : MaskedZero Machine.Config.zero := by
  intro k
  change BitVec.ofNat 8 ((Array.replicate cfgSize (0 : UInt8))[k.val]!).toNat &&& cfgMaskFin k = 0
  have hk : k.val < (Array.replicate cfgSize (0 : UInt8)).size := by
    simpa only [Array.size_replicate, cfgSize_eq] using k.isLt
  rw [getElem!_pos (Array.replicate cfgSize (0 : UInt8)) k.val hk, Array.getElem_replicate]
  exact BitVec.zero_and

/-- The observable byte image of the bank, including zeros on missing latches. -/
def bankImg (b : Bank.State) : Machine.Config :=
  ⟨⟨Array.ofFn fun k => UInt8.ofNat (Bank.read b k).toNat⟩⟩

theorem bankImg_masked (b : Bank.State) (c : Machine.Config)
    (h : ∀ k, Bank.read b k = BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k) :
    MaskedImage (bankImg b) c := by
  intro k
  rw [bankImg, bget_ofFn, h k]
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bget_lt c.img k.val)]
  rfl

theorem cfgView_bankImg (b : Bank.State) (c : Machine.Config)
    (h : ∀ k, Bank.read b k = BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k) :
    Machine.cfgView (bankImg b) = Machine.cfgView c :=
  cfgView_of_masked (bankImg_masked b c h)

theorem cfgPoly_bankImg (b : Bank.State) (c : Machine.Config)
    (h : ∀ k, Bank.read b k = BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k)
    (i : Fin 2) : (bankImg b).poly i.val = c.poly i.val :=
  poly_masked (bankImg_masked b c h) i

set_option maxHeartbeats 8000000 in
/-- Every implemented byte is an address accepted by the machine decoder. -/
theorem cfgMask_live_cfg (k : Fin Bank.BYTES) :
    cfgMaskFin k ≠ 0 → Machine.Config.isCfgAddr (LINE_BASE + k.val) = true := by
  revert k
  decide +kernel

end Metronome.ChipCut.Discharge.BankWire
