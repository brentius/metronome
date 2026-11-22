import Metronome.Bank
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: e8565711b8db50dacf60b3a34e468b64902578de945216a51eba4f035724ddde
-- Bank: the `md2_cfg_cells` instance `tt_um_brentius_metronome.u_cfg`. The mask bytes come
-- from its elaborated `MASK` parameter; the enable cones come from the GATE net
-- of every `g_byte[k].g_used.u_cg` cell, with `we1` and `addr1` bound free.
-- 284 of 480 mask bytes are non-zero (2112 latch
-- bits), so the family has 284 gates and 196 holes.
--
-- The proofs below close the family statement for all 480 offsets without
-- a case split: one `bv_decide` per live cone (`enable_k_spec`), one induction
-- over the gate list (`any_enable_spec`) and one kernel reduction that ties the
-- gate offsets to the elaborated mask bytes (`liveAt_addrOf`).

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000

namespace Metronome.BankEquivalence

/-- Window offsets in the elaborated bank. -/
abbrev cfgBytes : Nat := 480

/-- The elaborated `u_cfg` `MASK` parameter, one byte per offset. -/
abbrev bankMask : BitVec 3840 := 0x0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F0000000000000000000000000000000000000000000000000000000000000000000FFF0FFF07FF03000FFF0FFF07FF0300000000FFFFFFFF00000000FFFFFFFF00000000000000000000000000000000000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

/-- Bit `k` is set iff `MASK` byte `k` is non-zero: the offsets that own latches
and a clock gate. Same vector as the address-decode cut's `liveBytes`. -/
abbrev liveBytes : BitVec cfgBytes := 0x00F300F300F300F300F300F30FF30FF30FF30FF30FF30FF30FF30FF3000000007F7F0F0F00001F1F1F1F1F1F1FFFFFFF1FFFFFFF1FFFFFFF1FFFFFFF

/-- The MASK byte of offset `k`, read from the elaborated parameter. -/
def paramMask (k : Fin cfgBytes) : BitVec 8 := (bankMask >>> (8 * k.val)).truncate 8

/-- The MASK byte of offset `k` is non-zero, so the byte owns latches. -/
def paramLive (k : Fin cfgBytes) : Bool := paramMask k != 0

/-- One live byte of the elaborated bank: its window offset, the enable cone of
its `g_byte[k].g_used.u_cg` clock gate as a function of the staged write word,
and the per-byte proof that the cone is that offset's comparison. -/
structure Gate where
  /-- The window offset this gate selects. -/
  off : Nat
  /-- The offset fits the nine-bit bank address. -/
  off_lt : off < 512
  /-- The extracted gate enable, from the GATE net of `u_cg`. -/
  fn : Bool → BitVec 9 → Bool
  /-- The extracted cone equals `we1 && addr1 == off` at every address. -/
  spec : ∀ we1 addr1, fn we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 off))

/-- Gate enable of byte 0, extracted from `g_byte[0].g_used.u_cg`. -/
def enable0 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e0_0 := (addr1 == (0 : BitVec 9))
  let e0_1 := we1 && e0_0
  e0_1

/-- The extracted gate of byte 0 equals `we1 && addr1 == 0` at every one of
the 512 addresses, for either strobe value. -/
theorem enable0_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable0 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 0)) := by
  unfold enable0
  bv_decide

/-- Gate enable of byte 1, extracted from `g_byte[1].g_used.u_cg`. -/
def enable1 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e1_0 := (addr1 == (0 : BitVec 9))
  let e1_1 := we1 && e1_0
  e1_1

/-- The extracted gate of byte 1 equals `we1 && addr1 == 1` at every one of
the 512 addresses, for either strobe value. -/
theorem enable1_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable1 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 1)) := by
  unfold enable1
  bv_decide

/-- Gate enable of byte 2, extracted from `g_byte[2].g_used.u_cg`. -/
def enable2 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e2_0 := (addr1 == (2 : BitVec 9))
  let e2_1 := we1 && e2_0
  e2_1

/-- The extracted gate of byte 2 equals `we1 && addr1 == 2` at every one of
the 512 addresses, for either strobe value. -/
theorem enable2_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable2 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 2)) := by
  unfold enable2
  bv_decide

/-- Gate enable of byte 3, extracted from `g_byte[3].g_used.u_cg`. -/
def enable3 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e3_0 := (addr1 == (3 : BitVec 9))
  let e3_1 := we1 && e3_0
  e3_1

/-- The extracted gate of byte 3 equals `we1 && addr1 == 3` at every one of
the 512 addresses, for either strobe value. -/
theorem enable3_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable3 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 3)) := by
  unfold enable3
  bv_decide

/-- Gate enable of byte 4, extracted from `g_byte[4].g_used.u_cg`. -/
def enable4 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e4_0 := (addr1 == (4 : BitVec 9))
  let e4_1 := we1 && e4_0
  e4_1

/-- The extracted gate of byte 4 equals `we1 && addr1 == 4` at every one of
the 512 addresses, for either strobe value. -/
theorem enable4_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable4 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 4)) := by
  unfold enable4
  bv_decide

/-- Gate enable of byte 5, extracted from `g_byte[5].g_used.u_cg`. -/
def enable5 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e5_0 := (addr1 == (5 : BitVec 9))
  let e5_1 := we1 && e5_0
  e5_1

/-- The extracted gate of byte 5 equals `we1 && addr1 == 5` at every one of
the 512 addresses, for either strobe value. -/
theorem enable5_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable5 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 5)) := by
  unfold enable5
  bv_decide

/-- Gate enable of byte 6, extracted from `g_byte[6].g_used.u_cg`. -/
def enable6 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e6_0 := (addr1 == (6 : BitVec 9))
  let e6_1 := we1 && e6_0
  e6_1

/-- The extracted gate of byte 6 equals `we1 && addr1 == 6` at every one of
the 512 addresses, for either strobe value. -/
theorem enable6_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable6 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 6)) := by
  unfold enable6
  bv_decide

/-- Gate enable of byte 7, extracted from `g_byte[7].g_used.u_cg`. -/
def enable7 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e7_0 := (addr1 == (7 : BitVec 9))
  let e7_1 := we1 && e7_0
  e7_1

/-- The extracted gate of byte 7 equals `we1 && addr1 == 7` at every one of
the 512 addresses, for either strobe value. -/
theorem enable7_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable7 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 7)) := by
  unfold enable7
  bv_decide

/-- Gate enable of byte 8, extracted from `g_byte[8].g_used.u_cg`. -/
def enable8 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e8_0 := (addr1 == (8 : BitVec 9))
  let e8_1 := we1 && e8_0
  e8_1

/-- The extracted gate of byte 8 equals `we1 && addr1 == 8` at every one of
the 512 addresses, for either strobe value. -/
theorem enable8_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable8 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 8)) := by
  unfold enable8
  bv_decide

/-- Gate enable of byte 9, extracted from `g_byte[9].g_used.u_cg`. -/
def enable9 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e9_0 := (addr1 == (9 : BitVec 9))
  let e9_1 := we1 && e9_0
  e9_1

/-- The extracted gate of byte 9 equals `we1 && addr1 == 9` at every one of
the 512 addresses, for either strobe value. -/
theorem enable9_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable9 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 9)) := by
  unfold enable9
  bv_decide

/-- Gate enable of byte 10, extracted from `g_byte[10].g_used.u_cg`. -/
def enable10 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e10_0 := (addr1 == (10 : BitVec 9))
  let e10_1 := we1 && e10_0
  e10_1

/-- The extracted gate of byte 10 equals `we1 && addr1 == 10` at every one of
the 512 addresses, for either strobe value. -/
theorem enable10_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable10 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 10)) := by
  unfold enable10
  bv_decide

/-- Gate enable of byte 11, extracted from `g_byte[11].g_used.u_cg`. -/
def enable11 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e11_0 := (addr1 == (11 : BitVec 9))
  let e11_1 := we1 && e11_0
  e11_1

/-- The extracted gate of byte 11 equals `we1 && addr1 == 11` at every one of
the 512 addresses, for either strobe value. -/
theorem enable11_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable11 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 11)) := by
  unfold enable11
  bv_decide

/-- Gate enable of byte 12, extracted from `g_byte[12].g_used.u_cg`. -/
def enable12 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e12_0 := (addr1 == (12 : BitVec 9))
  let e12_1 := we1 && e12_0
  e12_1

/-- The extracted gate of byte 12 equals `we1 && addr1 == 12` at every one of
the 512 addresses, for either strobe value. -/
theorem enable12_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable12 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 12)) := by
  unfold enable12
  bv_decide

/-- Gate enable of byte 13, extracted from `g_byte[13].g_used.u_cg`. -/
def enable13 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e13_0 := (addr1 == (13 : BitVec 9))
  let e13_1 := we1 && e13_0
  e13_1

/-- The extracted gate of byte 13 equals `we1 && addr1 == 13` at every one of
the 512 addresses, for either strobe value. -/
theorem enable13_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable13 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 13)) := by
  unfold enable13
  bv_decide

/-- Gate enable of byte 14, extracted from `g_byte[14].g_used.u_cg`. -/
def enable14 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e14_0 := (addr1 == (14 : BitVec 9))
  let e14_1 := we1 && e14_0
  e14_1

/-- The extracted gate of byte 14 equals `we1 && addr1 == 14` at every one of
the 512 addresses, for either strobe value. -/
theorem enable14_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable14 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 14)) := by
  unfold enable14
  bv_decide

/-- Gate enable of byte 15, extracted from `g_byte[15].g_used.u_cg`. -/
def enable15 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e15_0 := (addr1 == (15 : BitVec 9))
  let e15_1 := we1 && e15_0
  e15_1

/-- The extracted gate of byte 15 equals `we1 && addr1 == 15` at every one of
the 512 addresses, for either strobe value. -/
theorem enable15_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable15 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 15)) := by
  unfold enable15
  bv_decide

/-- Gate enable of byte 16, extracted from `g_byte[16].g_used.u_cg`. -/
def enable16 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e16_0 := (addr1 == (16 : BitVec 9))
  let e16_1 := we1 && e16_0
  e16_1

/-- The extracted gate of byte 16 equals `we1 && addr1 == 16` at every one of
the 512 addresses, for either strobe value. -/
theorem enable16_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable16 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 16)) := by
  unfold enable16
  bv_decide

/-- Gate enable of byte 17, extracted from `g_byte[17].g_used.u_cg`. -/
def enable17 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e17_0 := (addr1 == (17 : BitVec 9))
  let e17_1 := we1 && e17_0
  e17_1

/-- The extracted gate of byte 17 equals `we1 && addr1 == 17` at every one of
the 512 addresses, for either strobe value. -/
theorem enable17_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable17 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 17)) := by
  unfold enable17
  bv_decide

/-- Gate enable of byte 18, extracted from `g_byte[18].g_used.u_cg`. -/
def enable18 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e18_0 := (addr1 == (18 : BitVec 9))
  let e18_1 := we1 && e18_0
  e18_1

/-- The extracted gate of byte 18 equals `we1 && addr1 == 18` at every one of
the 512 addresses, for either strobe value. -/
theorem enable18_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable18 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 18)) := by
  unfold enable18
  bv_decide

/-- Gate enable of byte 19, extracted from `g_byte[19].g_used.u_cg`. -/
def enable19 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e19_0 := (addr1 == (19 : BitVec 9))
  let e19_1 := we1 && e19_0
  e19_1

/-- The extracted gate of byte 19 equals `we1 && addr1 == 19` at every one of
the 512 addresses, for either strobe value. -/
theorem enable19_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable19 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 19)) := by
  unfold enable19
  bv_decide

/-- Gate enable of byte 20, extracted from `g_byte[20].g_used.u_cg`. -/
def enable20 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e20_0 := (addr1 == (20 : BitVec 9))
  let e20_1 := we1 && e20_0
  e20_1

/-- The extracted gate of byte 20 equals `we1 && addr1 == 20` at every one of
the 512 addresses, for either strobe value. -/
theorem enable20_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable20 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 20)) := by
  unfold enable20
  bv_decide

/-- Gate enable of byte 21, extracted from `g_byte[21].g_used.u_cg`. -/
def enable21 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e21_0 := (addr1 == (21 : BitVec 9))
  let e21_1 := we1 && e21_0
  e21_1

/-- The extracted gate of byte 21 equals `we1 && addr1 == 21` at every one of
the 512 addresses, for either strobe value. -/
theorem enable21_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable21 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 21)) := by
  unfold enable21
  bv_decide

/-- Gate enable of byte 22, extracted from `g_byte[22].g_used.u_cg`. -/
def enable22 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e22_0 := (addr1 == (22 : BitVec 9))
  let e22_1 := we1 && e22_0
  e22_1

/-- The extracted gate of byte 22 equals `we1 && addr1 == 22` at every one of
the 512 addresses, for either strobe value. -/
theorem enable22_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable22 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 22)) := by
  unfold enable22
  bv_decide

/-- Gate enable of byte 23, extracted from `g_byte[23].g_used.u_cg`. -/
def enable23 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e23_0 := (addr1 == (23 : BitVec 9))
  let e23_1 := we1 && e23_0
  e23_1

/-- The extracted gate of byte 23 equals `we1 && addr1 == 23` at every one of
the 512 addresses, for either strobe value. -/
theorem enable23_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable23 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 23)) := by
  unfold enable23
  bv_decide

/-- Gate enable of byte 24, extracted from `g_byte[24].g_used.u_cg`. -/
def enable24 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e24_0 := (addr1 == (24 : BitVec 9))
  let e24_1 := we1 && e24_0
  e24_1

/-- The extracted gate of byte 24 equals `we1 && addr1 == 24` at every one of
the 512 addresses, for either strobe value. -/
theorem enable24_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable24 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 24)) := by
  unfold enable24
  bv_decide

/-- Gate enable of byte 25, extracted from `g_byte[25].g_used.u_cg`. -/
def enable25 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e25_0 := (addr1 == (25 : BitVec 9))
  let e25_1 := we1 && e25_0
  e25_1

/-- The extracted gate of byte 25 equals `we1 && addr1 == 25` at every one of
the 512 addresses, for either strobe value. -/
theorem enable25_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable25 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 25)) := by
  unfold enable25
  bv_decide

/-- Gate enable of byte 26, extracted from `g_byte[26].g_used.u_cg`. -/
def enable26 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e26_0 := (addr1 == (26 : BitVec 9))
  let e26_1 := we1 && e26_0
  e26_1

/-- The extracted gate of byte 26 equals `we1 && addr1 == 26` at every one of
the 512 addresses, for either strobe value. -/
theorem enable26_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable26 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 26)) := by
  unfold enable26
  bv_decide

/-- Gate enable of byte 27, extracted from `g_byte[27].g_used.u_cg`. -/
def enable27 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e27_0 := (addr1 == (27 : BitVec 9))
  let e27_1 := we1 && e27_0
  e27_1

/-- The extracted gate of byte 27 equals `we1 && addr1 == 27` at every one of
the 512 addresses, for either strobe value. -/
theorem enable27_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable27 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 27)) := by
  unfold enable27
  bv_decide

/-- Gate enable of byte 28, extracted from `g_byte[28].g_used.u_cg`. -/
def enable28 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e28_0 := (addr1 == (28 : BitVec 9))
  let e28_1 := we1 && e28_0
  e28_1

/-- The extracted gate of byte 28 equals `we1 && addr1 == 28` at every one of
the 512 addresses, for either strobe value. -/
theorem enable28_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable28 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 28)) := by
  unfold enable28
  bv_decide

/-- Gate enable of byte 32, extracted from `g_byte[32].g_used.u_cg`. -/
def enable32 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e32_0 := (addr1 == (32 : BitVec 9))
  let e32_1 := we1 && e32_0
  e32_1

/-- The extracted gate of byte 32 equals `we1 && addr1 == 32` at every one of
the 512 addresses, for either strobe value. -/
theorem enable32_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable32 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 32)) := by
  unfold enable32
  bv_decide

/-- Gate enable of byte 33, extracted from `g_byte[33].g_used.u_cg`. -/
def enable33 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e33_0 := (addr1 == (33 : BitVec 9))
  let e33_1 := we1 && e33_0
  e33_1

/-- The extracted gate of byte 33 equals `we1 && addr1 == 33` at every one of
the 512 addresses, for either strobe value. -/
theorem enable33_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable33 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 33)) := by
  unfold enable33
  bv_decide

/-- Gate enable of byte 34, extracted from `g_byte[34].g_used.u_cg`. -/
def enable34 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e34_0 := (addr1 == (34 : BitVec 9))
  let e34_1 := we1 && e34_0
  e34_1

/-- The extracted gate of byte 34 equals `we1 && addr1 == 34` at every one of
the 512 addresses, for either strobe value. -/
theorem enable34_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable34 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 34)) := by
  unfold enable34
  bv_decide

/-- Gate enable of byte 35, extracted from `g_byte[35].g_used.u_cg`. -/
def enable35 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e35_0 := (addr1 == (35 : BitVec 9))
  let e35_1 := we1 && e35_0
  e35_1

/-- The extracted gate of byte 35 equals `we1 && addr1 == 35` at every one of
the 512 addresses, for either strobe value. -/
theorem enable35_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable35 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 35)) := by
  unfold enable35
  bv_decide

/-- Gate enable of byte 36, extracted from `g_byte[36].g_used.u_cg`. -/
def enable36 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e36_0 := (addr1 == (36 : BitVec 9))
  let e36_1 := we1 && e36_0
  e36_1

/-- The extracted gate of byte 36 equals `we1 && addr1 == 36` at every one of
the 512 addresses, for either strobe value. -/
theorem enable36_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable36 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 36)) := by
  unfold enable36
  bv_decide

/-- Gate enable of byte 37, extracted from `g_byte[37].g_used.u_cg`. -/
def enable37 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e37_0 := (addr1 == (37 : BitVec 9))
  let e37_1 := we1 && e37_0
  e37_1

/-- The extracted gate of byte 37 equals `we1 && addr1 == 37` at every one of
the 512 addresses, for either strobe value. -/
theorem enable37_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable37 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 37)) := by
  unfold enable37
  bv_decide

/-- Gate enable of byte 38, extracted from `g_byte[38].g_used.u_cg`. -/
def enable38 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e38_0 := (addr1 == (38 : BitVec 9))
  let e38_1 := we1 && e38_0
  e38_1

/-- The extracted gate of byte 38 equals `we1 && addr1 == 38` at every one of
the 512 addresses, for either strobe value. -/
theorem enable38_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable38 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 38)) := by
  unfold enable38
  bv_decide

/-- Gate enable of byte 39, extracted from `g_byte[39].g_used.u_cg`. -/
def enable39 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e39_0 := (addr1 == (39 : BitVec 9))
  let e39_1 := we1 && e39_0
  e39_1

/-- The extracted gate of byte 39 equals `we1 && addr1 == 39` at every one of
the 512 addresses, for either strobe value. -/
theorem enable39_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable39 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 39)) := by
  unfold enable39
  bv_decide

/-- Gate enable of byte 40, extracted from `g_byte[40].g_used.u_cg`. -/
def enable40 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e40_0 := (addr1 == (40 : BitVec 9))
  let e40_1 := we1 && e40_0
  e40_1

/-- The extracted gate of byte 40 equals `we1 && addr1 == 40` at every one of
the 512 addresses, for either strobe value. -/
theorem enable40_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable40 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 40)) := by
  unfold enable40
  bv_decide

/-- Gate enable of byte 41, extracted from `g_byte[41].g_used.u_cg`. -/
def enable41 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e41_0 := (addr1 == (41 : BitVec 9))
  let e41_1 := we1 && e41_0
  e41_1

/-- The extracted gate of byte 41 equals `we1 && addr1 == 41` at every one of
the 512 addresses, for either strobe value. -/
theorem enable41_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable41 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 41)) := by
  unfold enable41
  bv_decide

/-- Gate enable of byte 42, extracted from `g_byte[42].g_used.u_cg`. -/
def enable42 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e42_0 := (addr1 == (42 : BitVec 9))
  let e42_1 := we1 && e42_0
  e42_1

/-- The extracted gate of byte 42 equals `we1 && addr1 == 42` at every one of
the 512 addresses, for either strobe value. -/
theorem enable42_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable42 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 42)) := by
  unfold enable42
  bv_decide

/-- Gate enable of byte 43, extracted from `g_byte[43].g_used.u_cg`. -/
def enable43 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e43_0 := (addr1 == (43 : BitVec 9))
  let e43_1 := we1 && e43_0
  e43_1

/-- The extracted gate of byte 43 equals `we1 && addr1 == 43` at every one of
the 512 addresses, for either strobe value. -/
theorem enable43_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable43 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 43)) := by
  unfold enable43
  bv_decide

/-- Gate enable of byte 44, extracted from `g_byte[44].g_used.u_cg`. -/
def enable44 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e44_0 := (addr1 == (44 : BitVec 9))
  let e44_1 := we1 && e44_0
  e44_1

/-- The extracted gate of byte 44 equals `we1 && addr1 == 44` at every one of
the 512 addresses, for either strobe value. -/
theorem enable44_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable44 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 44)) := by
  unfold enable44
  bv_decide

/-- Gate enable of byte 45, extracted from `g_byte[45].g_used.u_cg`. -/
def enable45 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e45_0 := (addr1 == (45 : BitVec 9))
  let e45_1 := we1 && e45_0
  e45_1

/-- The extracted gate of byte 45 equals `we1 && addr1 == 45` at every one of
the 512 addresses, for either strobe value. -/
theorem enable45_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable45 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 45)) := by
  unfold enable45
  bv_decide

/-- Gate enable of byte 46, extracted from `g_byte[46].g_used.u_cg`. -/
def enable46 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e46_0 := (addr1 == (46 : BitVec 9))
  let e46_1 := we1 && e46_0
  e46_1

/-- The extracted gate of byte 46 equals `we1 && addr1 == 46` at every one of
the 512 addresses, for either strobe value. -/
theorem enable46_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable46 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 46)) := by
  unfold enable46
  bv_decide

/-- Gate enable of byte 47, extracted from `g_byte[47].g_used.u_cg`. -/
def enable47 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e47_0 := (addr1 == (47 : BitVec 9))
  let e47_1 := we1 && e47_0
  e47_1

/-- The extracted gate of byte 47 equals `we1 && addr1 == 47` at every one of
the 512 addresses, for either strobe value. -/
theorem enable47_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable47 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 47)) := by
  unfold enable47
  bv_decide

/-- Gate enable of byte 48, extracted from `g_byte[48].g_used.u_cg`. -/
def enable48 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e48_0 := (addr1 == (48 : BitVec 9))
  let e48_1 := we1 && e48_0
  e48_1

/-- The extracted gate of byte 48 equals `we1 && addr1 == 48` at every one of
the 512 addresses, for either strobe value. -/
theorem enable48_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable48 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 48)) := by
  unfold enable48
  bv_decide

/-- Gate enable of byte 49, extracted from `g_byte[49].g_used.u_cg`. -/
def enable49 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e49_0 := (addr1 == (49 : BitVec 9))
  let e49_1 := we1 && e49_0
  e49_1

/-- The extracted gate of byte 49 equals `we1 && addr1 == 49` at every one of
the 512 addresses, for either strobe value. -/
theorem enable49_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable49 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 49)) := by
  unfold enable49
  bv_decide

/-- Gate enable of byte 50, extracted from `g_byte[50].g_used.u_cg`. -/
def enable50 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e50_0 := (addr1 == (50 : BitVec 9))
  let e50_1 := we1 && e50_0
  e50_1

/-- The extracted gate of byte 50 equals `we1 && addr1 == 50` at every one of
the 512 addresses, for either strobe value. -/
theorem enable50_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable50 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 50)) := by
  unfold enable50
  bv_decide

/-- Gate enable of byte 51, extracted from `g_byte[51].g_used.u_cg`. -/
def enable51 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e51_0 := (addr1 == (51 : BitVec 9))
  let e51_1 := we1 && e51_0
  e51_1

/-- The extracted gate of byte 51 equals `we1 && addr1 == 51` at every one of
the 512 addresses, for either strobe value. -/
theorem enable51_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable51 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 51)) := by
  unfold enable51
  bv_decide

/-- Gate enable of byte 52, extracted from `g_byte[52].g_used.u_cg`. -/
def enable52 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e52_0 := (addr1 == (52 : BitVec 9))
  let e52_1 := we1 && e52_0
  e52_1

/-- The extracted gate of byte 52 equals `we1 && addr1 == 52` at every one of
the 512 addresses, for either strobe value. -/
theorem enable52_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable52 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 52)) := by
  unfold enable52
  bv_decide

/-- Gate enable of byte 53, extracted from `g_byte[53].g_used.u_cg`. -/
def enable53 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e53_0 := (addr1 == (53 : BitVec 9))
  let e53_1 := we1 && e53_0
  e53_1

/-- The extracted gate of byte 53 equals `we1 && addr1 == 53` at every one of
the 512 addresses, for either strobe value. -/
theorem enable53_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable53 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 53)) := by
  unfold enable53
  bv_decide

/-- Gate enable of byte 54, extracted from `g_byte[54].g_used.u_cg`. -/
def enable54 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e54_0 := (addr1 == (54 : BitVec 9))
  let e54_1 := we1 && e54_0
  e54_1

/-- The extracted gate of byte 54 equals `we1 && addr1 == 54` at every one of
the 512 addresses, for either strobe value. -/
theorem enable54_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable54 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 54)) := by
  unfold enable54
  bv_decide

/-- Gate enable of byte 55, extracted from `g_byte[55].g_used.u_cg`. -/
def enable55 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e55_0 := (addr1 == (55 : BitVec 9))
  let e55_1 := we1 && e55_0
  e55_1

/-- The extracted gate of byte 55 equals `we1 && addr1 == 55` at every one of
the 512 addresses, for either strobe value. -/
theorem enable55_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable55 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 55)) := by
  unfold enable55
  bv_decide

/-- Gate enable of byte 56, extracted from `g_byte[56].g_used.u_cg`. -/
def enable56 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e56_0 := (addr1 == (56 : BitVec 9))
  let e56_1 := we1 && e56_0
  e56_1

/-- The extracted gate of byte 56 equals `we1 && addr1 == 56` at every one of
the 512 addresses, for either strobe value. -/
theorem enable56_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable56 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 56)) := by
  unfold enable56
  bv_decide

/-- Gate enable of byte 57, extracted from `g_byte[57].g_used.u_cg`. -/
def enable57 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e57_0 := (addr1 == (57 : BitVec 9))
  let e57_1 := we1 && e57_0
  e57_1

/-- The extracted gate of byte 57 equals `we1 && addr1 == 57` at every one of
the 512 addresses, for either strobe value. -/
theorem enable57_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable57 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 57)) := by
  unfold enable57
  bv_decide

/-- Gate enable of byte 58, extracted from `g_byte[58].g_used.u_cg`. -/
def enable58 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e58_0 := (addr1 == (58 : BitVec 9))
  let e58_1 := we1 && e58_0
  e58_1

/-- The extracted gate of byte 58 equals `we1 && addr1 == 58` at every one of
the 512 addresses, for either strobe value. -/
theorem enable58_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable58 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 58)) := by
  unfold enable58
  bv_decide

/-- Gate enable of byte 59, extracted from `g_byte[59].g_used.u_cg`. -/
def enable59 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e59_0 := (addr1 == (59 : BitVec 9))
  let e59_1 := we1 && e59_0
  e59_1

/-- The extracted gate of byte 59 equals `we1 && addr1 == 59` at every one of
the 512 addresses, for either strobe value. -/
theorem enable59_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable59 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 59)) := by
  unfold enable59
  bv_decide

/-- Gate enable of byte 60, extracted from `g_byte[60].g_used.u_cg`. -/
def enable60 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e60_0 := (addr1 == (60 : BitVec 9))
  let e60_1 := we1 && e60_0
  e60_1

/-- The extracted gate of byte 60 equals `we1 && addr1 == 60` at every one of
the 512 addresses, for either strobe value. -/
theorem enable60_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable60 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 60)) := by
  unfold enable60
  bv_decide

/-- Gate enable of byte 64, extracted from `g_byte[64].g_used.u_cg`. -/
def enable64 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e64_0 := (addr1 == (64 : BitVec 9))
  let e64_1 := we1 && e64_0
  e64_1

/-- The extracted gate of byte 64 equals `we1 && addr1 == 64` at every one of
the 512 addresses, for either strobe value. -/
theorem enable64_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable64 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 64)) := by
  unfold enable64
  bv_decide

/-- Gate enable of byte 65, extracted from `g_byte[65].g_used.u_cg`. -/
def enable65 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e65_0 := (addr1 == (65 : BitVec 9))
  let e65_1 := we1 && e65_0
  e65_1

/-- The extracted gate of byte 65 equals `we1 && addr1 == 65` at every one of
the 512 addresses, for either strobe value. -/
theorem enable65_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable65 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 65)) := by
  unfold enable65
  bv_decide

/-- Gate enable of byte 66, extracted from `g_byte[66].g_used.u_cg`. -/
def enable66 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e66_0 := (addr1 == (66 : BitVec 9))
  let e66_1 := we1 && e66_0
  e66_1

/-- The extracted gate of byte 66 equals `we1 && addr1 == 66` at every one of
the 512 addresses, for either strobe value. -/
theorem enable66_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable66 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 66)) := by
  unfold enable66
  bv_decide

/-- Gate enable of byte 67, extracted from `g_byte[67].g_used.u_cg`. -/
def enable67 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e67_0 := (addr1 == (67 : BitVec 9))
  let e67_1 := we1 && e67_0
  e67_1

/-- The extracted gate of byte 67 equals `we1 && addr1 == 67` at every one of
the 512 addresses, for either strobe value. -/
theorem enable67_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable67 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 67)) := by
  unfold enable67
  bv_decide

/-- Gate enable of byte 68, extracted from `g_byte[68].g_used.u_cg`. -/
def enable68 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e68_0 := (addr1 == (68 : BitVec 9))
  let e68_1 := we1 && e68_0
  e68_1

/-- The extracted gate of byte 68 equals `we1 && addr1 == 68` at every one of
the 512 addresses, for either strobe value. -/
theorem enable68_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable68 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 68)) := by
  unfold enable68
  bv_decide

/-- Gate enable of byte 69, extracted from `g_byte[69].g_used.u_cg`. -/
def enable69 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e69_0 := (addr1 == (69 : BitVec 9))
  let e69_1 := we1 && e69_0
  e69_1

/-- The extracted gate of byte 69 equals `we1 && addr1 == 69` at every one of
the 512 addresses, for either strobe value. -/
theorem enable69_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable69 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 69)) := by
  unfold enable69
  bv_decide

/-- Gate enable of byte 70, extracted from `g_byte[70].g_used.u_cg`. -/
def enable70 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e70_0 := (addr1 == (70 : BitVec 9))
  let e70_1 := we1 && e70_0
  e70_1

/-- The extracted gate of byte 70 equals `we1 && addr1 == 70` at every one of
the 512 addresses, for either strobe value. -/
theorem enable70_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable70 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 70)) := by
  unfold enable70
  bv_decide

/-- Gate enable of byte 71, extracted from `g_byte[71].g_used.u_cg`. -/
def enable71 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e71_0 := (addr1 == (71 : BitVec 9))
  let e71_1 := we1 && e71_0
  e71_1

/-- The extracted gate of byte 71 equals `we1 && addr1 == 71` at every one of
the 512 addresses, for either strobe value. -/
theorem enable71_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable71 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 71)) := by
  unfold enable71
  bv_decide

/-- Gate enable of byte 72, extracted from `g_byte[72].g_used.u_cg`. -/
def enable72 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e72_0 := (addr1 == (72 : BitVec 9))
  let e72_1 := we1 && e72_0
  e72_1

/-- The extracted gate of byte 72 equals `we1 && addr1 == 72` at every one of
the 512 addresses, for either strobe value. -/
theorem enable72_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable72 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 72)) := by
  unfold enable72
  bv_decide

/-- Gate enable of byte 73, extracted from `g_byte[73].g_used.u_cg`. -/
def enable73 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e73_0 := (addr1 == (73 : BitVec 9))
  let e73_1 := we1 && e73_0
  e73_1

/-- The extracted gate of byte 73 equals `we1 && addr1 == 73` at every one of
the 512 addresses, for either strobe value. -/
theorem enable73_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable73 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 73)) := by
  unfold enable73
  bv_decide

/-- Gate enable of byte 74, extracted from `g_byte[74].g_used.u_cg`. -/
def enable74 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e74_0 := (addr1 == (74 : BitVec 9))
  let e74_1 := we1 && e74_0
  e74_1

/-- The extracted gate of byte 74 equals `we1 && addr1 == 74` at every one of
the 512 addresses, for either strobe value. -/
theorem enable74_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable74 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 74)) := by
  unfold enable74
  bv_decide

/-- Gate enable of byte 75, extracted from `g_byte[75].g_used.u_cg`. -/
def enable75 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e75_0 := (addr1 == (75 : BitVec 9))
  let e75_1 := we1 && e75_0
  e75_1

/-- The extracted gate of byte 75 equals `we1 && addr1 == 75` at every one of
the 512 addresses, for either strobe value. -/
theorem enable75_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable75 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 75)) := by
  unfold enable75
  bv_decide

/-- Gate enable of byte 76, extracted from `g_byte[76].g_used.u_cg`. -/
def enable76 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e76_0 := (addr1 == (76 : BitVec 9))
  let e76_1 := we1 && e76_0
  e76_1

/-- The extracted gate of byte 76 equals `we1 && addr1 == 76` at every one of
the 512 addresses, for either strobe value. -/
theorem enable76_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable76 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 76)) := by
  unfold enable76
  bv_decide

/-- Gate enable of byte 77, extracted from `g_byte[77].g_used.u_cg`. -/
def enable77 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e77_0 := (addr1 == (77 : BitVec 9))
  let e77_1 := we1 && e77_0
  e77_1

/-- The extracted gate of byte 77 equals `we1 && addr1 == 77` at every one of
the 512 addresses, for either strobe value. -/
theorem enable77_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable77 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 77)) := by
  unfold enable77
  bv_decide

/-- Gate enable of byte 78, extracted from `g_byte[78].g_used.u_cg`. -/
def enable78 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e78_0 := (addr1 == (78 : BitVec 9))
  let e78_1 := we1 && e78_0
  e78_1

/-- The extracted gate of byte 78 equals `we1 && addr1 == 78` at every one of
the 512 addresses, for either strobe value. -/
theorem enable78_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable78 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 78)) := by
  unfold enable78
  bv_decide

/-- Gate enable of byte 79, extracted from `g_byte[79].g_used.u_cg`. -/
def enable79 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e79_0 := (addr1 == (79 : BitVec 9))
  let e79_1 := we1 && e79_0
  e79_1

/-- The extracted gate of byte 79 equals `we1 && addr1 == 79` at every one of
the 512 addresses, for either strobe value. -/
theorem enable79_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable79 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 79)) := by
  unfold enable79
  bv_decide

/-- Gate enable of byte 80, extracted from `g_byte[80].g_used.u_cg`. -/
def enable80 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e80_0 := (addr1 == (80 : BitVec 9))
  let e80_1 := we1 && e80_0
  e80_1

/-- The extracted gate of byte 80 equals `we1 && addr1 == 80` at every one of
the 512 addresses, for either strobe value. -/
theorem enable80_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable80 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 80)) := by
  unfold enable80
  bv_decide

/-- Gate enable of byte 81, extracted from `g_byte[81].g_used.u_cg`. -/
def enable81 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e81_0 := (addr1 == (81 : BitVec 9))
  let e81_1 := we1 && e81_0
  e81_1

/-- The extracted gate of byte 81 equals `we1 && addr1 == 81` at every one of
the 512 addresses, for either strobe value. -/
theorem enable81_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable81 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 81)) := by
  unfold enable81
  bv_decide

/-- Gate enable of byte 82, extracted from `g_byte[82].g_used.u_cg`. -/
def enable82 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e82_0 := (addr1 == (82 : BitVec 9))
  let e82_1 := we1 && e82_0
  e82_1

/-- The extracted gate of byte 82 equals `we1 && addr1 == 82` at every one of
the 512 addresses, for either strobe value. -/
theorem enable82_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable82 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 82)) := by
  unfold enable82
  bv_decide

/-- Gate enable of byte 83, extracted from `g_byte[83].g_used.u_cg`. -/
def enable83 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e83_0 := (addr1 == (83 : BitVec 9))
  let e83_1 := we1 && e83_0
  e83_1

/-- The extracted gate of byte 83 equals `we1 && addr1 == 83` at every one of
the 512 addresses, for either strobe value. -/
theorem enable83_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable83 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 83)) := by
  unfold enable83
  bv_decide

/-- Gate enable of byte 84, extracted from `g_byte[84].g_used.u_cg`. -/
def enable84 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e84_0 := (addr1 == (84 : BitVec 9))
  let e84_1 := we1 && e84_0
  e84_1

/-- The extracted gate of byte 84 equals `we1 && addr1 == 84` at every one of
the 512 addresses, for either strobe value. -/
theorem enable84_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable84 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 84)) := by
  unfold enable84
  bv_decide

/-- Gate enable of byte 85, extracted from `g_byte[85].g_used.u_cg`. -/
def enable85 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e85_0 := (addr1 == (85 : BitVec 9))
  let e85_1 := we1 && e85_0
  e85_1

/-- The extracted gate of byte 85 equals `we1 && addr1 == 85` at every one of
the 512 addresses, for either strobe value. -/
theorem enable85_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable85 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 85)) := by
  unfold enable85
  bv_decide

/-- Gate enable of byte 86, extracted from `g_byte[86].g_used.u_cg`. -/
def enable86 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e86_0 := (addr1 == (86 : BitVec 9))
  let e86_1 := we1 && e86_0
  e86_1

/-- The extracted gate of byte 86 equals `we1 && addr1 == 86` at every one of
the 512 addresses, for either strobe value. -/
theorem enable86_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable86 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 86)) := by
  unfold enable86
  bv_decide

/-- Gate enable of byte 87, extracted from `g_byte[87].g_used.u_cg`. -/
def enable87 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e87_0 := (addr1 == (87 : BitVec 9))
  let e87_1 := we1 && e87_0
  e87_1

/-- The extracted gate of byte 87 equals `we1 && addr1 == 87` at every one of
the 512 addresses, for either strobe value. -/
theorem enable87_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable87 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 87)) := by
  unfold enable87
  bv_decide

/-- Gate enable of byte 88, extracted from `g_byte[88].g_used.u_cg`. -/
def enable88 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e88_0 := (addr1 == (88 : BitVec 9))
  let e88_1 := we1 && e88_0
  e88_1

/-- The extracted gate of byte 88 equals `we1 && addr1 == 88` at every one of
the 512 addresses, for either strobe value. -/
theorem enable88_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable88 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 88)) := by
  unfold enable88
  bv_decide

/-- Gate enable of byte 89, extracted from `g_byte[89].g_used.u_cg`. -/
def enable89 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e89_0 := (addr1 == (89 : BitVec 9))
  let e89_1 := we1 && e89_0
  e89_1

/-- The extracted gate of byte 89 equals `we1 && addr1 == 89` at every one of
the 512 addresses, for either strobe value. -/
theorem enable89_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable89 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 89)) := by
  unfold enable89
  bv_decide

/-- Gate enable of byte 90, extracted from `g_byte[90].g_used.u_cg`. -/
def enable90 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e90_0 := (addr1 == (90 : BitVec 9))
  let e90_1 := we1 && e90_0
  e90_1

/-- The extracted gate of byte 90 equals `we1 && addr1 == 90` at every one of
the 512 addresses, for either strobe value. -/
theorem enable90_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable90 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 90)) := by
  unfold enable90
  bv_decide

/-- Gate enable of byte 91, extracted from `g_byte[91].g_used.u_cg`. -/
def enable91 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e91_0 := (addr1 == (91 : BitVec 9))
  let e91_1 := we1 && e91_0
  e91_1

/-- The extracted gate of byte 91 equals `we1 && addr1 == 91` at every one of
the 512 addresses, for either strobe value. -/
theorem enable91_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable91 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 91)) := by
  unfold enable91
  bv_decide

/-- Gate enable of byte 92, extracted from `g_byte[92].g_used.u_cg`. -/
def enable92 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e92_0 := (addr1 == (92 : BitVec 9))
  let e92_1 := we1 && e92_0
  e92_1

/-- The extracted gate of byte 92 equals `we1 && addr1 == 92` at every one of
the 512 addresses, for either strobe value. -/
theorem enable92_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable92 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 92)) := by
  unfold enable92
  bv_decide

/-- Gate enable of byte 96, extracted from `g_byte[96].g_used.u_cg`. -/
def enable96 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e96_0 := (addr1 == (96 : BitVec 9))
  let e96_1 := we1 && e96_0
  e96_1

/-- The extracted gate of byte 96 equals `we1 && addr1 == 96` at every one of
the 512 addresses, for either strobe value. -/
theorem enable96_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable96 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 96)) := by
  unfold enable96
  bv_decide

/-- Gate enable of byte 97, extracted from `g_byte[97].g_used.u_cg`. -/
def enable97 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e97_0 := (addr1 == (97 : BitVec 9))
  let e97_1 := we1 && e97_0
  e97_1

/-- The extracted gate of byte 97 equals `we1 && addr1 == 97` at every one of
the 512 addresses, for either strobe value. -/
theorem enable97_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable97 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 97)) := by
  unfold enable97
  bv_decide

/-- Gate enable of byte 98, extracted from `g_byte[98].g_used.u_cg`. -/
def enable98 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e98_0 := (addr1 == (98 : BitVec 9))
  let e98_1 := we1 && e98_0
  e98_1

/-- The extracted gate of byte 98 equals `we1 && addr1 == 98` at every one of
the 512 addresses, for either strobe value. -/
theorem enable98_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable98 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 98)) := by
  unfold enable98
  bv_decide

/-- Gate enable of byte 99, extracted from `g_byte[99].g_used.u_cg`. -/
def enable99 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e99_0 := (addr1 == (99 : BitVec 9))
  let e99_1 := we1 && e99_0
  e99_1

/-- The extracted gate of byte 99 equals `we1 && addr1 == 99` at every one of
the 512 addresses, for either strobe value. -/
theorem enable99_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable99 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 99)) := by
  unfold enable99
  bv_decide

/-- Gate enable of byte 100, extracted from `g_byte[100].g_used.u_cg`. -/
def enable100 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e100_0 := (addr1 == (100 : BitVec 9))
  let e100_1 := we1 && e100_0
  e100_1

/-- The extracted gate of byte 100 equals `we1 && addr1 == 100` at every one of
the 512 addresses, for either strobe value. -/
theorem enable100_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable100 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 100)) := by
  unfold enable100
  bv_decide

/-- Gate enable of byte 101, extracted from `g_byte[101].g_used.u_cg`. -/
def enable101 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e101_0 := (addr1 == (101 : BitVec 9))
  let e101_1 := we1 && e101_0
  e101_1

/-- The extracted gate of byte 101 equals `we1 && addr1 == 101` at every one of
the 512 addresses, for either strobe value. -/
theorem enable101_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable101 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 101)) := by
  unfold enable101
  bv_decide

/-- Gate enable of byte 102, extracted from `g_byte[102].g_used.u_cg`. -/
def enable102 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e102_0 := (addr1 == (102 : BitVec 9))
  let e102_1 := we1 && e102_0
  e102_1

/-- The extracted gate of byte 102 equals `we1 && addr1 == 102` at every one of
the 512 addresses, for either strobe value. -/
theorem enable102_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable102 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 102)) := by
  unfold enable102
  bv_decide

/-- Gate enable of byte 103, extracted from `g_byte[103].g_used.u_cg`. -/
def enable103 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e103_0 := (addr1 == (103 : BitVec 9))
  let e103_1 := we1 && e103_0
  e103_1

/-- The extracted gate of byte 103 equals `we1 && addr1 == 103` at every one of
the 512 addresses, for either strobe value. -/
theorem enable103_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable103 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 103)) := by
  unfold enable103
  bv_decide

/-- Gate enable of byte 104, extracted from `g_byte[104].g_used.u_cg`. -/
def enable104 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e104_0 := (addr1 == (104 : BitVec 9))
  let e104_1 := we1 && e104_0
  e104_1

/-- The extracted gate of byte 104 equals `we1 && addr1 == 104` at every one of
the 512 addresses, for either strobe value. -/
theorem enable104_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable104 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 104)) := by
  unfold enable104
  bv_decide

/-- Gate enable of byte 105, extracted from `g_byte[105].g_used.u_cg`. -/
def enable105 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e105_0 := (addr1 == (105 : BitVec 9))
  let e105_1 := we1 && e105_0
  e105_1

/-- The extracted gate of byte 105 equals `we1 && addr1 == 105` at every one of
the 512 addresses, for either strobe value. -/
theorem enable105_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable105 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 105)) := by
  unfold enable105
  bv_decide

/-- Gate enable of byte 106, extracted from `g_byte[106].g_used.u_cg`. -/
def enable106 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e106_0 := (addr1 == (106 : BitVec 9))
  let e106_1 := we1 && e106_0
  e106_1

/-- The extracted gate of byte 106 equals `we1 && addr1 == 106` at every one of
the 512 addresses, for either strobe value. -/
theorem enable106_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable106 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 106)) := by
  unfold enable106
  bv_decide

/-- Gate enable of byte 107, extracted from `g_byte[107].g_used.u_cg`. -/
def enable107 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e107_0 := (addr1 == (107 : BitVec 9))
  let e107_1 := we1 && e107_0
  e107_1

/-- The extracted gate of byte 107 equals `we1 && addr1 == 107` at every one of
the 512 addresses, for either strobe value. -/
theorem enable107_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable107 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 107)) := by
  unfold enable107
  bv_decide

/-- Gate enable of byte 108, extracted from `g_byte[108].g_used.u_cg`. -/
def enable108 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e108_0 := (addr1 == (108 : BitVec 9))
  let e108_1 := we1 && e108_0
  e108_1

/-- The extracted gate of byte 108 equals `we1 && addr1 == 108` at every one of
the 512 addresses, for either strobe value. -/
theorem enable108_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable108 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 108)) := by
  unfold enable108
  bv_decide

/-- Gate enable of byte 109, extracted from `g_byte[109].g_used.u_cg`. -/
def enable109 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e109_0 := (addr1 == (109 : BitVec 9))
  let e109_1 := we1 && e109_0
  e109_1

/-- The extracted gate of byte 109 equals `we1 && addr1 == 109` at every one of
the 512 addresses, for either strobe value. -/
theorem enable109_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable109 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 109)) := by
  unfold enable109
  bv_decide

/-- Gate enable of byte 110, extracted from `g_byte[110].g_used.u_cg`. -/
def enable110 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e110_0 := (addr1 == (110 : BitVec 9))
  let e110_1 := we1 && e110_0
  e110_1

/-- The extracted gate of byte 110 equals `we1 && addr1 == 110` at every one of
the 512 addresses, for either strobe value. -/
theorem enable110_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable110 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 110)) := by
  unfold enable110
  bv_decide

/-- Gate enable of byte 111, extracted from `g_byte[111].g_used.u_cg`. -/
def enable111 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e111_0 := (addr1 == (111 : BitVec 9))
  let e111_1 := we1 && e111_0
  e111_1

/-- The extracted gate of byte 111 equals `we1 && addr1 == 111` at every one of
the 512 addresses, for either strobe value. -/
theorem enable111_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable111 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 111)) := by
  unfold enable111
  bv_decide

/-- Gate enable of byte 112, extracted from `g_byte[112].g_used.u_cg`. -/
def enable112 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e112_0 := (addr1 == (112 : BitVec 9))
  let e112_1 := we1 && e112_0
  e112_1

/-- The extracted gate of byte 112 equals `we1 && addr1 == 112` at every one of
the 512 addresses, for either strobe value. -/
theorem enable112_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable112 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 112)) := by
  unfold enable112
  bv_decide

/-- Gate enable of byte 113, extracted from `g_byte[113].g_used.u_cg`. -/
def enable113 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e113_0 := (addr1 == (113 : BitVec 9))
  let e113_1 := we1 && e113_0
  e113_1

/-- The extracted gate of byte 113 equals `we1 && addr1 == 113` at every one of
the 512 addresses, for either strobe value. -/
theorem enable113_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable113 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 113)) := by
  unfold enable113
  bv_decide

/-- Gate enable of byte 114, extracted from `g_byte[114].g_used.u_cg`. -/
def enable114 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e114_0 := (addr1 == (114 : BitVec 9))
  let e114_1 := we1 && e114_0
  e114_1

/-- The extracted gate of byte 114 equals `we1 && addr1 == 114` at every one of
the 512 addresses, for either strobe value. -/
theorem enable114_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable114 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 114)) := by
  unfold enable114
  bv_decide

/-- Gate enable of byte 115, extracted from `g_byte[115].g_used.u_cg`. -/
def enable115 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e115_0 := (addr1 == (115 : BitVec 9))
  let e115_1 := we1 && e115_0
  e115_1

/-- The extracted gate of byte 115 equals `we1 && addr1 == 115` at every one of
the 512 addresses, for either strobe value. -/
theorem enable115_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable115 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 115)) := by
  unfold enable115
  bv_decide

/-- Gate enable of byte 116, extracted from `g_byte[116].g_used.u_cg`. -/
def enable116 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e116_0 := (addr1 == (116 : BitVec 9))
  let e116_1 := we1 && e116_0
  e116_1

/-- The extracted gate of byte 116 equals `we1 && addr1 == 116` at every one of
the 512 addresses, for either strobe value. -/
theorem enable116_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable116 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 116)) := by
  unfold enable116
  bv_decide

/-- Gate enable of byte 117, extracted from `g_byte[117].g_used.u_cg`. -/
def enable117 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e117_0 := (addr1 == (117 : BitVec 9))
  let e117_1 := we1 && e117_0
  e117_1

/-- The extracted gate of byte 117 equals `we1 && addr1 == 117` at every one of
the 512 addresses, for either strobe value. -/
theorem enable117_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable117 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 117)) := by
  unfold enable117
  bv_decide

/-- Gate enable of byte 118, extracted from `g_byte[118].g_used.u_cg`. -/
def enable118 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e118_0 := (addr1 == (118 : BitVec 9))
  let e118_1 := we1 && e118_0
  e118_1

/-- The extracted gate of byte 118 equals `we1 && addr1 == 118` at every one of
the 512 addresses, for either strobe value. -/
theorem enable118_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable118 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 118)) := by
  unfold enable118
  bv_decide

/-- Gate enable of byte 119, extracted from `g_byte[119].g_used.u_cg`. -/
def enable119 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e119_0 := (addr1 == (119 : BitVec 9))
  let e119_1 := we1 && e119_0
  e119_1

/-- The extracted gate of byte 119 equals `we1 && addr1 == 119` at every one of
the 512 addresses, for either strobe value. -/
theorem enable119_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable119 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 119)) := by
  unfold enable119
  bv_decide

/-- Gate enable of byte 120, extracted from `g_byte[120].g_used.u_cg`. -/
def enable120 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e120_0 := (addr1 == (120 : BitVec 9))
  let e120_1 := we1 && e120_0
  e120_1

/-- The extracted gate of byte 120 equals `we1 && addr1 == 120` at every one of
the 512 addresses, for either strobe value. -/
theorem enable120_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable120 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 120)) := by
  unfold enable120
  bv_decide

/-- Gate enable of byte 121, extracted from `g_byte[121].g_used.u_cg`. -/
def enable121 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e121_0 := (addr1 == (121 : BitVec 9))
  let e121_1 := we1 && e121_0
  e121_1

/-- The extracted gate of byte 121 equals `we1 && addr1 == 121` at every one of
the 512 addresses, for either strobe value. -/
theorem enable121_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable121 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 121)) := by
  unfold enable121
  bv_decide

/-- Gate enable of byte 122, extracted from `g_byte[122].g_used.u_cg`. -/
def enable122 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e122_0 := (addr1 == (122 : BitVec 9))
  let e122_1 := we1 && e122_0
  e122_1

/-- The extracted gate of byte 122 equals `we1 && addr1 == 122` at every one of
the 512 addresses, for either strobe value. -/
theorem enable122_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable122 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 122)) := by
  unfold enable122
  bv_decide

/-- Gate enable of byte 123, extracted from `g_byte[123].g_used.u_cg`. -/
def enable123 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e123_0 := (addr1 == (123 : BitVec 9))
  let e123_1 := we1 && e123_0
  e123_1

/-- The extracted gate of byte 123 equals `we1 && addr1 == 123` at every one of
the 512 addresses, for either strobe value. -/
theorem enable123_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable123 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 123)) := by
  unfold enable123
  bv_decide

/-- Gate enable of byte 124, extracted from `g_byte[124].g_used.u_cg`. -/
def enable124 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e124_0 := (addr1 == (124 : BitVec 9))
  let e124_1 := we1 && e124_0
  e124_1

/-- The extracted gate of byte 124 equals `we1 && addr1 == 124` at every one of
the 512 addresses, for either strobe value. -/
theorem enable124_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable124 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 124)) := by
  unfold enable124
  bv_decide

/-- Gate enable of byte 128, extracted from `g_byte[128].g_used.u_cg`. -/
def enable128 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e128_0 := (addr1 == (128 : BitVec 9))
  let e128_1 := we1 && e128_0
  e128_1

/-- The extracted gate of byte 128 equals `we1 && addr1 == 128` at every one of
the 512 addresses, for either strobe value. -/
theorem enable128_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable128 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 128)) := by
  unfold enable128
  bv_decide

/-- Gate enable of byte 129, extracted from `g_byte[129].g_used.u_cg`. -/
def enable129 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e129_0 := (addr1 == (129 : BitVec 9))
  let e129_1 := we1 && e129_0
  e129_1

/-- The extracted gate of byte 129 equals `we1 && addr1 == 129` at every one of
the 512 addresses, for either strobe value. -/
theorem enable129_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable129 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 129)) := by
  unfold enable129
  bv_decide

/-- Gate enable of byte 130, extracted from `g_byte[130].g_used.u_cg`. -/
def enable130 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e130_0 := (addr1 == (130 : BitVec 9))
  let e130_1 := we1 && e130_0
  e130_1

/-- The extracted gate of byte 130 equals `we1 && addr1 == 130` at every one of
the 512 addresses, for either strobe value. -/
theorem enable130_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable130 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 130)) := by
  unfold enable130
  bv_decide

/-- Gate enable of byte 131, extracted from `g_byte[131].g_used.u_cg`. -/
def enable131 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e131_0 := (addr1 == (131 : BitVec 9))
  let e131_1 := we1 && e131_0
  e131_1

/-- The extracted gate of byte 131 equals `we1 && addr1 == 131` at every one of
the 512 addresses, for either strobe value. -/
theorem enable131_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable131 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 131)) := by
  unfold enable131
  bv_decide

/-- Gate enable of byte 132, extracted from `g_byte[132].g_used.u_cg`. -/
def enable132 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e132_0 := (addr1 == (132 : BitVec 9))
  let e132_1 := we1 && e132_0
  e132_1

/-- The extracted gate of byte 132 equals `we1 && addr1 == 132` at every one of
the 512 addresses, for either strobe value. -/
theorem enable132_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable132 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 132)) := by
  unfold enable132
  bv_decide

/-- Gate enable of byte 136, extracted from `g_byte[136].g_used.u_cg`. -/
def enable136 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e136_0 := (addr1 == (136 : BitVec 9))
  let e136_1 := we1 && e136_0
  e136_1

/-- The extracted gate of byte 136 equals `we1 && addr1 == 136` at every one of
the 512 addresses, for either strobe value. -/
theorem enable136_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable136 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 136)) := by
  unfold enable136
  bv_decide

/-- Gate enable of byte 137, extracted from `g_byte[137].g_used.u_cg`. -/
def enable137 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e137_0 := (addr1 == (137 : BitVec 9))
  let e137_1 := we1 && e137_0
  e137_1

/-- The extracted gate of byte 137 equals `we1 && addr1 == 137` at every one of
the 512 addresses, for either strobe value. -/
theorem enable137_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable137 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 137)) := by
  unfold enable137
  bv_decide

/-- Gate enable of byte 138, extracted from `g_byte[138].g_used.u_cg`. -/
def enable138 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e138_0 := (addr1 == (138 : BitVec 9))
  let e138_1 := we1 && e138_0
  e138_1

/-- The extracted gate of byte 138 equals `we1 && addr1 == 138` at every one of
the 512 addresses, for either strobe value. -/
theorem enable138_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable138 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 138)) := by
  unfold enable138
  bv_decide

/-- Gate enable of byte 139, extracted from `g_byte[139].g_used.u_cg`. -/
def enable139 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e139_0 := (addr1 == (139 : BitVec 9))
  let e139_1 := we1 && e139_0
  e139_1

/-- The extracted gate of byte 139 equals `we1 && addr1 == 139` at every one of
the 512 addresses, for either strobe value. -/
theorem enable139_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable139 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 139)) := by
  unfold enable139
  bv_decide

/-- Gate enable of byte 140, extracted from `g_byte[140].g_used.u_cg`. -/
def enable140 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e140_0 := (addr1 == (140 : BitVec 9))
  let e140_1 := we1 && e140_0
  e140_1

/-- The extracted gate of byte 140 equals `we1 && addr1 == 140` at every one of
the 512 addresses, for either strobe value. -/
theorem enable140_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable140 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 140)) := by
  unfold enable140
  bv_decide

/-- Gate enable of byte 144, extracted from `g_byte[144].g_used.u_cg`. -/
def enable144 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e144_0 := (addr1 == (144 : BitVec 9))
  let e144_1 := we1 && e144_0
  e144_1

/-- The extracted gate of byte 144 equals `we1 && addr1 == 144` at every one of
the 512 addresses, for either strobe value. -/
theorem enable144_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable144 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 144)) := by
  unfold enable144
  bv_decide

/-- Gate enable of byte 145, extracted from `g_byte[145].g_used.u_cg`. -/
def enable145 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e145_0 := (addr1 == (145 : BitVec 9))
  let e145_1 := we1 && e145_0
  e145_1

/-- The extracted gate of byte 145 equals `we1 && addr1 == 145` at every one of
the 512 addresses, for either strobe value. -/
theorem enable145_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable145 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 145)) := by
  unfold enable145
  bv_decide

/-- Gate enable of byte 146, extracted from `g_byte[146].g_used.u_cg`. -/
def enable146 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e146_0 := (addr1 == (146 : BitVec 9))
  let e146_1 := we1 && e146_0
  e146_1

/-- The extracted gate of byte 146 equals `we1 && addr1 == 146` at every one of
the 512 addresses, for either strobe value. -/
theorem enable146_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable146 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 146)) := by
  unfold enable146
  bv_decide

/-- Gate enable of byte 147, extracted from `g_byte[147].g_used.u_cg`. -/
def enable147 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e147_0 := (addr1 == (147 : BitVec 9))
  let e147_1 := we1 && e147_0
  e147_1

/-- The extracted gate of byte 147 equals `we1 && addr1 == 147` at every one of
the 512 addresses, for either strobe value. -/
theorem enable147_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable147 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 147)) := by
  unfold enable147
  bv_decide

/-- Gate enable of byte 148, extracted from `g_byte[148].g_used.u_cg`. -/
def enable148 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e148_0 := (addr1 == (148 : BitVec 9))
  let e148_1 := we1 && e148_0
  e148_1

/-- The extracted gate of byte 148 equals `we1 && addr1 == 148` at every one of
the 512 addresses, for either strobe value. -/
theorem enable148_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable148 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 148)) := by
  unfold enable148
  bv_decide

/-- Gate enable of byte 152, extracted from `g_byte[152].g_used.u_cg`. -/
def enable152 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e152_0 := (addr1 == (152 : BitVec 9))
  let e152_1 := we1 && e152_0
  e152_1

/-- The extracted gate of byte 152 equals `we1 && addr1 == 152` at every one of
the 512 addresses, for either strobe value. -/
theorem enable152_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable152 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 152)) := by
  unfold enable152
  bv_decide

/-- Gate enable of byte 153, extracted from `g_byte[153].g_used.u_cg`. -/
def enable153 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e153_0 := (addr1 == (153 : BitVec 9))
  let e153_1 := we1 && e153_0
  e153_1

/-- The extracted gate of byte 153 equals `we1 && addr1 == 153` at every one of
the 512 addresses, for either strobe value. -/
theorem enable153_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable153 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 153)) := by
  unfold enable153
  bv_decide

/-- Gate enable of byte 154, extracted from `g_byte[154].g_used.u_cg`. -/
def enable154 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e154_0 := (addr1 == (154 : BitVec 9))
  let e154_1 := we1 && e154_0
  e154_1

/-- The extracted gate of byte 154 equals `we1 && addr1 == 154` at every one of
the 512 addresses, for either strobe value. -/
theorem enable154_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable154 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 154)) := by
  unfold enable154
  bv_decide

/-- Gate enable of byte 155, extracted from `g_byte[155].g_used.u_cg`. -/
def enable155 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e155_0 := (addr1 == (155 : BitVec 9))
  let e155_1 := we1 && e155_0
  e155_1

/-- The extracted gate of byte 155 equals `we1 && addr1 == 155` at every one of
the 512 addresses, for either strobe value. -/
theorem enable155_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable155 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 155)) := by
  unfold enable155
  bv_decide

/-- Gate enable of byte 156, extracted from `g_byte[156].g_used.u_cg`. -/
def enable156 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e156_0 := (addr1 == (156 : BitVec 9))
  let e156_1 := we1 && e156_0
  e156_1

/-- The extracted gate of byte 156 equals `we1 && addr1 == 156` at every one of
the 512 addresses, for either strobe value. -/
theorem enable156_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable156 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 156)) := by
  unfold enable156
  bv_decide

/-- Gate enable of byte 160, extracted from `g_byte[160].g_used.u_cg`. -/
def enable160 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e160_0 := (addr1 == (160 : BitVec 9))
  let e160_1 := we1 && e160_0
  e160_1

/-- The extracted gate of byte 160 equals `we1 && addr1 == 160` at every one of
the 512 addresses, for either strobe value. -/
theorem enable160_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable160 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 160)) := by
  unfold enable160
  bv_decide

/-- Gate enable of byte 161, extracted from `g_byte[161].g_used.u_cg`. -/
def enable161 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e161_0 := (addr1 == (161 : BitVec 9))
  let e161_1 := we1 && e161_0
  e161_1

/-- The extracted gate of byte 161 equals `we1 && addr1 == 161` at every one of
the 512 addresses, for either strobe value. -/
theorem enable161_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable161 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 161)) := by
  unfold enable161
  bv_decide

/-- Gate enable of byte 162, extracted from `g_byte[162].g_used.u_cg`. -/
def enable162 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e162_0 := (addr1 == (162 : BitVec 9))
  let e162_1 := we1 && e162_0
  e162_1

/-- The extracted gate of byte 162 equals `we1 && addr1 == 162` at every one of
the 512 addresses, for either strobe value. -/
theorem enable162_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable162 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 162)) := by
  unfold enable162
  bv_decide

/-- Gate enable of byte 163, extracted from `g_byte[163].g_used.u_cg`. -/
def enable163 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e163_0 := (addr1 == (163 : BitVec 9))
  let e163_1 := we1 && e163_0
  e163_1

/-- The extracted gate of byte 163 equals `we1 && addr1 == 163` at every one of
the 512 addresses, for either strobe value. -/
theorem enable163_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable163 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 163)) := by
  unfold enable163
  bv_decide

/-- Gate enable of byte 164, extracted from `g_byte[164].g_used.u_cg`. -/
def enable164 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e164_0 := (addr1 == (164 : BitVec 9))
  let e164_1 := we1 && e164_0
  e164_1

/-- The extracted gate of byte 164 equals `we1 && addr1 == 164` at every one of
the 512 addresses, for either strobe value. -/
theorem enable164_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable164 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 164)) := by
  unfold enable164
  bv_decide

/-- Gate enable of byte 168, extracted from `g_byte[168].g_used.u_cg`. -/
def enable168 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e168_0 := (addr1 == (168 : BitVec 9))
  let e168_1 := we1 && e168_0
  e168_1

/-- The extracted gate of byte 168 equals `we1 && addr1 == 168` at every one of
the 512 addresses, for either strobe value. -/
theorem enable168_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable168 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 168)) := by
  unfold enable168
  bv_decide

/-- Gate enable of byte 169, extracted from `g_byte[169].g_used.u_cg`. -/
def enable169 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e169_0 := (addr1 == (169 : BitVec 9))
  let e169_1 := we1 && e169_0
  e169_1

/-- The extracted gate of byte 169 equals `we1 && addr1 == 169` at every one of
the 512 addresses, for either strobe value. -/
theorem enable169_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable169 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 169)) := by
  unfold enable169
  bv_decide

/-- Gate enable of byte 170, extracted from `g_byte[170].g_used.u_cg`. -/
def enable170 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e170_0 := (addr1 == (170 : BitVec 9))
  let e170_1 := we1 && e170_0
  e170_1

/-- The extracted gate of byte 170 equals `we1 && addr1 == 170` at every one of
the 512 addresses, for either strobe value. -/
theorem enable170_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable170 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 170)) := by
  unfold enable170
  bv_decide

/-- Gate enable of byte 171, extracted from `g_byte[171].g_used.u_cg`. -/
def enable171 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e171_0 := (addr1 == (171 : BitVec 9))
  let e171_1 := we1 && e171_0
  e171_1

/-- The extracted gate of byte 171 equals `we1 && addr1 == 171` at every one of
the 512 addresses, for either strobe value. -/
theorem enable171_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable171 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 171)) := by
  unfold enable171
  bv_decide

/-- Gate enable of byte 172, extracted from `g_byte[172].g_used.u_cg`. -/
def enable172 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e172_0 := (addr1 == (172 : BitVec 9))
  let e172_1 := we1 && e172_0
  e172_1

/-- The extracted gate of byte 172 equals `we1 && addr1 == 172` at every one of
the 512 addresses, for either strobe value. -/
theorem enable172_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable172 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 172)) := by
  unfold enable172
  bv_decide

/-- Gate enable of byte 192, extracted from `g_byte[192].g_used.u_cg`. -/
def enable192 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e192_0 := (addr1 == (192 : BitVec 9))
  let e192_1 := we1 && e192_0
  e192_1

/-- The extracted gate of byte 192 equals `we1 && addr1 == 192` at every one of
the 512 addresses, for either strobe value. -/
theorem enable192_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable192 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 192)) := by
  unfold enable192
  bv_decide

/-- Gate enable of byte 193, extracted from `g_byte[193].g_used.u_cg`. -/
def enable193 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e193_0 := (addr1 == (193 : BitVec 9))
  let e193_1 := we1 && e193_0
  e193_1

/-- The extracted gate of byte 193 equals `we1 && addr1 == 193` at every one of
the 512 addresses, for either strobe value. -/
theorem enable193_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable193 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 193)) := by
  unfold enable193
  bv_decide

/-- Gate enable of byte 194, extracted from `g_byte[194].g_used.u_cg`. -/
def enable194 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e194_0 := (addr1 == (194 : BitVec 9))
  let e194_1 := we1 && e194_0
  e194_1

/-- The extracted gate of byte 194 equals `we1 && addr1 == 194` at every one of
the 512 addresses, for either strobe value. -/
theorem enable194_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable194 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 194)) := by
  unfold enable194
  bv_decide

/-- Gate enable of byte 195, extracted from `g_byte[195].g_used.u_cg`. -/
def enable195 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e195_0 := (addr1 == (195 : BitVec 9))
  let e195_1 := we1 && e195_0
  e195_1

/-- The extracted gate of byte 195 equals `we1 && addr1 == 195` at every one of
the 512 addresses, for either strobe value. -/
theorem enable195_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable195 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 195)) := by
  unfold enable195
  bv_decide

/-- Gate enable of byte 200, extracted from `g_byte[200].g_used.u_cg`. -/
def enable200 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e200_0 := (addr1 == (200 : BitVec 9))
  let e200_1 := we1 && e200_0
  e200_1

/-- The extracted gate of byte 200 equals `we1 && addr1 == 200` at every one of
the 512 addresses, for either strobe value. -/
theorem enable200_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable200 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 200)) := by
  unfold enable200
  bv_decide

/-- Gate enable of byte 201, extracted from `g_byte[201].g_used.u_cg`. -/
def enable201 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e201_0 := (addr1 == (201 : BitVec 9))
  let e201_1 := we1 && e201_0
  e201_1

/-- The extracted gate of byte 201 equals `we1 && addr1 == 201` at every one of
the 512 addresses, for either strobe value. -/
theorem enable201_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable201 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 201)) := by
  unfold enable201
  bv_decide

/-- Gate enable of byte 202, extracted from `g_byte[202].g_used.u_cg`. -/
def enable202 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e202_0 := (addr1 == (202 : BitVec 9))
  let e202_1 := we1 && e202_0
  e202_1

/-- The extracted gate of byte 202 equals `we1 && addr1 == 202` at every one of
the 512 addresses, for either strobe value. -/
theorem enable202_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable202 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 202)) := by
  unfold enable202
  bv_decide

/-- Gate enable of byte 203, extracted from `g_byte[203].g_used.u_cg`. -/
def enable203 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e203_0 := (addr1 == (203 : BitVec 9))
  let e203_1 := we1 && e203_0
  e203_1

/-- The extracted gate of byte 203 equals `we1 && addr1 == 203` at every one of
the 512 addresses, for either strobe value. -/
theorem enable203_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable203 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 203)) := by
  unfold enable203
  bv_decide

/-- Gate enable of byte 208, extracted from `g_byte[208].g_used.u_cg`. -/
def enable208 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e208_0 := (addr1 == (208 : BitVec 9))
  let e208_1 := we1 && e208_0
  e208_1

/-- The extracted gate of byte 208 equals `we1 && addr1 == 208` at every one of
the 512 addresses, for either strobe value. -/
theorem enable208_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable208 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 208)) := by
  unfold enable208
  bv_decide

/-- Gate enable of byte 209, extracted from `g_byte[209].g_used.u_cg`. -/
def enable209 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e209_0 := (addr1 == (209 : BitVec 9))
  let e209_1 := we1 && e209_0
  e209_1

/-- The extracted gate of byte 209 equals `we1 && addr1 == 209` at every one of
the 512 addresses, for either strobe value. -/
theorem enable209_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable209 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 209)) := by
  unfold enable209
  bv_decide

/-- Gate enable of byte 210, extracted from `g_byte[210].g_used.u_cg`. -/
def enable210 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e210_0 := (addr1 == (210 : BitVec 9))
  let e210_1 := we1 && e210_0
  e210_1

/-- The extracted gate of byte 210 equals `we1 && addr1 == 210` at every one of
the 512 addresses, for either strobe value. -/
theorem enable210_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable210 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 210)) := by
  unfold enable210
  bv_decide

/-- Gate enable of byte 211, extracted from `g_byte[211].g_used.u_cg`. -/
def enable211 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e211_0 := (addr1 == (211 : BitVec 9))
  let e211_1 := we1 && e211_0
  e211_1

/-- The extracted gate of byte 211 equals `we1 && addr1 == 211` at every one of
the 512 addresses, for either strobe value. -/
theorem enable211_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable211 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 211)) := by
  unfold enable211
  bv_decide

/-- Gate enable of byte 212, extracted from `g_byte[212].g_used.u_cg`. -/
def enable212 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e212_0 := (addr1 == (212 : BitVec 9))
  let e212_1 := we1 && e212_0
  e212_1

/-- The extracted gate of byte 212 equals `we1 && addr1 == 212` at every one of
the 512 addresses, for either strobe value. -/
theorem enable212_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable212 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 212)) := by
  unfold enable212
  bv_decide

/-- Gate enable of byte 213, extracted from `g_byte[213].g_used.u_cg`. -/
def enable213 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e213_0 := (addr1 == (213 : BitVec 9))
  let e213_1 := we1 && e213_0
  e213_1

/-- The extracted gate of byte 213 equals `we1 && addr1 == 213` at every one of
the 512 addresses, for either strobe value. -/
theorem enable213_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable213 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 213)) := by
  unfold enable213
  bv_decide

/-- Gate enable of byte 214, extracted from `g_byte[214].g_used.u_cg`. -/
def enable214 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e214_0 := (addr1 == (214 : BitVec 9))
  let e214_1 := we1 && e214_0
  e214_1

/-- The extracted gate of byte 214 equals `we1 && addr1 == 214` at every one of
the 512 addresses, for either strobe value. -/
theorem enable214_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable214 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 214)) := by
  unfold enable214
  bv_decide

/-- Gate enable of byte 216, extracted from `g_byte[216].g_used.u_cg`. -/
def enable216 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e216_0 := (addr1 == (216 : BitVec 9))
  let e216_1 := we1 && e216_0
  e216_1

/-- The extracted gate of byte 216 equals `we1 && addr1 == 216` at every one of
the 512 addresses, for either strobe value. -/
theorem enable216_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable216 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 216)) := by
  unfold enable216
  bv_decide

/-- Gate enable of byte 217, extracted from `g_byte[217].g_used.u_cg`. -/
def enable217 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e217_0 := (addr1 == (217 : BitVec 9))
  let e217_1 := we1 && e217_0
  e217_1

/-- The extracted gate of byte 217 equals `we1 && addr1 == 217` at every one of
the 512 addresses, for either strobe value. -/
theorem enable217_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable217 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 217)) := by
  unfold enable217
  bv_decide

/-- Gate enable of byte 218, extracted from `g_byte[218].g_used.u_cg`. -/
def enable218 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e218_0 := (addr1 == (218 : BitVec 9))
  let e218_1 := we1 && e218_0
  e218_1

/-- The extracted gate of byte 218 equals `we1 && addr1 == 218` at every one of
the 512 addresses, for either strobe value. -/
theorem enable218_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable218 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 218)) := by
  unfold enable218
  bv_decide

/-- Gate enable of byte 219, extracted from `g_byte[219].g_used.u_cg`. -/
def enable219 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e219_0 := (addr1 == (219 : BitVec 9))
  let e219_1 := we1 && e219_0
  e219_1

/-- The extracted gate of byte 219 equals `we1 && addr1 == 219` at every one of
the 512 addresses, for either strobe value. -/
theorem enable219_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable219 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 219)) := by
  unfold enable219
  bv_decide

/-- Gate enable of byte 220, extracted from `g_byte[220].g_used.u_cg`. -/
def enable220 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e220_0 := (addr1 == (220 : BitVec 9))
  let e220_1 := we1 && e220_0
  e220_1

/-- The extracted gate of byte 220 equals `we1 && addr1 == 220` at every one of
the 512 addresses, for either strobe value. -/
theorem enable220_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable220 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 220)) := by
  unfold enable220
  bv_decide

/-- Gate enable of byte 221, extracted from `g_byte[221].g_used.u_cg`. -/
def enable221 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e221_0 := (addr1 == (221 : BitVec 9))
  let e221_1 := we1 && e221_0
  e221_1

/-- The extracted gate of byte 221 equals `we1 && addr1 == 221` at every one of
the 512 addresses, for either strobe value. -/
theorem enable221_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable221 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 221)) := by
  unfold enable221
  bv_decide

/-- Gate enable of byte 222, extracted from `g_byte[222].g_used.u_cg`. -/
def enable222 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e222_0 := (addr1 == (222 : BitVec 9))
  let e222_1 := we1 && e222_0
  e222_1

/-- The extracted gate of byte 222 equals `we1 && addr1 == 222` at every one of
the 512 addresses, for either strobe value. -/
theorem enable222_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable222 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 222)) := by
  unfold enable222
  bv_decide

/-- Gate enable of byte 256, extracted from `g_byte[256].g_used.u_cg`. -/
def enable256 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e256_0 := (addr1 == (256 : BitVec 9))
  let e256_1 := we1 && e256_0
  e256_1

/-- The extracted gate of byte 256 equals `we1 && addr1 == 256` at every one of
the 512 addresses, for either strobe value. -/
theorem enable256_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable256 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 256)) := by
  unfold enable256
  bv_decide

/-- Gate enable of byte 257, extracted from `g_byte[257].g_used.u_cg`. -/
def enable257 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e257_0 := (addr1 == (257 : BitVec 9))
  let e257_1 := we1 && e257_0
  e257_1

/-- The extracted gate of byte 257 equals `we1 && addr1 == 257` at every one of
the 512 addresses, for either strobe value. -/
theorem enable257_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable257 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 257)) := by
  unfold enable257
  bv_decide

/-- Gate enable of byte 260, extracted from `g_byte[260].g_used.u_cg`. -/
def enable260 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e260_0 := (addr1 == (260 : BitVec 9))
  let e260_1 := we1 && e260_0
  e260_1

/-- The extracted gate of byte 260 equals `we1 && addr1 == 260` at every one of
the 512 addresses, for either strobe value. -/
theorem enable260_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable260 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 260)) := by
  unfold enable260
  bv_decide

/-- Gate enable of byte 261, extracted from `g_byte[261].g_used.u_cg`. -/
def enable261 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e261_0 := (addr1 == (261 : BitVec 9))
  let e261_1 := we1 && e261_0
  e261_1

/-- The extracted gate of byte 261 equals `we1 && addr1 == 261` at every one of
the 512 addresses, for either strobe value. -/
theorem enable261_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable261 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 261)) := by
  unfold enable261
  bv_decide

/-- Gate enable of byte 262, extracted from `g_byte[262].g_used.u_cg`. -/
def enable262 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e262_0 := (addr1 == (262 : BitVec 9))
  let e262_1 := we1 && e262_0
  e262_1

/-- The extracted gate of byte 262 equals `we1 && addr1 == 262` at every one of
the 512 addresses, for either strobe value. -/
theorem enable262_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable262 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 262)) := by
  unfold enable262
  bv_decide

/-- Gate enable of byte 263, extracted from `g_byte[263].g_used.u_cg`. -/
def enable263 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e263_0 := (addr1 == (263 : BitVec 9))
  let e263_1 := we1 && e263_0
  e263_1

/-- The extracted gate of byte 263 equals `we1 && addr1 == 263` at every one of
the 512 addresses, for either strobe value. -/
theorem enable263_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable263 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 263)) := by
  unfold enable263
  bv_decide

/-- Gate enable of byte 264, extracted from `g_byte[264].g_used.u_cg`. -/
def enable264 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e264_0 := (addr1 == (264 : BitVec 9))
  let e264_1 := we1 && e264_0
  e264_1

/-- The extracted gate of byte 264 equals `we1 && addr1 == 264` at every one of
the 512 addresses, for either strobe value. -/
theorem enable264_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable264 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 264)) := by
  unfold enable264
  bv_decide

/-- Gate enable of byte 265, extracted from `g_byte[265].g_used.u_cg`. -/
def enable265 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e265_0 := (addr1 == (265 : BitVec 9))
  let e265_1 := we1 && e265_0
  e265_1

/-- The extracted gate of byte 265 equals `we1 && addr1 == 265` at every one of
the 512 addresses, for either strobe value. -/
theorem enable265_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable265 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 265)) := by
  unfold enable265
  bv_decide

/-- Gate enable of byte 266, extracted from `g_byte[266].g_used.u_cg`. -/
def enable266 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e266_0 := (addr1 == (266 : BitVec 9))
  let e266_1 := we1 && e266_0
  e266_1

/-- The extracted gate of byte 266 equals `we1 && addr1 == 266` at every one of
the 512 addresses, for either strobe value. -/
theorem enable266_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable266 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 266)) := by
  unfold enable266
  bv_decide

/-- Gate enable of byte 267, extracted from `g_byte[267].g_used.u_cg`. -/
def enable267 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e267_0 := (addr1 == (267 : BitVec 9))
  let e267_1 := we1 && e267_0
  e267_1

/-- The extracted gate of byte 267 equals `we1 && addr1 == 267` at every one of
the 512 addresses, for either strobe value. -/
theorem enable267_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable267 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 267)) := by
  unfold enable267
  bv_decide

/-- Gate enable of byte 272, extracted from `g_byte[272].g_used.u_cg`. -/
def enable272 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e272_0 := (addr1 == (272 : BitVec 9))
  let e272_1 := we1 && e272_0
  e272_1

/-- The extracted gate of byte 272 equals `we1 && addr1 == 272` at every one of
the 512 addresses, for either strobe value. -/
theorem enable272_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable272 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 272)) := by
  unfold enable272
  bv_decide

/-- Gate enable of byte 273, extracted from `g_byte[273].g_used.u_cg`. -/
def enable273 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e273_0 := (addr1 == (273 : BitVec 9))
  let e273_1 := we1 && e273_0
  e273_1

/-- The extracted gate of byte 273 equals `we1 && addr1 == 273` at every one of
the 512 addresses, for either strobe value. -/
theorem enable273_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable273 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 273)) := by
  unfold enable273
  bv_decide

/-- Gate enable of byte 276, extracted from `g_byte[276].g_used.u_cg`. -/
def enable276 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e276_0 := (addr1 == (276 : BitVec 9))
  let e276_1 := we1 && e276_0
  e276_1

/-- The extracted gate of byte 276 equals `we1 && addr1 == 276` at every one of
the 512 addresses, for either strobe value. -/
theorem enable276_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable276 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 276)) := by
  unfold enable276
  bv_decide

/-- Gate enable of byte 277, extracted from `g_byte[277].g_used.u_cg`. -/
def enable277 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e277_0 := (addr1 == (277 : BitVec 9))
  let e277_1 := we1 && e277_0
  e277_1

/-- The extracted gate of byte 277 equals `we1 && addr1 == 277` at every one of
the 512 addresses, for either strobe value. -/
theorem enable277_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable277 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 277)) := by
  unfold enable277
  bv_decide

/-- Gate enable of byte 278, extracted from `g_byte[278].g_used.u_cg`. -/
def enable278 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e278_0 := (addr1 == (278 : BitVec 9))
  let e278_1 := we1 && e278_0
  e278_1

/-- The extracted gate of byte 278 equals `we1 && addr1 == 278` at every one of
the 512 addresses, for either strobe value. -/
theorem enable278_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable278 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 278)) := by
  unfold enable278
  bv_decide

/-- Gate enable of byte 279, extracted from `g_byte[279].g_used.u_cg`. -/
def enable279 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e279_0 := (addr1 == (279 : BitVec 9))
  let e279_1 := we1 && e279_0
  e279_1

/-- The extracted gate of byte 279 equals `we1 && addr1 == 279` at every one of
the 512 addresses, for either strobe value. -/
theorem enable279_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable279 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 279)) := by
  unfold enable279
  bv_decide

/-- Gate enable of byte 280, extracted from `g_byte[280].g_used.u_cg`. -/
def enable280 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e280_0 := (addr1 == (280 : BitVec 9))
  let e280_1 := we1 && e280_0
  e280_1

/-- The extracted gate of byte 280 equals `we1 && addr1 == 280` at every one of
the 512 addresses, for either strobe value. -/
theorem enable280_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable280 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 280)) := by
  unfold enable280
  bv_decide

/-- Gate enable of byte 281, extracted from `g_byte[281].g_used.u_cg`. -/
def enable281 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e281_0 := (addr1 == (281 : BitVec 9))
  let e281_1 := we1 && e281_0
  e281_1

/-- The extracted gate of byte 281 equals `we1 && addr1 == 281` at every one of
the 512 addresses, for either strobe value. -/
theorem enable281_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable281 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 281)) := by
  unfold enable281
  bv_decide

/-- Gate enable of byte 282, extracted from `g_byte[282].g_used.u_cg`. -/
def enable282 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e282_0 := (addr1 == (282 : BitVec 9))
  let e282_1 := we1 && e282_0
  e282_1

/-- The extracted gate of byte 282 equals `we1 && addr1 == 282` at every one of
the 512 addresses, for either strobe value. -/
theorem enable282_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable282 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 282)) := by
  unfold enable282
  bv_decide

/-- Gate enable of byte 283, extracted from `g_byte[283].g_used.u_cg`. -/
def enable283 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e283_0 := (addr1 == (283 : BitVec 9))
  let e283_1 := we1 && e283_0
  e283_1

/-- The extracted gate of byte 283 equals `we1 && addr1 == 283` at every one of
the 512 addresses, for either strobe value. -/
theorem enable283_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable283 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 283)) := by
  unfold enable283
  bv_decide

/-- Gate enable of byte 288, extracted from `g_byte[288].g_used.u_cg`. -/
def enable288 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e288_0 := (addr1 == (288 : BitVec 9))
  let e288_1 := we1 && e288_0
  e288_1

/-- The extracted gate of byte 288 equals `we1 && addr1 == 288` at every one of
the 512 addresses, for either strobe value. -/
theorem enable288_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable288 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 288)) := by
  unfold enable288
  bv_decide

/-- Gate enable of byte 289, extracted from `g_byte[289].g_used.u_cg`. -/
def enable289 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e289_0 := (addr1 == (289 : BitVec 9))
  let e289_1 := we1 && e289_0
  e289_1

/-- The extracted gate of byte 289 equals `we1 && addr1 == 289` at every one of
the 512 addresses, for either strobe value. -/
theorem enable289_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable289 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 289)) := by
  unfold enable289
  bv_decide

/-- Gate enable of byte 292, extracted from `g_byte[292].g_used.u_cg`. -/
def enable292 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e292_0 := (addr1 == (292 : BitVec 9))
  let e292_1 := we1 && e292_0
  e292_1

/-- The extracted gate of byte 292 equals `we1 && addr1 == 292` at every one of
the 512 addresses, for either strobe value. -/
theorem enable292_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable292 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 292)) := by
  unfold enable292
  bv_decide

/-- Gate enable of byte 293, extracted from `g_byte[293].g_used.u_cg`. -/
def enable293 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e293_0 := (addr1 == (293 : BitVec 9))
  let e293_1 := we1 && e293_0
  e293_1

/-- The extracted gate of byte 293 equals `we1 && addr1 == 293` at every one of
the 512 addresses, for either strobe value. -/
theorem enable293_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable293 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 293)) := by
  unfold enable293
  bv_decide

/-- Gate enable of byte 294, extracted from `g_byte[294].g_used.u_cg`. -/
def enable294 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e294_0 := (addr1 == (294 : BitVec 9))
  let e294_1 := we1 && e294_0
  e294_1

/-- The extracted gate of byte 294 equals `we1 && addr1 == 294` at every one of
the 512 addresses, for either strobe value. -/
theorem enable294_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable294 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 294)) := by
  unfold enable294
  bv_decide

/-- Gate enable of byte 295, extracted from `g_byte[295].g_used.u_cg`. -/
def enable295 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e295_0 := (addr1 == (295 : BitVec 9))
  let e295_1 := we1 && e295_0
  e295_1

/-- The extracted gate of byte 295 equals `we1 && addr1 == 295` at every one of
the 512 addresses, for either strobe value. -/
theorem enable295_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable295 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 295)) := by
  unfold enable295
  bv_decide

/-- Gate enable of byte 296, extracted from `g_byte[296].g_used.u_cg`. -/
def enable296 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e296_0 := (addr1 == (296 : BitVec 9))
  let e296_1 := we1 && e296_0
  e296_1

/-- The extracted gate of byte 296 equals `we1 && addr1 == 296` at every one of
the 512 addresses, for either strobe value. -/
theorem enable296_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable296 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 296)) := by
  unfold enable296
  bv_decide

/-- Gate enable of byte 297, extracted from `g_byte[297].g_used.u_cg`. -/
def enable297 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e297_0 := (addr1 == (297 : BitVec 9))
  let e297_1 := we1 && e297_0
  e297_1

/-- The extracted gate of byte 297 equals `we1 && addr1 == 297` at every one of
the 512 addresses, for either strobe value. -/
theorem enable297_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable297 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 297)) := by
  unfold enable297
  bv_decide

/-- Gate enable of byte 298, extracted from `g_byte[298].g_used.u_cg`. -/
def enable298 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e298_0 := (addr1 == (298 : BitVec 9))
  let e298_1 := we1 && e298_0
  e298_1

/-- The extracted gate of byte 298 equals `we1 && addr1 == 298` at every one of
the 512 addresses, for either strobe value. -/
theorem enable298_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable298 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 298)) := by
  unfold enable298
  bv_decide

/-- Gate enable of byte 299, extracted from `g_byte[299].g_used.u_cg`. -/
def enable299 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e299_0 := (addr1 == (299 : BitVec 9))
  let e299_1 := we1 && e299_0
  e299_1

/-- The extracted gate of byte 299 equals `we1 && addr1 == 299` at every one of
the 512 addresses, for either strobe value. -/
theorem enable299_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable299 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 299)) := by
  unfold enable299
  bv_decide

/-- Gate enable of byte 304, extracted from `g_byte[304].g_used.u_cg`. -/
def enable304 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e304_0 := (addr1 == (304 : BitVec 9))
  let e304_1 := we1 && e304_0
  e304_1

/-- The extracted gate of byte 304 equals `we1 && addr1 == 304` at every one of
the 512 addresses, for either strobe value. -/
theorem enable304_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable304 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 304)) := by
  unfold enable304
  bv_decide

/-- Gate enable of byte 305, extracted from `g_byte[305].g_used.u_cg`. -/
def enable305 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e305_0 := (addr1 == (305 : BitVec 9))
  let e305_1 := we1 && e305_0
  e305_1

/-- The extracted gate of byte 305 equals `we1 && addr1 == 305` at every one of
the 512 addresses, for either strobe value. -/
theorem enable305_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable305 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 305)) := by
  unfold enable305
  bv_decide

/-- Gate enable of byte 308, extracted from `g_byte[308].g_used.u_cg`. -/
def enable308 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e308_0 := (addr1 == (308 : BitVec 9))
  let e308_1 := we1 && e308_0
  e308_1

/-- The extracted gate of byte 308 equals `we1 && addr1 == 308` at every one of
the 512 addresses, for either strobe value. -/
theorem enable308_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable308 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 308)) := by
  unfold enable308
  bv_decide

/-- Gate enable of byte 309, extracted from `g_byte[309].g_used.u_cg`. -/
def enable309 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e309_0 := (addr1 == (309 : BitVec 9))
  let e309_1 := we1 && e309_0
  e309_1

/-- The extracted gate of byte 309 equals `we1 && addr1 == 309` at every one of
the 512 addresses, for either strobe value. -/
theorem enable309_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable309 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 309)) := by
  unfold enable309
  bv_decide

/-- Gate enable of byte 310, extracted from `g_byte[310].g_used.u_cg`. -/
def enable310 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e310_0 := (addr1 == (310 : BitVec 9))
  let e310_1 := we1 && e310_0
  e310_1

/-- The extracted gate of byte 310 equals `we1 && addr1 == 310` at every one of
the 512 addresses, for either strobe value. -/
theorem enable310_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable310 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 310)) := by
  unfold enable310
  bv_decide

/-- Gate enable of byte 311, extracted from `g_byte[311].g_used.u_cg`. -/
def enable311 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e311_0 := (addr1 == (311 : BitVec 9))
  let e311_1 := we1 && e311_0
  e311_1

/-- The extracted gate of byte 311 equals `we1 && addr1 == 311` at every one of
the 512 addresses, for either strobe value. -/
theorem enable311_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable311 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 311)) := by
  unfold enable311
  bv_decide

/-- Gate enable of byte 312, extracted from `g_byte[312].g_used.u_cg`. -/
def enable312 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e312_0 := (addr1 == (312 : BitVec 9))
  let e312_1 := we1 && e312_0
  e312_1

/-- The extracted gate of byte 312 equals `we1 && addr1 == 312` at every one of
the 512 addresses, for either strobe value. -/
theorem enable312_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable312 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 312)) := by
  unfold enable312
  bv_decide

/-- Gate enable of byte 313, extracted from `g_byte[313].g_used.u_cg`. -/
def enable313 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e313_0 := (addr1 == (313 : BitVec 9))
  let e313_1 := we1 && e313_0
  e313_1

/-- The extracted gate of byte 313 equals `we1 && addr1 == 313` at every one of
the 512 addresses, for either strobe value. -/
theorem enable313_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable313 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 313)) := by
  unfold enable313
  bv_decide

/-- Gate enable of byte 314, extracted from `g_byte[314].g_used.u_cg`. -/
def enable314 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e314_0 := (addr1 == (314 : BitVec 9))
  let e314_1 := we1 && e314_0
  e314_1

/-- The extracted gate of byte 314 equals `we1 && addr1 == 314` at every one of
the 512 addresses, for either strobe value. -/
theorem enable314_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable314 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 314)) := by
  unfold enable314
  bv_decide

/-- Gate enable of byte 315, extracted from `g_byte[315].g_used.u_cg`. -/
def enable315 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e315_0 := (addr1 == (315 : BitVec 9))
  let e315_1 := we1 && e315_0
  e315_1

/-- The extracted gate of byte 315 equals `we1 && addr1 == 315` at every one of
the 512 addresses, for either strobe value. -/
theorem enable315_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable315 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 315)) := by
  unfold enable315
  bv_decide

/-- Gate enable of byte 320, extracted from `g_byte[320].g_used.u_cg`. -/
def enable320 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e320_0 := (addr1 == (320 : BitVec 9))
  let e320_1 := we1 && e320_0
  e320_1

/-- The extracted gate of byte 320 equals `we1 && addr1 == 320` at every one of
the 512 addresses, for either strobe value. -/
theorem enable320_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable320 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 320)) := by
  unfold enable320
  bv_decide

/-- Gate enable of byte 321, extracted from `g_byte[321].g_used.u_cg`. -/
def enable321 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e321_0 := (addr1 == (321 : BitVec 9))
  let e321_1 := we1 && e321_0
  e321_1

/-- The extracted gate of byte 321 equals `we1 && addr1 == 321` at every one of
the 512 addresses, for either strobe value. -/
theorem enable321_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable321 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 321)) := by
  unfold enable321
  bv_decide

/-- Gate enable of byte 324, extracted from `g_byte[324].g_used.u_cg`. -/
def enable324 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e324_0 := (addr1 == (324 : BitVec 9))
  let e324_1 := we1 && e324_0
  e324_1

/-- The extracted gate of byte 324 equals `we1 && addr1 == 324` at every one of
the 512 addresses, for either strobe value. -/
theorem enable324_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable324 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 324)) := by
  unfold enable324
  bv_decide

/-- Gate enable of byte 325, extracted from `g_byte[325].g_used.u_cg`. -/
def enable325 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e325_0 := (addr1 == (325 : BitVec 9))
  let e325_1 := we1 && e325_0
  e325_1

/-- The extracted gate of byte 325 equals `we1 && addr1 == 325` at every one of
the 512 addresses, for either strobe value. -/
theorem enable325_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable325 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 325)) := by
  unfold enable325
  bv_decide

/-- Gate enable of byte 326, extracted from `g_byte[326].g_used.u_cg`. -/
def enable326 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e326_0 := (addr1 == (326 : BitVec 9))
  let e326_1 := we1 && e326_0
  e326_1

/-- The extracted gate of byte 326 equals `we1 && addr1 == 326` at every one of
the 512 addresses, for either strobe value. -/
theorem enable326_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable326 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 326)) := by
  unfold enable326
  bv_decide

/-- Gate enable of byte 327, extracted from `g_byte[327].g_used.u_cg`. -/
def enable327 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e327_0 := (addr1 == (327 : BitVec 9))
  let e327_1 := we1 && e327_0
  e327_1

/-- The extracted gate of byte 327 equals `we1 && addr1 == 327` at every one of
the 512 addresses, for either strobe value. -/
theorem enable327_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable327 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 327)) := by
  unfold enable327
  bv_decide

/-- Gate enable of byte 328, extracted from `g_byte[328].g_used.u_cg`. -/
def enable328 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e328_0 := (addr1 == (328 : BitVec 9))
  let e328_1 := we1 && e328_0
  e328_1

/-- The extracted gate of byte 328 equals `we1 && addr1 == 328` at every one of
the 512 addresses, for either strobe value. -/
theorem enable328_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable328 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 328)) := by
  unfold enable328
  bv_decide

/-- Gate enable of byte 329, extracted from `g_byte[329].g_used.u_cg`. -/
def enable329 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e329_0 := (addr1 == (329 : BitVec 9))
  let e329_1 := we1 && e329_0
  e329_1

/-- The extracted gate of byte 329 equals `we1 && addr1 == 329` at every one of
the 512 addresses, for either strobe value. -/
theorem enable329_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable329 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 329)) := by
  unfold enable329
  bv_decide

/-- Gate enable of byte 330, extracted from `g_byte[330].g_used.u_cg`. -/
def enable330 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e330_0 := (addr1 == (330 : BitVec 9))
  let e330_1 := we1 && e330_0
  e330_1

/-- The extracted gate of byte 330 equals `we1 && addr1 == 330` at every one of
the 512 addresses, for either strobe value. -/
theorem enable330_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable330 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 330)) := by
  unfold enable330
  bv_decide

/-- Gate enable of byte 331, extracted from `g_byte[331].g_used.u_cg`. -/
def enable331 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e331_0 := (addr1 == (331 : BitVec 9))
  let e331_1 := we1 && e331_0
  e331_1

/-- The extracted gate of byte 331 equals `we1 && addr1 == 331` at every one of
the 512 addresses, for either strobe value. -/
theorem enable331_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable331 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 331)) := by
  unfold enable331
  bv_decide

/-- Gate enable of byte 336, extracted from `g_byte[336].g_used.u_cg`. -/
def enable336 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e336_0 := (addr1 == (336 : BitVec 9))
  let e336_1 := we1 && e336_0
  e336_1

/-- The extracted gate of byte 336 equals `we1 && addr1 == 336` at every one of
the 512 addresses, for either strobe value. -/
theorem enable336_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable336 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 336)) := by
  unfold enable336
  bv_decide

/-- Gate enable of byte 337, extracted from `g_byte[337].g_used.u_cg`. -/
def enable337 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e337_0 := (addr1 == (337 : BitVec 9))
  let e337_1 := we1 && e337_0
  e337_1

/-- The extracted gate of byte 337 equals `we1 && addr1 == 337` at every one of
the 512 addresses, for either strobe value. -/
theorem enable337_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable337 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 337)) := by
  unfold enable337
  bv_decide

/-- Gate enable of byte 340, extracted from `g_byte[340].g_used.u_cg`. -/
def enable340 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e340_0 := (addr1 == (340 : BitVec 9))
  let e340_1 := we1 && e340_0
  e340_1

/-- The extracted gate of byte 340 equals `we1 && addr1 == 340` at every one of
the 512 addresses, for either strobe value. -/
theorem enable340_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable340 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 340)) := by
  unfold enable340
  bv_decide

/-- Gate enable of byte 341, extracted from `g_byte[341].g_used.u_cg`. -/
def enable341 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e341_0 := (addr1 == (341 : BitVec 9))
  let e341_1 := we1 && e341_0
  e341_1

/-- The extracted gate of byte 341 equals `we1 && addr1 == 341` at every one of
the 512 addresses, for either strobe value. -/
theorem enable341_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable341 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 341)) := by
  unfold enable341
  bv_decide

/-- Gate enable of byte 342, extracted from `g_byte[342].g_used.u_cg`. -/
def enable342 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e342_0 := (addr1 == (342 : BitVec 9))
  let e342_1 := we1 && e342_0
  e342_1

/-- The extracted gate of byte 342 equals `we1 && addr1 == 342` at every one of
the 512 addresses, for either strobe value. -/
theorem enable342_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable342 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 342)) := by
  unfold enable342
  bv_decide

/-- Gate enable of byte 343, extracted from `g_byte[343].g_used.u_cg`. -/
def enable343 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e343_0 := (addr1 == (343 : BitVec 9))
  let e343_1 := we1 && e343_0
  e343_1

/-- The extracted gate of byte 343 equals `we1 && addr1 == 343` at every one of
the 512 addresses, for either strobe value. -/
theorem enable343_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable343 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 343)) := by
  unfold enable343
  bv_decide

/-- Gate enable of byte 344, extracted from `g_byte[344].g_used.u_cg`. -/
def enable344 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e344_0 := (addr1 == (344 : BitVec 9))
  let e344_1 := we1 && e344_0
  e344_1

/-- The extracted gate of byte 344 equals `we1 && addr1 == 344` at every one of
the 512 addresses, for either strobe value. -/
theorem enable344_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable344 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 344)) := by
  unfold enable344
  bv_decide

/-- Gate enable of byte 345, extracted from `g_byte[345].g_used.u_cg`. -/
def enable345 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e345_0 := (addr1 == (345 : BitVec 9))
  let e345_1 := we1 && e345_0
  e345_1

/-- The extracted gate of byte 345 equals `we1 && addr1 == 345` at every one of
the 512 addresses, for either strobe value. -/
theorem enable345_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable345 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 345)) := by
  unfold enable345
  bv_decide

/-- Gate enable of byte 346, extracted from `g_byte[346].g_used.u_cg`. -/
def enable346 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e346_0 := (addr1 == (346 : BitVec 9))
  let e346_1 := we1 && e346_0
  e346_1

/-- The extracted gate of byte 346 equals `we1 && addr1 == 346` at every one of
the 512 addresses, for either strobe value. -/
theorem enable346_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable346 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 346)) := by
  unfold enable346
  bv_decide

/-- Gate enable of byte 347, extracted from `g_byte[347].g_used.u_cg`. -/
def enable347 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e347_0 := (addr1 == (347 : BitVec 9))
  let e347_1 := we1 && e347_0
  e347_1

/-- The extracted gate of byte 347 equals `we1 && addr1 == 347` at every one of
the 512 addresses, for either strobe value. -/
theorem enable347_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable347 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 347)) := by
  unfold enable347
  bv_decide

/-- Gate enable of byte 352, extracted from `g_byte[352].g_used.u_cg`. -/
def enable352 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e352_0 := (addr1 == (352 : BitVec 9))
  let e352_1 := we1 && e352_0
  e352_1

/-- The extracted gate of byte 352 equals `we1 && addr1 == 352` at every one of
the 512 addresses, for either strobe value. -/
theorem enable352_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable352 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 352)) := by
  unfold enable352
  bv_decide

/-- Gate enable of byte 353, extracted from `g_byte[353].g_used.u_cg`. -/
def enable353 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e353_0 := (addr1 == (353 : BitVec 9))
  let e353_1 := we1 && e353_0
  e353_1

/-- The extracted gate of byte 353 equals `we1 && addr1 == 353` at every one of
the 512 addresses, for either strobe value. -/
theorem enable353_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable353 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 353)) := by
  unfold enable353
  bv_decide

/-- Gate enable of byte 356, extracted from `g_byte[356].g_used.u_cg`. -/
def enable356 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e356_0 := (addr1 == (356 : BitVec 9))
  let e356_1 := we1 && e356_0
  e356_1

/-- The extracted gate of byte 356 equals `we1 && addr1 == 356` at every one of
the 512 addresses, for either strobe value. -/
theorem enable356_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable356 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 356)) := by
  unfold enable356
  bv_decide

/-- Gate enable of byte 357, extracted from `g_byte[357].g_used.u_cg`. -/
def enable357 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e357_0 := (addr1 == (357 : BitVec 9))
  let e357_1 := we1 && e357_0
  e357_1

/-- The extracted gate of byte 357 equals `we1 && addr1 == 357` at every one of
the 512 addresses, for either strobe value. -/
theorem enable357_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable357 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 357)) := by
  unfold enable357
  bv_decide

/-- Gate enable of byte 358, extracted from `g_byte[358].g_used.u_cg`. -/
def enable358 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e358_0 := (addr1 == (358 : BitVec 9))
  let e358_1 := we1 && e358_0
  e358_1

/-- The extracted gate of byte 358 equals `we1 && addr1 == 358` at every one of
the 512 addresses, for either strobe value. -/
theorem enable358_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable358 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 358)) := by
  unfold enable358
  bv_decide

/-- Gate enable of byte 359, extracted from `g_byte[359].g_used.u_cg`. -/
def enable359 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e359_0 := (addr1 == (359 : BitVec 9))
  let e359_1 := we1 && e359_0
  e359_1

/-- The extracted gate of byte 359 equals `we1 && addr1 == 359` at every one of
the 512 addresses, for either strobe value. -/
theorem enable359_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable359 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 359)) := by
  unfold enable359
  bv_decide

/-- Gate enable of byte 360, extracted from `g_byte[360].g_used.u_cg`. -/
def enable360 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e360_0 := (addr1 == (360 : BitVec 9))
  let e360_1 := we1 && e360_0
  e360_1

/-- The extracted gate of byte 360 equals `we1 && addr1 == 360` at every one of
the 512 addresses, for either strobe value. -/
theorem enable360_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable360 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 360)) := by
  unfold enable360
  bv_decide

/-- Gate enable of byte 361, extracted from `g_byte[361].g_used.u_cg`. -/
def enable361 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e361_0 := (addr1 == (361 : BitVec 9))
  let e361_1 := we1 && e361_0
  e361_1

/-- The extracted gate of byte 361 equals `we1 && addr1 == 361` at every one of
the 512 addresses, for either strobe value. -/
theorem enable361_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable361 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 361)) := by
  unfold enable361
  bv_decide

/-- Gate enable of byte 362, extracted from `g_byte[362].g_used.u_cg`. -/
def enable362 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e362_0 := (addr1 == (362 : BitVec 9))
  let e362_1 := we1 && e362_0
  e362_1

/-- The extracted gate of byte 362 equals `we1 && addr1 == 362` at every one of
the 512 addresses, for either strobe value. -/
theorem enable362_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable362 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 362)) := by
  unfold enable362
  bv_decide

/-- Gate enable of byte 363, extracted from `g_byte[363].g_used.u_cg`. -/
def enable363 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e363_0 := (addr1 == (363 : BitVec 9))
  let e363_1 := we1 && e363_0
  e363_1

/-- The extracted gate of byte 363 equals `we1 && addr1 == 363` at every one of
the 512 addresses, for either strobe value. -/
theorem enable363_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable363 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 363)) := by
  unfold enable363
  bv_decide

/-- Gate enable of byte 368, extracted from `g_byte[368].g_used.u_cg`. -/
def enable368 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e368_0 := (addr1 == (368 : BitVec 9))
  let e368_1 := we1 && e368_0
  e368_1

/-- The extracted gate of byte 368 equals `we1 && addr1 == 368` at every one of
the 512 addresses, for either strobe value. -/
theorem enable368_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable368 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 368)) := by
  unfold enable368
  bv_decide

/-- Gate enable of byte 369, extracted from `g_byte[369].g_used.u_cg`. -/
def enable369 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e369_0 := (addr1 == (369 : BitVec 9))
  let e369_1 := we1 && e369_0
  e369_1

/-- The extracted gate of byte 369 equals `we1 && addr1 == 369` at every one of
the 512 addresses, for either strobe value. -/
theorem enable369_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable369 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 369)) := by
  unfold enable369
  bv_decide

/-- Gate enable of byte 372, extracted from `g_byte[372].g_used.u_cg`. -/
def enable372 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e372_0 := (addr1 == (372 : BitVec 9))
  let e372_1 := we1 && e372_0
  e372_1

/-- The extracted gate of byte 372 equals `we1 && addr1 == 372` at every one of
the 512 addresses, for either strobe value. -/
theorem enable372_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable372 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 372)) := by
  unfold enable372
  bv_decide

/-- Gate enable of byte 373, extracted from `g_byte[373].g_used.u_cg`. -/
def enable373 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e373_0 := (addr1 == (373 : BitVec 9))
  let e373_1 := we1 && e373_0
  e373_1

/-- The extracted gate of byte 373 equals `we1 && addr1 == 373` at every one of
the 512 addresses, for either strobe value. -/
theorem enable373_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable373 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 373)) := by
  unfold enable373
  bv_decide

/-- Gate enable of byte 374, extracted from `g_byte[374].g_used.u_cg`. -/
def enable374 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e374_0 := (addr1 == (374 : BitVec 9))
  let e374_1 := we1 && e374_0
  e374_1

/-- The extracted gate of byte 374 equals `we1 && addr1 == 374` at every one of
the 512 addresses, for either strobe value. -/
theorem enable374_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable374 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 374)) := by
  unfold enable374
  bv_decide

/-- Gate enable of byte 375, extracted from `g_byte[375].g_used.u_cg`. -/
def enable375 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e375_0 := (addr1 == (375 : BitVec 9))
  let e375_1 := we1 && e375_0
  e375_1

/-- The extracted gate of byte 375 equals `we1 && addr1 == 375` at every one of
the 512 addresses, for either strobe value. -/
theorem enable375_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable375 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 375)) := by
  unfold enable375
  bv_decide

/-- Gate enable of byte 376, extracted from `g_byte[376].g_used.u_cg`. -/
def enable376 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e376_0 := (addr1 == (376 : BitVec 9))
  let e376_1 := we1 && e376_0
  e376_1

/-- The extracted gate of byte 376 equals `we1 && addr1 == 376` at every one of
the 512 addresses, for either strobe value. -/
theorem enable376_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable376 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 376)) := by
  unfold enable376
  bv_decide

/-- Gate enable of byte 377, extracted from `g_byte[377].g_used.u_cg`. -/
def enable377 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e377_0 := (addr1 == (377 : BitVec 9))
  let e377_1 := we1 && e377_0
  e377_1

/-- The extracted gate of byte 377 equals `we1 && addr1 == 377` at every one of
the 512 addresses, for either strobe value. -/
theorem enable377_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable377 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 377)) := by
  unfold enable377
  bv_decide

/-- Gate enable of byte 378, extracted from `g_byte[378].g_used.u_cg`. -/
def enable378 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e378_0 := (addr1 == (378 : BitVec 9))
  let e378_1 := we1 && e378_0
  e378_1

/-- The extracted gate of byte 378 equals `we1 && addr1 == 378` at every one of
the 512 addresses, for either strobe value. -/
theorem enable378_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable378 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 378)) := by
  unfold enable378
  bv_decide

/-- Gate enable of byte 379, extracted from `g_byte[379].g_used.u_cg`. -/
def enable379 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e379_0 := (addr1 == (379 : BitVec 9))
  let e379_1 := we1 && e379_0
  e379_1

/-- The extracted gate of byte 379 equals `we1 && addr1 == 379` at every one of
the 512 addresses, for either strobe value. -/
theorem enable379_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable379 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 379)) := by
  unfold enable379
  bv_decide

/-- Gate enable of byte 384, extracted from `g_byte[384].g_used.u_cg`. -/
def enable384 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e384_0 := (addr1 == (384 : BitVec 9))
  let e384_1 := we1 && e384_0
  e384_1

/-- The extracted gate of byte 384 equals `we1 && addr1 == 384` at every one of
the 512 addresses, for either strobe value. -/
theorem enable384_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable384 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 384)) := by
  unfold enable384
  bv_decide

/-- Gate enable of byte 385, extracted from `g_byte[385].g_used.u_cg`. -/
def enable385 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e385_0 := (addr1 == (385 : BitVec 9))
  let e385_1 := we1 && e385_0
  e385_1

/-- The extracted gate of byte 385 equals `we1 && addr1 == 385` at every one of
the 512 addresses, for either strobe value. -/
theorem enable385_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable385 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 385)) := by
  unfold enable385
  bv_decide

/-- Gate enable of byte 388, extracted from `g_byte[388].g_used.u_cg`. -/
def enable388 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e388_0 := (addr1 == (388 : BitVec 9))
  let e388_1 := we1 && e388_0
  e388_1

/-- The extracted gate of byte 388 equals `we1 && addr1 == 388` at every one of
the 512 addresses, for either strobe value. -/
theorem enable388_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable388 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 388)) := by
  unfold enable388
  bv_decide

/-- Gate enable of byte 389, extracted from `g_byte[389].g_used.u_cg`. -/
def enable389 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e389_0 := (addr1 == (389 : BitVec 9))
  let e389_1 := we1 && e389_0
  e389_1

/-- The extracted gate of byte 389 equals `we1 && addr1 == 389` at every one of
the 512 addresses, for either strobe value. -/
theorem enable389_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable389 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 389)) := by
  unfold enable389
  bv_decide

/-- Gate enable of byte 390, extracted from `g_byte[390].g_used.u_cg`. -/
def enable390 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e390_0 := (addr1 == (390 : BitVec 9))
  let e390_1 := we1 && e390_0
  e390_1

/-- The extracted gate of byte 390 equals `we1 && addr1 == 390` at every one of
the 512 addresses, for either strobe value. -/
theorem enable390_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable390 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 390)) := by
  unfold enable390
  bv_decide

/-- Gate enable of byte 391, extracted from `g_byte[391].g_used.u_cg`. -/
def enable391 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e391_0 := (addr1 == (391 : BitVec 9))
  let e391_1 := we1 && e391_0
  e391_1

/-- The extracted gate of byte 391 equals `we1 && addr1 == 391` at every one of
the 512 addresses, for either strobe value. -/
theorem enable391_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable391 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 391)) := by
  unfold enable391
  bv_decide

/-- Gate enable of byte 400, extracted from `g_byte[400].g_used.u_cg`. -/
def enable400 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e400_0 := (addr1 == (400 : BitVec 9))
  let e400_1 := we1 && e400_0
  e400_1

/-- The extracted gate of byte 400 equals `we1 && addr1 == 400` at every one of
the 512 addresses, for either strobe value. -/
theorem enable400_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable400 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 400)) := by
  unfold enable400
  bv_decide

/-- Gate enable of byte 401, extracted from `g_byte[401].g_used.u_cg`. -/
def enable401 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e401_0 := (addr1 == (401 : BitVec 9))
  let e401_1 := we1 && e401_0
  e401_1

/-- The extracted gate of byte 401 equals `we1 && addr1 == 401` at every one of
the 512 addresses, for either strobe value. -/
theorem enable401_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable401 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 401)) := by
  unfold enable401
  bv_decide

/-- Gate enable of byte 404, extracted from `g_byte[404].g_used.u_cg`. -/
def enable404 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e404_0 := (addr1 == (404 : BitVec 9))
  let e404_1 := we1 && e404_0
  e404_1

/-- The extracted gate of byte 404 equals `we1 && addr1 == 404` at every one of
the 512 addresses, for either strobe value. -/
theorem enable404_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable404 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 404)) := by
  unfold enable404
  bv_decide

/-- Gate enable of byte 405, extracted from `g_byte[405].g_used.u_cg`. -/
def enable405 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e405_0 := (addr1 == (405 : BitVec 9))
  let e405_1 := we1 && e405_0
  e405_1

/-- The extracted gate of byte 405 equals `we1 && addr1 == 405` at every one of
the 512 addresses, for either strobe value. -/
theorem enable405_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable405 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 405)) := by
  unfold enable405
  bv_decide

/-- Gate enable of byte 406, extracted from `g_byte[406].g_used.u_cg`. -/
def enable406 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e406_0 := (addr1 == (406 : BitVec 9))
  let e406_1 := we1 && e406_0
  e406_1

/-- The extracted gate of byte 406 equals `we1 && addr1 == 406` at every one of
the 512 addresses, for either strobe value. -/
theorem enable406_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable406 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 406)) := by
  unfold enable406
  bv_decide

/-- Gate enable of byte 407, extracted from `g_byte[407].g_used.u_cg`. -/
def enable407 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e407_0 := (addr1 == (407 : BitVec 9))
  let e407_1 := we1 && e407_0
  e407_1

/-- The extracted gate of byte 407 equals `we1 && addr1 == 407` at every one of
the 512 addresses, for either strobe value. -/
theorem enable407_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable407 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 407)) := by
  unfold enable407
  bv_decide

/-- Gate enable of byte 416, extracted from `g_byte[416].g_used.u_cg`. -/
def enable416 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e416_0 := (addr1 == (416 : BitVec 9))
  let e416_1 := we1 && e416_0
  e416_1

/-- The extracted gate of byte 416 equals `we1 && addr1 == 416` at every one of
the 512 addresses, for either strobe value. -/
theorem enable416_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable416 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 416)) := by
  unfold enable416
  bv_decide

/-- Gate enable of byte 417, extracted from `g_byte[417].g_used.u_cg`. -/
def enable417 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e417_0 := (addr1 == (417 : BitVec 9))
  let e417_1 := we1 && e417_0
  e417_1

/-- The extracted gate of byte 417 equals `we1 && addr1 == 417` at every one of
the 512 addresses, for either strobe value. -/
theorem enable417_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable417 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 417)) := by
  unfold enable417
  bv_decide

/-- Gate enable of byte 420, extracted from `g_byte[420].g_used.u_cg`. -/
def enable420 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e420_0 := (addr1 == (420 : BitVec 9))
  let e420_1 := we1 && e420_0
  e420_1

/-- The extracted gate of byte 420 equals `we1 && addr1 == 420` at every one of
the 512 addresses, for either strobe value. -/
theorem enable420_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable420 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 420)) := by
  unfold enable420
  bv_decide

/-- Gate enable of byte 421, extracted from `g_byte[421].g_used.u_cg`. -/
def enable421 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e421_0 := (addr1 == (421 : BitVec 9))
  let e421_1 := we1 && e421_0
  e421_1

/-- The extracted gate of byte 421 equals `we1 && addr1 == 421` at every one of
the 512 addresses, for either strobe value. -/
theorem enable421_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable421 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 421)) := by
  unfold enable421
  bv_decide

/-- Gate enable of byte 422, extracted from `g_byte[422].g_used.u_cg`. -/
def enable422 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e422_0 := (addr1 == (422 : BitVec 9))
  let e422_1 := we1 && e422_0
  e422_1

/-- The extracted gate of byte 422 equals `we1 && addr1 == 422` at every one of
the 512 addresses, for either strobe value. -/
theorem enable422_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable422 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 422)) := by
  unfold enable422
  bv_decide

/-- Gate enable of byte 423, extracted from `g_byte[423].g_used.u_cg`. -/
def enable423 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e423_0 := (addr1 == (423 : BitVec 9))
  let e423_1 := we1 && e423_0
  e423_1

/-- The extracted gate of byte 423 equals `we1 && addr1 == 423` at every one of
the 512 addresses, for either strobe value. -/
theorem enable423_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable423 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 423)) := by
  unfold enable423
  bv_decide

/-- Gate enable of byte 432, extracted from `g_byte[432].g_used.u_cg`. -/
def enable432 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e432_0 := (addr1 == (432 : BitVec 9))
  let e432_1 := we1 && e432_0
  e432_1

/-- The extracted gate of byte 432 equals `we1 && addr1 == 432` at every one of
the 512 addresses, for either strobe value. -/
theorem enable432_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable432 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 432)) := by
  unfold enable432
  bv_decide

/-- Gate enable of byte 433, extracted from `g_byte[433].g_used.u_cg`. -/
def enable433 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e433_0 := (addr1 == (433 : BitVec 9))
  let e433_1 := we1 && e433_0
  e433_1

/-- The extracted gate of byte 433 equals `we1 && addr1 == 433` at every one of
the 512 addresses, for either strobe value. -/
theorem enable433_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable433 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 433)) := by
  unfold enable433
  bv_decide

/-- Gate enable of byte 436, extracted from `g_byte[436].g_used.u_cg`. -/
def enable436 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e436_0 := (addr1 == (436 : BitVec 9))
  let e436_1 := we1 && e436_0
  e436_1

/-- The extracted gate of byte 436 equals `we1 && addr1 == 436` at every one of
the 512 addresses, for either strobe value. -/
theorem enable436_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable436 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 436)) := by
  unfold enable436
  bv_decide

/-- Gate enable of byte 437, extracted from `g_byte[437].g_used.u_cg`. -/
def enable437 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e437_0 := (addr1 == (437 : BitVec 9))
  let e437_1 := we1 && e437_0
  e437_1

/-- The extracted gate of byte 437 equals `we1 && addr1 == 437` at every one of
the 512 addresses, for either strobe value. -/
theorem enable437_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable437 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 437)) := by
  unfold enable437
  bv_decide

/-- Gate enable of byte 438, extracted from `g_byte[438].g_used.u_cg`. -/
def enable438 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e438_0 := (addr1 == (438 : BitVec 9))
  let e438_1 := we1 && e438_0
  e438_1

/-- The extracted gate of byte 438 equals `we1 && addr1 == 438` at every one of
the 512 addresses, for either strobe value. -/
theorem enable438_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable438 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 438)) := by
  unfold enable438
  bv_decide

/-- Gate enable of byte 439, extracted from `g_byte[439].g_used.u_cg`. -/
def enable439 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e439_0 := (addr1 == (439 : BitVec 9))
  let e439_1 := we1 && e439_0
  e439_1

/-- The extracted gate of byte 439 equals `we1 && addr1 == 439` at every one of
the 512 addresses, for either strobe value. -/
theorem enable439_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable439 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 439)) := by
  unfold enable439
  bv_decide

/-- Gate enable of byte 448, extracted from `g_byte[448].g_used.u_cg`. -/
def enable448 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e448_0 := (addr1 == (448 : BitVec 9))
  let e448_1 := we1 && e448_0
  e448_1

/-- The extracted gate of byte 448 equals `we1 && addr1 == 448` at every one of
the 512 addresses, for either strobe value. -/
theorem enable448_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable448 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 448)) := by
  unfold enable448
  bv_decide

/-- Gate enable of byte 449, extracted from `g_byte[449].g_used.u_cg`. -/
def enable449 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e449_0 := (addr1 == (449 : BitVec 9))
  let e449_1 := we1 && e449_0
  e449_1

/-- The extracted gate of byte 449 equals `we1 && addr1 == 449` at every one of
the 512 addresses, for either strobe value. -/
theorem enable449_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable449 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 449)) := by
  unfold enable449
  bv_decide

/-- Gate enable of byte 452, extracted from `g_byte[452].g_used.u_cg`. -/
def enable452 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e452_0 := (addr1 == (452 : BitVec 9))
  let e452_1 := we1 && e452_0
  e452_1

/-- The extracted gate of byte 452 equals `we1 && addr1 == 452` at every one of
the 512 addresses, for either strobe value. -/
theorem enable452_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable452 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 452)) := by
  unfold enable452
  bv_decide

/-- Gate enable of byte 453, extracted from `g_byte[453].g_used.u_cg`. -/
def enable453 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e453_0 := (addr1 == (453 : BitVec 9))
  let e453_1 := we1 && e453_0
  e453_1

/-- The extracted gate of byte 453 equals `we1 && addr1 == 453` at every one of
the 512 addresses, for either strobe value. -/
theorem enable453_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable453 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 453)) := by
  unfold enable453
  bv_decide

/-- Gate enable of byte 454, extracted from `g_byte[454].g_used.u_cg`. -/
def enable454 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e454_0 := (addr1 == (454 : BitVec 9))
  let e454_1 := we1 && e454_0
  e454_1

/-- The extracted gate of byte 454 equals `we1 && addr1 == 454` at every one of
the 512 addresses, for either strobe value. -/
theorem enable454_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable454 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 454)) := by
  unfold enable454
  bv_decide

/-- Gate enable of byte 455, extracted from `g_byte[455].g_used.u_cg`. -/
def enable455 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e455_0 := (addr1 == (455 : BitVec 9))
  let e455_1 := we1 && e455_0
  e455_1

/-- The extracted gate of byte 455 equals `we1 && addr1 == 455` at every one of
the 512 addresses, for either strobe value. -/
theorem enable455_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable455 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 455)) := by
  unfold enable455
  bv_decide

/-- Gate enable of byte 464, extracted from `g_byte[464].g_used.u_cg`. -/
def enable464 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e464_0 := (addr1 == (464 : BitVec 9))
  let e464_1 := we1 && e464_0
  e464_1

/-- The extracted gate of byte 464 equals `we1 && addr1 == 464` at every one of
the 512 addresses, for either strobe value. -/
theorem enable464_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable464 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 464)) := by
  unfold enable464
  bv_decide

/-- Gate enable of byte 465, extracted from `g_byte[465].g_used.u_cg`. -/
def enable465 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e465_0 := (addr1 == (465 : BitVec 9))
  let e465_1 := we1 && e465_0
  e465_1

/-- The extracted gate of byte 465 equals `we1 && addr1 == 465` at every one of
the 512 addresses, for either strobe value. -/
theorem enable465_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable465 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 465)) := by
  unfold enable465
  bv_decide

/-- Gate enable of byte 468, extracted from `g_byte[468].g_used.u_cg`. -/
def enable468 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e468_0 := (addr1 == (468 : BitVec 9))
  let e468_1 := we1 && e468_0
  e468_1

/-- The extracted gate of byte 468 equals `we1 && addr1 == 468` at every one of
the 512 addresses, for either strobe value. -/
theorem enable468_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable468 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 468)) := by
  unfold enable468
  bv_decide

/-- Gate enable of byte 469, extracted from `g_byte[469].g_used.u_cg`. -/
def enable469 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e469_0 := (addr1 == (469 : BitVec 9))
  let e469_1 := we1 && e469_0
  e469_1

/-- The extracted gate of byte 469 equals `we1 && addr1 == 469` at every one of
the 512 addresses, for either strobe value. -/
theorem enable469_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable469 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 469)) := by
  unfold enable469
  bv_decide

/-- Gate enable of byte 470, extracted from `g_byte[470].g_used.u_cg`. -/
def enable470 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e470_0 := (addr1 == (470 : BitVec 9))
  let e470_1 := we1 && e470_0
  e470_1

/-- The extracted gate of byte 470 equals `we1 && addr1 == 470` at every one of
the 512 addresses, for either strobe value. -/
theorem enable470_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable470 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 470)) := by
  unfold enable470
  bv_decide

/-- Gate enable of byte 471, extracted from `g_byte[471].g_used.u_cg`. -/
def enable471 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let e471_0 := (addr1 == (471 : BitVec 9))
  let e471_1 := we1 && e471_0
  e471_1

/-- The extracted gate of byte 471 equals `we1 && addr1 == 471` at every one of
the 512 addresses, for either strobe value. -/
theorem enable471_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable471 we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 471)) := by
  unfold enable471
  bv_decide

/-- Every live byte of the elaborated bank: its offset, its extracted enable
cone and its per-byte equivalence. -/
def gates : List Gate :=
  [    ⟨0, by decide, enable0, enable0_spec⟩,
    ⟨1, by decide, enable1, enable1_spec⟩,
    ⟨2, by decide, enable2, enable2_spec⟩,
    ⟨3, by decide, enable3, enable3_spec⟩,
    ⟨4, by decide, enable4, enable4_spec⟩,
    ⟨5, by decide, enable5, enable5_spec⟩,
    ⟨6, by decide, enable6, enable6_spec⟩,
    ⟨7, by decide, enable7, enable7_spec⟩,
    ⟨8, by decide, enable8, enable8_spec⟩,
    ⟨9, by decide, enable9, enable9_spec⟩,
    ⟨10, by decide, enable10, enable10_spec⟩,
    ⟨11, by decide, enable11, enable11_spec⟩,
    ⟨12, by decide, enable12, enable12_spec⟩,
    ⟨13, by decide, enable13, enable13_spec⟩,
    ⟨14, by decide, enable14, enable14_spec⟩,
    ⟨15, by decide, enable15, enable15_spec⟩,
    ⟨16, by decide, enable16, enable16_spec⟩,
    ⟨17, by decide, enable17, enable17_spec⟩,
    ⟨18, by decide, enable18, enable18_spec⟩,
    ⟨19, by decide, enable19, enable19_spec⟩,
    ⟨20, by decide, enable20, enable20_spec⟩,
    ⟨21, by decide, enable21, enable21_spec⟩,
    ⟨22, by decide, enable22, enable22_spec⟩,
    ⟨23, by decide, enable23, enable23_spec⟩,
    ⟨24, by decide, enable24, enable24_spec⟩,
    ⟨25, by decide, enable25, enable25_spec⟩,
    ⟨26, by decide, enable26, enable26_spec⟩,
    ⟨27, by decide, enable27, enable27_spec⟩,
    ⟨28, by decide, enable28, enable28_spec⟩,
    ⟨32, by decide, enable32, enable32_spec⟩,
    ⟨33, by decide, enable33, enable33_spec⟩,
    ⟨34, by decide, enable34, enable34_spec⟩,
    ⟨35, by decide, enable35, enable35_spec⟩,
    ⟨36, by decide, enable36, enable36_spec⟩,
    ⟨37, by decide, enable37, enable37_spec⟩,
    ⟨38, by decide, enable38, enable38_spec⟩,
    ⟨39, by decide, enable39, enable39_spec⟩,
    ⟨40, by decide, enable40, enable40_spec⟩,
    ⟨41, by decide, enable41, enable41_spec⟩,
    ⟨42, by decide, enable42, enable42_spec⟩,
    ⟨43, by decide, enable43, enable43_spec⟩,
    ⟨44, by decide, enable44, enable44_spec⟩,
    ⟨45, by decide, enable45, enable45_spec⟩,
    ⟨46, by decide, enable46, enable46_spec⟩,
    ⟨47, by decide, enable47, enable47_spec⟩,
    ⟨48, by decide, enable48, enable48_spec⟩,
    ⟨49, by decide, enable49, enable49_spec⟩,
    ⟨50, by decide, enable50, enable50_spec⟩,
    ⟨51, by decide, enable51, enable51_spec⟩,
    ⟨52, by decide, enable52, enable52_spec⟩,
    ⟨53, by decide, enable53, enable53_spec⟩,
    ⟨54, by decide, enable54, enable54_spec⟩,
    ⟨55, by decide, enable55, enable55_spec⟩,
    ⟨56, by decide, enable56, enable56_spec⟩,
    ⟨57, by decide, enable57, enable57_spec⟩,
    ⟨58, by decide, enable58, enable58_spec⟩,
    ⟨59, by decide, enable59, enable59_spec⟩,
    ⟨60, by decide, enable60, enable60_spec⟩,
    ⟨64, by decide, enable64, enable64_spec⟩,
    ⟨65, by decide, enable65, enable65_spec⟩,
    ⟨66, by decide, enable66, enable66_spec⟩,
    ⟨67, by decide, enable67, enable67_spec⟩,
    ⟨68, by decide, enable68, enable68_spec⟩,
    ⟨69, by decide, enable69, enable69_spec⟩,
    ⟨70, by decide, enable70, enable70_spec⟩,
    ⟨71, by decide, enable71, enable71_spec⟩,
    ⟨72, by decide, enable72, enable72_spec⟩,
    ⟨73, by decide, enable73, enable73_spec⟩,
    ⟨74, by decide, enable74, enable74_spec⟩,
    ⟨75, by decide, enable75, enable75_spec⟩,
    ⟨76, by decide, enable76, enable76_spec⟩,
    ⟨77, by decide, enable77, enable77_spec⟩,
    ⟨78, by decide, enable78, enable78_spec⟩,
    ⟨79, by decide, enable79, enable79_spec⟩,
    ⟨80, by decide, enable80, enable80_spec⟩,
    ⟨81, by decide, enable81, enable81_spec⟩,
    ⟨82, by decide, enable82, enable82_spec⟩,
    ⟨83, by decide, enable83, enable83_spec⟩,
    ⟨84, by decide, enable84, enable84_spec⟩,
    ⟨85, by decide, enable85, enable85_spec⟩,
    ⟨86, by decide, enable86, enable86_spec⟩,
    ⟨87, by decide, enable87, enable87_spec⟩,
    ⟨88, by decide, enable88, enable88_spec⟩,
    ⟨89, by decide, enable89, enable89_spec⟩,
    ⟨90, by decide, enable90, enable90_spec⟩,
    ⟨91, by decide, enable91, enable91_spec⟩,
    ⟨92, by decide, enable92, enable92_spec⟩,
    ⟨96, by decide, enable96, enable96_spec⟩,
    ⟨97, by decide, enable97, enable97_spec⟩,
    ⟨98, by decide, enable98, enable98_spec⟩,
    ⟨99, by decide, enable99, enable99_spec⟩,
    ⟨100, by decide, enable100, enable100_spec⟩,
    ⟨101, by decide, enable101, enable101_spec⟩,
    ⟨102, by decide, enable102, enable102_spec⟩,
    ⟨103, by decide, enable103, enable103_spec⟩,
    ⟨104, by decide, enable104, enable104_spec⟩,
    ⟨105, by decide, enable105, enable105_spec⟩,
    ⟨106, by decide, enable106, enable106_spec⟩,
    ⟨107, by decide, enable107, enable107_spec⟩,
    ⟨108, by decide, enable108, enable108_spec⟩,
    ⟨109, by decide, enable109, enable109_spec⟩,
    ⟨110, by decide, enable110, enable110_spec⟩,
    ⟨111, by decide, enable111, enable111_spec⟩,
    ⟨112, by decide, enable112, enable112_spec⟩,
    ⟨113, by decide, enable113, enable113_spec⟩,
    ⟨114, by decide, enable114, enable114_spec⟩,
    ⟨115, by decide, enable115, enable115_spec⟩,
    ⟨116, by decide, enable116, enable116_spec⟩,
    ⟨117, by decide, enable117, enable117_spec⟩,
    ⟨118, by decide, enable118, enable118_spec⟩,
    ⟨119, by decide, enable119, enable119_spec⟩,
    ⟨120, by decide, enable120, enable120_spec⟩,
    ⟨121, by decide, enable121, enable121_spec⟩,
    ⟨122, by decide, enable122, enable122_spec⟩,
    ⟨123, by decide, enable123, enable123_spec⟩,
    ⟨124, by decide, enable124, enable124_spec⟩,
    ⟨128, by decide, enable128, enable128_spec⟩,
    ⟨129, by decide, enable129, enable129_spec⟩,
    ⟨130, by decide, enable130, enable130_spec⟩,
    ⟨131, by decide, enable131, enable131_spec⟩,
    ⟨132, by decide, enable132, enable132_spec⟩,
    ⟨136, by decide, enable136, enable136_spec⟩,
    ⟨137, by decide, enable137, enable137_spec⟩,
    ⟨138, by decide, enable138, enable138_spec⟩,
    ⟨139, by decide, enable139, enable139_spec⟩,
    ⟨140, by decide, enable140, enable140_spec⟩,
    ⟨144, by decide, enable144, enable144_spec⟩,
    ⟨145, by decide, enable145, enable145_spec⟩,
    ⟨146, by decide, enable146, enable146_spec⟩,
    ⟨147, by decide, enable147, enable147_spec⟩,
    ⟨148, by decide, enable148, enable148_spec⟩,
    ⟨152, by decide, enable152, enable152_spec⟩,
    ⟨153, by decide, enable153, enable153_spec⟩,
    ⟨154, by decide, enable154, enable154_spec⟩,
    ⟨155, by decide, enable155, enable155_spec⟩,
    ⟨156, by decide, enable156, enable156_spec⟩,
    ⟨160, by decide, enable160, enable160_spec⟩,
    ⟨161, by decide, enable161, enable161_spec⟩,
    ⟨162, by decide, enable162, enable162_spec⟩,
    ⟨163, by decide, enable163, enable163_spec⟩,
    ⟨164, by decide, enable164, enable164_spec⟩,
    ⟨168, by decide, enable168, enable168_spec⟩,
    ⟨169, by decide, enable169, enable169_spec⟩,
    ⟨170, by decide, enable170, enable170_spec⟩,
    ⟨171, by decide, enable171, enable171_spec⟩,
    ⟨172, by decide, enable172, enable172_spec⟩,
    ⟨192, by decide, enable192, enable192_spec⟩,
    ⟨193, by decide, enable193, enable193_spec⟩,
    ⟨194, by decide, enable194, enable194_spec⟩,
    ⟨195, by decide, enable195, enable195_spec⟩,
    ⟨200, by decide, enable200, enable200_spec⟩,
    ⟨201, by decide, enable201, enable201_spec⟩,
    ⟨202, by decide, enable202, enable202_spec⟩,
    ⟨203, by decide, enable203, enable203_spec⟩,
    ⟨208, by decide, enable208, enable208_spec⟩,
    ⟨209, by decide, enable209, enable209_spec⟩,
    ⟨210, by decide, enable210, enable210_spec⟩,
    ⟨211, by decide, enable211, enable211_spec⟩,
    ⟨212, by decide, enable212, enable212_spec⟩,
    ⟨213, by decide, enable213, enable213_spec⟩,
    ⟨214, by decide, enable214, enable214_spec⟩,
    ⟨216, by decide, enable216, enable216_spec⟩,
    ⟨217, by decide, enable217, enable217_spec⟩,
    ⟨218, by decide, enable218, enable218_spec⟩,
    ⟨219, by decide, enable219, enable219_spec⟩,
    ⟨220, by decide, enable220, enable220_spec⟩,
    ⟨221, by decide, enable221, enable221_spec⟩,
    ⟨222, by decide, enable222, enable222_spec⟩,
    ⟨256, by decide, enable256, enable256_spec⟩,
    ⟨257, by decide, enable257, enable257_spec⟩,
    ⟨260, by decide, enable260, enable260_spec⟩,
    ⟨261, by decide, enable261, enable261_spec⟩,
    ⟨262, by decide, enable262, enable262_spec⟩,
    ⟨263, by decide, enable263, enable263_spec⟩,
    ⟨264, by decide, enable264, enable264_spec⟩,
    ⟨265, by decide, enable265, enable265_spec⟩,
    ⟨266, by decide, enable266, enable266_spec⟩,
    ⟨267, by decide, enable267, enable267_spec⟩,
    ⟨272, by decide, enable272, enable272_spec⟩,
    ⟨273, by decide, enable273, enable273_spec⟩,
    ⟨276, by decide, enable276, enable276_spec⟩,
    ⟨277, by decide, enable277, enable277_spec⟩,
    ⟨278, by decide, enable278, enable278_spec⟩,
    ⟨279, by decide, enable279, enable279_spec⟩,
    ⟨280, by decide, enable280, enable280_spec⟩,
    ⟨281, by decide, enable281, enable281_spec⟩,
    ⟨282, by decide, enable282, enable282_spec⟩,
    ⟨283, by decide, enable283, enable283_spec⟩,
    ⟨288, by decide, enable288, enable288_spec⟩,
    ⟨289, by decide, enable289, enable289_spec⟩,
    ⟨292, by decide, enable292, enable292_spec⟩,
    ⟨293, by decide, enable293, enable293_spec⟩,
    ⟨294, by decide, enable294, enable294_spec⟩,
    ⟨295, by decide, enable295, enable295_spec⟩,
    ⟨296, by decide, enable296, enable296_spec⟩,
    ⟨297, by decide, enable297, enable297_spec⟩,
    ⟨298, by decide, enable298, enable298_spec⟩,
    ⟨299, by decide, enable299, enable299_spec⟩,
    ⟨304, by decide, enable304, enable304_spec⟩,
    ⟨305, by decide, enable305, enable305_spec⟩,
    ⟨308, by decide, enable308, enable308_spec⟩,
    ⟨309, by decide, enable309, enable309_spec⟩,
    ⟨310, by decide, enable310, enable310_spec⟩,
    ⟨311, by decide, enable311, enable311_spec⟩,
    ⟨312, by decide, enable312, enable312_spec⟩,
    ⟨313, by decide, enable313, enable313_spec⟩,
    ⟨314, by decide, enable314, enable314_spec⟩,
    ⟨315, by decide, enable315, enable315_spec⟩,
    ⟨320, by decide, enable320, enable320_spec⟩,
    ⟨321, by decide, enable321, enable321_spec⟩,
    ⟨324, by decide, enable324, enable324_spec⟩,
    ⟨325, by decide, enable325, enable325_spec⟩,
    ⟨326, by decide, enable326, enable326_spec⟩,
    ⟨327, by decide, enable327, enable327_spec⟩,
    ⟨328, by decide, enable328, enable328_spec⟩,
    ⟨329, by decide, enable329, enable329_spec⟩,
    ⟨330, by decide, enable330, enable330_spec⟩,
    ⟨331, by decide, enable331, enable331_spec⟩,
    ⟨336, by decide, enable336, enable336_spec⟩,
    ⟨337, by decide, enable337, enable337_spec⟩,
    ⟨340, by decide, enable340, enable340_spec⟩,
    ⟨341, by decide, enable341, enable341_spec⟩,
    ⟨342, by decide, enable342, enable342_spec⟩,
    ⟨343, by decide, enable343, enable343_spec⟩,
    ⟨344, by decide, enable344, enable344_spec⟩,
    ⟨345, by decide, enable345, enable345_spec⟩,
    ⟨346, by decide, enable346, enable346_spec⟩,
    ⟨347, by decide, enable347, enable347_spec⟩,
    ⟨352, by decide, enable352, enable352_spec⟩,
    ⟨353, by decide, enable353, enable353_spec⟩,
    ⟨356, by decide, enable356, enable356_spec⟩,
    ⟨357, by decide, enable357, enable357_spec⟩,
    ⟨358, by decide, enable358, enable358_spec⟩,
    ⟨359, by decide, enable359, enable359_spec⟩,
    ⟨360, by decide, enable360, enable360_spec⟩,
    ⟨361, by decide, enable361, enable361_spec⟩,
    ⟨362, by decide, enable362, enable362_spec⟩,
    ⟨363, by decide, enable363, enable363_spec⟩,
    ⟨368, by decide, enable368, enable368_spec⟩,
    ⟨369, by decide, enable369, enable369_spec⟩,
    ⟨372, by decide, enable372, enable372_spec⟩,
    ⟨373, by decide, enable373, enable373_spec⟩,
    ⟨374, by decide, enable374, enable374_spec⟩,
    ⟨375, by decide, enable375, enable375_spec⟩,
    ⟨376, by decide, enable376, enable376_spec⟩,
    ⟨377, by decide, enable377, enable377_spec⟩,
    ⟨378, by decide, enable378, enable378_spec⟩,
    ⟨379, by decide, enable379, enable379_spec⟩,
    ⟨384, by decide, enable384, enable384_spec⟩,
    ⟨385, by decide, enable385, enable385_spec⟩,
    ⟨388, by decide, enable388, enable388_spec⟩,
    ⟨389, by decide, enable389, enable389_spec⟩,
    ⟨390, by decide, enable390, enable390_spec⟩,
    ⟨391, by decide, enable391, enable391_spec⟩,
    ⟨400, by decide, enable400, enable400_spec⟩,
    ⟨401, by decide, enable401, enable401_spec⟩,
    ⟨404, by decide, enable404, enable404_spec⟩,
    ⟨405, by decide, enable405, enable405_spec⟩,
    ⟨406, by decide, enable406, enable406_spec⟩,
    ⟨407, by decide, enable407, enable407_spec⟩,
    ⟨416, by decide, enable416, enable416_spec⟩,
    ⟨417, by decide, enable417, enable417_spec⟩,
    ⟨420, by decide, enable420, enable420_spec⟩,
    ⟨421, by decide, enable421, enable421_spec⟩,
    ⟨422, by decide, enable422, enable422_spec⟩,
    ⟨423, by decide, enable423, enable423_spec⟩,
    ⟨432, by decide, enable432, enable432_spec⟩,
    ⟨433, by decide, enable433, enable433_spec⟩,
    ⟨436, by decide, enable436, enable436_spec⟩,
    ⟨437, by decide, enable437, enable437_spec⟩,
    ⟨438, by decide, enable438, enable438_spec⟩,
    ⟨439, by decide, enable439, enable439_spec⟩,
    ⟨448, by decide, enable448, enable448_spec⟩,
    ⟨449, by decide, enable449, enable449_spec⟩,
    ⟨452, by decide, enable452, enable452_spec⟩,
    ⟨453, by decide, enable453, enable453_spec⟩,
    ⟨454, by decide, enable454, enable454_spec⟩,
    ⟨455, by decide, enable455, enable455_spec⟩,
    ⟨464, by decide, enable464, enable464_spec⟩,
    ⟨465, by decide, enable465, enable465_spec⟩,
    ⟨468, by decide, enable468, enable468_spec⟩,
    ⟨469, by decide, enable469, enable469_spec⟩,
    ⟨470, by decide, enable470, enable470_spec⟩,
    ⟨471, by decide, enable471, enable471_spec⟩]

/-- The offset `k` carries a gate: the extracted family's own live set. -/
def liveAt (k : BitVec 9) : Bool :=
  gates.any (fun g => k.toNat == g.off)

/-- The gate family of the elaborated bank as one function of the byte index and
the staged write word: the cone of the gate at offset `k`, `false` at a mask-zero
or out-of-window index. -/
def enableAt (k : BitVec 9) (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  gates.any (fun g => k.toNat == g.off && g.fn we1 addr1)

/-! ## The family law

The per-byte theorems above are the RTL link one live byte at a time. The
assembly is a single lemma over the gate list: it uses each gate's own theorem
once and never enumerates the 480 offsets. -/

/-- `a || (a && b) = a`: the only open gate absorbs the closed rest. -/
private theorem or_and_self (a b : Bool) : (a || (a && b)) = a := by
  cases a <;> simp

/-- **The family law.** A list of gates whose cones each implement their own
offset comparison yields, at byte index `k`, exactly the gate at `k`: an index
that is not an offset in the list carries no gate, and the only open gate is the
gate whose offset is `k`. -/
theorem any_enable_spec (l : List Gate) (k : BitVec 9) (we1 : Bool)
    (addr1 : BitVec 9) :
    l.any (fun g => k.toNat == g.off && g.fn we1 addr1) =
      (we1 && (addr1 == k) && l.any (fun g => k.toNat == g.off)) := by
  induction l with
  | nil => simp
  | cons g rest ih =>
    simp only [List.any_cons]
    rw [g.spec we1 addr1, ih]
    cases hc : (k.toNat == g.off)
    · simp
    · have h1 : k.toNat = g.off := by simpa using hc
      have hk : k = BitVec.ofNat 9 g.off := by
        apply BitVec.toNat_inj.mp
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using g.off_lt)]
        exact h1
      rw [hk]
      simp only [Bool.true_and, Bool.true_or, Bool.and_true]
      exact or_and_self _ _

/-- **The family theorem.** The whole extracted gate family — every inlined
`g_byte[k].g_used.u_cg` cone — is the arithmetic per-byte rule, and it carries no
gate at a mask-zero or out-of-window index. No hypothesis, no per-offset case
analysis: this is the statement the composition used to assume. -/
theorem enableAt_spec (k : BitVec 9) (we1 : Bool) (addr1 : BitVec 9) :
    enableAt k we1 addr1 = (we1 && (addr1 == k) && liveAt k) :=
  any_enable_spec gates k we1 addr1

/-- The family's live set at a window offset is exactly "the elaborated `MASK`
byte is non-zero", so the gates and the latches agree on which offsets exist.
Kernel reduction over the 480 offsets. -/
theorem liveAt_addrOf (i : Fin cfgBytes) :
    liveAt (Metronome.Bank.addrOf i) = paramLive i := by
  decide +revert

/-- The same live set as the bit vector the address-decode cut uses: bit `k` is
set iff `MASK` byte `k` is non-zero. -/
theorem liveBytes_getLsb (i : Fin cfgBytes) :
    liveBytes.getLsb i = paramLive i := by
  decide +revert

/-- A non-zero `MASK` byte has a gate. -/
theorem liveAt_of_live (i : Fin cfgBytes) (h : paramMask i ≠ 0) :
    liveAt (Metronome.Bank.addrOf i) = true := by
  rw [liveAt_addrOf]
  simpa [paramLive] using h

/-- A mask-zero offset has no gate. -/
theorem liveAt_of_hole (i : Fin cfgBytes) (h : paramMask i = 0) :
    liveAt (Metronome.Bank.addrOf i) = false := by
  rw [liveAt_addrOf]
  simp [paramLive, h]

/-! ## Composition with the latch-bank specification -/

/-- Every live byte's extracted gate is its specification gate. -/
theorem enableAt_eq_gateOpen (i : Fin cfgBytes) (h : paramMask i ≠ 0)
    (we1 : Bool) (addr1 : BitVec 9) :
    enableAt (Metronome.Bank.addrOf i) we1 addr1 =
      Metronome.Bank.gateOpen we1 addr1 i := by
  rw [enableAt_spec, liveAt_of_live i h, Metronome.Bank.gateOpen]
  simp

/-- A mask-zero offset carries no gate at all, so its clock gate does not exist
rather than staying closed: the family is closed there. -/
theorem enableAt_hole (i : Fin cfgBytes) (h : paramMask i = 0)
    (we1 : Bool) (addr1 : BitVec 9) :
    enableAt (Metronome.Bank.addrOf i) we1 addr1 = false := by
  rw [enableAt_spec, liveAt_of_hole i h]
  simp

/-- At most one extracted gate of the bank is open at a time. -/
theorem rtl_gates_exclusive (i j : Fin cfgBytes) (h : i ≠ j) (we1 : Bool)
    (addr1 : BitVec 9) :
    (enableAt (Metronome.Bank.addrOf i) we1 addr1 &&
      enableAt (Metronome.Bank.addrOf j) we1 addr1) = false := by
  by_cases hi : paramMask i = 0
  · rw [enableAt_hole i hi]
    simp
  · by_cases hj : paramMask j = 0
    · rw [enableAt_hole j hj]
      simp
    · rw [enableAt_eq_gateOpen i hi, enableAt_eq_gateOpen j hj]
      exact Metronome.Bank.gateOpen_exclusive i j h we1 addr1

/-- The elaborated bank state: the elaborated `MASK` and an arbitrary latch
content. -/
def latchState (latch : Fin cfgBytes → BitVec 8) : Metronome.Bank.State :=
  ⟨paramMask, latch⟩

/-- **Hypothesis-free write step.** A transparency phase of the *extracted*
gate family has the read value of the specified write step, for any staged
write word and any latch content. -/
theorem bank_step_read (latch : Fin cfgBytes → BitVec 8) (we1 : Bool)
    (addr1 : BitVec 9) (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.phase (latchState latch)
          (fun k => enableAt (Metronome.Bank.addrOf k) we1 addr1) data1) =
      Metronome.Bank.read
        (Metronome.Bank.step (latchState latch) we1 addr1 data1) :=
  Metronome.Bank.phase_read_of_live_gates (latchState latch)
    (fun k we1 addr1 => enableAt (Metronome.Bank.addrOf k) we1 addr1)
    (fun k we1 addr1 h => enableAt_eq_gateOpen k h we1 addr1)
    (fun k we1 addr1 h => enableAt_hole k h we1 addr1)
    we1 addr1 data1

/-- **The write contract, unconditionally.** An issued write to byte `k` of the
elaborated bank sets exactly that byte's mask bits to `data1 & MASK`. -/
theorem bank_write_exact_all (latch : Fin cfgBytes → BitVec 8)
    (k : Fin cfgBytes) (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.phase (latchState latch)
          (fun j => enableAt (Metronome.Bank.addrOf j) true
            (Metronome.Bank.addrOf k)) data1) k =
      data1 &&& paramMask k :=
  Metronome.Bank.write_exact_of_live_gates (latchState latch)
    (fun j we1 addr1 => enableAt (Metronome.Bank.addrOf j) we1 addr1)
    (fun j we1 addr1 h => enableAt_eq_gateOpen j h we1 addr1)
    (fun j we1 addr1 h => enableAt_hole j h we1 addr1)
    k data1

/-- ... and leaves every other byte unchanged. -/
theorem bank_write_others_all (latch : Fin cfgBytes → BitVec 8)
    (k j : Fin cfgBytes) (h : j ≠ k) (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.phase (latchState latch)
          (fun i => enableAt (Metronome.Bank.addrOf i) true
            (Metronome.Bank.addrOf k)) data1) j =
      Metronome.Bank.read (latchState latch) j :=
  Metronome.Bank.write_others_of_live_gates (latchState latch)
    (fun i we1 addr1 => enableAt (Metronome.Bank.addrOf i) we1 addr1)
    (fun i we1 addr1 h => enableAt_eq_gateOpen i h we1 addr1)
    (fun i we1 addr1 h => enableAt_hole i h we1 addr1)
    k j h data1

/-! ## Concrete witnesses on the elaborated mask -/

/-- A live witness offset: its gate and latch set are checked below. -/
abbrev liveWitness : Fin cfgBytes := ⟨0, by decide⟩

/-- A mask-zero witness offset: no gate and no latch. -/
abbrev holeWitness : Fin cfgBytes := ⟨479, by decide⟩

/-- The live witness offset has a non-zero mask byte, so it has latches. -/
theorem witness_live_mask : paramMask liveWitness ≠ 0 := by
  decide

/-- The hole witness offset has a zero mask byte. -/
theorem witness_hole_mask : paramMask holeWitness = 0 := by
  decide

/-- The extracted gate of the live witness offset opens at that offset. -/
theorem witness_gate_open :
    enableAt (Metronome.Bank.addrOf liveWitness) true
      (Metronome.Bank.addrOf liveWitness) = true := by
  rw [enableAt_spec, liveAt_of_live liveWitness witness_live_mask]
  simp

/-- The hole witness offset has no gate even when addressed directly. -/
theorem witness_hole_closed :
    enableAt (Metronome.Bank.addrOf holeWitness) true
      (Metronome.Bank.addrOf holeWitness) = false := by
  rw [enableAt_hole holeWitness witness_hole_mask]

/-- A write to the mask-zero witness offset changes nothing on the elaborated
mask, whatever the strobe, address and data. -/
theorem bank_hole_noop (latch : Fin cfgBytes → BitVec 8) (we1 : Bool)
    (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.phase (latchState latch)
          (fun j => enableAt (Metronome.Bank.addrOf j) we1
            (Metronome.Bank.addrOf holeWitness)) data1) =
      Metronome.Bank.read (latchState latch) :=
  Metronome.Bank.write_mask_zero_of_live_gates (latchState latch)
    (fun j w a => enableAt (Metronome.Bank.addrOf j) w a)
    (fun j w a h => enableAt_eq_gateOpen j h w a)
    (fun j w a h => enableAt_hole j h w a)
    holeWitness witness_hole_mask we1 data1

-- Axiom audit. `bank_check.py` records these and rejects `sorryAx`.
#print axioms any_enable_spec
#print axioms enableAt_spec
#print axioms liveAt_addrOf
#print axioms liveBytes_getLsb
#print axioms enableAt_eq_gateOpen
#print axioms enableAt_hole
#print axioms rtl_gates_exclusive
#print axioms bank_step_read
#print axioms bank_write_exact_all
#print axioms bank_write_others_all
#print axioms witness_live_mask
#print axioms witness_hole_mask
#print axioms witness_gate_open
#print axioms witness_hole_closed
#print axioms bank_hole_noop
