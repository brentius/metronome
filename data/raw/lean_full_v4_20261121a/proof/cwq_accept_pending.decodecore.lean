import Metronome.Compose
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: eadb8c1dd5a75ef86197b197ad10c6f7c6f04fade08cde35434c15f646f8706d
-- Configuration window and bank mask come from the elaborated chip top:
-- CFG_LO from the `a_cfg = ha - CFG_LO` subtraction, the span from the
-- `in_cfg` comparison, and MASK from the specialized `u_cfg` instance.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000

namespace Metronome.Decode

abbrev cfgLo : BitVec 16 := 0x2000
abbrev cfgHi : BitVec 16 := 0x21E0
abbrev cfgBytes : Nat := 480

/-- The elaborated `u_cfg` MASK parameter, one byte per window offset. -/
abbrev bankMask : BitVec 3840 := 0x0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F0000000000000000000000000000000000000000000000000000000000000000000FFF0FFF07FF03000FFF0FFF07FF0300000000FFFFFFFF00000000FFFFFFFF00000000000000000000000000000000000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

/-- Bit k is set iff bank byte k contains at least one latch. -/
abbrev liveBytes : BitVec 480 := 0x00F300F300F300F300F300F30FF30FF30FF30FF30FF30FF30FF30FF3000000007F7F0F0F00001F1F1F1F1F1F1FFFFFFF1FFFFFFF1FFFFFFF1FFFFFFF

abbrev maskByte (off : Nat) : BitVec 8 :=
  (bankMask >>> (8 * off)).truncate 8

abbrev inWindow (a : BitVec 16) : Bool :=
  cfgLo <= a && a < cfgHi

/-- The maximal runs of non-zero mask bytes, as absolute addresses. -/
abbrev maskLive (a : BitVec 16) : Bool :=
    (a >= (0x2000 : BitVec 16) && a < (0x201D : BitVec 16)) ||
    (a >= (0x2020 : BitVec 16) && a < (0x203D : BitVec 16)) ||
    (a >= (0x2040 : BitVec 16) && a < (0x205D : BitVec 16)) ||
    (a >= (0x2060 : BitVec 16) && a < (0x207D : BitVec 16)) ||
    (a >= (0x2080 : BitVec 16) && a < (0x2085 : BitVec 16)) ||
    (a >= (0x2088 : BitVec 16) && a < (0x208D : BitVec 16)) ||
    (a >= (0x2090 : BitVec 16) && a < (0x2095 : BitVec 16)) ||
    (a >= (0x2098 : BitVec 16) && a < (0x209D : BitVec 16)) ||
    (a >= (0x20A0 : BitVec 16) && a < (0x20A5 : BitVec 16)) ||
    (a >= (0x20A8 : BitVec 16) && a < (0x20AD : BitVec 16)) ||
    (a >= (0x20C0 : BitVec 16) && a < (0x20C4 : BitVec 16)) ||
    (a >= (0x20C8 : BitVec 16) && a < (0x20CC : BitVec 16)) ||
    (a >= (0x20D0 : BitVec 16) && a < (0x20D7 : BitVec 16)) ||
    (a >= (0x20D8 : BitVec 16) && a < (0x20DF : BitVec 16)) ||
    (a >= (0x2100 : BitVec 16) && a < (0x2102 : BitVec 16)) ||
    (a >= (0x2104 : BitVec 16) && a < (0x210C : BitVec 16)) ||
    (a >= (0x2110 : BitVec 16) && a < (0x2112 : BitVec 16)) ||
    (a >= (0x2114 : BitVec 16) && a < (0x211C : BitVec 16)) ||
    (a >= (0x2120 : BitVec 16) && a < (0x2122 : BitVec 16)) ||
    (a >= (0x2124 : BitVec 16) && a < (0x212C : BitVec 16)) ||
    (a >= (0x2130 : BitVec 16) && a < (0x2132 : BitVec 16)) ||
    (a >= (0x2134 : BitVec 16) && a < (0x213C : BitVec 16)) ||
    (a >= (0x2140 : BitVec 16) && a < (0x2142 : BitVec 16)) ||
    (a >= (0x2144 : BitVec 16) && a < (0x214C : BitVec 16)) ||
    (a >= (0x2150 : BitVec 16) && a < (0x2152 : BitVec 16)) ||
    (a >= (0x2154 : BitVec 16) && a < (0x215C : BitVec 16)) ||
    (a >= (0x2160 : BitVec 16) && a < (0x2162 : BitVec 16)) ||
    (a >= (0x2164 : BitVec 16) && a < (0x216C : BitVec 16)) ||
    (a >= (0x2170 : BitVec 16) && a < (0x2172 : BitVec 16)) ||
    (a >= (0x2174 : BitVec 16) && a < (0x217C : BitVec 16)) ||
    (a >= (0x2180 : BitVec 16) && a < (0x2182 : BitVec 16)) ||
    (a >= (0x2184 : BitVec 16) && a < (0x2188 : BitVec 16)) ||
    (a >= (0x2190 : BitVec 16) && a < (0x2192 : BitVec 16)) ||
    (a >= (0x2194 : BitVec 16) && a < (0x2198 : BitVec 16)) ||
    (a >= (0x21A0 : BitVec 16) && a < (0x21A2 : BitVec 16)) ||
    (a >= (0x21A4 : BitVec 16) && a < (0x21A8 : BitVec 16)) ||
    (a >= (0x21B0 : BitVec 16) && a < (0x21B2 : BitVec 16)) ||
    (a >= (0x21B4 : BitVec 16) && a < (0x21B8 : BitVec 16)) ||
    (a >= (0x21C0 : BitVec 16) && a < (0x21C2 : BitVec 16)) ||
    (a >= (0x21C4 : BitVec 16) && a < (0x21C8 : BitVec 16)) ||
    (a >= (0x21D0 : BitVec 16) && a < (0x21D2 : BitVec 16)) ||
    (a >= (0x21D4 : BitVec 16) && a < (0x21D8 : BitVec 16))

abbrev byteFlag (a : BitVec 16) : Bool :=
  (((liveBytes >>> (a - cfgLo).toNat) &&& (1 : BitVec 480)) != 0)

abbrev specLive (a : BitVec 16) : Bool :=
  inWindow a && maskLive a

/-- The run list is exactly the set of non-zero mask bytes. -/
theorem runs_match_mask : forall i : Fin cfgBytes,
    maskLive (cfgLo + BitVec.ofNat 16 i.val) = liveBytes.getLsb i := by
  decide

/-- The extracted flag vector is exactly "the MASK byte is non-zero". -/
theorem liveBytes_eq_mask : forall i : Fin cfgBytes,
    liveBytes.getLsb i = (maskByte i.val != 0) := by
  decide

/-- info: 'Metronome.Decode.runs_match_mask' depends on axioms: [propext] -/
#guard_msgs in #print axioms runs_match_mask

/-- info: 'Metronome.Decode.liveBytes_eq_mask' depends on axioms: [propext] -/
#guard_msgs in #print axioms liveBytes_eq_mask

/-- Interval membership and the flag-vector lookup agree for every address. -/
theorem maskLive_eq_byteFlag (a : BitVec 16) :
    maskLive a = byteFlag a := by
  bv_decide

theorem cfgHi_is_window : cfgHi = cfgLo + BitVec.ofNat 16 cfgBytes := by
  decide

/-- The full 16-bit window offset fits the nine-bit bank address, so no
information is lost by the `a_cfg[8:0]` / low-nine-bit connection. -/
theorem offset_fits_nine (a : BitVec 16) (live : specLive a = true) :
    (a - cfgLo) < (512 : BitVec 16) := by
  bv_decide

theorem first_live : specLive 0x2000 = true := by
  decide

theorem last_live : specLive 0x21D7 = true := by
  decide

theorem hole_201D : specLive 0x201D = false := by
  decide

theorem indexed_tail : inWindow 0x21DF = true ∧
    specLive 0x21DF = false := by
  decide

theorem partial_byte : maskByte 0xD0 = 0x03 ∧ specLive 0x20D0 = true := by
  decide

theorem out_of_window : specLive 0x21E0 = false := by
  decide

theorem wrapped_below : specLive 0x1FFF = false := by
  decide

abbrev rtlCoreLive (a : BitVec 16) : Bool :=
  let decode0 := (a >= (8192 : BitVec 16))
  let decode1 := (a < (8320 : BitVec 16))
  let decode2 := decode0 && decode1
  let decode3 := (((BitVec.ushiftRight (536870911 : BitVec 32) ((BitVec.truncate 5 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 32)) != 0)
  let decode4 := decode2 && decode3
  let decode5 := (a >= (8320 : BitVec 16))
  let decode6 := (a < (8368 : BitVec 16))
  let decode7 := decode5 && decode6
  let decode8 := (((BitVec.ushiftRight (31 : BitVec 8) ((BitVec.truncate 3 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 8)) != 0)
  let decode9 := decode7 && decode8
  let decode10 := decode4 || decode9
  let decode11 := (a >= (8384 : BitVec 16))
  let decode12 := (a < (8400 : BitVec 16))
  let decode13 := decode11 && decode12
  let decode14 := (((BitVec.ushiftRight (15 : BitVec 8) ((BitVec.truncate 3 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 8)) != 0)
  let decode15 := decode13 && decode14
  let decode16 := decode10 || decode15
  let decode17 := (a >= (8400 : BitVec 16))
  let decode18 := (a < (8416 : BitVec 16))
  let decode19 := decode17 && decode18
  let decode20 := (((BitVec.ushiftRight (127 : BitVec 8) ((BitVec.truncate 3 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 8)) != 0)
  let decode21 := decode19 && decode20
  let decode22 := decode16 || decode21
  let decode23 := (a >= (8448 : BitVec 16))
  let decode24 := (a < (8576 : BitVec 16))
  let decode25 := decode23 && decode24
  let decode26 := (((BitVec.ushiftRight (4083 : BitVec 16) ((BitVec.truncate 4 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let decode27 := decode25 && decode26
  let decode28 := decode22 || decode27
  let decode29 := (a >= (8576 : BitVec 16))
  let decode30 := (a < (8672 : BitVec 16))
  let decode31 := decode29 && decode30
  let decode32 := (((BitVec.ushiftRight (243 : BitVec 16) ((BitVec.truncate 4 (BitVec.ushiftRight a 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let decode33 := decode31 && decode32
  let decode34 := decode28 || decode33
  decode34

/-- The elaborated core `cw_is_cfg` equals the mask rule at every 16-bit
address. -/
theorem rtlCoreLive_eq_spec (a : BitVec 16) :
    rtlCoreLive a = specLive a := by
  bv_decide

/-- The nine low bits taken by the core arbiter are the low bits of the
window offset; `cfgLo` is nine-bit aligned. This is a total identity. -/
theorem core_low_bits_are_offset (a : BitVec 16) :
    a.truncate 9 = (a - cfgLo).truncate 9 := by
  bv_decide

theorem core_first_live : rtlCoreLive 0x2000 = true := by
  decide

theorem core_last_live : rtlCoreLive 0x21D7 = true := by
  decide

theorem core_hole : rtlCoreLive 0x201D = false := by
  decide

theorem core_wrapped : rtlCoreLive 0x1FFF = false := by
  decide

theorem core_out_of_window : rtlCoreLive 0x21E0 = false := by
  decide

-- See the host file: this equality carries the same native LRAT certificate
-- axiom from `bv_decide`.
#print axioms rtlCoreLive_eq_spec

end Metronome.Decode
