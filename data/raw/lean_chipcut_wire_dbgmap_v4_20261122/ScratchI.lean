import Metronome.ChipCut.Discharge.Glue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-- Widening to 32 bits is injective on 16-bit words (with a `Nat` value
below `2^16`). -/
theorem setWidth32_eq_ofNat {a : BitVec 16} {n : Nat} (hn : n < 65536)
    (h : BitVec.setWidth 32 a = BitVec.ofNat 32 n) : a = BitVec.ofNat 16 n := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
  have ha : a.toNat < 2 ^ 32 := by omega
  have hn' : n < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn'] at h'
  apply BitVec.eq_of_toNat_eq
  rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- A host `DBG`-window byte strobe holds exactly for a write of that offset. -/
theorem hostDbg_eq {w : Bool} {a : BitVec 16} {D : Nat} (hD : D < 0x20) :
    Strobes.hostDbg w a D = true ↔ w = true ∧ a = BitVec.ofNat 16 D := by
  unfold Strobes.hostDbg
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hw, he⟩
    exact ⟨hw, setWidth32_eq_ofNat (by omega) he⟩
  · rintro ⟨hw, rfl⟩
    refine ⟨hw, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : D < 65536), Nat.mod_eq_of_lt (by omega : D < 2 ^ 32)]

/-- `dbgOff a`'s value. -/
theorem dbgOff_toNat (a : BitVec 16) :
    (dbgOff a).toNat = (a.toNat + 56224) % 65536 := by
  have h9312 : BitVec.toNat (9312 : BitVec 16) = 9312 := by decide
  have h316 : (2 : Nat) ^ 16 = 65536 := by decide
  unfold dbgOff
  rw [BitVec.toNat_sub, h9312, h316]
  show (65536 - 9312 + a.toNat) % 65536 = (a.toNat + 56224) % 65536
  congr 1
  omega

/-- `dbgOff a = D` pins the address (`D` inside the window). -/
theorem dbgOff_eq_addr {a : BitVec 16} {D : Nat} (hD : D < 0x20)
    (h : dbgOff a = BitVec.ofNat 16 D) : a = BitVec.ofNat 16 (0x2460 + D) := by
  have hh : (dbgOff a).toNat = D := by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : D < 65536)]
  rw [dbgOff_toNat] at hh
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x2460 + D < 65536)]
  by_cases hge : (9312 : Nat) ≤ a.toNat
  · have hval : (a.toNat + 56224) % 65536 = a.toNat - 9312 := by
      rw [show a.toNat + 56224 = (a.toNat - 9312) + 65536 from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · have hval : (a.toNat + 56224) % 65536 = a.toNat + 56224 :=
      Nat.mod_eq_of_lt (by omega)
    omega

/-- The value of the RTL's 32-bit `cw_dbg_off`. -/
theorem cwDbgOff_toNat (a : BitVec 16) :
    (Strobes.cwDbgOff a).toNat = (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 := by
  have h9312 : BitVec.toNat (BitVec.setWidth 32 (9312 : BitVec 16)) = 9312 := by decide
  have ha : BitVec.toNat (BitVec.setWidth 32 a) = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  have halt : a.toNat < 65536 := a.isLt
  unfold Strobes.cwDbgOff Strobes.haDbgBase
  rw [BitVec.toNat_sub, h9312, ha]
  show (2 ^ 32 - 9312 + a.toNat) % 2 ^ 32 = (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32
  congr 1
  omega

/-- The RTL's 32-bit `cw_dbg_off` equal to `D` (inside the window) pins the
queued address. -/
theorem cwDbgOff_eq_addr {a : BitVec 16} {D : Nat} (hD : D < 0x20)
    (h : (Strobes.cwDbgOff a == BitVec.ofNat 32 D) = true) : a.toNat = 0x2460 + D := by
  have he : Strobes.cwDbgOff a = BitVec.ofNat 32 D := beq_iff_eq.mp h
  have hh : (Strobes.cwDbgOff a).toNat = D := by
    rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : D < 2 ^ 32)]
  rw [cwDbgOff_toNat] at hh
  by_cases hge : (9312 : Nat) ≤ a.toNat
  · have hval : (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 = a.toNat - 9312 := by
      rw [show a.toNat + (2 ^ 32 - 9312) = (a.toNat - 9312) + 2 ^ 32 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hval : (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 = a.toNat + (2 ^ 32 - 9312) :=
      Nat.mod_eq_of_lt (by omega)
    omega

end Metronome.ChipCut.Discharge.DbgMapWire
