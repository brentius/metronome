import Metronome.Machine

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

open Metronome

namespace Probe7

def offOf (a : Nat) : BitVec 9 := Machine.Util.bv 9 a

def addrOf (o : BitVec 9) : Nat := 0x2000 + o.toNat

def cfgAddrCheck : Bool :=
  (List.range 0x10000).all fun a =>
    !(Machine.Config.isCfgAddr a) || (0x2000 ≤ a && a < 0x21E0)

theorem cfgAddrCheck_eq : cfgAddrCheck = true := by decide

theorem isCfgAddr_window (a : Nat) (ha : a < 0x10000)
    (h : Machine.Config.isCfgAddr a = true) : 0x2000 ≤ a ∧ a < 0x21E0 := by
  have hc : cfgAddrCheck = true := cfgAddrCheck_eq
  rw [cfgAddrCheck, List.all_eq_true] at hc
  have hx := hc a (List.mem_range.mpr ha)
  simpa [h] using hx

theorem addrOf_offOf_window (a : Nat) (ha : a < 0x10000)
    (h : Machine.Config.isCfgAddr a = true) : addrOf (offOf a) = a := by
  have hb := isCfgAddr_window a ha h
  unfold addrOf offOf Machine.Util.bv
  rw [BitVec.toNat_ofNat]
  have hmod : a % 512 = a - 0x2000 := by omega
  rw [hmod]
  omega

end Probe7
