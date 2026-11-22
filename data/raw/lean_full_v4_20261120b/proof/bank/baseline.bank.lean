import Metronome.Bank
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b
-- Bank: the `md2_cfg_cells` instance `tt_um_brentius_metronome.u_cfg`. The mask bytes come
-- from its elaborated `MASK` parameter; the enable cones come from the GATE net
-- of every `g_byte[k].g_used.u_cg` cell, with `we1` and `addr1` bound free.
-- 284 of 480 mask bytes are non-zero (2112 latch bits).

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000

namespace Metronome.BankEquivalence

/-- Window offsets in the elaborated bank. -/
abbrev cfgBytes : Nat := 480

/-- The elaborated `u_cfg` `MASK` parameter, one byte per offset. -/
abbrev bankMask : BitVec 3840 := 0x0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F0000000000000000FFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F00000000FFFFFFFFFFFFFFFF00003F1F0000000000000000000000000000000000000000000000000000000000000000000FFF0FFF07FF03000FFF0FFF07FF0300000000FFFFFFFF00000000FFFFFFFF00000000000000000000000000000000000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFF3F3FFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000FFFFFFFFFFFFFFFFFF03FF7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

/-- The MASK byte of offset `k`, read from the elaborated parameter. -/
def paramMask (k : Fin cfgBytes) : BitVec 8 := (bankMask >>> (8 * k.val)).truncate 8

/-- A live witness offset: its gate and latch set are checked below. -/
abbrev liveWitness : Fin cfgBytes := ⟨0, by decide⟩

/-- A mask-zero witness offset: no gate and no latch. -/
abbrev holeWitness : Fin cfgBytes := ⟨479, by decide⟩

/-- The bank state of the concrete witnesses: the elaborated mask, and an
arbitrary (zero) initial latch content. -/
def maskState : Metronome.Bank.State := ⟨paramMask, fun _ => 0⟩

/-- Gate enable of byte 0, extracted from `g_byte[0].g_used.u_cg`. -/
def enable0 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable0_0 := (addr1 == (0 : BitVec 9))
  let enable0_1 := we1 && enable0_0
  enable0_1

/-- The extracted gate of byte 0 equals `we1 && addr1 == 0` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable0_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable0 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 0) := by
  unfold enable0
  bv_decide

/-- Byte 0's extracted gate opens at its own offset and only there. -/
theorem enable0_open :
    enable0 true (Metronome.Bank.addrOf ⟨0, by decide⟩) = true := by
  rw [enable0_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable0_spec
#print axioms enable0_open

/-- Gate enable of byte 1, extracted from `g_byte[1].g_used.u_cg`. -/
def enable1 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable1_0 := (addr1 == (1 : BitVec 9))
  let enable1_1 := we1 && enable1_0
  enable1_1

/-- The extracted gate of byte 1 equals `we1 && addr1 == 1` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable1_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable1 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 1) := by
  unfold enable1
  bv_decide

/-- Byte 1's extracted gate opens at its own offset and only there. -/
theorem enable1_open :
    enable1 true (Metronome.Bank.addrOf ⟨1, by decide⟩) = true := by
  rw [enable1_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable1_spec
#print axioms enable1_open

/-- Gate enable of byte 2, extracted from `g_byte[2].g_used.u_cg`. -/
def enable2 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable2_0 := (addr1 == (2 : BitVec 9))
  let enable2_1 := we1 && enable2_0
  enable2_1

/-- The extracted gate of byte 2 equals `we1 && addr1 == 2` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable2_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable2 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 2) := by
  unfold enable2
  bv_decide

/-- Byte 2's extracted gate opens at its own offset and only there. -/
theorem enable2_open :
    enable2 true (Metronome.Bank.addrOf ⟨2, by decide⟩) = true := by
  rw [enable2_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable2_spec
#print axioms enable2_open

/-- Gate enable of byte 3, extracted from `g_byte[3].g_used.u_cg`. -/
def enable3 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable3_0 := (addr1 == (3 : BitVec 9))
  let enable3_1 := we1 && enable3_0
  enable3_1

/-- The extracted gate of byte 3 equals `we1 && addr1 == 3` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable3_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable3 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 3) := by
  unfold enable3
  bv_decide

/-- Byte 3's extracted gate opens at its own offset and only there. -/
theorem enable3_open :
    enable3 true (Metronome.Bank.addrOf ⟨3, by decide⟩) = true := by
  rw [enable3_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable3_spec
#print axioms enable3_open

/-- Gate enable of byte 4, extracted from `g_byte[4].g_used.u_cg`. -/
def enable4 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable4_0 := (addr1 == (4 : BitVec 9))
  let enable4_1 := we1 && enable4_0
  enable4_1

/-- The extracted gate of byte 4 equals `we1 && addr1 == 4` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable4_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable4 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 4) := by
  unfold enable4
  bv_decide

/-- Byte 4's extracted gate opens at its own offset and only there. -/
theorem enable4_open :
    enable4 true (Metronome.Bank.addrOf ⟨4, by decide⟩) = true := by
  rw [enable4_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable4_spec
#print axioms enable4_open

/-- Gate enable of byte 5, extracted from `g_byte[5].g_used.u_cg`. -/
def enable5 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable5_0 := (addr1 == (5 : BitVec 9))
  let enable5_1 := we1 && enable5_0
  enable5_1

/-- The extracted gate of byte 5 equals `we1 && addr1 == 5` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable5_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable5 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 5) := by
  unfold enable5
  bv_decide

/-- Byte 5's extracted gate opens at its own offset and only there. -/
theorem enable5_open :
    enable5 true (Metronome.Bank.addrOf ⟨5, by decide⟩) = true := by
  rw [enable5_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable5_spec
#print axioms enable5_open

/-- Gate enable of byte 6, extracted from `g_byte[6].g_used.u_cg`. -/
def enable6 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable6_0 := (addr1 == (6 : BitVec 9))
  let enable6_1 := we1 && enable6_0
  enable6_1

/-- The extracted gate of byte 6 equals `we1 && addr1 == 6` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable6_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable6 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 6) := by
  unfold enable6
  bv_decide

/-- Byte 6's extracted gate opens at its own offset and only there. -/
theorem enable6_open :
    enable6 true (Metronome.Bank.addrOf ⟨6, by decide⟩) = true := by
  rw [enable6_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable6_spec
#print axioms enable6_open

/-- Gate enable of byte 7, extracted from `g_byte[7].g_used.u_cg`. -/
def enable7 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable7_0 := (addr1 == (7 : BitVec 9))
  let enable7_1 := we1 && enable7_0
  enable7_1

/-- The extracted gate of byte 7 equals `we1 && addr1 == 7` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable7_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable7 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 7) := by
  unfold enable7
  bv_decide

/-- Byte 7's extracted gate opens at its own offset and only there. -/
theorem enable7_open :
    enable7 true (Metronome.Bank.addrOf ⟨7, by decide⟩) = true := by
  rw [enable7_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable7_spec
#print axioms enable7_open

/-- Gate enable of byte 8, extracted from `g_byte[8].g_used.u_cg`. -/
def enable8 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable8_0 := (addr1 == (8 : BitVec 9))
  let enable8_1 := we1 && enable8_0
  enable8_1

/-- The extracted gate of byte 8 equals `we1 && addr1 == 8` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable8_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable8 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 8) := by
  unfold enable8
  bv_decide

/-- Byte 8's extracted gate opens at its own offset and only there. -/
theorem enable8_open :
    enable8 true (Metronome.Bank.addrOf ⟨8, by decide⟩) = true := by
  rw [enable8_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable8_spec
#print axioms enable8_open

/-- Gate enable of byte 9, extracted from `g_byte[9].g_used.u_cg`. -/
def enable9 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable9_0 := (addr1 == (9 : BitVec 9))
  let enable9_1 := we1 && enable9_0
  enable9_1

/-- The extracted gate of byte 9 equals `we1 && addr1 == 9` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable9_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable9 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 9) := by
  unfold enable9
  bv_decide

/-- Byte 9's extracted gate opens at its own offset and only there. -/
theorem enable9_open :
    enable9 true (Metronome.Bank.addrOf ⟨9, by decide⟩) = true := by
  rw [enable9_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable9_spec
#print axioms enable9_open

/-- Gate enable of byte 10, extracted from `g_byte[10].g_used.u_cg`. -/
def enable10 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable10_0 := (addr1 == (10 : BitVec 9))
  let enable10_1 := we1 && enable10_0
  enable10_1

/-- The extracted gate of byte 10 equals `we1 && addr1 == 10` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable10_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable10 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 10) := by
  unfold enable10
  bv_decide

/-- Byte 10's extracted gate opens at its own offset and only there. -/
theorem enable10_open :
    enable10 true (Metronome.Bank.addrOf ⟨10, by decide⟩) = true := by
  rw [enable10_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable10_spec
#print axioms enable10_open

/-- Gate enable of byte 11, extracted from `g_byte[11].g_used.u_cg`. -/
def enable11 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable11_0 := (addr1 == (11 : BitVec 9))
  let enable11_1 := we1 && enable11_0
  enable11_1

/-- The extracted gate of byte 11 equals `we1 && addr1 == 11` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable11_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable11 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 11) := by
  unfold enable11
  bv_decide

/-- Byte 11's extracted gate opens at its own offset and only there. -/
theorem enable11_open :
    enable11 true (Metronome.Bank.addrOf ⟨11, by decide⟩) = true := by
  rw [enable11_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable11_spec
#print axioms enable11_open

/-- Gate enable of byte 12, extracted from `g_byte[12].g_used.u_cg`. -/
def enable12 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable12_0 := (addr1 == (12 : BitVec 9))
  let enable12_1 := we1 && enable12_0
  enable12_1

/-- The extracted gate of byte 12 equals `we1 && addr1 == 12` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable12_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable12 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 12) := by
  unfold enable12
  bv_decide

/-- Byte 12's extracted gate opens at its own offset and only there. -/
theorem enable12_open :
    enable12 true (Metronome.Bank.addrOf ⟨12, by decide⟩) = true := by
  rw [enable12_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable12_spec
#print axioms enable12_open

/-- Gate enable of byte 13, extracted from `g_byte[13].g_used.u_cg`. -/
def enable13 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable13_0 := (addr1 == (13 : BitVec 9))
  let enable13_1 := we1 && enable13_0
  enable13_1

/-- The extracted gate of byte 13 equals `we1 && addr1 == 13` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable13_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable13 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 13) := by
  unfold enable13
  bv_decide

/-- Byte 13's extracted gate opens at its own offset and only there. -/
theorem enable13_open :
    enable13 true (Metronome.Bank.addrOf ⟨13, by decide⟩) = true := by
  rw [enable13_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable13_spec
#print axioms enable13_open

/-- Gate enable of byte 14, extracted from `g_byte[14].g_used.u_cg`. -/
def enable14 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable14_0 := (addr1 == (14 : BitVec 9))
  let enable14_1 := we1 && enable14_0
  enable14_1

/-- The extracted gate of byte 14 equals `we1 && addr1 == 14` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable14_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable14 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 14) := by
  unfold enable14
  bv_decide

/-- Byte 14's extracted gate opens at its own offset and only there. -/
theorem enable14_open :
    enable14 true (Metronome.Bank.addrOf ⟨14, by decide⟩) = true := by
  rw [enable14_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable14_spec
#print axioms enable14_open

/-- Gate enable of byte 15, extracted from `g_byte[15].g_used.u_cg`. -/
def enable15 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable15_0 := (addr1 == (15 : BitVec 9))
  let enable15_1 := we1 && enable15_0
  enable15_1

/-- The extracted gate of byte 15 equals `we1 && addr1 == 15` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable15_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable15 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 15) := by
  unfold enable15
  bv_decide

/-- Byte 15's extracted gate opens at its own offset and only there. -/
theorem enable15_open :
    enable15 true (Metronome.Bank.addrOf ⟨15, by decide⟩) = true := by
  rw [enable15_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable15_spec
#print axioms enable15_open

/-- Gate enable of byte 16, extracted from `g_byte[16].g_used.u_cg`. -/
def enable16 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable16_0 := (addr1 == (16 : BitVec 9))
  let enable16_1 := we1 && enable16_0
  enable16_1

/-- The extracted gate of byte 16 equals `we1 && addr1 == 16` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable16_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable16 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 16) := by
  unfold enable16
  bv_decide

/-- Byte 16's extracted gate opens at its own offset and only there. -/
theorem enable16_open :
    enable16 true (Metronome.Bank.addrOf ⟨16, by decide⟩) = true := by
  rw [enable16_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable16_spec
#print axioms enable16_open

/-- Gate enable of byte 17, extracted from `g_byte[17].g_used.u_cg`. -/
def enable17 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable17_0 := (addr1 == (17 : BitVec 9))
  let enable17_1 := we1 && enable17_0
  enable17_1

/-- The extracted gate of byte 17 equals `we1 && addr1 == 17` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable17_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable17 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 17) := by
  unfold enable17
  bv_decide

/-- Byte 17's extracted gate opens at its own offset and only there. -/
theorem enable17_open :
    enable17 true (Metronome.Bank.addrOf ⟨17, by decide⟩) = true := by
  rw [enable17_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable17_spec
#print axioms enable17_open

/-- Gate enable of byte 18, extracted from `g_byte[18].g_used.u_cg`. -/
def enable18 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable18_0 := (addr1 == (18 : BitVec 9))
  let enable18_1 := we1 && enable18_0
  enable18_1

/-- The extracted gate of byte 18 equals `we1 && addr1 == 18` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable18_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable18 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 18) := by
  unfold enable18
  bv_decide

/-- Byte 18's extracted gate opens at its own offset and only there. -/
theorem enable18_open :
    enable18 true (Metronome.Bank.addrOf ⟨18, by decide⟩) = true := by
  rw [enable18_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable18_spec
#print axioms enable18_open

/-- Gate enable of byte 19, extracted from `g_byte[19].g_used.u_cg`. -/
def enable19 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable19_0 := (addr1 == (19 : BitVec 9))
  let enable19_1 := we1 && enable19_0
  enable19_1

/-- The extracted gate of byte 19 equals `we1 && addr1 == 19` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable19_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable19 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 19) := by
  unfold enable19
  bv_decide

/-- Byte 19's extracted gate opens at its own offset and only there. -/
theorem enable19_open :
    enable19 true (Metronome.Bank.addrOf ⟨19, by decide⟩) = true := by
  rw [enable19_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable19_spec
#print axioms enable19_open

/-- Gate enable of byte 20, extracted from `g_byte[20].g_used.u_cg`. -/
def enable20 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable20_0 := (addr1 == (20 : BitVec 9))
  let enable20_1 := we1 && enable20_0
  enable20_1

/-- The extracted gate of byte 20 equals `we1 && addr1 == 20` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable20_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable20 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 20) := by
  unfold enable20
  bv_decide

/-- Byte 20's extracted gate opens at its own offset and only there. -/
theorem enable20_open :
    enable20 true (Metronome.Bank.addrOf ⟨20, by decide⟩) = true := by
  rw [enable20_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable20_spec
#print axioms enable20_open

/-- Gate enable of byte 21, extracted from `g_byte[21].g_used.u_cg`. -/
def enable21 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable21_0 := (addr1 == (21 : BitVec 9))
  let enable21_1 := we1 && enable21_0
  enable21_1

/-- The extracted gate of byte 21 equals `we1 && addr1 == 21` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable21_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable21 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 21) := by
  unfold enable21
  bv_decide

/-- Byte 21's extracted gate opens at its own offset and only there. -/
theorem enable21_open :
    enable21 true (Metronome.Bank.addrOf ⟨21, by decide⟩) = true := by
  rw [enable21_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable21_spec
#print axioms enable21_open

/-- Gate enable of byte 22, extracted from `g_byte[22].g_used.u_cg`. -/
def enable22 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable22_0 := (addr1 == (22 : BitVec 9))
  let enable22_1 := we1 && enable22_0
  enable22_1

/-- The extracted gate of byte 22 equals `we1 && addr1 == 22` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable22_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable22 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 22) := by
  unfold enable22
  bv_decide

/-- Byte 22's extracted gate opens at its own offset and only there. -/
theorem enable22_open :
    enable22 true (Metronome.Bank.addrOf ⟨22, by decide⟩) = true := by
  rw [enable22_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable22_spec
#print axioms enable22_open

/-- Gate enable of byte 23, extracted from `g_byte[23].g_used.u_cg`. -/
def enable23 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable23_0 := (addr1 == (23 : BitVec 9))
  let enable23_1 := we1 && enable23_0
  enable23_1

/-- The extracted gate of byte 23 equals `we1 && addr1 == 23` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable23_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable23 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 23) := by
  unfold enable23
  bv_decide

/-- Byte 23's extracted gate opens at its own offset and only there. -/
theorem enable23_open :
    enable23 true (Metronome.Bank.addrOf ⟨23, by decide⟩) = true := by
  rw [enable23_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable23_spec
#print axioms enable23_open

/-- Gate enable of byte 24, extracted from `g_byte[24].g_used.u_cg`. -/
def enable24 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable24_0 := (addr1 == (24 : BitVec 9))
  let enable24_1 := we1 && enable24_0
  enable24_1

/-- The extracted gate of byte 24 equals `we1 && addr1 == 24` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable24_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable24 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 24) := by
  unfold enable24
  bv_decide

/-- Byte 24's extracted gate opens at its own offset and only there. -/
theorem enable24_open :
    enable24 true (Metronome.Bank.addrOf ⟨24, by decide⟩) = true := by
  rw [enable24_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable24_spec
#print axioms enable24_open

/-- Gate enable of byte 25, extracted from `g_byte[25].g_used.u_cg`. -/
def enable25 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable25_0 := (addr1 == (25 : BitVec 9))
  let enable25_1 := we1 && enable25_0
  enable25_1

/-- The extracted gate of byte 25 equals `we1 && addr1 == 25` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable25_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable25 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 25) := by
  unfold enable25
  bv_decide

/-- Byte 25's extracted gate opens at its own offset and only there. -/
theorem enable25_open :
    enable25 true (Metronome.Bank.addrOf ⟨25, by decide⟩) = true := by
  rw [enable25_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable25_spec
#print axioms enable25_open

/-- Gate enable of byte 26, extracted from `g_byte[26].g_used.u_cg`. -/
def enable26 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable26_0 := (addr1 == (26 : BitVec 9))
  let enable26_1 := we1 && enable26_0
  enable26_1

/-- The extracted gate of byte 26 equals `we1 && addr1 == 26` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable26_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable26 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 26) := by
  unfold enable26
  bv_decide

/-- Byte 26's extracted gate opens at its own offset and only there. -/
theorem enable26_open :
    enable26 true (Metronome.Bank.addrOf ⟨26, by decide⟩) = true := by
  rw [enable26_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable26_spec
#print axioms enable26_open

/-- Gate enable of byte 27, extracted from `g_byte[27].g_used.u_cg`. -/
def enable27 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable27_0 := (addr1 == (27 : BitVec 9))
  let enable27_1 := we1 && enable27_0
  enable27_1

/-- The extracted gate of byte 27 equals `we1 && addr1 == 27` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable27_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable27 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 27) := by
  unfold enable27
  bv_decide

/-- Byte 27's extracted gate opens at its own offset and only there. -/
theorem enable27_open :
    enable27 true (Metronome.Bank.addrOf ⟨27, by decide⟩) = true := by
  rw [enable27_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable27_spec
#print axioms enable27_open

/-- Gate enable of byte 28, extracted from `g_byte[28].g_used.u_cg`. -/
def enable28 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable28_0 := (addr1 == (28 : BitVec 9))
  let enable28_1 := we1 && enable28_0
  enable28_1

/-- The extracted gate of byte 28 equals `we1 && addr1 == 28` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable28_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable28 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 28) := by
  unfold enable28
  bv_decide

/-- Byte 28's extracted gate opens at its own offset and only there. -/
theorem enable28_open :
    enable28 true (Metronome.Bank.addrOf ⟨28, by decide⟩) = true := by
  rw [enable28_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable28_spec
#print axioms enable28_open

/-- Gate enable of byte 32, extracted from `g_byte[32].g_used.u_cg`. -/
def enable32 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable32_0 := (addr1 == (32 : BitVec 9))
  let enable32_1 := we1 && enable32_0
  enable32_1

/-- The extracted gate of byte 32 equals `we1 && addr1 == 32` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable32_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable32 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 32) := by
  unfold enable32
  bv_decide

/-- Byte 32's extracted gate opens at its own offset and only there. -/
theorem enable32_open :
    enable32 true (Metronome.Bank.addrOf ⟨32, by decide⟩) = true := by
  rw [enable32_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable32_spec
#print axioms enable32_open

/-- Gate enable of byte 33, extracted from `g_byte[33].g_used.u_cg`. -/
def enable33 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable33_0 := (addr1 == (33 : BitVec 9))
  let enable33_1 := we1 && enable33_0
  enable33_1

/-- The extracted gate of byte 33 equals `we1 && addr1 == 33` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable33_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable33 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 33) := by
  unfold enable33
  bv_decide

/-- Byte 33's extracted gate opens at its own offset and only there. -/
theorem enable33_open :
    enable33 true (Metronome.Bank.addrOf ⟨33, by decide⟩) = true := by
  rw [enable33_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable33_spec
#print axioms enable33_open

/-- Gate enable of byte 34, extracted from `g_byte[34].g_used.u_cg`. -/
def enable34 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable34_0 := (addr1 == (34 : BitVec 9))
  let enable34_1 := we1 && enable34_0
  enable34_1

/-- The extracted gate of byte 34 equals `we1 && addr1 == 34` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable34_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable34 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 34) := by
  unfold enable34
  bv_decide

/-- Byte 34's extracted gate opens at its own offset and only there. -/
theorem enable34_open :
    enable34 true (Metronome.Bank.addrOf ⟨34, by decide⟩) = true := by
  rw [enable34_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable34_spec
#print axioms enable34_open

/-- Gate enable of byte 35, extracted from `g_byte[35].g_used.u_cg`. -/
def enable35 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable35_0 := (addr1 == (35 : BitVec 9))
  let enable35_1 := we1 && enable35_0
  enable35_1

/-- The extracted gate of byte 35 equals `we1 && addr1 == 35` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable35_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable35 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 35) := by
  unfold enable35
  bv_decide

/-- Byte 35's extracted gate opens at its own offset and only there. -/
theorem enable35_open :
    enable35 true (Metronome.Bank.addrOf ⟨35, by decide⟩) = true := by
  rw [enable35_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable35_spec
#print axioms enable35_open

/-- Gate enable of byte 36, extracted from `g_byte[36].g_used.u_cg`. -/
def enable36 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable36_0 := (addr1 == (36 : BitVec 9))
  let enable36_1 := we1 && enable36_0
  enable36_1

/-- The extracted gate of byte 36 equals `we1 && addr1 == 36` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable36_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable36 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 36) := by
  unfold enable36
  bv_decide

/-- Byte 36's extracted gate opens at its own offset and only there. -/
theorem enable36_open :
    enable36 true (Metronome.Bank.addrOf ⟨36, by decide⟩) = true := by
  rw [enable36_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable36_spec
#print axioms enable36_open

/-- Gate enable of byte 37, extracted from `g_byte[37].g_used.u_cg`. -/
def enable37 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable37_0 := (addr1 == (37 : BitVec 9))
  let enable37_1 := we1 && enable37_0
  enable37_1

/-- The extracted gate of byte 37 equals `we1 && addr1 == 37` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable37_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable37 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 37) := by
  unfold enable37
  bv_decide

/-- Byte 37's extracted gate opens at its own offset and only there. -/
theorem enable37_open :
    enable37 true (Metronome.Bank.addrOf ⟨37, by decide⟩) = true := by
  rw [enable37_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable37_spec
#print axioms enable37_open

/-- Gate enable of byte 38, extracted from `g_byte[38].g_used.u_cg`. -/
def enable38 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable38_0 := (addr1 == (38 : BitVec 9))
  let enable38_1 := we1 && enable38_0
  enable38_1

/-- The extracted gate of byte 38 equals `we1 && addr1 == 38` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable38_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable38 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 38) := by
  unfold enable38
  bv_decide

/-- Byte 38's extracted gate opens at its own offset and only there. -/
theorem enable38_open :
    enable38 true (Metronome.Bank.addrOf ⟨38, by decide⟩) = true := by
  rw [enable38_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable38_spec
#print axioms enable38_open

/-- Gate enable of byte 39, extracted from `g_byte[39].g_used.u_cg`. -/
def enable39 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable39_0 := (addr1 == (39 : BitVec 9))
  let enable39_1 := we1 && enable39_0
  enable39_1

/-- The extracted gate of byte 39 equals `we1 && addr1 == 39` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable39_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable39 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 39) := by
  unfold enable39
  bv_decide

/-- Byte 39's extracted gate opens at its own offset and only there. -/
theorem enable39_open :
    enable39 true (Metronome.Bank.addrOf ⟨39, by decide⟩) = true := by
  rw [enable39_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable39_spec
#print axioms enable39_open

/-- Gate enable of byte 40, extracted from `g_byte[40].g_used.u_cg`. -/
def enable40 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable40_0 := (addr1 == (40 : BitVec 9))
  let enable40_1 := we1 && enable40_0
  enable40_1

/-- The extracted gate of byte 40 equals `we1 && addr1 == 40` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable40_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable40 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 40) := by
  unfold enable40
  bv_decide

/-- Byte 40's extracted gate opens at its own offset and only there. -/
theorem enable40_open :
    enable40 true (Metronome.Bank.addrOf ⟨40, by decide⟩) = true := by
  rw [enable40_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable40_spec
#print axioms enable40_open

/-- Gate enable of byte 41, extracted from `g_byte[41].g_used.u_cg`. -/
def enable41 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable41_0 := (addr1 == (41 : BitVec 9))
  let enable41_1 := we1 && enable41_0
  enable41_1

/-- The extracted gate of byte 41 equals `we1 && addr1 == 41` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable41_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable41 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 41) := by
  unfold enable41
  bv_decide

/-- Byte 41's extracted gate opens at its own offset and only there. -/
theorem enable41_open :
    enable41 true (Metronome.Bank.addrOf ⟨41, by decide⟩) = true := by
  rw [enable41_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable41_spec
#print axioms enable41_open

/-- Gate enable of byte 42, extracted from `g_byte[42].g_used.u_cg`. -/
def enable42 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable42_0 := (addr1 == (42 : BitVec 9))
  let enable42_1 := we1 && enable42_0
  enable42_1

/-- The extracted gate of byte 42 equals `we1 && addr1 == 42` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable42_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable42 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 42) := by
  unfold enable42
  bv_decide

/-- Byte 42's extracted gate opens at its own offset and only there. -/
theorem enable42_open :
    enable42 true (Metronome.Bank.addrOf ⟨42, by decide⟩) = true := by
  rw [enable42_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable42_spec
#print axioms enable42_open

/-- Gate enable of byte 43, extracted from `g_byte[43].g_used.u_cg`. -/
def enable43 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable43_0 := (addr1 == (43 : BitVec 9))
  let enable43_1 := we1 && enable43_0
  enable43_1

/-- The extracted gate of byte 43 equals `we1 && addr1 == 43` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable43_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable43 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 43) := by
  unfold enable43
  bv_decide

/-- Byte 43's extracted gate opens at its own offset and only there. -/
theorem enable43_open :
    enable43 true (Metronome.Bank.addrOf ⟨43, by decide⟩) = true := by
  rw [enable43_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable43_spec
#print axioms enable43_open

/-- Gate enable of byte 44, extracted from `g_byte[44].g_used.u_cg`. -/
def enable44 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable44_0 := (addr1 == (44 : BitVec 9))
  let enable44_1 := we1 && enable44_0
  enable44_1

/-- The extracted gate of byte 44 equals `we1 && addr1 == 44` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable44_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable44 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 44) := by
  unfold enable44
  bv_decide

/-- Byte 44's extracted gate opens at its own offset and only there. -/
theorem enable44_open :
    enable44 true (Metronome.Bank.addrOf ⟨44, by decide⟩) = true := by
  rw [enable44_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable44_spec
#print axioms enable44_open

/-- Gate enable of byte 45, extracted from `g_byte[45].g_used.u_cg`. -/
def enable45 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable45_0 := (addr1 == (45 : BitVec 9))
  let enable45_1 := we1 && enable45_0
  enable45_1

/-- The extracted gate of byte 45 equals `we1 && addr1 == 45` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable45_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable45 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 45) := by
  unfold enable45
  bv_decide

/-- Byte 45's extracted gate opens at its own offset and only there. -/
theorem enable45_open :
    enable45 true (Metronome.Bank.addrOf ⟨45, by decide⟩) = true := by
  rw [enable45_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable45_spec
#print axioms enable45_open

/-- Gate enable of byte 46, extracted from `g_byte[46].g_used.u_cg`. -/
def enable46 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable46_0 := (addr1 == (46 : BitVec 9))
  let enable46_1 := we1 && enable46_0
  enable46_1

/-- The extracted gate of byte 46 equals `we1 && addr1 == 46` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable46_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable46 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 46) := by
  unfold enable46
  bv_decide

/-- Byte 46's extracted gate opens at its own offset and only there. -/
theorem enable46_open :
    enable46 true (Metronome.Bank.addrOf ⟨46, by decide⟩) = true := by
  rw [enable46_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable46_spec
#print axioms enable46_open

/-- Gate enable of byte 47, extracted from `g_byte[47].g_used.u_cg`. -/
def enable47 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable47_0 := (addr1 == (47 : BitVec 9))
  let enable47_1 := we1 && enable47_0
  enable47_1

/-- The extracted gate of byte 47 equals `we1 && addr1 == 47` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable47_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable47 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 47) := by
  unfold enable47
  bv_decide

/-- Byte 47's extracted gate opens at its own offset and only there. -/
theorem enable47_open :
    enable47 true (Metronome.Bank.addrOf ⟨47, by decide⟩) = true := by
  rw [enable47_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable47_spec
#print axioms enable47_open

/-- Gate enable of byte 48, extracted from `g_byte[48].g_used.u_cg`. -/
def enable48 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable48_0 := (addr1 == (48 : BitVec 9))
  let enable48_1 := we1 && enable48_0
  enable48_1

/-- The extracted gate of byte 48 equals `we1 && addr1 == 48` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable48_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable48 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 48) := by
  unfold enable48
  bv_decide

/-- Byte 48's extracted gate opens at its own offset and only there. -/
theorem enable48_open :
    enable48 true (Metronome.Bank.addrOf ⟨48, by decide⟩) = true := by
  rw [enable48_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable48_spec
#print axioms enable48_open

/-- Gate enable of byte 49, extracted from `g_byte[49].g_used.u_cg`. -/
def enable49 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable49_0 := (addr1 == (49 : BitVec 9))
  let enable49_1 := we1 && enable49_0
  enable49_1

/-- The extracted gate of byte 49 equals `we1 && addr1 == 49` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable49_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable49 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 49) := by
  unfold enable49
  bv_decide

/-- Byte 49's extracted gate opens at its own offset and only there. -/
theorem enable49_open :
    enable49 true (Metronome.Bank.addrOf ⟨49, by decide⟩) = true := by
  rw [enable49_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable49_spec
#print axioms enable49_open

/-- Gate enable of byte 50, extracted from `g_byte[50].g_used.u_cg`. -/
def enable50 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable50_0 := (addr1 == (50 : BitVec 9))
  let enable50_1 := we1 && enable50_0
  enable50_1

/-- The extracted gate of byte 50 equals `we1 && addr1 == 50` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable50_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable50 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 50) := by
  unfold enable50
  bv_decide

/-- Byte 50's extracted gate opens at its own offset and only there. -/
theorem enable50_open :
    enable50 true (Metronome.Bank.addrOf ⟨50, by decide⟩) = true := by
  rw [enable50_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable50_spec
#print axioms enable50_open

/-- Gate enable of byte 51, extracted from `g_byte[51].g_used.u_cg`. -/
def enable51 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable51_0 := (addr1 == (51 : BitVec 9))
  let enable51_1 := we1 && enable51_0
  enable51_1

/-- The extracted gate of byte 51 equals `we1 && addr1 == 51` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable51_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable51 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 51) := by
  unfold enable51
  bv_decide

/-- Byte 51's extracted gate opens at its own offset and only there. -/
theorem enable51_open :
    enable51 true (Metronome.Bank.addrOf ⟨51, by decide⟩) = true := by
  rw [enable51_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable51_spec
#print axioms enable51_open

/-- Gate enable of byte 52, extracted from `g_byte[52].g_used.u_cg`. -/
def enable52 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable52_0 := (addr1 == (52 : BitVec 9))
  let enable52_1 := we1 && enable52_0
  enable52_1

/-- The extracted gate of byte 52 equals `we1 && addr1 == 52` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable52_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable52 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 52) := by
  unfold enable52
  bv_decide

/-- Byte 52's extracted gate opens at its own offset and only there. -/
theorem enable52_open :
    enable52 true (Metronome.Bank.addrOf ⟨52, by decide⟩) = true := by
  rw [enable52_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable52_spec
#print axioms enable52_open

/-- Gate enable of byte 53, extracted from `g_byte[53].g_used.u_cg`. -/
def enable53 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable53_0 := (addr1 == (53 : BitVec 9))
  let enable53_1 := we1 && enable53_0
  enable53_1

/-- The extracted gate of byte 53 equals `we1 && addr1 == 53` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable53_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable53 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 53) := by
  unfold enable53
  bv_decide

/-- Byte 53's extracted gate opens at its own offset and only there. -/
theorem enable53_open :
    enable53 true (Metronome.Bank.addrOf ⟨53, by decide⟩) = true := by
  rw [enable53_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable53_spec
#print axioms enable53_open

/-- Gate enable of byte 54, extracted from `g_byte[54].g_used.u_cg`. -/
def enable54 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable54_0 := (addr1 == (54 : BitVec 9))
  let enable54_1 := we1 && enable54_0
  enable54_1

/-- The extracted gate of byte 54 equals `we1 && addr1 == 54` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable54_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable54 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 54) := by
  unfold enable54
  bv_decide

/-- Byte 54's extracted gate opens at its own offset and only there. -/
theorem enable54_open :
    enable54 true (Metronome.Bank.addrOf ⟨54, by decide⟩) = true := by
  rw [enable54_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable54_spec
#print axioms enable54_open

/-- Gate enable of byte 55, extracted from `g_byte[55].g_used.u_cg`. -/
def enable55 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable55_0 := (addr1 == (55 : BitVec 9))
  let enable55_1 := we1 && enable55_0
  enable55_1

/-- The extracted gate of byte 55 equals `we1 && addr1 == 55` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable55_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable55 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 55) := by
  unfold enable55
  bv_decide

/-- Byte 55's extracted gate opens at its own offset and only there. -/
theorem enable55_open :
    enable55 true (Metronome.Bank.addrOf ⟨55, by decide⟩) = true := by
  rw [enable55_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable55_spec
#print axioms enable55_open

/-- Gate enable of byte 56, extracted from `g_byte[56].g_used.u_cg`. -/
def enable56 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable56_0 := (addr1 == (56 : BitVec 9))
  let enable56_1 := we1 && enable56_0
  enable56_1

/-- The extracted gate of byte 56 equals `we1 && addr1 == 56` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable56_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable56 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 56) := by
  unfold enable56
  bv_decide

/-- Byte 56's extracted gate opens at its own offset and only there. -/
theorem enable56_open :
    enable56 true (Metronome.Bank.addrOf ⟨56, by decide⟩) = true := by
  rw [enable56_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable56_spec
#print axioms enable56_open

/-- Gate enable of byte 57, extracted from `g_byte[57].g_used.u_cg`. -/
def enable57 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable57_0 := (addr1 == (57 : BitVec 9))
  let enable57_1 := we1 && enable57_0
  enable57_1

/-- The extracted gate of byte 57 equals `we1 && addr1 == 57` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable57_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable57 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 57) := by
  unfold enable57
  bv_decide

/-- Byte 57's extracted gate opens at its own offset and only there. -/
theorem enable57_open :
    enable57 true (Metronome.Bank.addrOf ⟨57, by decide⟩) = true := by
  rw [enable57_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable57_spec
#print axioms enable57_open

/-- Gate enable of byte 58, extracted from `g_byte[58].g_used.u_cg`. -/
def enable58 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable58_0 := (addr1 == (58 : BitVec 9))
  let enable58_1 := we1 && enable58_0
  enable58_1

/-- The extracted gate of byte 58 equals `we1 && addr1 == 58` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable58_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable58 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 58) := by
  unfold enable58
  bv_decide

/-- Byte 58's extracted gate opens at its own offset and only there. -/
theorem enable58_open :
    enable58 true (Metronome.Bank.addrOf ⟨58, by decide⟩) = true := by
  rw [enable58_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable58_spec
#print axioms enable58_open

/-- Gate enable of byte 59, extracted from `g_byte[59].g_used.u_cg`. -/
def enable59 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable59_0 := (addr1 == (59 : BitVec 9))
  let enable59_1 := we1 && enable59_0
  enable59_1

/-- The extracted gate of byte 59 equals `we1 && addr1 == 59` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable59_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable59 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 59) := by
  unfold enable59
  bv_decide

/-- Byte 59's extracted gate opens at its own offset and only there. -/
theorem enable59_open :
    enable59 true (Metronome.Bank.addrOf ⟨59, by decide⟩) = true := by
  rw [enable59_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable59_spec
#print axioms enable59_open

/-- Gate enable of byte 60, extracted from `g_byte[60].g_used.u_cg`. -/
def enable60 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable60_0 := (addr1 == (60 : BitVec 9))
  let enable60_1 := we1 && enable60_0
  enable60_1

/-- The extracted gate of byte 60 equals `we1 && addr1 == 60` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable60_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable60 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 60) := by
  unfold enable60
  bv_decide

/-- Byte 60's extracted gate opens at its own offset and only there. -/
theorem enable60_open :
    enable60 true (Metronome.Bank.addrOf ⟨60, by decide⟩) = true := by
  rw [enable60_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable60_spec
#print axioms enable60_open

/-- Gate enable of byte 64, extracted from `g_byte[64].g_used.u_cg`. -/
def enable64 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable64_0 := (addr1 == (64 : BitVec 9))
  let enable64_1 := we1 && enable64_0
  enable64_1

/-- The extracted gate of byte 64 equals `we1 && addr1 == 64` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable64_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable64 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 64) := by
  unfold enable64
  bv_decide

/-- Byte 64's extracted gate opens at its own offset and only there. -/
theorem enable64_open :
    enable64 true (Metronome.Bank.addrOf ⟨64, by decide⟩) = true := by
  rw [enable64_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable64_spec
#print axioms enable64_open

/-- Gate enable of byte 65, extracted from `g_byte[65].g_used.u_cg`. -/
def enable65 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable65_0 := (addr1 == (65 : BitVec 9))
  let enable65_1 := we1 && enable65_0
  enable65_1

/-- The extracted gate of byte 65 equals `we1 && addr1 == 65` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable65_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable65 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 65) := by
  unfold enable65
  bv_decide

/-- Byte 65's extracted gate opens at its own offset and only there. -/
theorem enable65_open :
    enable65 true (Metronome.Bank.addrOf ⟨65, by decide⟩) = true := by
  rw [enable65_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable65_spec
#print axioms enable65_open

/-- Gate enable of byte 66, extracted from `g_byte[66].g_used.u_cg`. -/
def enable66 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable66_0 := (addr1 == (66 : BitVec 9))
  let enable66_1 := we1 && enable66_0
  enable66_1

/-- The extracted gate of byte 66 equals `we1 && addr1 == 66` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable66_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable66 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 66) := by
  unfold enable66
  bv_decide

/-- Byte 66's extracted gate opens at its own offset and only there. -/
theorem enable66_open :
    enable66 true (Metronome.Bank.addrOf ⟨66, by decide⟩) = true := by
  rw [enable66_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable66_spec
#print axioms enable66_open

/-- Gate enable of byte 67, extracted from `g_byte[67].g_used.u_cg`. -/
def enable67 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable67_0 := (addr1 == (67 : BitVec 9))
  let enable67_1 := we1 && enable67_0
  enable67_1

/-- The extracted gate of byte 67 equals `we1 && addr1 == 67` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable67_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable67 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 67) := by
  unfold enable67
  bv_decide

/-- Byte 67's extracted gate opens at its own offset and only there. -/
theorem enable67_open :
    enable67 true (Metronome.Bank.addrOf ⟨67, by decide⟩) = true := by
  rw [enable67_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable67_spec
#print axioms enable67_open

/-- Gate enable of byte 68, extracted from `g_byte[68].g_used.u_cg`. -/
def enable68 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable68_0 := (addr1 == (68 : BitVec 9))
  let enable68_1 := we1 && enable68_0
  enable68_1

/-- The extracted gate of byte 68 equals `we1 && addr1 == 68` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable68_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable68 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 68) := by
  unfold enable68
  bv_decide

/-- Byte 68's extracted gate opens at its own offset and only there. -/
theorem enable68_open :
    enable68 true (Metronome.Bank.addrOf ⟨68, by decide⟩) = true := by
  rw [enable68_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable68_spec
#print axioms enable68_open

/-- Gate enable of byte 69, extracted from `g_byte[69].g_used.u_cg`. -/
def enable69 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable69_0 := (addr1 == (69 : BitVec 9))
  let enable69_1 := we1 && enable69_0
  enable69_1

/-- The extracted gate of byte 69 equals `we1 && addr1 == 69` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable69_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable69 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 69) := by
  unfold enable69
  bv_decide

/-- Byte 69's extracted gate opens at its own offset and only there. -/
theorem enable69_open :
    enable69 true (Metronome.Bank.addrOf ⟨69, by decide⟩) = true := by
  rw [enable69_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable69_spec
#print axioms enable69_open

/-- Gate enable of byte 70, extracted from `g_byte[70].g_used.u_cg`. -/
def enable70 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable70_0 := (addr1 == (70 : BitVec 9))
  let enable70_1 := we1 && enable70_0
  enable70_1

/-- The extracted gate of byte 70 equals `we1 && addr1 == 70` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable70_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable70 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 70) := by
  unfold enable70
  bv_decide

/-- Byte 70's extracted gate opens at its own offset and only there. -/
theorem enable70_open :
    enable70 true (Metronome.Bank.addrOf ⟨70, by decide⟩) = true := by
  rw [enable70_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable70_spec
#print axioms enable70_open

/-- Gate enable of byte 71, extracted from `g_byte[71].g_used.u_cg`. -/
def enable71 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable71_0 := (addr1 == (71 : BitVec 9))
  let enable71_1 := we1 && enable71_0
  enable71_1

/-- The extracted gate of byte 71 equals `we1 && addr1 == 71` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable71_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable71 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 71) := by
  unfold enable71
  bv_decide

/-- Byte 71's extracted gate opens at its own offset and only there. -/
theorem enable71_open :
    enable71 true (Metronome.Bank.addrOf ⟨71, by decide⟩) = true := by
  rw [enable71_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable71_spec
#print axioms enable71_open

/-- Gate enable of byte 72, extracted from `g_byte[72].g_used.u_cg`. -/
def enable72 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable72_0 := (addr1 == (72 : BitVec 9))
  let enable72_1 := we1 && enable72_0
  enable72_1

/-- The extracted gate of byte 72 equals `we1 && addr1 == 72` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable72_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable72 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 72) := by
  unfold enable72
  bv_decide

/-- Byte 72's extracted gate opens at its own offset and only there. -/
theorem enable72_open :
    enable72 true (Metronome.Bank.addrOf ⟨72, by decide⟩) = true := by
  rw [enable72_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable72_spec
#print axioms enable72_open

/-- Gate enable of byte 73, extracted from `g_byte[73].g_used.u_cg`. -/
def enable73 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable73_0 := (addr1 == (73 : BitVec 9))
  let enable73_1 := we1 && enable73_0
  enable73_1

/-- The extracted gate of byte 73 equals `we1 && addr1 == 73` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable73_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable73 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 73) := by
  unfold enable73
  bv_decide

/-- Byte 73's extracted gate opens at its own offset and only there. -/
theorem enable73_open :
    enable73 true (Metronome.Bank.addrOf ⟨73, by decide⟩) = true := by
  rw [enable73_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable73_spec
#print axioms enable73_open

/-- Gate enable of byte 74, extracted from `g_byte[74].g_used.u_cg`. -/
def enable74 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable74_0 := (addr1 == (74 : BitVec 9))
  let enable74_1 := we1 && enable74_0
  enable74_1

/-- The extracted gate of byte 74 equals `we1 && addr1 == 74` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable74_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable74 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 74) := by
  unfold enable74
  bv_decide

/-- Byte 74's extracted gate opens at its own offset and only there. -/
theorem enable74_open :
    enable74 true (Metronome.Bank.addrOf ⟨74, by decide⟩) = true := by
  rw [enable74_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable74_spec
#print axioms enable74_open

/-- Gate enable of byte 75, extracted from `g_byte[75].g_used.u_cg`. -/
def enable75 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable75_0 := (addr1 == (75 : BitVec 9))
  let enable75_1 := we1 && enable75_0
  enable75_1

/-- The extracted gate of byte 75 equals `we1 && addr1 == 75` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable75_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable75 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 75) := by
  unfold enable75
  bv_decide

/-- Byte 75's extracted gate opens at its own offset and only there. -/
theorem enable75_open :
    enable75 true (Metronome.Bank.addrOf ⟨75, by decide⟩) = true := by
  rw [enable75_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable75_spec
#print axioms enable75_open

/-- Gate enable of byte 76, extracted from `g_byte[76].g_used.u_cg`. -/
def enable76 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable76_0 := (addr1 == (76 : BitVec 9))
  let enable76_1 := we1 && enable76_0
  enable76_1

/-- The extracted gate of byte 76 equals `we1 && addr1 == 76` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable76_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable76 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 76) := by
  unfold enable76
  bv_decide

/-- Byte 76's extracted gate opens at its own offset and only there. -/
theorem enable76_open :
    enable76 true (Metronome.Bank.addrOf ⟨76, by decide⟩) = true := by
  rw [enable76_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable76_spec
#print axioms enable76_open

/-- Gate enable of byte 77, extracted from `g_byte[77].g_used.u_cg`. -/
def enable77 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable77_0 := (addr1 == (77 : BitVec 9))
  let enable77_1 := we1 && enable77_0
  enable77_1

/-- The extracted gate of byte 77 equals `we1 && addr1 == 77` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable77_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable77 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 77) := by
  unfold enable77
  bv_decide

/-- Byte 77's extracted gate opens at its own offset and only there. -/
theorem enable77_open :
    enable77 true (Metronome.Bank.addrOf ⟨77, by decide⟩) = true := by
  rw [enable77_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable77_spec
#print axioms enable77_open

/-- Gate enable of byte 78, extracted from `g_byte[78].g_used.u_cg`. -/
def enable78 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable78_0 := (addr1 == (78 : BitVec 9))
  let enable78_1 := we1 && enable78_0
  enable78_1

/-- The extracted gate of byte 78 equals `we1 && addr1 == 78` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable78_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable78 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 78) := by
  unfold enable78
  bv_decide

/-- Byte 78's extracted gate opens at its own offset and only there. -/
theorem enable78_open :
    enable78 true (Metronome.Bank.addrOf ⟨78, by decide⟩) = true := by
  rw [enable78_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable78_spec
#print axioms enable78_open

/-- Gate enable of byte 79, extracted from `g_byte[79].g_used.u_cg`. -/
def enable79 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable79_0 := (addr1 == (79 : BitVec 9))
  let enable79_1 := we1 && enable79_0
  enable79_1

/-- The extracted gate of byte 79 equals `we1 && addr1 == 79` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable79_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable79 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 79) := by
  unfold enable79
  bv_decide

/-- Byte 79's extracted gate opens at its own offset and only there. -/
theorem enable79_open :
    enable79 true (Metronome.Bank.addrOf ⟨79, by decide⟩) = true := by
  rw [enable79_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable79_spec
#print axioms enable79_open

/-- Gate enable of byte 80, extracted from `g_byte[80].g_used.u_cg`. -/
def enable80 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable80_0 := (addr1 == (80 : BitVec 9))
  let enable80_1 := we1 && enable80_0
  enable80_1

/-- The extracted gate of byte 80 equals `we1 && addr1 == 80` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable80_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable80 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 80) := by
  unfold enable80
  bv_decide

/-- Byte 80's extracted gate opens at its own offset and only there. -/
theorem enable80_open :
    enable80 true (Metronome.Bank.addrOf ⟨80, by decide⟩) = true := by
  rw [enable80_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable80_spec
#print axioms enable80_open

/-- Gate enable of byte 81, extracted from `g_byte[81].g_used.u_cg`. -/
def enable81 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable81_0 := (addr1 == (81 : BitVec 9))
  let enable81_1 := we1 && enable81_0
  enable81_1

/-- The extracted gate of byte 81 equals `we1 && addr1 == 81` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable81_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable81 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 81) := by
  unfold enable81
  bv_decide

/-- Byte 81's extracted gate opens at its own offset and only there. -/
theorem enable81_open :
    enable81 true (Metronome.Bank.addrOf ⟨81, by decide⟩) = true := by
  rw [enable81_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable81_spec
#print axioms enable81_open

/-- Gate enable of byte 82, extracted from `g_byte[82].g_used.u_cg`. -/
def enable82 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable82_0 := (addr1 == (82 : BitVec 9))
  let enable82_1 := we1 && enable82_0
  enable82_1

/-- The extracted gate of byte 82 equals `we1 && addr1 == 82` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable82_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable82 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 82) := by
  unfold enable82
  bv_decide

/-- Byte 82's extracted gate opens at its own offset and only there. -/
theorem enable82_open :
    enable82 true (Metronome.Bank.addrOf ⟨82, by decide⟩) = true := by
  rw [enable82_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable82_spec
#print axioms enable82_open

/-- Gate enable of byte 83, extracted from `g_byte[83].g_used.u_cg`. -/
def enable83 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable83_0 := (addr1 == (83 : BitVec 9))
  let enable83_1 := we1 && enable83_0
  enable83_1

/-- The extracted gate of byte 83 equals `we1 && addr1 == 83` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable83_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable83 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 83) := by
  unfold enable83
  bv_decide

/-- Byte 83's extracted gate opens at its own offset and only there. -/
theorem enable83_open :
    enable83 true (Metronome.Bank.addrOf ⟨83, by decide⟩) = true := by
  rw [enable83_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable83_spec
#print axioms enable83_open

/-- Gate enable of byte 84, extracted from `g_byte[84].g_used.u_cg`. -/
def enable84 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable84_0 := (addr1 == (84 : BitVec 9))
  let enable84_1 := we1 && enable84_0
  enable84_1

/-- The extracted gate of byte 84 equals `we1 && addr1 == 84` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable84_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable84 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 84) := by
  unfold enable84
  bv_decide

/-- Byte 84's extracted gate opens at its own offset and only there. -/
theorem enable84_open :
    enable84 true (Metronome.Bank.addrOf ⟨84, by decide⟩) = true := by
  rw [enable84_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable84_spec
#print axioms enable84_open

/-- Gate enable of byte 85, extracted from `g_byte[85].g_used.u_cg`. -/
def enable85 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable85_0 := (addr1 == (85 : BitVec 9))
  let enable85_1 := we1 && enable85_0
  enable85_1

/-- The extracted gate of byte 85 equals `we1 && addr1 == 85` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable85_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable85 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 85) := by
  unfold enable85
  bv_decide

/-- Byte 85's extracted gate opens at its own offset and only there. -/
theorem enable85_open :
    enable85 true (Metronome.Bank.addrOf ⟨85, by decide⟩) = true := by
  rw [enable85_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable85_spec
#print axioms enable85_open

/-- Gate enable of byte 86, extracted from `g_byte[86].g_used.u_cg`. -/
def enable86 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable86_0 := (addr1 == (86 : BitVec 9))
  let enable86_1 := we1 && enable86_0
  enable86_1

/-- The extracted gate of byte 86 equals `we1 && addr1 == 86` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable86_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable86 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 86) := by
  unfold enable86
  bv_decide

/-- Byte 86's extracted gate opens at its own offset and only there. -/
theorem enable86_open :
    enable86 true (Metronome.Bank.addrOf ⟨86, by decide⟩) = true := by
  rw [enable86_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable86_spec
#print axioms enable86_open

/-- Gate enable of byte 87, extracted from `g_byte[87].g_used.u_cg`. -/
def enable87 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable87_0 := (addr1 == (87 : BitVec 9))
  let enable87_1 := we1 && enable87_0
  enable87_1

/-- The extracted gate of byte 87 equals `we1 && addr1 == 87` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable87_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable87 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 87) := by
  unfold enable87
  bv_decide

/-- Byte 87's extracted gate opens at its own offset and only there. -/
theorem enable87_open :
    enable87 true (Metronome.Bank.addrOf ⟨87, by decide⟩) = true := by
  rw [enable87_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable87_spec
#print axioms enable87_open

/-- Gate enable of byte 88, extracted from `g_byte[88].g_used.u_cg`. -/
def enable88 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable88_0 := (addr1 == (88 : BitVec 9))
  let enable88_1 := we1 && enable88_0
  enable88_1

/-- The extracted gate of byte 88 equals `we1 && addr1 == 88` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable88_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable88 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 88) := by
  unfold enable88
  bv_decide

/-- Byte 88's extracted gate opens at its own offset and only there. -/
theorem enable88_open :
    enable88 true (Metronome.Bank.addrOf ⟨88, by decide⟩) = true := by
  rw [enable88_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable88_spec
#print axioms enable88_open

/-- Gate enable of byte 89, extracted from `g_byte[89].g_used.u_cg`. -/
def enable89 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable89_0 := (addr1 == (89 : BitVec 9))
  let enable89_1 := we1 && enable89_0
  enable89_1

/-- The extracted gate of byte 89 equals `we1 && addr1 == 89` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable89_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable89 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 89) := by
  unfold enable89
  bv_decide

/-- Byte 89's extracted gate opens at its own offset and only there. -/
theorem enable89_open :
    enable89 true (Metronome.Bank.addrOf ⟨89, by decide⟩) = true := by
  rw [enable89_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable89_spec
#print axioms enable89_open

/-- Gate enable of byte 90, extracted from `g_byte[90].g_used.u_cg`. -/
def enable90 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable90_0 := (addr1 == (90 : BitVec 9))
  let enable90_1 := we1 && enable90_0
  enable90_1

/-- The extracted gate of byte 90 equals `we1 && addr1 == 90` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable90_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable90 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 90) := by
  unfold enable90
  bv_decide

/-- Byte 90's extracted gate opens at its own offset and only there. -/
theorem enable90_open :
    enable90 true (Metronome.Bank.addrOf ⟨90, by decide⟩) = true := by
  rw [enable90_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable90_spec
#print axioms enable90_open

/-- Gate enable of byte 91, extracted from `g_byte[91].g_used.u_cg`. -/
def enable91 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable91_0 := (addr1 == (91 : BitVec 9))
  let enable91_1 := we1 && enable91_0
  enable91_1

/-- The extracted gate of byte 91 equals `we1 && addr1 == 91` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable91_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable91 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 91) := by
  unfold enable91
  bv_decide

/-- Byte 91's extracted gate opens at its own offset and only there. -/
theorem enable91_open :
    enable91 true (Metronome.Bank.addrOf ⟨91, by decide⟩) = true := by
  rw [enable91_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable91_spec
#print axioms enable91_open

/-- Gate enable of byte 92, extracted from `g_byte[92].g_used.u_cg`. -/
def enable92 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable92_0 := (addr1 == (92 : BitVec 9))
  let enable92_1 := we1 && enable92_0
  enable92_1

/-- The extracted gate of byte 92 equals `we1 && addr1 == 92` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable92_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable92 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 92) := by
  unfold enable92
  bv_decide

/-- Byte 92's extracted gate opens at its own offset and only there. -/
theorem enable92_open :
    enable92 true (Metronome.Bank.addrOf ⟨92, by decide⟩) = true := by
  rw [enable92_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable92_spec
#print axioms enable92_open

/-- Gate enable of byte 96, extracted from `g_byte[96].g_used.u_cg`. -/
def enable96 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable96_0 := (addr1 == (96 : BitVec 9))
  let enable96_1 := we1 && enable96_0
  enable96_1

/-- The extracted gate of byte 96 equals `we1 && addr1 == 96` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable96_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable96 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 96) := by
  unfold enable96
  bv_decide

/-- Byte 96's extracted gate opens at its own offset and only there. -/
theorem enable96_open :
    enable96 true (Metronome.Bank.addrOf ⟨96, by decide⟩) = true := by
  rw [enable96_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable96_spec
#print axioms enable96_open

/-- Gate enable of byte 97, extracted from `g_byte[97].g_used.u_cg`. -/
def enable97 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable97_0 := (addr1 == (97 : BitVec 9))
  let enable97_1 := we1 && enable97_0
  enable97_1

/-- The extracted gate of byte 97 equals `we1 && addr1 == 97` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable97_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable97 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 97) := by
  unfold enable97
  bv_decide

/-- Byte 97's extracted gate opens at its own offset and only there. -/
theorem enable97_open :
    enable97 true (Metronome.Bank.addrOf ⟨97, by decide⟩) = true := by
  rw [enable97_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable97_spec
#print axioms enable97_open

/-- Gate enable of byte 98, extracted from `g_byte[98].g_used.u_cg`. -/
def enable98 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable98_0 := (addr1 == (98 : BitVec 9))
  let enable98_1 := we1 && enable98_0
  enable98_1

/-- The extracted gate of byte 98 equals `we1 && addr1 == 98` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable98_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable98 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 98) := by
  unfold enable98
  bv_decide

/-- Byte 98's extracted gate opens at its own offset and only there. -/
theorem enable98_open :
    enable98 true (Metronome.Bank.addrOf ⟨98, by decide⟩) = true := by
  rw [enable98_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable98_spec
#print axioms enable98_open

/-- Gate enable of byte 99, extracted from `g_byte[99].g_used.u_cg`. -/
def enable99 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable99_0 := (addr1 == (99 : BitVec 9))
  let enable99_1 := we1 && enable99_0
  enable99_1

/-- The extracted gate of byte 99 equals `we1 && addr1 == 99` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable99_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable99 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 99) := by
  unfold enable99
  bv_decide

/-- Byte 99's extracted gate opens at its own offset and only there. -/
theorem enable99_open :
    enable99 true (Metronome.Bank.addrOf ⟨99, by decide⟩) = true := by
  rw [enable99_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable99_spec
#print axioms enable99_open

/-- Gate enable of byte 100, extracted from `g_byte[100].g_used.u_cg`. -/
def enable100 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable100_0 := (addr1 == (100 : BitVec 9))
  let enable100_1 := we1 && enable100_0
  enable100_1

/-- The extracted gate of byte 100 equals `we1 && addr1 == 100` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable100_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable100 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 100) := by
  unfold enable100
  bv_decide

/-- Byte 100's extracted gate opens at its own offset and only there. -/
theorem enable100_open :
    enable100 true (Metronome.Bank.addrOf ⟨100, by decide⟩) = true := by
  rw [enable100_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable100_spec
#print axioms enable100_open

/-- Gate enable of byte 101, extracted from `g_byte[101].g_used.u_cg`. -/
def enable101 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable101_0 := (addr1 == (101 : BitVec 9))
  let enable101_1 := we1 && enable101_0
  enable101_1

/-- The extracted gate of byte 101 equals `we1 && addr1 == 101` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable101_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable101 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 101) := by
  unfold enable101
  bv_decide

/-- Byte 101's extracted gate opens at its own offset and only there. -/
theorem enable101_open :
    enable101 true (Metronome.Bank.addrOf ⟨101, by decide⟩) = true := by
  rw [enable101_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable101_spec
#print axioms enable101_open

/-- Gate enable of byte 102, extracted from `g_byte[102].g_used.u_cg`. -/
def enable102 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable102_0 := (addr1 == (102 : BitVec 9))
  let enable102_1 := we1 && enable102_0
  enable102_1

/-- The extracted gate of byte 102 equals `we1 && addr1 == 102` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable102_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable102 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 102) := by
  unfold enable102
  bv_decide

/-- Byte 102's extracted gate opens at its own offset and only there. -/
theorem enable102_open :
    enable102 true (Metronome.Bank.addrOf ⟨102, by decide⟩) = true := by
  rw [enable102_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable102_spec
#print axioms enable102_open

/-- Gate enable of byte 103, extracted from `g_byte[103].g_used.u_cg`. -/
def enable103 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable103_0 := (addr1 == (103 : BitVec 9))
  let enable103_1 := we1 && enable103_0
  enable103_1

/-- The extracted gate of byte 103 equals `we1 && addr1 == 103` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable103_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable103 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 103) := by
  unfold enable103
  bv_decide

/-- Byte 103's extracted gate opens at its own offset and only there. -/
theorem enable103_open :
    enable103 true (Metronome.Bank.addrOf ⟨103, by decide⟩) = true := by
  rw [enable103_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable103_spec
#print axioms enable103_open

/-- Gate enable of byte 104, extracted from `g_byte[104].g_used.u_cg`. -/
def enable104 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable104_0 := (addr1 == (104 : BitVec 9))
  let enable104_1 := we1 && enable104_0
  enable104_1

/-- The extracted gate of byte 104 equals `we1 && addr1 == 104` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable104_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable104 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 104) := by
  unfold enable104
  bv_decide

/-- Byte 104's extracted gate opens at its own offset and only there. -/
theorem enable104_open :
    enable104 true (Metronome.Bank.addrOf ⟨104, by decide⟩) = true := by
  rw [enable104_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable104_spec
#print axioms enable104_open

/-- Gate enable of byte 105, extracted from `g_byte[105].g_used.u_cg`. -/
def enable105 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable105_0 := (addr1 == (105 : BitVec 9))
  let enable105_1 := we1 && enable105_0
  enable105_1

/-- The extracted gate of byte 105 equals `we1 && addr1 == 105` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable105_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable105 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 105) := by
  unfold enable105
  bv_decide

/-- Byte 105's extracted gate opens at its own offset and only there. -/
theorem enable105_open :
    enable105 true (Metronome.Bank.addrOf ⟨105, by decide⟩) = true := by
  rw [enable105_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable105_spec
#print axioms enable105_open

/-- Gate enable of byte 106, extracted from `g_byte[106].g_used.u_cg`. -/
def enable106 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable106_0 := (addr1 == (106 : BitVec 9))
  let enable106_1 := we1 && enable106_0
  enable106_1

/-- The extracted gate of byte 106 equals `we1 && addr1 == 106` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable106_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable106 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 106) := by
  unfold enable106
  bv_decide

/-- Byte 106's extracted gate opens at its own offset and only there. -/
theorem enable106_open :
    enable106 true (Metronome.Bank.addrOf ⟨106, by decide⟩) = true := by
  rw [enable106_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable106_spec
#print axioms enable106_open

/-- Gate enable of byte 107, extracted from `g_byte[107].g_used.u_cg`. -/
def enable107 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable107_0 := (addr1 == (107 : BitVec 9))
  let enable107_1 := we1 && enable107_0
  enable107_1

/-- The extracted gate of byte 107 equals `we1 && addr1 == 107` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable107_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable107 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 107) := by
  unfold enable107
  bv_decide

/-- Byte 107's extracted gate opens at its own offset and only there. -/
theorem enable107_open :
    enable107 true (Metronome.Bank.addrOf ⟨107, by decide⟩) = true := by
  rw [enable107_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable107_spec
#print axioms enable107_open

/-- Gate enable of byte 108, extracted from `g_byte[108].g_used.u_cg`. -/
def enable108 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable108_0 := (addr1 == (108 : BitVec 9))
  let enable108_1 := we1 && enable108_0
  enable108_1

/-- The extracted gate of byte 108 equals `we1 && addr1 == 108` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable108_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable108 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 108) := by
  unfold enable108
  bv_decide

/-- Byte 108's extracted gate opens at its own offset and only there. -/
theorem enable108_open :
    enable108 true (Metronome.Bank.addrOf ⟨108, by decide⟩) = true := by
  rw [enable108_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable108_spec
#print axioms enable108_open

/-- Gate enable of byte 109, extracted from `g_byte[109].g_used.u_cg`. -/
def enable109 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable109_0 := (addr1 == (109 : BitVec 9))
  let enable109_1 := we1 && enable109_0
  enable109_1

/-- The extracted gate of byte 109 equals `we1 && addr1 == 109` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable109_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable109 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 109) := by
  unfold enable109
  bv_decide

/-- Byte 109's extracted gate opens at its own offset and only there. -/
theorem enable109_open :
    enable109 true (Metronome.Bank.addrOf ⟨109, by decide⟩) = true := by
  rw [enable109_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable109_spec
#print axioms enable109_open

/-- Gate enable of byte 110, extracted from `g_byte[110].g_used.u_cg`. -/
def enable110 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable110_0 := (addr1 == (110 : BitVec 9))
  let enable110_1 := we1 && enable110_0
  enable110_1

/-- The extracted gate of byte 110 equals `we1 && addr1 == 110` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable110_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable110 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 110) := by
  unfold enable110
  bv_decide

/-- Byte 110's extracted gate opens at its own offset and only there. -/
theorem enable110_open :
    enable110 true (Metronome.Bank.addrOf ⟨110, by decide⟩) = true := by
  rw [enable110_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable110_spec
#print axioms enable110_open

/-- Gate enable of byte 111, extracted from `g_byte[111].g_used.u_cg`. -/
def enable111 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable111_0 := (addr1 == (111 : BitVec 9))
  let enable111_1 := we1 && enable111_0
  enable111_1

/-- The extracted gate of byte 111 equals `we1 && addr1 == 111` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable111_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable111 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 111) := by
  unfold enable111
  bv_decide

/-- Byte 111's extracted gate opens at its own offset and only there. -/
theorem enable111_open :
    enable111 true (Metronome.Bank.addrOf ⟨111, by decide⟩) = true := by
  rw [enable111_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable111_spec
#print axioms enable111_open

/-- Gate enable of byte 112, extracted from `g_byte[112].g_used.u_cg`. -/
def enable112 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable112_0 := (addr1 == (112 : BitVec 9))
  let enable112_1 := we1 && enable112_0
  enable112_1

/-- The extracted gate of byte 112 equals `we1 && addr1 == 112` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable112_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable112 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 112) := by
  unfold enable112
  bv_decide

/-- Byte 112's extracted gate opens at its own offset and only there. -/
theorem enable112_open :
    enable112 true (Metronome.Bank.addrOf ⟨112, by decide⟩) = true := by
  rw [enable112_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable112_spec
#print axioms enable112_open

/-- Gate enable of byte 113, extracted from `g_byte[113].g_used.u_cg`. -/
def enable113 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable113_0 := (addr1 == (113 : BitVec 9))
  let enable113_1 := we1 && enable113_0
  enable113_1

/-- The extracted gate of byte 113 equals `we1 && addr1 == 113` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable113_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable113 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 113) := by
  unfold enable113
  bv_decide

/-- Byte 113's extracted gate opens at its own offset and only there. -/
theorem enable113_open :
    enable113 true (Metronome.Bank.addrOf ⟨113, by decide⟩) = true := by
  rw [enable113_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable113_spec
#print axioms enable113_open

/-- Gate enable of byte 114, extracted from `g_byte[114].g_used.u_cg`. -/
def enable114 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable114_0 := (addr1 == (114 : BitVec 9))
  let enable114_1 := we1 && enable114_0
  enable114_1

/-- The extracted gate of byte 114 equals `we1 && addr1 == 114` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable114_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable114 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 114) := by
  unfold enable114
  bv_decide

/-- Byte 114's extracted gate opens at its own offset and only there. -/
theorem enable114_open :
    enable114 true (Metronome.Bank.addrOf ⟨114, by decide⟩) = true := by
  rw [enable114_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable114_spec
#print axioms enable114_open

/-- Gate enable of byte 115, extracted from `g_byte[115].g_used.u_cg`. -/
def enable115 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable115_0 := (addr1 == (115 : BitVec 9))
  let enable115_1 := we1 && enable115_0
  enable115_1

/-- The extracted gate of byte 115 equals `we1 && addr1 == 115` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable115_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable115 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 115) := by
  unfold enable115
  bv_decide

/-- Byte 115's extracted gate opens at its own offset and only there. -/
theorem enable115_open :
    enable115 true (Metronome.Bank.addrOf ⟨115, by decide⟩) = true := by
  rw [enable115_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable115_spec
#print axioms enable115_open

/-- Gate enable of byte 116, extracted from `g_byte[116].g_used.u_cg`. -/
def enable116 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable116_0 := (addr1 == (116 : BitVec 9))
  let enable116_1 := we1 && enable116_0
  enable116_1

/-- The extracted gate of byte 116 equals `we1 && addr1 == 116` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable116_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable116 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 116) := by
  unfold enable116
  bv_decide

/-- Byte 116's extracted gate opens at its own offset and only there. -/
theorem enable116_open :
    enable116 true (Metronome.Bank.addrOf ⟨116, by decide⟩) = true := by
  rw [enable116_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable116_spec
#print axioms enable116_open

/-- Gate enable of byte 117, extracted from `g_byte[117].g_used.u_cg`. -/
def enable117 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable117_0 := (addr1 == (117 : BitVec 9))
  let enable117_1 := we1 && enable117_0
  enable117_1

/-- The extracted gate of byte 117 equals `we1 && addr1 == 117` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable117_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable117 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 117) := by
  unfold enable117
  bv_decide

/-- Byte 117's extracted gate opens at its own offset and only there. -/
theorem enable117_open :
    enable117 true (Metronome.Bank.addrOf ⟨117, by decide⟩) = true := by
  rw [enable117_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable117_spec
#print axioms enable117_open

/-- Gate enable of byte 118, extracted from `g_byte[118].g_used.u_cg`. -/
def enable118 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable118_0 := (addr1 == (118 : BitVec 9))
  let enable118_1 := we1 && enable118_0
  enable118_1

/-- The extracted gate of byte 118 equals `we1 && addr1 == 118` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable118_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable118 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 118) := by
  unfold enable118
  bv_decide

/-- Byte 118's extracted gate opens at its own offset and only there. -/
theorem enable118_open :
    enable118 true (Metronome.Bank.addrOf ⟨118, by decide⟩) = true := by
  rw [enable118_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable118_spec
#print axioms enable118_open

/-- Gate enable of byte 119, extracted from `g_byte[119].g_used.u_cg`. -/
def enable119 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable119_0 := (addr1 == (119 : BitVec 9))
  let enable119_1 := we1 && enable119_0
  enable119_1

/-- The extracted gate of byte 119 equals `we1 && addr1 == 119` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable119_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable119 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 119) := by
  unfold enable119
  bv_decide

/-- Byte 119's extracted gate opens at its own offset and only there. -/
theorem enable119_open :
    enable119 true (Metronome.Bank.addrOf ⟨119, by decide⟩) = true := by
  rw [enable119_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable119_spec
#print axioms enable119_open

/-- Gate enable of byte 120, extracted from `g_byte[120].g_used.u_cg`. -/
def enable120 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable120_0 := (addr1 == (120 : BitVec 9))
  let enable120_1 := we1 && enable120_0
  enable120_1

/-- The extracted gate of byte 120 equals `we1 && addr1 == 120` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable120_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable120 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 120) := by
  unfold enable120
  bv_decide

/-- Byte 120's extracted gate opens at its own offset and only there. -/
theorem enable120_open :
    enable120 true (Metronome.Bank.addrOf ⟨120, by decide⟩) = true := by
  rw [enable120_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable120_spec
#print axioms enable120_open

/-- Gate enable of byte 121, extracted from `g_byte[121].g_used.u_cg`. -/
def enable121 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable121_0 := (addr1 == (121 : BitVec 9))
  let enable121_1 := we1 && enable121_0
  enable121_1

/-- The extracted gate of byte 121 equals `we1 && addr1 == 121` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable121_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable121 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 121) := by
  unfold enable121
  bv_decide

/-- Byte 121's extracted gate opens at its own offset and only there. -/
theorem enable121_open :
    enable121 true (Metronome.Bank.addrOf ⟨121, by decide⟩) = true := by
  rw [enable121_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable121_spec
#print axioms enable121_open

/-- Gate enable of byte 122, extracted from `g_byte[122].g_used.u_cg`. -/
def enable122 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable122_0 := (addr1 == (122 : BitVec 9))
  let enable122_1 := we1 && enable122_0
  enable122_1

/-- The extracted gate of byte 122 equals `we1 && addr1 == 122` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable122_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable122 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 122) := by
  unfold enable122
  bv_decide

/-- Byte 122's extracted gate opens at its own offset and only there. -/
theorem enable122_open :
    enable122 true (Metronome.Bank.addrOf ⟨122, by decide⟩) = true := by
  rw [enable122_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable122_spec
#print axioms enable122_open

/-- Gate enable of byte 123, extracted from `g_byte[123].g_used.u_cg`. -/
def enable123 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable123_0 := (addr1 == (123 : BitVec 9))
  let enable123_1 := we1 && enable123_0
  enable123_1

/-- The extracted gate of byte 123 equals `we1 && addr1 == 123` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable123_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable123 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 123) := by
  unfold enable123
  bv_decide

/-- Byte 123's extracted gate opens at its own offset and only there. -/
theorem enable123_open :
    enable123 true (Metronome.Bank.addrOf ⟨123, by decide⟩) = true := by
  rw [enable123_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable123_spec
#print axioms enable123_open

/-- Gate enable of byte 124, extracted from `g_byte[124].g_used.u_cg`. -/
def enable124 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable124_0 := (addr1 == (124 : BitVec 9))
  let enable124_1 := we1 && enable124_0
  enable124_1

/-- The extracted gate of byte 124 equals `we1 && addr1 == 124` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable124_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable124 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 124) := by
  unfold enable124
  bv_decide

/-- Byte 124's extracted gate opens at its own offset and only there. -/
theorem enable124_open :
    enable124 true (Metronome.Bank.addrOf ⟨124, by decide⟩) = true := by
  rw [enable124_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable124_spec
#print axioms enable124_open

/-- Gate enable of byte 128, extracted from `g_byte[128].g_used.u_cg`. -/
def enable128 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable128_0 := (addr1 == (128 : BitVec 9))
  let enable128_1 := we1 && enable128_0
  enable128_1

/-- The extracted gate of byte 128 equals `we1 && addr1 == 128` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable128_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable128 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 128) := by
  unfold enable128
  bv_decide

/-- Byte 128's extracted gate opens at its own offset and only there. -/
theorem enable128_open :
    enable128 true (Metronome.Bank.addrOf ⟨128, by decide⟩) = true := by
  rw [enable128_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable128_spec
#print axioms enable128_open

/-- Gate enable of byte 129, extracted from `g_byte[129].g_used.u_cg`. -/
def enable129 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable129_0 := (addr1 == (129 : BitVec 9))
  let enable129_1 := we1 && enable129_0
  enable129_1

/-- The extracted gate of byte 129 equals `we1 && addr1 == 129` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable129_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable129 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 129) := by
  unfold enable129
  bv_decide

/-- Byte 129's extracted gate opens at its own offset and only there. -/
theorem enable129_open :
    enable129 true (Metronome.Bank.addrOf ⟨129, by decide⟩) = true := by
  rw [enable129_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable129_spec
#print axioms enable129_open

/-- Gate enable of byte 130, extracted from `g_byte[130].g_used.u_cg`. -/
def enable130 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable130_0 := (addr1 == (130 : BitVec 9))
  let enable130_1 := we1 && enable130_0
  enable130_1

/-- The extracted gate of byte 130 equals `we1 && addr1 == 130` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable130_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable130 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 130) := by
  unfold enable130
  bv_decide

/-- Byte 130's extracted gate opens at its own offset and only there. -/
theorem enable130_open :
    enable130 true (Metronome.Bank.addrOf ⟨130, by decide⟩) = true := by
  rw [enable130_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable130_spec
#print axioms enable130_open

/-- Gate enable of byte 131, extracted from `g_byte[131].g_used.u_cg`. -/
def enable131 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable131_0 := (addr1 == (131 : BitVec 9))
  let enable131_1 := we1 && enable131_0
  enable131_1

/-- The extracted gate of byte 131 equals `we1 && addr1 == 131` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable131_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable131 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 131) := by
  unfold enable131
  bv_decide

/-- Byte 131's extracted gate opens at its own offset and only there. -/
theorem enable131_open :
    enable131 true (Metronome.Bank.addrOf ⟨131, by decide⟩) = true := by
  rw [enable131_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable131_spec
#print axioms enable131_open

/-- Gate enable of byte 132, extracted from `g_byte[132].g_used.u_cg`. -/
def enable132 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable132_0 := (addr1 == (132 : BitVec 9))
  let enable132_1 := we1 && enable132_0
  enable132_1

/-- The extracted gate of byte 132 equals `we1 && addr1 == 132` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable132_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable132 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 132) := by
  unfold enable132
  bv_decide

/-- Byte 132's extracted gate opens at its own offset and only there. -/
theorem enable132_open :
    enable132 true (Metronome.Bank.addrOf ⟨132, by decide⟩) = true := by
  rw [enable132_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable132_spec
#print axioms enable132_open

/-- Gate enable of byte 136, extracted from `g_byte[136].g_used.u_cg`. -/
def enable136 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable136_0 := (addr1 == (136 : BitVec 9))
  let enable136_1 := we1 && enable136_0
  enable136_1

/-- The extracted gate of byte 136 equals `we1 && addr1 == 136` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable136_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable136 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 136) := by
  unfold enable136
  bv_decide

/-- Byte 136's extracted gate opens at its own offset and only there. -/
theorem enable136_open :
    enable136 true (Metronome.Bank.addrOf ⟨136, by decide⟩) = true := by
  rw [enable136_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable136_spec
#print axioms enable136_open

/-- Gate enable of byte 137, extracted from `g_byte[137].g_used.u_cg`. -/
def enable137 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable137_0 := (addr1 == (137 : BitVec 9))
  let enable137_1 := we1 && enable137_0
  enable137_1

/-- The extracted gate of byte 137 equals `we1 && addr1 == 137` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable137_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable137 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 137) := by
  unfold enable137
  bv_decide

/-- Byte 137's extracted gate opens at its own offset and only there. -/
theorem enable137_open :
    enable137 true (Metronome.Bank.addrOf ⟨137, by decide⟩) = true := by
  rw [enable137_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable137_spec
#print axioms enable137_open

/-- Gate enable of byte 138, extracted from `g_byte[138].g_used.u_cg`. -/
def enable138 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable138_0 := (addr1 == (138 : BitVec 9))
  let enable138_1 := we1 && enable138_0
  enable138_1

/-- The extracted gate of byte 138 equals `we1 && addr1 == 138` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable138_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable138 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 138) := by
  unfold enable138
  bv_decide

/-- Byte 138's extracted gate opens at its own offset and only there. -/
theorem enable138_open :
    enable138 true (Metronome.Bank.addrOf ⟨138, by decide⟩) = true := by
  rw [enable138_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable138_spec
#print axioms enable138_open

/-- Gate enable of byte 139, extracted from `g_byte[139].g_used.u_cg`. -/
def enable139 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable139_0 := (addr1 == (139 : BitVec 9))
  let enable139_1 := we1 && enable139_0
  enable139_1

/-- The extracted gate of byte 139 equals `we1 && addr1 == 139` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable139_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable139 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 139) := by
  unfold enable139
  bv_decide

/-- Byte 139's extracted gate opens at its own offset and only there. -/
theorem enable139_open :
    enable139 true (Metronome.Bank.addrOf ⟨139, by decide⟩) = true := by
  rw [enable139_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable139_spec
#print axioms enable139_open

/-- Gate enable of byte 140, extracted from `g_byte[140].g_used.u_cg`. -/
def enable140 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable140_0 := (addr1 == (140 : BitVec 9))
  let enable140_1 := we1 && enable140_0
  enable140_1

/-- The extracted gate of byte 140 equals `we1 && addr1 == 140` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable140_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable140 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 140) := by
  unfold enable140
  bv_decide

/-- Byte 140's extracted gate opens at its own offset and only there. -/
theorem enable140_open :
    enable140 true (Metronome.Bank.addrOf ⟨140, by decide⟩) = true := by
  rw [enable140_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable140_spec
#print axioms enable140_open

/-- Gate enable of byte 144, extracted from `g_byte[144].g_used.u_cg`. -/
def enable144 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable144_0 := (addr1 == (144 : BitVec 9))
  let enable144_1 := we1 && enable144_0
  enable144_1

/-- The extracted gate of byte 144 equals `we1 && addr1 == 144` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable144_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable144 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 144) := by
  unfold enable144
  bv_decide

/-- Byte 144's extracted gate opens at its own offset and only there. -/
theorem enable144_open :
    enable144 true (Metronome.Bank.addrOf ⟨144, by decide⟩) = true := by
  rw [enable144_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable144_spec
#print axioms enable144_open

/-- Gate enable of byte 145, extracted from `g_byte[145].g_used.u_cg`. -/
def enable145 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable145_0 := (addr1 == (145 : BitVec 9))
  let enable145_1 := we1 && enable145_0
  enable145_1

/-- The extracted gate of byte 145 equals `we1 && addr1 == 145` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable145_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable145 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 145) := by
  unfold enable145
  bv_decide

/-- Byte 145's extracted gate opens at its own offset and only there. -/
theorem enable145_open :
    enable145 true (Metronome.Bank.addrOf ⟨145, by decide⟩) = true := by
  rw [enable145_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable145_spec
#print axioms enable145_open

/-- Gate enable of byte 146, extracted from `g_byte[146].g_used.u_cg`. -/
def enable146 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable146_0 := (addr1 == (146 : BitVec 9))
  let enable146_1 := we1 && enable146_0
  enable146_1

/-- The extracted gate of byte 146 equals `we1 && addr1 == 146` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable146_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable146 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 146) := by
  unfold enable146
  bv_decide

/-- Byte 146's extracted gate opens at its own offset and only there. -/
theorem enable146_open :
    enable146 true (Metronome.Bank.addrOf ⟨146, by decide⟩) = true := by
  rw [enable146_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable146_spec
#print axioms enable146_open

/-- Gate enable of byte 147, extracted from `g_byte[147].g_used.u_cg`. -/
def enable147 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable147_0 := (addr1 == (147 : BitVec 9))
  let enable147_1 := we1 && enable147_0
  enable147_1

/-- The extracted gate of byte 147 equals `we1 && addr1 == 147` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable147_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable147 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 147) := by
  unfold enable147
  bv_decide

/-- Byte 147's extracted gate opens at its own offset and only there. -/
theorem enable147_open :
    enable147 true (Metronome.Bank.addrOf ⟨147, by decide⟩) = true := by
  rw [enable147_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable147_spec
#print axioms enable147_open

/-- Gate enable of byte 148, extracted from `g_byte[148].g_used.u_cg`. -/
def enable148 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable148_0 := (addr1 == (148 : BitVec 9))
  let enable148_1 := we1 && enable148_0
  enable148_1

/-- The extracted gate of byte 148 equals `we1 && addr1 == 148` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable148_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable148 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 148) := by
  unfold enable148
  bv_decide

/-- Byte 148's extracted gate opens at its own offset and only there. -/
theorem enable148_open :
    enable148 true (Metronome.Bank.addrOf ⟨148, by decide⟩) = true := by
  rw [enable148_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable148_spec
#print axioms enable148_open

/-- Gate enable of byte 152, extracted from `g_byte[152].g_used.u_cg`. -/
def enable152 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable152_0 := (addr1 == (152 : BitVec 9))
  let enable152_1 := we1 && enable152_0
  enable152_1

/-- The extracted gate of byte 152 equals `we1 && addr1 == 152` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable152_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable152 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 152) := by
  unfold enable152
  bv_decide

/-- Byte 152's extracted gate opens at its own offset and only there. -/
theorem enable152_open :
    enable152 true (Metronome.Bank.addrOf ⟨152, by decide⟩) = true := by
  rw [enable152_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable152_spec
#print axioms enable152_open

/-- Gate enable of byte 153, extracted from `g_byte[153].g_used.u_cg`. -/
def enable153 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable153_0 := (addr1 == (153 : BitVec 9))
  let enable153_1 := we1 && enable153_0
  enable153_1

/-- The extracted gate of byte 153 equals `we1 && addr1 == 153` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable153_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable153 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 153) := by
  unfold enable153
  bv_decide

/-- Byte 153's extracted gate opens at its own offset and only there. -/
theorem enable153_open :
    enable153 true (Metronome.Bank.addrOf ⟨153, by decide⟩) = true := by
  rw [enable153_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable153_spec
#print axioms enable153_open

/-- Gate enable of byte 154, extracted from `g_byte[154].g_used.u_cg`. -/
def enable154 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable154_0 := (addr1 == (154 : BitVec 9))
  let enable154_1 := we1 && enable154_0
  enable154_1

/-- The extracted gate of byte 154 equals `we1 && addr1 == 154` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable154_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable154 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 154) := by
  unfold enable154
  bv_decide

/-- Byte 154's extracted gate opens at its own offset and only there. -/
theorem enable154_open :
    enable154 true (Metronome.Bank.addrOf ⟨154, by decide⟩) = true := by
  rw [enable154_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable154_spec
#print axioms enable154_open

/-- Gate enable of byte 155, extracted from `g_byte[155].g_used.u_cg`. -/
def enable155 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable155_0 := (addr1 == (155 : BitVec 9))
  let enable155_1 := we1 && enable155_0
  enable155_1

/-- The extracted gate of byte 155 equals `we1 && addr1 == 155` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable155_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable155 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 155) := by
  unfold enable155
  bv_decide

/-- Byte 155's extracted gate opens at its own offset and only there. -/
theorem enable155_open :
    enable155 true (Metronome.Bank.addrOf ⟨155, by decide⟩) = true := by
  rw [enable155_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable155_spec
#print axioms enable155_open

/-- Gate enable of byte 156, extracted from `g_byte[156].g_used.u_cg`. -/
def enable156 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable156_0 := (addr1 == (156 : BitVec 9))
  let enable156_1 := we1 && enable156_0
  enable156_1

/-- The extracted gate of byte 156 equals `we1 && addr1 == 156` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable156_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable156 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 156) := by
  unfold enable156
  bv_decide

/-- Byte 156's extracted gate opens at its own offset and only there. -/
theorem enable156_open :
    enable156 true (Metronome.Bank.addrOf ⟨156, by decide⟩) = true := by
  rw [enable156_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable156_spec
#print axioms enable156_open

/-- Gate enable of byte 160, extracted from `g_byte[160].g_used.u_cg`. -/
def enable160 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable160_0 := (addr1 == (160 : BitVec 9))
  let enable160_1 := we1 && enable160_0
  enable160_1

/-- The extracted gate of byte 160 equals `we1 && addr1 == 160` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable160_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable160 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 160) := by
  unfold enable160
  bv_decide

/-- Byte 160's extracted gate opens at its own offset and only there. -/
theorem enable160_open :
    enable160 true (Metronome.Bank.addrOf ⟨160, by decide⟩) = true := by
  rw [enable160_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable160_spec
#print axioms enable160_open

/-- Gate enable of byte 161, extracted from `g_byte[161].g_used.u_cg`. -/
def enable161 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable161_0 := (addr1 == (161 : BitVec 9))
  let enable161_1 := we1 && enable161_0
  enable161_1

/-- The extracted gate of byte 161 equals `we1 && addr1 == 161` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable161_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable161 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 161) := by
  unfold enable161
  bv_decide

/-- Byte 161's extracted gate opens at its own offset and only there. -/
theorem enable161_open :
    enable161 true (Metronome.Bank.addrOf ⟨161, by decide⟩) = true := by
  rw [enable161_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable161_spec
#print axioms enable161_open

/-- Gate enable of byte 162, extracted from `g_byte[162].g_used.u_cg`. -/
def enable162 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable162_0 := (addr1 == (162 : BitVec 9))
  let enable162_1 := we1 && enable162_0
  enable162_1

/-- The extracted gate of byte 162 equals `we1 && addr1 == 162` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable162_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable162 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 162) := by
  unfold enable162
  bv_decide

/-- Byte 162's extracted gate opens at its own offset and only there. -/
theorem enable162_open :
    enable162 true (Metronome.Bank.addrOf ⟨162, by decide⟩) = true := by
  rw [enable162_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable162_spec
#print axioms enable162_open

/-- Gate enable of byte 163, extracted from `g_byte[163].g_used.u_cg`. -/
def enable163 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable163_0 := (addr1 == (163 : BitVec 9))
  let enable163_1 := we1 && enable163_0
  enable163_1

/-- The extracted gate of byte 163 equals `we1 && addr1 == 163` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable163_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable163 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 163) := by
  unfold enable163
  bv_decide

/-- Byte 163's extracted gate opens at its own offset and only there. -/
theorem enable163_open :
    enable163 true (Metronome.Bank.addrOf ⟨163, by decide⟩) = true := by
  rw [enable163_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable163_spec
#print axioms enable163_open

/-- Gate enable of byte 164, extracted from `g_byte[164].g_used.u_cg`. -/
def enable164 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable164_0 := (addr1 == (164 : BitVec 9))
  let enable164_1 := we1 && enable164_0
  enable164_1

/-- The extracted gate of byte 164 equals `we1 && addr1 == 164` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable164_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable164 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 164) := by
  unfold enable164
  bv_decide

/-- Byte 164's extracted gate opens at its own offset and only there. -/
theorem enable164_open :
    enable164 true (Metronome.Bank.addrOf ⟨164, by decide⟩) = true := by
  rw [enable164_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable164_spec
#print axioms enable164_open

/-- Gate enable of byte 168, extracted from `g_byte[168].g_used.u_cg`. -/
def enable168 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable168_0 := (addr1 == (168 : BitVec 9))
  let enable168_1 := we1 && enable168_0
  enable168_1

/-- The extracted gate of byte 168 equals `we1 && addr1 == 168` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable168_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable168 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 168) := by
  unfold enable168
  bv_decide

/-- Byte 168's extracted gate opens at its own offset and only there. -/
theorem enable168_open :
    enable168 true (Metronome.Bank.addrOf ⟨168, by decide⟩) = true := by
  rw [enable168_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable168_spec
#print axioms enable168_open

/-- Gate enable of byte 169, extracted from `g_byte[169].g_used.u_cg`. -/
def enable169 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable169_0 := (addr1 == (169 : BitVec 9))
  let enable169_1 := we1 && enable169_0
  enable169_1

/-- The extracted gate of byte 169 equals `we1 && addr1 == 169` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable169_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable169 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 169) := by
  unfold enable169
  bv_decide

/-- Byte 169's extracted gate opens at its own offset and only there. -/
theorem enable169_open :
    enable169 true (Metronome.Bank.addrOf ⟨169, by decide⟩) = true := by
  rw [enable169_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable169_spec
#print axioms enable169_open

/-- Gate enable of byte 170, extracted from `g_byte[170].g_used.u_cg`. -/
def enable170 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable170_0 := (addr1 == (170 : BitVec 9))
  let enable170_1 := we1 && enable170_0
  enable170_1

/-- The extracted gate of byte 170 equals `we1 && addr1 == 170` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable170_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable170 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 170) := by
  unfold enable170
  bv_decide

/-- Byte 170's extracted gate opens at its own offset and only there. -/
theorem enable170_open :
    enable170 true (Metronome.Bank.addrOf ⟨170, by decide⟩) = true := by
  rw [enable170_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable170_spec
#print axioms enable170_open

/-- Gate enable of byte 171, extracted from `g_byte[171].g_used.u_cg`. -/
def enable171 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable171_0 := (addr1 == (171 : BitVec 9))
  let enable171_1 := we1 && enable171_0
  enable171_1

/-- The extracted gate of byte 171 equals `we1 && addr1 == 171` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable171_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable171 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 171) := by
  unfold enable171
  bv_decide

/-- Byte 171's extracted gate opens at its own offset and only there. -/
theorem enable171_open :
    enable171 true (Metronome.Bank.addrOf ⟨171, by decide⟩) = true := by
  rw [enable171_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable171_spec
#print axioms enable171_open

/-- Gate enable of byte 172, extracted from `g_byte[172].g_used.u_cg`. -/
def enable172 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable172_0 := (addr1 == (172 : BitVec 9))
  let enable172_1 := we1 && enable172_0
  enable172_1

/-- The extracted gate of byte 172 equals `we1 && addr1 == 172` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable172_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable172 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 172) := by
  unfold enable172
  bv_decide

/-- Byte 172's extracted gate opens at its own offset and only there. -/
theorem enable172_open :
    enable172 true (Metronome.Bank.addrOf ⟨172, by decide⟩) = true := by
  rw [enable172_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable172_spec
#print axioms enable172_open

/-- Gate enable of byte 192, extracted from `g_byte[192].g_used.u_cg`. -/
def enable192 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable192_0 := (addr1 == (192 : BitVec 9))
  let enable192_1 := we1 && enable192_0
  enable192_1

/-- The extracted gate of byte 192 equals `we1 && addr1 == 192` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable192_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable192 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 192) := by
  unfold enable192
  bv_decide

/-- Byte 192's extracted gate opens at its own offset and only there. -/
theorem enable192_open :
    enable192 true (Metronome.Bank.addrOf ⟨192, by decide⟩) = true := by
  rw [enable192_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable192_spec
#print axioms enable192_open

/-- Gate enable of byte 193, extracted from `g_byte[193].g_used.u_cg`. -/
def enable193 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable193_0 := (addr1 == (193 : BitVec 9))
  let enable193_1 := we1 && enable193_0
  enable193_1

/-- The extracted gate of byte 193 equals `we1 && addr1 == 193` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable193_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable193 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 193) := by
  unfold enable193
  bv_decide

/-- Byte 193's extracted gate opens at its own offset and only there. -/
theorem enable193_open :
    enable193 true (Metronome.Bank.addrOf ⟨193, by decide⟩) = true := by
  rw [enable193_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable193_spec
#print axioms enable193_open

/-- Gate enable of byte 194, extracted from `g_byte[194].g_used.u_cg`. -/
def enable194 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable194_0 := (addr1 == (194 : BitVec 9))
  let enable194_1 := we1 && enable194_0
  enable194_1

/-- The extracted gate of byte 194 equals `we1 && addr1 == 194` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable194_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable194 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 194) := by
  unfold enable194
  bv_decide

/-- Byte 194's extracted gate opens at its own offset and only there. -/
theorem enable194_open :
    enable194 true (Metronome.Bank.addrOf ⟨194, by decide⟩) = true := by
  rw [enable194_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable194_spec
#print axioms enable194_open

/-- Gate enable of byte 195, extracted from `g_byte[195].g_used.u_cg`. -/
def enable195 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable195_0 := (addr1 == (195 : BitVec 9))
  let enable195_1 := we1 && enable195_0
  enable195_1

/-- The extracted gate of byte 195 equals `we1 && addr1 == 195` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable195_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable195 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 195) := by
  unfold enable195
  bv_decide

/-- Byte 195's extracted gate opens at its own offset and only there. -/
theorem enable195_open :
    enable195 true (Metronome.Bank.addrOf ⟨195, by decide⟩) = true := by
  rw [enable195_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable195_spec
#print axioms enable195_open

/-- Gate enable of byte 200, extracted from `g_byte[200].g_used.u_cg`. -/
def enable200 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable200_0 := (addr1 == (200 : BitVec 9))
  let enable200_1 := we1 && enable200_0
  enable200_1

/-- The extracted gate of byte 200 equals `we1 && addr1 == 200` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable200_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable200 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 200) := by
  unfold enable200
  bv_decide

/-- Byte 200's extracted gate opens at its own offset and only there. -/
theorem enable200_open :
    enable200 true (Metronome.Bank.addrOf ⟨200, by decide⟩) = true := by
  rw [enable200_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable200_spec
#print axioms enable200_open

/-- Gate enable of byte 201, extracted from `g_byte[201].g_used.u_cg`. -/
def enable201 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable201_0 := (addr1 == (201 : BitVec 9))
  let enable201_1 := we1 && enable201_0
  enable201_1

/-- The extracted gate of byte 201 equals `we1 && addr1 == 201` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable201_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable201 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 201) := by
  unfold enable201
  bv_decide

/-- Byte 201's extracted gate opens at its own offset and only there. -/
theorem enable201_open :
    enable201 true (Metronome.Bank.addrOf ⟨201, by decide⟩) = true := by
  rw [enable201_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable201_spec
#print axioms enable201_open

/-- Gate enable of byte 202, extracted from `g_byte[202].g_used.u_cg`. -/
def enable202 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable202_0 := (addr1 == (202 : BitVec 9))
  let enable202_1 := we1 && enable202_0
  enable202_1

/-- The extracted gate of byte 202 equals `we1 && addr1 == 202` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable202_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable202 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 202) := by
  unfold enable202
  bv_decide

/-- Byte 202's extracted gate opens at its own offset and only there. -/
theorem enable202_open :
    enable202 true (Metronome.Bank.addrOf ⟨202, by decide⟩) = true := by
  rw [enable202_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable202_spec
#print axioms enable202_open

/-- Gate enable of byte 203, extracted from `g_byte[203].g_used.u_cg`. -/
def enable203 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable203_0 := (addr1 == (203 : BitVec 9))
  let enable203_1 := we1 && enable203_0
  enable203_1

/-- The extracted gate of byte 203 equals `we1 && addr1 == 203` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable203_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable203 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 203) := by
  unfold enable203
  bv_decide

/-- Byte 203's extracted gate opens at its own offset and only there. -/
theorem enable203_open :
    enable203 true (Metronome.Bank.addrOf ⟨203, by decide⟩) = true := by
  rw [enable203_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable203_spec
#print axioms enable203_open

/-- Gate enable of byte 208, extracted from `g_byte[208].g_used.u_cg`. -/
def enable208 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable208_0 := (addr1 == (208 : BitVec 9))
  let enable208_1 := we1 && enable208_0
  enable208_1

/-- The extracted gate of byte 208 equals `we1 && addr1 == 208` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable208_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable208 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 208) := by
  unfold enable208
  bv_decide

/-- Byte 208's extracted gate opens at its own offset and only there. -/
theorem enable208_open :
    enable208 true (Metronome.Bank.addrOf ⟨208, by decide⟩) = true := by
  rw [enable208_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable208_spec
#print axioms enable208_open

/-- Gate enable of byte 209, extracted from `g_byte[209].g_used.u_cg`. -/
def enable209 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable209_0 := (addr1 == (209 : BitVec 9))
  let enable209_1 := we1 && enable209_0
  enable209_1

/-- The extracted gate of byte 209 equals `we1 && addr1 == 209` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable209_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable209 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 209) := by
  unfold enable209
  bv_decide

/-- Byte 209's extracted gate opens at its own offset and only there. -/
theorem enable209_open :
    enable209 true (Metronome.Bank.addrOf ⟨209, by decide⟩) = true := by
  rw [enable209_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable209_spec
#print axioms enable209_open

/-- Gate enable of byte 210, extracted from `g_byte[210].g_used.u_cg`. -/
def enable210 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable210_0 := (addr1 == (210 : BitVec 9))
  let enable210_1 := we1 && enable210_0
  enable210_1

/-- The extracted gate of byte 210 equals `we1 && addr1 == 210` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable210_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable210 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 210) := by
  unfold enable210
  bv_decide

/-- Byte 210's extracted gate opens at its own offset and only there. -/
theorem enable210_open :
    enable210 true (Metronome.Bank.addrOf ⟨210, by decide⟩) = true := by
  rw [enable210_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable210_spec
#print axioms enable210_open

/-- Gate enable of byte 211, extracted from `g_byte[211].g_used.u_cg`. -/
def enable211 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable211_0 := (addr1 == (211 : BitVec 9))
  let enable211_1 := we1 && enable211_0
  enable211_1

/-- The extracted gate of byte 211 equals `we1 && addr1 == 211` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable211_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable211 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 211) := by
  unfold enable211
  bv_decide

/-- Byte 211's extracted gate opens at its own offset and only there. -/
theorem enable211_open :
    enable211 true (Metronome.Bank.addrOf ⟨211, by decide⟩) = true := by
  rw [enable211_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable211_spec
#print axioms enable211_open

/-- Gate enable of byte 212, extracted from `g_byte[212].g_used.u_cg`. -/
def enable212 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable212_0 := (addr1 == (212 : BitVec 9))
  let enable212_1 := we1 && enable212_0
  enable212_1

/-- The extracted gate of byte 212 equals `we1 && addr1 == 212` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable212_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable212 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 212) := by
  unfold enable212
  bv_decide

/-- Byte 212's extracted gate opens at its own offset and only there. -/
theorem enable212_open :
    enable212 true (Metronome.Bank.addrOf ⟨212, by decide⟩) = true := by
  rw [enable212_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable212_spec
#print axioms enable212_open

/-- Gate enable of byte 213, extracted from `g_byte[213].g_used.u_cg`. -/
def enable213 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable213_0 := (addr1 == (213 : BitVec 9))
  let enable213_1 := we1 && enable213_0
  enable213_1

/-- The extracted gate of byte 213 equals `we1 && addr1 == 213` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable213_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable213 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 213) := by
  unfold enable213
  bv_decide

/-- Byte 213's extracted gate opens at its own offset and only there. -/
theorem enable213_open :
    enable213 true (Metronome.Bank.addrOf ⟨213, by decide⟩) = true := by
  rw [enable213_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable213_spec
#print axioms enable213_open

/-- Gate enable of byte 214, extracted from `g_byte[214].g_used.u_cg`. -/
def enable214 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable214_0 := (addr1 == (214 : BitVec 9))
  let enable214_1 := we1 && enable214_0
  enable214_1

/-- The extracted gate of byte 214 equals `we1 && addr1 == 214` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable214_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable214 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 214) := by
  unfold enable214
  bv_decide

/-- Byte 214's extracted gate opens at its own offset and only there. -/
theorem enable214_open :
    enable214 true (Metronome.Bank.addrOf ⟨214, by decide⟩) = true := by
  rw [enable214_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable214_spec
#print axioms enable214_open

/-- Gate enable of byte 216, extracted from `g_byte[216].g_used.u_cg`. -/
def enable216 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable216_0 := (addr1 == (216 : BitVec 9))
  let enable216_1 := we1 && enable216_0
  enable216_1

/-- The extracted gate of byte 216 equals `we1 && addr1 == 216` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable216_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable216 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 216) := by
  unfold enable216
  bv_decide

/-- Byte 216's extracted gate opens at its own offset and only there. -/
theorem enable216_open :
    enable216 true (Metronome.Bank.addrOf ⟨216, by decide⟩) = true := by
  rw [enable216_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable216_spec
#print axioms enable216_open

/-- Gate enable of byte 217, extracted from `g_byte[217].g_used.u_cg`. -/
def enable217 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable217_0 := (addr1 == (217 : BitVec 9))
  let enable217_1 := we1 && enable217_0
  enable217_1

/-- The extracted gate of byte 217 equals `we1 && addr1 == 217` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable217_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable217 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 217) := by
  unfold enable217
  bv_decide

/-- Byte 217's extracted gate opens at its own offset and only there. -/
theorem enable217_open :
    enable217 true (Metronome.Bank.addrOf ⟨217, by decide⟩) = true := by
  rw [enable217_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable217_spec
#print axioms enable217_open

/-- Gate enable of byte 218, extracted from `g_byte[218].g_used.u_cg`. -/
def enable218 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable218_0 := (addr1 == (218 : BitVec 9))
  let enable218_1 := we1 && enable218_0
  enable218_1

/-- The extracted gate of byte 218 equals `we1 && addr1 == 218` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable218_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable218 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 218) := by
  unfold enable218
  bv_decide

/-- Byte 218's extracted gate opens at its own offset and only there. -/
theorem enable218_open :
    enable218 true (Metronome.Bank.addrOf ⟨218, by decide⟩) = true := by
  rw [enable218_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable218_spec
#print axioms enable218_open

/-- Gate enable of byte 219, extracted from `g_byte[219].g_used.u_cg`. -/
def enable219 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable219_0 := (addr1 == (219 : BitVec 9))
  let enable219_1 := we1 && enable219_0
  enable219_1

/-- The extracted gate of byte 219 equals `we1 && addr1 == 219` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable219_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable219 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 219) := by
  unfold enable219
  bv_decide

/-- Byte 219's extracted gate opens at its own offset and only there. -/
theorem enable219_open :
    enable219 true (Metronome.Bank.addrOf ⟨219, by decide⟩) = true := by
  rw [enable219_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable219_spec
#print axioms enable219_open

/-- Gate enable of byte 220, extracted from `g_byte[220].g_used.u_cg`. -/
def enable220 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable220_0 := (addr1 == (220 : BitVec 9))
  let enable220_1 := we1 && enable220_0
  enable220_1

/-- The extracted gate of byte 220 equals `we1 && addr1 == 220` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable220_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable220 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 220) := by
  unfold enable220
  bv_decide

/-- Byte 220's extracted gate opens at its own offset and only there. -/
theorem enable220_open :
    enable220 true (Metronome.Bank.addrOf ⟨220, by decide⟩) = true := by
  rw [enable220_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable220_spec
#print axioms enable220_open

/-- Gate enable of byte 221, extracted from `g_byte[221].g_used.u_cg`. -/
def enable221 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable221_0 := (addr1 == (221 : BitVec 9))
  let enable221_1 := we1 && enable221_0
  enable221_1

/-- The extracted gate of byte 221 equals `we1 && addr1 == 221` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable221_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable221 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 221) := by
  unfold enable221
  bv_decide

/-- Byte 221's extracted gate opens at its own offset and only there. -/
theorem enable221_open :
    enable221 true (Metronome.Bank.addrOf ⟨221, by decide⟩) = true := by
  rw [enable221_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable221_spec
#print axioms enable221_open

/-- Gate enable of byte 222, extracted from `g_byte[222].g_used.u_cg`. -/
def enable222 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable222_0 := (addr1 == (222 : BitVec 9))
  let enable222_1 := we1 && enable222_0
  enable222_1

/-- The extracted gate of byte 222 equals `we1 && addr1 == 222` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable222_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable222 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 222) := by
  unfold enable222
  bv_decide

/-- Byte 222's extracted gate opens at its own offset and only there. -/
theorem enable222_open :
    enable222 true (Metronome.Bank.addrOf ⟨222, by decide⟩) = true := by
  rw [enable222_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable222_spec
#print axioms enable222_open

/-- Gate enable of byte 256, extracted from `g_byte[256].g_used.u_cg`. -/
def enable256 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable256_0 := (addr1 == (256 : BitVec 9))
  let enable256_1 := we1 && enable256_0
  enable256_1

/-- The extracted gate of byte 256 equals `we1 && addr1 == 256` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable256_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable256 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 256) := by
  unfold enable256
  bv_decide

/-- Byte 256's extracted gate opens at its own offset and only there. -/
theorem enable256_open :
    enable256 true (Metronome.Bank.addrOf ⟨256, by decide⟩) = true := by
  rw [enable256_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable256_spec
#print axioms enable256_open

/-- Gate enable of byte 257, extracted from `g_byte[257].g_used.u_cg`. -/
def enable257 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable257_0 := (addr1 == (257 : BitVec 9))
  let enable257_1 := we1 && enable257_0
  enable257_1

/-- The extracted gate of byte 257 equals `we1 && addr1 == 257` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable257_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable257 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 257) := by
  unfold enable257
  bv_decide

/-- Byte 257's extracted gate opens at its own offset and only there. -/
theorem enable257_open :
    enable257 true (Metronome.Bank.addrOf ⟨257, by decide⟩) = true := by
  rw [enable257_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable257_spec
#print axioms enable257_open

/-- Gate enable of byte 260, extracted from `g_byte[260].g_used.u_cg`. -/
def enable260 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable260_0 := (addr1 == (260 : BitVec 9))
  let enable260_1 := we1 && enable260_0
  enable260_1

/-- The extracted gate of byte 260 equals `we1 && addr1 == 260` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable260_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable260 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 260) := by
  unfold enable260
  bv_decide

/-- Byte 260's extracted gate opens at its own offset and only there. -/
theorem enable260_open :
    enable260 true (Metronome.Bank.addrOf ⟨260, by decide⟩) = true := by
  rw [enable260_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable260_spec
#print axioms enable260_open

/-- Gate enable of byte 261, extracted from `g_byte[261].g_used.u_cg`. -/
def enable261 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable261_0 := (addr1 == (261 : BitVec 9))
  let enable261_1 := we1 && enable261_0
  enable261_1

/-- The extracted gate of byte 261 equals `we1 && addr1 == 261` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable261_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable261 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 261) := by
  unfold enable261
  bv_decide

/-- Byte 261's extracted gate opens at its own offset and only there. -/
theorem enable261_open :
    enable261 true (Metronome.Bank.addrOf ⟨261, by decide⟩) = true := by
  rw [enable261_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable261_spec
#print axioms enable261_open

/-- Gate enable of byte 262, extracted from `g_byte[262].g_used.u_cg`. -/
def enable262 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable262_0 := (addr1 == (262 : BitVec 9))
  let enable262_1 := we1 && enable262_0
  enable262_1

/-- The extracted gate of byte 262 equals `we1 && addr1 == 262` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable262_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable262 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 262) := by
  unfold enable262
  bv_decide

/-- Byte 262's extracted gate opens at its own offset and only there. -/
theorem enable262_open :
    enable262 true (Metronome.Bank.addrOf ⟨262, by decide⟩) = true := by
  rw [enable262_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable262_spec
#print axioms enable262_open

/-- Gate enable of byte 263, extracted from `g_byte[263].g_used.u_cg`. -/
def enable263 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable263_0 := (addr1 == (263 : BitVec 9))
  let enable263_1 := we1 && enable263_0
  enable263_1

/-- The extracted gate of byte 263 equals `we1 && addr1 == 263` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable263_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable263 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 263) := by
  unfold enable263
  bv_decide

/-- Byte 263's extracted gate opens at its own offset and only there. -/
theorem enable263_open :
    enable263 true (Metronome.Bank.addrOf ⟨263, by decide⟩) = true := by
  rw [enable263_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable263_spec
#print axioms enable263_open

/-- Gate enable of byte 264, extracted from `g_byte[264].g_used.u_cg`. -/
def enable264 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable264_0 := (addr1 == (264 : BitVec 9))
  let enable264_1 := we1 && enable264_0
  enable264_1

/-- The extracted gate of byte 264 equals `we1 && addr1 == 264` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable264_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable264 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 264) := by
  unfold enable264
  bv_decide

/-- Byte 264's extracted gate opens at its own offset and only there. -/
theorem enable264_open :
    enable264 true (Metronome.Bank.addrOf ⟨264, by decide⟩) = true := by
  rw [enable264_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable264_spec
#print axioms enable264_open

/-- Gate enable of byte 265, extracted from `g_byte[265].g_used.u_cg`. -/
def enable265 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable265_0 := (addr1 == (265 : BitVec 9))
  let enable265_1 := we1 && enable265_0
  enable265_1

/-- The extracted gate of byte 265 equals `we1 && addr1 == 265` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable265_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable265 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 265) := by
  unfold enable265
  bv_decide

/-- Byte 265's extracted gate opens at its own offset and only there. -/
theorem enable265_open :
    enable265 true (Metronome.Bank.addrOf ⟨265, by decide⟩) = true := by
  rw [enable265_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable265_spec
#print axioms enable265_open

/-- Gate enable of byte 266, extracted from `g_byte[266].g_used.u_cg`. -/
def enable266 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable266_0 := (addr1 == (266 : BitVec 9))
  let enable266_1 := we1 && enable266_0
  enable266_1

/-- The extracted gate of byte 266 equals `we1 && addr1 == 266` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable266_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable266 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 266) := by
  unfold enable266
  bv_decide

/-- Byte 266's extracted gate opens at its own offset and only there. -/
theorem enable266_open :
    enable266 true (Metronome.Bank.addrOf ⟨266, by decide⟩) = true := by
  rw [enable266_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable266_spec
#print axioms enable266_open

/-- Gate enable of byte 267, extracted from `g_byte[267].g_used.u_cg`. -/
def enable267 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable267_0 := (addr1 == (267 : BitVec 9))
  let enable267_1 := we1 && enable267_0
  enable267_1

/-- The extracted gate of byte 267 equals `we1 && addr1 == 267` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable267_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable267 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 267) := by
  unfold enable267
  bv_decide

/-- Byte 267's extracted gate opens at its own offset and only there. -/
theorem enable267_open :
    enable267 true (Metronome.Bank.addrOf ⟨267, by decide⟩) = true := by
  rw [enable267_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable267_spec
#print axioms enable267_open

/-- Gate enable of byte 272, extracted from `g_byte[272].g_used.u_cg`. -/
def enable272 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable272_0 := (addr1 == (272 : BitVec 9))
  let enable272_1 := we1 && enable272_0
  enable272_1

/-- The extracted gate of byte 272 equals `we1 && addr1 == 272` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable272_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable272 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 272) := by
  unfold enable272
  bv_decide

/-- Byte 272's extracted gate opens at its own offset and only there. -/
theorem enable272_open :
    enable272 true (Metronome.Bank.addrOf ⟨272, by decide⟩) = true := by
  rw [enable272_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable272_spec
#print axioms enable272_open

/-- Gate enable of byte 273, extracted from `g_byte[273].g_used.u_cg`. -/
def enable273 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable273_0 := (addr1 == (273 : BitVec 9))
  let enable273_1 := we1 && enable273_0
  enable273_1

/-- The extracted gate of byte 273 equals `we1 && addr1 == 273` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable273_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable273 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 273) := by
  unfold enable273
  bv_decide

/-- Byte 273's extracted gate opens at its own offset and only there. -/
theorem enable273_open :
    enable273 true (Metronome.Bank.addrOf ⟨273, by decide⟩) = true := by
  rw [enable273_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable273_spec
#print axioms enable273_open

/-- Gate enable of byte 276, extracted from `g_byte[276].g_used.u_cg`. -/
def enable276 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable276_0 := (addr1 == (276 : BitVec 9))
  let enable276_1 := we1 && enable276_0
  enable276_1

/-- The extracted gate of byte 276 equals `we1 && addr1 == 276` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable276_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable276 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 276) := by
  unfold enable276
  bv_decide

/-- Byte 276's extracted gate opens at its own offset and only there. -/
theorem enable276_open :
    enable276 true (Metronome.Bank.addrOf ⟨276, by decide⟩) = true := by
  rw [enable276_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable276_spec
#print axioms enable276_open

/-- Gate enable of byte 277, extracted from `g_byte[277].g_used.u_cg`. -/
def enable277 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable277_0 := (addr1 == (277 : BitVec 9))
  let enable277_1 := we1 && enable277_0
  enable277_1

/-- The extracted gate of byte 277 equals `we1 && addr1 == 277` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable277_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable277 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 277) := by
  unfold enable277
  bv_decide

/-- Byte 277's extracted gate opens at its own offset and only there. -/
theorem enable277_open :
    enable277 true (Metronome.Bank.addrOf ⟨277, by decide⟩) = true := by
  rw [enable277_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable277_spec
#print axioms enable277_open

/-- Gate enable of byte 278, extracted from `g_byte[278].g_used.u_cg`. -/
def enable278 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable278_0 := (addr1 == (278 : BitVec 9))
  let enable278_1 := we1 && enable278_0
  enable278_1

/-- The extracted gate of byte 278 equals `we1 && addr1 == 278` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable278_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable278 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 278) := by
  unfold enable278
  bv_decide

/-- Byte 278's extracted gate opens at its own offset and only there. -/
theorem enable278_open :
    enable278 true (Metronome.Bank.addrOf ⟨278, by decide⟩) = true := by
  rw [enable278_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable278_spec
#print axioms enable278_open

/-- Gate enable of byte 279, extracted from `g_byte[279].g_used.u_cg`. -/
def enable279 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable279_0 := (addr1 == (279 : BitVec 9))
  let enable279_1 := we1 && enable279_0
  enable279_1

/-- The extracted gate of byte 279 equals `we1 && addr1 == 279` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable279_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable279 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 279) := by
  unfold enable279
  bv_decide

/-- Byte 279's extracted gate opens at its own offset and only there. -/
theorem enable279_open :
    enable279 true (Metronome.Bank.addrOf ⟨279, by decide⟩) = true := by
  rw [enable279_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable279_spec
#print axioms enable279_open

/-- Gate enable of byte 280, extracted from `g_byte[280].g_used.u_cg`. -/
def enable280 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable280_0 := (addr1 == (280 : BitVec 9))
  let enable280_1 := we1 && enable280_0
  enable280_1

/-- The extracted gate of byte 280 equals `we1 && addr1 == 280` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable280_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable280 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 280) := by
  unfold enable280
  bv_decide

/-- Byte 280's extracted gate opens at its own offset and only there. -/
theorem enable280_open :
    enable280 true (Metronome.Bank.addrOf ⟨280, by decide⟩) = true := by
  rw [enable280_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable280_spec
#print axioms enable280_open

/-- Gate enable of byte 281, extracted from `g_byte[281].g_used.u_cg`. -/
def enable281 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable281_0 := (addr1 == (281 : BitVec 9))
  let enable281_1 := we1 && enable281_0
  enable281_1

/-- The extracted gate of byte 281 equals `we1 && addr1 == 281` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable281_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable281 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 281) := by
  unfold enable281
  bv_decide

/-- Byte 281's extracted gate opens at its own offset and only there. -/
theorem enable281_open :
    enable281 true (Metronome.Bank.addrOf ⟨281, by decide⟩) = true := by
  rw [enable281_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable281_spec
#print axioms enable281_open

/-- Gate enable of byte 282, extracted from `g_byte[282].g_used.u_cg`. -/
def enable282 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable282_0 := (addr1 == (282 : BitVec 9))
  let enable282_1 := we1 && enable282_0
  enable282_1

/-- The extracted gate of byte 282 equals `we1 && addr1 == 282` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable282_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable282 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 282) := by
  unfold enable282
  bv_decide

/-- Byte 282's extracted gate opens at its own offset and only there. -/
theorem enable282_open :
    enable282 true (Metronome.Bank.addrOf ⟨282, by decide⟩) = true := by
  rw [enable282_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable282_spec
#print axioms enable282_open

/-- Gate enable of byte 283, extracted from `g_byte[283].g_used.u_cg`. -/
def enable283 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable283_0 := (addr1 == (283 : BitVec 9))
  let enable283_1 := we1 && enable283_0
  enable283_1

/-- The extracted gate of byte 283 equals `we1 && addr1 == 283` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable283_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable283 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 283) := by
  unfold enable283
  bv_decide

/-- Byte 283's extracted gate opens at its own offset and only there. -/
theorem enable283_open :
    enable283 true (Metronome.Bank.addrOf ⟨283, by decide⟩) = true := by
  rw [enable283_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable283_spec
#print axioms enable283_open

/-- Gate enable of byte 288, extracted from `g_byte[288].g_used.u_cg`. -/
def enable288 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable288_0 := (addr1 == (288 : BitVec 9))
  let enable288_1 := we1 && enable288_0
  enable288_1

/-- The extracted gate of byte 288 equals `we1 && addr1 == 288` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable288_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable288 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 288) := by
  unfold enable288
  bv_decide

/-- Byte 288's extracted gate opens at its own offset and only there. -/
theorem enable288_open :
    enable288 true (Metronome.Bank.addrOf ⟨288, by decide⟩) = true := by
  rw [enable288_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable288_spec
#print axioms enable288_open

/-- Gate enable of byte 289, extracted from `g_byte[289].g_used.u_cg`. -/
def enable289 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable289_0 := (addr1 == (289 : BitVec 9))
  let enable289_1 := we1 && enable289_0
  enable289_1

/-- The extracted gate of byte 289 equals `we1 && addr1 == 289` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable289_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable289 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 289) := by
  unfold enable289
  bv_decide

/-- Byte 289's extracted gate opens at its own offset and only there. -/
theorem enable289_open :
    enable289 true (Metronome.Bank.addrOf ⟨289, by decide⟩) = true := by
  rw [enable289_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable289_spec
#print axioms enable289_open

/-- Gate enable of byte 292, extracted from `g_byte[292].g_used.u_cg`. -/
def enable292 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable292_0 := (addr1 == (292 : BitVec 9))
  let enable292_1 := we1 && enable292_0
  enable292_1

/-- The extracted gate of byte 292 equals `we1 && addr1 == 292` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable292_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable292 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 292) := by
  unfold enable292
  bv_decide

/-- Byte 292's extracted gate opens at its own offset and only there. -/
theorem enable292_open :
    enable292 true (Metronome.Bank.addrOf ⟨292, by decide⟩) = true := by
  rw [enable292_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable292_spec
#print axioms enable292_open

/-- Gate enable of byte 293, extracted from `g_byte[293].g_used.u_cg`. -/
def enable293 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable293_0 := (addr1 == (293 : BitVec 9))
  let enable293_1 := we1 && enable293_0
  enable293_1

/-- The extracted gate of byte 293 equals `we1 && addr1 == 293` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable293_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable293 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 293) := by
  unfold enable293
  bv_decide

/-- Byte 293's extracted gate opens at its own offset and only there. -/
theorem enable293_open :
    enable293 true (Metronome.Bank.addrOf ⟨293, by decide⟩) = true := by
  rw [enable293_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable293_spec
#print axioms enable293_open

/-- Gate enable of byte 294, extracted from `g_byte[294].g_used.u_cg`. -/
def enable294 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable294_0 := (addr1 == (294 : BitVec 9))
  let enable294_1 := we1 && enable294_0
  enable294_1

/-- The extracted gate of byte 294 equals `we1 && addr1 == 294` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable294_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable294 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 294) := by
  unfold enable294
  bv_decide

/-- Byte 294's extracted gate opens at its own offset and only there. -/
theorem enable294_open :
    enable294 true (Metronome.Bank.addrOf ⟨294, by decide⟩) = true := by
  rw [enable294_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable294_spec
#print axioms enable294_open

/-- Gate enable of byte 295, extracted from `g_byte[295].g_used.u_cg`. -/
def enable295 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable295_0 := (addr1 == (295 : BitVec 9))
  let enable295_1 := we1 && enable295_0
  enable295_1

/-- The extracted gate of byte 295 equals `we1 && addr1 == 295` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable295_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable295 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 295) := by
  unfold enable295
  bv_decide

/-- Byte 295's extracted gate opens at its own offset and only there. -/
theorem enable295_open :
    enable295 true (Metronome.Bank.addrOf ⟨295, by decide⟩) = true := by
  rw [enable295_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable295_spec
#print axioms enable295_open

/-- Gate enable of byte 296, extracted from `g_byte[296].g_used.u_cg`. -/
def enable296 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable296_0 := (addr1 == (296 : BitVec 9))
  let enable296_1 := we1 && enable296_0
  enable296_1

/-- The extracted gate of byte 296 equals `we1 && addr1 == 296` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable296_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable296 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 296) := by
  unfold enable296
  bv_decide

/-- Byte 296's extracted gate opens at its own offset and only there. -/
theorem enable296_open :
    enable296 true (Metronome.Bank.addrOf ⟨296, by decide⟩) = true := by
  rw [enable296_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable296_spec
#print axioms enable296_open

/-- Gate enable of byte 297, extracted from `g_byte[297].g_used.u_cg`. -/
def enable297 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable297_0 := (addr1 == (297 : BitVec 9))
  let enable297_1 := we1 && enable297_0
  enable297_1

/-- The extracted gate of byte 297 equals `we1 && addr1 == 297` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable297_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable297 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 297) := by
  unfold enable297
  bv_decide

/-- Byte 297's extracted gate opens at its own offset and only there. -/
theorem enable297_open :
    enable297 true (Metronome.Bank.addrOf ⟨297, by decide⟩) = true := by
  rw [enable297_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable297_spec
#print axioms enable297_open

/-- Gate enable of byte 298, extracted from `g_byte[298].g_used.u_cg`. -/
def enable298 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable298_0 := (addr1 == (298 : BitVec 9))
  let enable298_1 := we1 && enable298_0
  enable298_1

/-- The extracted gate of byte 298 equals `we1 && addr1 == 298` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable298_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable298 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 298) := by
  unfold enable298
  bv_decide

/-- Byte 298's extracted gate opens at its own offset and only there. -/
theorem enable298_open :
    enable298 true (Metronome.Bank.addrOf ⟨298, by decide⟩) = true := by
  rw [enable298_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable298_spec
#print axioms enable298_open

/-- Gate enable of byte 299, extracted from `g_byte[299].g_used.u_cg`. -/
def enable299 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable299_0 := (addr1 == (299 : BitVec 9))
  let enable299_1 := we1 && enable299_0
  enable299_1

/-- The extracted gate of byte 299 equals `we1 && addr1 == 299` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable299_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable299 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 299) := by
  unfold enable299
  bv_decide

/-- Byte 299's extracted gate opens at its own offset and only there. -/
theorem enable299_open :
    enable299 true (Metronome.Bank.addrOf ⟨299, by decide⟩) = true := by
  rw [enable299_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable299_spec
#print axioms enable299_open

/-- Gate enable of byte 304, extracted from `g_byte[304].g_used.u_cg`. -/
def enable304 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable304_0 := (addr1 == (304 : BitVec 9))
  let enable304_1 := we1 && enable304_0
  enable304_1

/-- The extracted gate of byte 304 equals `we1 && addr1 == 304` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable304_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable304 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 304) := by
  unfold enable304
  bv_decide

/-- Byte 304's extracted gate opens at its own offset and only there. -/
theorem enable304_open :
    enable304 true (Metronome.Bank.addrOf ⟨304, by decide⟩) = true := by
  rw [enable304_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable304_spec
#print axioms enable304_open

/-- Gate enable of byte 305, extracted from `g_byte[305].g_used.u_cg`. -/
def enable305 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable305_0 := (addr1 == (305 : BitVec 9))
  let enable305_1 := we1 && enable305_0
  enable305_1

/-- The extracted gate of byte 305 equals `we1 && addr1 == 305` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable305_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable305 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 305) := by
  unfold enable305
  bv_decide

/-- Byte 305's extracted gate opens at its own offset and only there. -/
theorem enable305_open :
    enable305 true (Metronome.Bank.addrOf ⟨305, by decide⟩) = true := by
  rw [enable305_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable305_spec
#print axioms enable305_open

/-- Gate enable of byte 308, extracted from `g_byte[308].g_used.u_cg`. -/
def enable308 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable308_0 := (addr1 == (308 : BitVec 9))
  let enable308_1 := we1 && enable308_0
  enable308_1

/-- The extracted gate of byte 308 equals `we1 && addr1 == 308` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable308_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable308 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 308) := by
  unfold enable308
  bv_decide

/-- Byte 308's extracted gate opens at its own offset and only there. -/
theorem enable308_open :
    enable308 true (Metronome.Bank.addrOf ⟨308, by decide⟩) = true := by
  rw [enable308_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable308_spec
#print axioms enable308_open

/-- Gate enable of byte 309, extracted from `g_byte[309].g_used.u_cg`. -/
def enable309 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable309_0 := (addr1 == (309 : BitVec 9))
  let enable309_1 := we1 && enable309_0
  enable309_1

/-- The extracted gate of byte 309 equals `we1 && addr1 == 309` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable309_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable309 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 309) := by
  unfold enable309
  bv_decide

/-- Byte 309's extracted gate opens at its own offset and only there. -/
theorem enable309_open :
    enable309 true (Metronome.Bank.addrOf ⟨309, by decide⟩) = true := by
  rw [enable309_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable309_spec
#print axioms enable309_open

/-- Gate enable of byte 310, extracted from `g_byte[310].g_used.u_cg`. -/
def enable310 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable310_0 := (addr1 == (310 : BitVec 9))
  let enable310_1 := we1 && enable310_0
  enable310_1

/-- The extracted gate of byte 310 equals `we1 && addr1 == 310` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable310_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable310 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 310) := by
  unfold enable310
  bv_decide

/-- Byte 310's extracted gate opens at its own offset and only there. -/
theorem enable310_open :
    enable310 true (Metronome.Bank.addrOf ⟨310, by decide⟩) = true := by
  rw [enable310_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable310_spec
#print axioms enable310_open

/-- Gate enable of byte 311, extracted from `g_byte[311].g_used.u_cg`. -/
def enable311 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable311_0 := (addr1 == (311 : BitVec 9))
  let enable311_1 := we1 && enable311_0
  enable311_1

/-- The extracted gate of byte 311 equals `we1 && addr1 == 311` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable311_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable311 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 311) := by
  unfold enable311
  bv_decide

/-- Byte 311's extracted gate opens at its own offset and only there. -/
theorem enable311_open :
    enable311 true (Metronome.Bank.addrOf ⟨311, by decide⟩) = true := by
  rw [enable311_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable311_spec
#print axioms enable311_open

/-- Gate enable of byte 312, extracted from `g_byte[312].g_used.u_cg`. -/
def enable312 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable312_0 := (addr1 == (312 : BitVec 9))
  let enable312_1 := we1 && enable312_0
  enable312_1

/-- The extracted gate of byte 312 equals `we1 && addr1 == 312` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable312_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable312 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 312) := by
  unfold enable312
  bv_decide

/-- Byte 312's extracted gate opens at its own offset and only there. -/
theorem enable312_open :
    enable312 true (Metronome.Bank.addrOf ⟨312, by decide⟩) = true := by
  rw [enable312_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable312_spec
#print axioms enable312_open

/-- Gate enable of byte 313, extracted from `g_byte[313].g_used.u_cg`. -/
def enable313 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable313_0 := (addr1 == (313 : BitVec 9))
  let enable313_1 := we1 && enable313_0
  enable313_1

/-- The extracted gate of byte 313 equals `we1 && addr1 == 313` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable313_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable313 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 313) := by
  unfold enable313
  bv_decide

/-- Byte 313's extracted gate opens at its own offset and only there. -/
theorem enable313_open :
    enable313 true (Metronome.Bank.addrOf ⟨313, by decide⟩) = true := by
  rw [enable313_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable313_spec
#print axioms enable313_open

/-- Gate enable of byte 314, extracted from `g_byte[314].g_used.u_cg`. -/
def enable314 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable314_0 := (addr1 == (314 : BitVec 9))
  let enable314_1 := we1 && enable314_0
  enable314_1

/-- The extracted gate of byte 314 equals `we1 && addr1 == 314` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable314_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable314 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 314) := by
  unfold enable314
  bv_decide

/-- Byte 314's extracted gate opens at its own offset and only there. -/
theorem enable314_open :
    enable314 true (Metronome.Bank.addrOf ⟨314, by decide⟩) = true := by
  rw [enable314_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable314_spec
#print axioms enable314_open

/-- Gate enable of byte 315, extracted from `g_byte[315].g_used.u_cg`. -/
def enable315 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable315_0 := (addr1 == (315 : BitVec 9))
  let enable315_1 := we1 && enable315_0
  enable315_1

/-- The extracted gate of byte 315 equals `we1 && addr1 == 315` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable315_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable315 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 315) := by
  unfold enable315
  bv_decide

/-- Byte 315's extracted gate opens at its own offset and only there. -/
theorem enable315_open :
    enable315 true (Metronome.Bank.addrOf ⟨315, by decide⟩) = true := by
  rw [enable315_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable315_spec
#print axioms enable315_open

/-- Gate enable of byte 320, extracted from `g_byte[320].g_used.u_cg`. -/
def enable320 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable320_0 := (addr1 == (320 : BitVec 9))
  let enable320_1 := we1 && enable320_0
  enable320_1

/-- The extracted gate of byte 320 equals `we1 && addr1 == 320` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable320_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable320 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 320) := by
  unfold enable320
  bv_decide

/-- Byte 320's extracted gate opens at its own offset and only there. -/
theorem enable320_open :
    enable320 true (Metronome.Bank.addrOf ⟨320, by decide⟩) = true := by
  rw [enable320_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable320_spec
#print axioms enable320_open

/-- Gate enable of byte 321, extracted from `g_byte[321].g_used.u_cg`. -/
def enable321 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable321_0 := (addr1 == (321 : BitVec 9))
  let enable321_1 := we1 && enable321_0
  enable321_1

/-- The extracted gate of byte 321 equals `we1 && addr1 == 321` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable321_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable321 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 321) := by
  unfold enable321
  bv_decide

/-- Byte 321's extracted gate opens at its own offset and only there. -/
theorem enable321_open :
    enable321 true (Metronome.Bank.addrOf ⟨321, by decide⟩) = true := by
  rw [enable321_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable321_spec
#print axioms enable321_open

/-- Gate enable of byte 324, extracted from `g_byte[324].g_used.u_cg`. -/
def enable324 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable324_0 := (addr1 == (324 : BitVec 9))
  let enable324_1 := we1 && enable324_0
  enable324_1

/-- The extracted gate of byte 324 equals `we1 && addr1 == 324` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable324_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable324 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 324) := by
  unfold enable324
  bv_decide

/-- Byte 324's extracted gate opens at its own offset and only there. -/
theorem enable324_open :
    enable324 true (Metronome.Bank.addrOf ⟨324, by decide⟩) = true := by
  rw [enable324_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable324_spec
#print axioms enable324_open

/-- Gate enable of byte 325, extracted from `g_byte[325].g_used.u_cg`. -/
def enable325 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable325_0 := (addr1 == (325 : BitVec 9))
  let enable325_1 := we1 && enable325_0
  enable325_1

/-- The extracted gate of byte 325 equals `we1 && addr1 == 325` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable325_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable325 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 325) := by
  unfold enable325
  bv_decide

/-- Byte 325's extracted gate opens at its own offset and only there. -/
theorem enable325_open :
    enable325 true (Metronome.Bank.addrOf ⟨325, by decide⟩) = true := by
  rw [enable325_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable325_spec
#print axioms enable325_open

/-- Gate enable of byte 326, extracted from `g_byte[326].g_used.u_cg`. -/
def enable326 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable326_0 := (addr1 == (326 : BitVec 9))
  let enable326_1 := we1 && enable326_0
  enable326_1

/-- The extracted gate of byte 326 equals `we1 && addr1 == 326` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable326_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable326 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 326) := by
  unfold enable326
  bv_decide

/-- Byte 326's extracted gate opens at its own offset and only there. -/
theorem enable326_open :
    enable326 true (Metronome.Bank.addrOf ⟨326, by decide⟩) = true := by
  rw [enable326_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable326_spec
#print axioms enable326_open

/-- Gate enable of byte 327, extracted from `g_byte[327].g_used.u_cg`. -/
def enable327 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable327_0 := (addr1 == (327 : BitVec 9))
  let enable327_1 := we1 && enable327_0
  enable327_1

/-- The extracted gate of byte 327 equals `we1 && addr1 == 327` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable327_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable327 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 327) := by
  unfold enable327
  bv_decide

/-- Byte 327's extracted gate opens at its own offset and only there. -/
theorem enable327_open :
    enable327 true (Metronome.Bank.addrOf ⟨327, by decide⟩) = true := by
  rw [enable327_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable327_spec
#print axioms enable327_open

/-- Gate enable of byte 328, extracted from `g_byte[328].g_used.u_cg`. -/
def enable328 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable328_0 := (addr1 == (328 : BitVec 9))
  let enable328_1 := we1 && enable328_0
  enable328_1

/-- The extracted gate of byte 328 equals `we1 && addr1 == 328` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable328_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable328 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 328) := by
  unfold enable328
  bv_decide

/-- Byte 328's extracted gate opens at its own offset and only there. -/
theorem enable328_open :
    enable328 true (Metronome.Bank.addrOf ⟨328, by decide⟩) = true := by
  rw [enable328_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable328_spec
#print axioms enable328_open

/-- Gate enable of byte 329, extracted from `g_byte[329].g_used.u_cg`. -/
def enable329 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable329_0 := (addr1 == (329 : BitVec 9))
  let enable329_1 := we1 && enable329_0
  enable329_1

/-- The extracted gate of byte 329 equals `we1 && addr1 == 329` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable329_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable329 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 329) := by
  unfold enable329
  bv_decide

/-- Byte 329's extracted gate opens at its own offset and only there. -/
theorem enable329_open :
    enable329 true (Metronome.Bank.addrOf ⟨329, by decide⟩) = true := by
  rw [enable329_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable329_spec
#print axioms enable329_open

/-- Gate enable of byte 330, extracted from `g_byte[330].g_used.u_cg`. -/
def enable330 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable330_0 := (addr1 == (330 : BitVec 9))
  let enable330_1 := we1 && enable330_0
  enable330_1

/-- The extracted gate of byte 330 equals `we1 && addr1 == 330` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable330_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable330 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 330) := by
  unfold enable330
  bv_decide

/-- Byte 330's extracted gate opens at its own offset and only there. -/
theorem enable330_open :
    enable330 true (Metronome.Bank.addrOf ⟨330, by decide⟩) = true := by
  rw [enable330_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable330_spec
#print axioms enable330_open

/-- Gate enable of byte 331, extracted from `g_byte[331].g_used.u_cg`. -/
def enable331 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable331_0 := (addr1 == (331 : BitVec 9))
  let enable331_1 := we1 && enable331_0
  enable331_1

/-- The extracted gate of byte 331 equals `we1 && addr1 == 331` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable331_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable331 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 331) := by
  unfold enable331
  bv_decide

/-- Byte 331's extracted gate opens at its own offset and only there. -/
theorem enable331_open :
    enable331 true (Metronome.Bank.addrOf ⟨331, by decide⟩) = true := by
  rw [enable331_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable331_spec
#print axioms enable331_open

/-- Gate enable of byte 336, extracted from `g_byte[336].g_used.u_cg`. -/
def enable336 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable336_0 := (addr1 == (336 : BitVec 9))
  let enable336_1 := we1 && enable336_0
  enable336_1

/-- The extracted gate of byte 336 equals `we1 && addr1 == 336` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable336_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable336 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 336) := by
  unfold enable336
  bv_decide

/-- Byte 336's extracted gate opens at its own offset and only there. -/
theorem enable336_open :
    enable336 true (Metronome.Bank.addrOf ⟨336, by decide⟩) = true := by
  rw [enable336_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable336_spec
#print axioms enable336_open

/-- Gate enable of byte 337, extracted from `g_byte[337].g_used.u_cg`. -/
def enable337 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable337_0 := (addr1 == (337 : BitVec 9))
  let enable337_1 := we1 && enable337_0
  enable337_1

/-- The extracted gate of byte 337 equals `we1 && addr1 == 337` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable337_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable337 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 337) := by
  unfold enable337
  bv_decide

/-- Byte 337's extracted gate opens at its own offset and only there. -/
theorem enable337_open :
    enable337 true (Metronome.Bank.addrOf ⟨337, by decide⟩) = true := by
  rw [enable337_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable337_spec
#print axioms enable337_open

/-- Gate enable of byte 340, extracted from `g_byte[340].g_used.u_cg`. -/
def enable340 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable340_0 := (addr1 == (340 : BitVec 9))
  let enable340_1 := we1 && enable340_0
  enable340_1

/-- The extracted gate of byte 340 equals `we1 && addr1 == 340` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable340_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable340 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 340) := by
  unfold enable340
  bv_decide

/-- Byte 340's extracted gate opens at its own offset and only there. -/
theorem enable340_open :
    enable340 true (Metronome.Bank.addrOf ⟨340, by decide⟩) = true := by
  rw [enable340_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable340_spec
#print axioms enable340_open

/-- Gate enable of byte 341, extracted from `g_byte[341].g_used.u_cg`. -/
def enable341 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable341_0 := (addr1 == (341 : BitVec 9))
  let enable341_1 := we1 && enable341_0
  enable341_1

/-- The extracted gate of byte 341 equals `we1 && addr1 == 341` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable341_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable341 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 341) := by
  unfold enable341
  bv_decide

/-- Byte 341's extracted gate opens at its own offset and only there. -/
theorem enable341_open :
    enable341 true (Metronome.Bank.addrOf ⟨341, by decide⟩) = true := by
  rw [enable341_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable341_spec
#print axioms enable341_open

/-- Gate enable of byte 342, extracted from `g_byte[342].g_used.u_cg`. -/
def enable342 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable342_0 := (addr1 == (342 : BitVec 9))
  let enable342_1 := we1 && enable342_0
  enable342_1

/-- The extracted gate of byte 342 equals `we1 && addr1 == 342` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable342_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable342 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 342) := by
  unfold enable342
  bv_decide

/-- Byte 342's extracted gate opens at its own offset and only there. -/
theorem enable342_open :
    enable342 true (Metronome.Bank.addrOf ⟨342, by decide⟩) = true := by
  rw [enable342_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable342_spec
#print axioms enable342_open

/-- Gate enable of byte 343, extracted from `g_byte[343].g_used.u_cg`. -/
def enable343 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable343_0 := (addr1 == (343 : BitVec 9))
  let enable343_1 := we1 && enable343_0
  enable343_1

/-- The extracted gate of byte 343 equals `we1 && addr1 == 343` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable343_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable343 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 343) := by
  unfold enable343
  bv_decide

/-- Byte 343's extracted gate opens at its own offset and only there. -/
theorem enable343_open :
    enable343 true (Metronome.Bank.addrOf ⟨343, by decide⟩) = true := by
  rw [enable343_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable343_spec
#print axioms enable343_open

/-- Gate enable of byte 344, extracted from `g_byte[344].g_used.u_cg`. -/
def enable344 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable344_0 := (addr1 == (344 : BitVec 9))
  let enable344_1 := we1 && enable344_0
  enable344_1

/-- The extracted gate of byte 344 equals `we1 && addr1 == 344` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable344_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable344 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 344) := by
  unfold enable344
  bv_decide

/-- Byte 344's extracted gate opens at its own offset and only there. -/
theorem enable344_open :
    enable344 true (Metronome.Bank.addrOf ⟨344, by decide⟩) = true := by
  rw [enable344_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable344_spec
#print axioms enable344_open

/-- Gate enable of byte 345, extracted from `g_byte[345].g_used.u_cg`. -/
def enable345 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable345_0 := (addr1 == (345 : BitVec 9))
  let enable345_1 := we1 && enable345_0
  enable345_1

/-- The extracted gate of byte 345 equals `we1 && addr1 == 345` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable345_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable345 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 345) := by
  unfold enable345
  bv_decide

/-- Byte 345's extracted gate opens at its own offset and only there. -/
theorem enable345_open :
    enable345 true (Metronome.Bank.addrOf ⟨345, by decide⟩) = true := by
  rw [enable345_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable345_spec
#print axioms enable345_open

/-- Gate enable of byte 346, extracted from `g_byte[346].g_used.u_cg`. -/
def enable346 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable346_0 := (addr1 == (346 : BitVec 9))
  let enable346_1 := we1 && enable346_0
  enable346_1

/-- The extracted gate of byte 346 equals `we1 && addr1 == 346` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable346_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable346 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 346) := by
  unfold enable346
  bv_decide

/-- Byte 346's extracted gate opens at its own offset and only there. -/
theorem enable346_open :
    enable346 true (Metronome.Bank.addrOf ⟨346, by decide⟩) = true := by
  rw [enable346_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable346_spec
#print axioms enable346_open

/-- Gate enable of byte 347, extracted from `g_byte[347].g_used.u_cg`. -/
def enable347 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable347_0 := (addr1 == (347 : BitVec 9))
  let enable347_1 := we1 && enable347_0
  enable347_1

/-- The extracted gate of byte 347 equals `we1 && addr1 == 347` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable347_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable347 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 347) := by
  unfold enable347
  bv_decide

/-- Byte 347's extracted gate opens at its own offset and only there. -/
theorem enable347_open :
    enable347 true (Metronome.Bank.addrOf ⟨347, by decide⟩) = true := by
  rw [enable347_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable347_spec
#print axioms enable347_open

/-- Gate enable of byte 352, extracted from `g_byte[352].g_used.u_cg`. -/
def enable352 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable352_0 := (addr1 == (352 : BitVec 9))
  let enable352_1 := we1 && enable352_0
  enable352_1

/-- The extracted gate of byte 352 equals `we1 && addr1 == 352` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable352_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable352 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 352) := by
  unfold enable352
  bv_decide

/-- Byte 352's extracted gate opens at its own offset and only there. -/
theorem enable352_open :
    enable352 true (Metronome.Bank.addrOf ⟨352, by decide⟩) = true := by
  rw [enable352_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable352_spec
#print axioms enable352_open

/-- Gate enable of byte 353, extracted from `g_byte[353].g_used.u_cg`. -/
def enable353 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable353_0 := (addr1 == (353 : BitVec 9))
  let enable353_1 := we1 && enable353_0
  enable353_1

/-- The extracted gate of byte 353 equals `we1 && addr1 == 353` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable353_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable353 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 353) := by
  unfold enable353
  bv_decide

/-- Byte 353's extracted gate opens at its own offset and only there. -/
theorem enable353_open :
    enable353 true (Metronome.Bank.addrOf ⟨353, by decide⟩) = true := by
  rw [enable353_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable353_spec
#print axioms enable353_open

/-- Gate enable of byte 356, extracted from `g_byte[356].g_used.u_cg`. -/
def enable356 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable356_0 := (addr1 == (356 : BitVec 9))
  let enable356_1 := we1 && enable356_0
  enable356_1

/-- The extracted gate of byte 356 equals `we1 && addr1 == 356` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable356_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable356 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 356) := by
  unfold enable356
  bv_decide

/-- Byte 356's extracted gate opens at its own offset and only there. -/
theorem enable356_open :
    enable356 true (Metronome.Bank.addrOf ⟨356, by decide⟩) = true := by
  rw [enable356_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable356_spec
#print axioms enable356_open

/-- Gate enable of byte 357, extracted from `g_byte[357].g_used.u_cg`. -/
def enable357 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable357_0 := (addr1 == (357 : BitVec 9))
  let enable357_1 := we1 && enable357_0
  enable357_1

/-- The extracted gate of byte 357 equals `we1 && addr1 == 357` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable357_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable357 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 357) := by
  unfold enable357
  bv_decide

/-- Byte 357's extracted gate opens at its own offset and only there. -/
theorem enable357_open :
    enable357 true (Metronome.Bank.addrOf ⟨357, by decide⟩) = true := by
  rw [enable357_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable357_spec
#print axioms enable357_open

/-- Gate enable of byte 358, extracted from `g_byte[358].g_used.u_cg`. -/
def enable358 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable358_0 := (addr1 == (358 : BitVec 9))
  let enable358_1 := we1 && enable358_0
  enable358_1

/-- The extracted gate of byte 358 equals `we1 && addr1 == 358` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable358_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable358 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 358) := by
  unfold enable358
  bv_decide

/-- Byte 358's extracted gate opens at its own offset and only there. -/
theorem enable358_open :
    enable358 true (Metronome.Bank.addrOf ⟨358, by decide⟩) = true := by
  rw [enable358_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable358_spec
#print axioms enable358_open

/-- Gate enable of byte 359, extracted from `g_byte[359].g_used.u_cg`. -/
def enable359 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable359_0 := (addr1 == (359 : BitVec 9))
  let enable359_1 := we1 && enable359_0
  enable359_1

/-- The extracted gate of byte 359 equals `we1 && addr1 == 359` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable359_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable359 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 359) := by
  unfold enable359
  bv_decide

/-- Byte 359's extracted gate opens at its own offset and only there. -/
theorem enable359_open :
    enable359 true (Metronome.Bank.addrOf ⟨359, by decide⟩) = true := by
  rw [enable359_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable359_spec
#print axioms enable359_open

/-- Gate enable of byte 360, extracted from `g_byte[360].g_used.u_cg`. -/
def enable360 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable360_0 := (addr1 == (360 : BitVec 9))
  let enable360_1 := we1 && enable360_0
  enable360_1

/-- The extracted gate of byte 360 equals `we1 && addr1 == 360` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable360_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable360 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 360) := by
  unfold enable360
  bv_decide

/-- Byte 360's extracted gate opens at its own offset and only there. -/
theorem enable360_open :
    enable360 true (Metronome.Bank.addrOf ⟨360, by decide⟩) = true := by
  rw [enable360_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable360_spec
#print axioms enable360_open

/-- Gate enable of byte 361, extracted from `g_byte[361].g_used.u_cg`. -/
def enable361 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable361_0 := (addr1 == (361 : BitVec 9))
  let enable361_1 := we1 && enable361_0
  enable361_1

/-- The extracted gate of byte 361 equals `we1 && addr1 == 361` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable361_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable361 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 361) := by
  unfold enable361
  bv_decide

/-- Byte 361's extracted gate opens at its own offset and only there. -/
theorem enable361_open :
    enable361 true (Metronome.Bank.addrOf ⟨361, by decide⟩) = true := by
  rw [enable361_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable361_spec
#print axioms enable361_open

/-- Gate enable of byte 362, extracted from `g_byte[362].g_used.u_cg`. -/
def enable362 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable362_0 := (addr1 == (362 : BitVec 9))
  let enable362_1 := we1 && enable362_0
  enable362_1

/-- The extracted gate of byte 362 equals `we1 && addr1 == 362` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable362_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable362 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 362) := by
  unfold enable362
  bv_decide

/-- Byte 362's extracted gate opens at its own offset and only there. -/
theorem enable362_open :
    enable362 true (Metronome.Bank.addrOf ⟨362, by decide⟩) = true := by
  rw [enable362_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable362_spec
#print axioms enable362_open

/-- Gate enable of byte 363, extracted from `g_byte[363].g_used.u_cg`. -/
def enable363 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable363_0 := (addr1 == (363 : BitVec 9))
  let enable363_1 := we1 && enable363_0
  enable363_1

/-- The extracted gate of byte 363 equals `we1 && addr1 == 363` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable363_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable363 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 363) := by
  unfold enable363
  bv_decide

/-- Byte 363's extracted gate opens at its own offset and only there. -/
theorem enable363_open :
    enable363 true (Metronome.Bank.addrOf ⟨363, by decide⟩) = true := by
  rw [enable363_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable363_spec
#print axioms enable363_open

/-- Gate enable of byte 368, extracted from `g_byte[368].g_used.u_cg`. -/
def enable368 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable368_0 := (addr1 == (368 : BitVec 9))
  let enable368_1 := we1 && enable368_0
  enable368_1

/-- The extracted gate of byte 368 equals `we1 && addr1 == 368` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable368_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable368 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 368) := by
  unfold enable368
  bv_decide

/-- Byte 368's extracted gate opens at its own offset and only there. -/
theorem enable368_open :
    enable368 true (Metronome.Bank.addrOf ⟨368, by decide⟩) = true := by
  rw [enable368_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable368_spec
#print axioms enable368_open

/-- Gate enable of byte 369, extracted from `g_byte[369].g_used.u_cg`. -/
def enable369 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable369_0 := (addr1 == (369 : BitVec 9))
  let enable369_1 := we1 && enable369_0
  enable369_1

/-- The extracted gate of byte 369 equals `we1 && addr1 == 369` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable369_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable369 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 369) := by
  unfold enable369
  bv_decide

/-- Byte 369's extracted gate opens at its own offset and only there. -/
theorem enable369_open :
    enable369 true (Metronome.Bank.addrOf ⟨369, by decide⟩) = true := by
  rw [enable369_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable369_spec
#print axioms enable369_open

/-- Gate enable of byte 372, extracted from `g_byte[372].g_used.u_cg`. -/
def enable372 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable372_0 := (addr1 == (372 : BitVec 9))
  let enable372_1 := we1 && enable372_0
  enable372_1

/-- The extracted gate of byte 372 equals `we1 && addr1 == 372` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable372_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable372 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 372) := by
  unfold enable372
  bv_decide

/-- Byte 372's extracted gate opens at its own offset and only there. -/
theorem enable372_open :
    enable372 true (Metronome.Bank.addrOf ⟨372, by decide⟩) = true := by
  rw [enable372_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable372_spec
#print axioms enable372_open

/-- Gate enable of byte 373, extracted from `g_byte[373].g_used.u_cg`. -/
def enable373 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable373_0 := (addr1 == (373 : BitVec 9))
  let enable373_1 := we1 && enable373_0
  enable373_1

/-- The extracted gate of byte 373 equals `we1 && addr1 == 373` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable373_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable373 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 373) := by
  unfold enable373
  bv_decide

/-- Byte 373's extracted gate opens at its own offset and only there. -/
theorem enable373_open :
    enable373 true (Metronome.Bank.addrOf ⟨373, by decide⟩) = true := by
  rw [enable373_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable373_spec
#print axioms enable373_open

/-- Gate enable of byte 374, extracted from `g_byte[374].g_used.u_cg`. -/
def enable374 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable374_0 := (addr1 == (374 : BitVec 9))
  let enable374_1 := we1 && enable374_0
  enable374_1

/-- The extracted gate of byte 374 equals `we1 && addr1 == 374` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable374_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable374 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 374) := by
  unfold enable374
  bv_decide

/-- Byte 374's extracted gate opens at its own offset and only there. -/
theorem enable374_open :
    enable374 true (Metronome.Bank.addrOf ⟨374, by decide⟩) = true := by
  rw [enable374_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable374_spec
#print axioms enable374_open

/-- Gate enable of byte 375, extracted from `g_byte[375].g_used.u_cg`. -/
def enable375 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable375_0 := (addr1 == (375 : BitVec 9))
  let enable375_1 := we1 && enable375_0
  enable375_1

/-- The extracted gate of byte 375 equals `we1 && addr1 == 375` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable375_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable375 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 375) := by
  unfold enable375
  bv_decide

/-- Byte 375's extracted gate opens at its own offset and only there. -/
theorem enable375_open :
    enable375 true (Metronome.Bank.addrOf ⟨375, by decide⟩) = true := by
  rw [enable375_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable375_spec
#print axioms enable375_open

/-- Gate enable of byte 376, extracted from `g_byte[376].g_used.u_cg`. -/
def enable376 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable376_0 := (addr1 == (376 : BitVec 9))
  let enable376_1 := we1 && enable376_0
  enable376_1

/-- The extracted gate of byte 376 equals `we1 && addr1 == 376` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable376_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable376 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 376) := by
  unfold enable376
  bv_decide

/-- Byte 376's extracted gate opens at its own offset and only there. -/
theorem enable376_open :
    enable376 true (Metronome.Bank.addrOf ⟨376, by decide⟩) = true := by
  rw [enable376_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable376_spec
#print axioms enable376_open

/-- Gate enable of byte 377, extracted from `g_byte[377].g_used.u_cg`. -/
def enable377 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable377_0 := (addr1 == (377 : BitVec 9))
  let enable377_1 := we1 && enable377_0
  enable377_1

/-- The extracted gate of byte 377 equals `we1 && addr1 == 377` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable377_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable377 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 377) := by
  unfold enable377
  bv_decide

/-- Byte 377's extracted gate opens at its own offset and only there. -/
theorem enable377_open :
    enable377 true (Metronome.Bank.addrOf ⟨377, by decide⟩) = true := by
  rw [enable377_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable377_spec
#print axioms enable377_open

/-- Gate enable of byte 378, extracted from `g_byte[378].g_used.u_cg`. -/
def enable378 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable378_0 := (addr1 == (378 : BitVec 9))
  let enable378_1 := we1 && enable378_0
  enable378_1

/-- The extracted gate of byte 378 equals `we1 && addr1 == 378` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable378_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable378 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 378) := by
  unfold enable378
  bv_decide

/-- Byte 378's extracted gate opens at its own offset and only there. -/
theorem enable378_open :
    enable378 true (Metronome.Bank.addrOf ⟨378, by decide⟩) = true := by
  rw [enable378_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable378_spec
#print axioms enable378_open

/-- Gate enable of byte 379, extracted from `g_byte[379].g_used.u_cg`. -/
def enable379 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable379_0 := (addr1 == (379 : BitVec 9))
  let enable379_1 := we1 && enable379_0
  enable379_1

/-- The extracted gate of byte 379 equals `we1 && addr1 == 379` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable379_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable379 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 379) := by
  unfold enable379
  bv_decide

/-- Byte 379's extracted gate opens at its own offset and only there. -/
theorem enable379_open :
    enable379 true (Metronome.Bank.addrOf ⟨379, by decide⟩) = true := by
  rw [enable379_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable379_spec
#print axioms enable379_open

/-- Gate enable of byte 384, extracted from `g_byte[384].g_used.u_cg`. -/
def enable384 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable384_0 := (addr1 == (384 : BitVec 9))
  let enable384_1 := we1 && enable384_0
  enable384_1

/-- The extracted gate of byte 384 equals `we1 && addr1 == 384` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable384_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable384 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 384) := by
  unfold enable384
  bv_decide

/-- Byte 384's extracted gate opens at its own offset and only there. -/
theorem enable384_open :
    enable384 true (Metronome.Bank.addrOf ⟨384, by decide⟩) = true := by
  rw [enable384_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable384_spec
#print axioms enable384_open

/-- Gate enable of byte 385, extracted from `g_byte[385].g_used.u_cg`. -/
def enable385 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable385_0 := (addr1 == (385 : BitVec 9))
  let enable385_1 := we1 && enable385_0
  enable385_1

/-- The extracted gate of byte 385 equals `we1 && addr1 == 385` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable385_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable385 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 385) := by
  unfold enable385
  bv_decide

/-- Byte 385's extracted gate opens at its own offset and only there. -/
theorem enable385_open :
    enable385 true (Metronome.Bank.addrOf ⟨385, by decide⟩) = true := by
  rw [enable385_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable385_spec
#print axioms enable385_open

/-- Gate enable of byte 388, extracted from `g_byte[388].g_used.u_cg`. -/
def enable388 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable388_0 := (addr1 == (388 : BitVec 9))
  let enable388_1 := we1 && enable388_0
  enable388_1

/-- The extracted gate of byte 388 equals `we1 && addr1 == 388` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable388_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable388 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 388) := by
  unfold enable388
  bv_decide

/-- Byte 388's extracted gate opens at its own offset and only there. -/
theorem enable388_open :
    enable388 true (Metronome.Bank.addrOf ⟨388, by decide⟩) = true := by
  rw [enable388_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable388_spec
#print axioms enable388_open

/-- Gate enable of byte 389, extracted from `g_byte[389].g_used.u_cg`. -/
def enable389 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable389_0 := (addr1 == (389 : BitVec 9))
  let enable389_1 := we1 && enable389_0
  enable389_1

/-- The extracted gate of byte 389 equals `we1 && addr1 == 389` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable389_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable389 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 389) := by
  unfold enable389
  bv_decide

/-- Byte 389's extracted gate opens at its own offset and only there. -/
theorem enable389_open :
    enable389 true (Metronome.Bank.addrOf ⟨389, by decide⟩) = true := by
  rw [enable389_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable389_spec
#print axioms enable389_open

/-- Gate enable of byte 390, extracted from `g_byte[390].g_used.u_cg`. -/
def enable390 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable390_0 := (addr1 == (390 : BitVec 9))
  let enable390_1 := we1 && enable390_0
  enable390_1

/-- The extracted gate of byte 390 equals `we1 && addr1 == 390` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable390_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable390 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 390) := by
  unfold enable390
  bv_decide

/-- Byte 390's extracted gate opens at its own offset and only there. -/
theorem enable390_open :
    enable390 true (Metronome.Bank.addrOf ⟨390, by decide⟩) = true := by
  rw [enable390_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable390_spec
#print axioms enable390_open

/-- Gate enable of byte 391, extracted from `g_byte[391].g_used.u_cg`. -/
def enable391 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable391_0 := (addr1 == (391 : BitVec 9))
  let enable391_1 := we1 && enable391_0
  enable391_1

/-- The extracted gate of byte 391 equals `we1 && addr1 == 391` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable391_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable391 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 391) := by
  unfold enable391
  bv_decide

/-- Byte 391's extracted gate opens at its own offset and only there. -/
theorem enable391_open :
    enable391 true (Metronome.Bank.addrOf ⟨391, by decide⟩) = true := by
  rw [enable391_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable391_spec
#print axioms enable391_open

/-- Gate enable of byte 400, extracted from `g_byte[400].g_used.u_cg`. -/
def enable400 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable400_0 := (addr1 == (400 : BitVec 9))
  let enable400_1 := we1 && enable400_0
  enable400_1

/-- The extracted gate of byte 400 equals `we1 && addr1 == 400` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable400_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable400 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 400) := by
  unfold enable400
  bv_decide

/-- Byte 400's extracted gate opens at its own offset and only there. -/
theorem enable400_open :
    enable400 true (Metronome.Bank.addrOf ⟨400, by decide⟩) = true := by
  rw [enable400_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable400_spec
#print axioms enable400_open

/-- Gate enable of byte 401, extracted from `g_byte[401].g_used.u_cg`. -/
def enable401 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable401_0 := (addr1 == (401 : BitVec 9))
  let enable401_1 := we1 && enable401_0
  enable401_1

/-- The extracted gate of byte 401 equals `we1 && addr1 == 401` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable401_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable401 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 401) := by
  unfold enable401
  bv_decide

/-- Byte 401's extracted gate opens at its own offset and only there. -/
theorem enable401_open :
    enable401 true (Metronome.Bank.addrOf ⟨401, by decide⟩) = true := by
  rw [enable401_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable401_spec
#print axioms enable401_open

/-- Gate enable of byte 404, extracted from `g_byte[404].g_used.u_cg`. -/
def enable404 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable404_0 := (addr1 == (404 : BitVec 9))
  let enable404_1 := we1 && enable404_0
  enable404_1

/-- The extracted gate of byte 404 equals `we1 && addr1 == 404` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable404_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable404 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 404) := by
  unfold enable404
  bv_decide

/-- Byte 404's extracted gate opens at its own offset and only there. -/
theorem enable404_open :
    enable404 true (Metronome.Bank.addrOf ⟨404, by decide⟩) = true := by
  rw [enable404_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable404_spec
#print axioms enable404_open

/-- Gate enable of byte 405, extracted from `g_byte[405].g_used.u_cg`. -/
def enable405 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable405_0 := (addr1 == (405 : BitVec 9))
  let enable405_1 := we1 && enable405_0
  enable405_1

/-- The extracted gate of byte 405 equals `we1 && addr1 == 405` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable405_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable405 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 405) := by
  unfold enable405
  bv_decide

/-- Byte 405's extracted gate opens at its own offset and only there. -/
theorem enable405_open :
    enable405 true (Metronome.Bank.addrOf ⟨405, by decide⟩) = true := by
  rw [enable405_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable405_spec
#print axioms enable405_open

/-- Gate enable of byte 406, extracted from `g_byte[406].g_used.u_cg`. -/
def enable406 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable406_0 := (addr1 == (406 : BitVec 9))
  let enable406_1 := we1 && enable406_0
  enable406_1

/-- The extracted gate of byte 406 equals `we1 && addr1 == 406` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable406_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable406 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 406) := by
  unfold enable406
  bv_decide

/-- Byte 406's extracted gate opens at its own offset and only there. -/
theorem enable406_open :
    enable406 true (Metronome.Bank.addrOf ⟨406, by decide⟩) = true := by
  rw [enable406_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable406_spec
#print axioms enable406_open

/-- Gate enable of byte 407, extracted from `g_byte[407].g_used.u_cg`. -/
def enable407 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable407_0 := (addr1 == (407 : BitVec 9))
  let enable407_1 := we1 && enable407_0
  enable407_1

/-- The extracted gate of byte 407 equals `we1 && addr1 == 407` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable407_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable407 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 407) := by
  unfold enable407
  bv_decide

/-- Byte 407's extracted gate opens at its own offset and only there. -/
theorem enable407_open :
    enable407 true (Metronome.Bank.addrOf ⟨407, by decide⟩) = true := by
  rw [enable407_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable407_spec
#print axioms enable407_open

/-- Gate enable of byte 416, extracted from `g_byte[416].g_used.u_cg`. -/
def enable416 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable416_0 := (addr1 == (416 : BitVec 9))
  let enable416_1 := we1 && enable416_0
  enable416_1

/-- The extracted gate of byte 416 equals `we1 && addr1 == 416` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable416_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable416 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 416) := by
  unfold enable416
  bv_decide

/-- Byte 416's extracted gate opens at its own offset and only there. -/
theorem enable416_open :
    enable416 true (Metronome.Bank.addrOf ⟨416, by decide⟩) = true := by
  rw [enable416_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable416_spec
#print axioms enable416_open

/-- Gate enable of byte 417, extracted from `g_byte[417].g_used.u_cg`. -/
def enable417 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable417_0 := (addr1 == (417 : BitVec 9))
  let enable417_1 := we1 && enable417_0
  enable417_1

/-- The extracted gate of byte 417 equals `we1 && addr1 == 417` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable417_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable417 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 417) := by
  unfold enable417
  bv_decide

/-- Byte 417's extracted gate opens at its own offset and only there. -/
theorem enable417_open :
    enable417 true (Metronome.Bank.addrOf ⟨417, by decide⟩) = true := by
  rw [enable417_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable417_spec
#print axioms enable417_open

/-- Gate enable of byte 420, extracted from `g_byte[420].g_used.u_cg`. -/
def enable420 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable420_0 := (addr1 == (420 : BitVec 9))
  let enable420_1 := we1 && enable420_0
  enable420_1

/-- The extracted gate of byte 420 equals `we1 && addr1 == 420` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable420_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable420 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 420) := by
  unfold enable420
  bv_decide

/-- Byte 420's extracted gate opens at its own offset and only there. -/
theorem enable420_open :
    enable420 true (Metronome.Bank.addrOf ⟨420, by decide⟩) = true := by
  rw [enable420_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable420_spec
#print axioms enable420_open

/-- Gate enable of byte 421, extracted from `g_byte[421].g_used.u_cg`. -/
def enable421 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable421_0 := (addr1 == (421 : BitVec 9))
  let enable421_1 := we1 && enable421_0
  enable421_1

/-- The extracted gate of byte 421 equals `we1 && addr1 == 421` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable421_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable421 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 421) := by
  unfold enable421
  bv_decide

/-- Byte 421's extracted gate opens at its own offset and only there. -/
theorem enable421_open :
    enable421 true (Metronome.Bank.addrOf ⟨421, by decide⟩) = true := by
  rw [enable421_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable421_spec
#print axioms enable421_open

/-- Gate enable of byte 422, extracted from `g_byte[422].g_used.u_cg`. -/
def enable422 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable422_0 := (addr1 == (422 : BitVec 9))
  let enable422_1 := we1 && enable422_0
  enable422_1

/-- The extracted gate of byte 422 equals `we1 && addr1 == 422` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable422_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable422 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 422) := by
  unfold enable422
  bv_decide

/-- Byte 422's extracted gate opens at its own offset and only there. -/
theorem enable422_open :
    enable422 true (Metronome.Bank.addrOf ⟨422, by decide⟩) = true := by
  rw [enable422_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable422_spec
#print axioms enable422_open

/-- Gate enable of byte 423, extracted from `g_byte[423].g_used.u_cg`. -/
def enable423 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable423_0 := (addr1 == (423 : BitVec 9))
  let enable423_1 := we1 && enable423_0
  enable423_1

/-- The extracted gate of byte 423 equals `we1 && addr1 == 423` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable423_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable423 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 423) := by
  unfold enable423
  bv_decide

/-- Byte 423's extracted gate opens at its own offset and only there. -/
theorem enable423_open :
    enable423 true (Metronome.Bank.addrOf ⟨423, by decide⟩) = true := by
  rw [enable423_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable423_spec
#print axioms enable423_open

/-- Gate enable of byte 432, extracted from `g_byte[432].g_used.u_cg`. -/
def enable432 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable432_0 := (addr1 == (432 : BitVec 9))
  let enable432_1 := we1 && enable432_0
  enable432_1

/-- The extracted gate of byte 432 equals `we1 && addr1 == 432` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable432_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable432 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 432) := by
  unfold enable432
  bv_decide

/-- Byte 432's extracted gate opens at its own offset and only there. -/
theorem enable432_open :
    enable432 true (Metronome.Bank.addrOf ⟨432, by decide⟩) = true := by
  rw [enable432_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable432_spec
#print axioms enable432_open

/-- Gate enable of byte 433, extracted from `g_byte[433].g_used.u_cg`. -/
def enable433 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable433_0 := (addr1 == (433 : BitVec 9))
  let enable433_1 := we1 && enable433_0
  enable433_1

/-- The extracted gate of byte 433 equals `we1 && addr1 == 433` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable433_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable433 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 433) := by
  unfold enable433
  bv_decide

/-- Byte 433's extracted gate opens at its own offset and only there. -/
theorem enable433_open :
    enable433 true (Metronome.Bank.addrOf ⟨433, by decide⟩) = true := by
  rw [enable433_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable433_spec
#print axioms enable433_open

/-- Gate enable of byte 436, extracted from `g_byte[436].g_used.u_cg`. -/
def enable436 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable436_0 := (addr1 == (436 : BitVec 9))
  let enable436_1 := we1 && enable436_0
  enable436_1

/-- The extracted gate of byte 436 equals `we1 && addr1 == 436` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable436_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable436 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 436) := by
  unfold enable436
  bv_decide

/-- Byte 436's extracted gate opens at its own offset and only there. -/
theorem enable436_open :
    enable436 true (Metronome.Bank.addrOf ⟨436, by decide⟩) = true := by
  rw [enable436_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable436_spec
#print axioms enable436_open

/-- Gate enable of byte 437, extracted from `g_byte[437].g_used.u_cg`. -/
def enable437 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable437_0 := (addr1 == (437 : BitVec 9))
  let enable437_1 := we1 && enable437_0
  enable437_1

/-- The extracted gate of byte 437 equals `we1 && addr1 == 437` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable437_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable437 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 437) := by
  unfold enable437
  bv_decide

/-- Byte 437's extracted gate opens at its own offset and only there. -/
theorem enable437_open :
    enable437 true (Metronome.Bank.addrOf ⟨437, by decide⟩) = true := by
  rw [enable437_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable437_spec
#print axioms enable437_open

/-- Gate enable of byte 438, extracted from `g_byte[438].g_used.u_cg`. -/
def enable438 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable438_0 := (addr1 == (438 : BitVec 9))
  let enable438_1 := we1 && enable438_0
  enable438_1

/-- The extracted gate of byte 438 equals `we1 && addr1 == 438` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable438_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable438 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 438) := by
  unfold enable438
  bv_decide

/-- Byte 438's extracted gate opens at its own offset and only there. -/
theorem enable438_open :
    enable438 true (Metronome.Bank.addrOf ⟨438, by decide⟩) = true := by
  rw [enable438_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable438_spec
#print axioms enable438_open

/-- Gate enable of byte 439, extracted from `g_byte[439].g_used.u_cg`. -/
def enable439 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable439_0 := (addr1 == (439 : BitVec 9))
  let enable439_1 := we1 && enable439_0
  enable439_1

/-- The extracted gate of byte 439 equals `we1 && addr1 == 439` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable439_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable439 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 439) := by
  unfold enable439
  bv_decide

/-- Byte 439's extracted gate opens at its own offset and only there. -/
theorem enable439_open :
    enable439 true (Metronome.Bank.addrOf ⟨439, by decide⟩) = true := by
  rw [enable439_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable439_spec
#print axioms enable439_open

/-- Gate enable of byte 448, extracted from `g_byte[448].g_used.u_cg`. -/
def enable448 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable448_0 := (addr1 == (448 : BitVec 9))
  let enable448_1 := we1 && enable448_0
  enable448_1

/-- The extracted gate of byte 448 equals `we1 && addr1 == 448` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable448_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable448 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 448) := by
  unfold enable448
  bv_decide

/-- Byte 448's extracted gate opens at its own offset and only there. -/
theorem enable448_open :
    enable448 true (Metronome.Bank.addrOf ⟨448, by decide⟩) = true := by
  rw [enable448_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable448_spec
#print axioms enable448_open

/-- Gate enable of byte 449, extracted from `g_byte[449].g_used.u_cg`. -/
def enable449 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable449_0 := (addr1 == (449 : BitVec 9))
  let enable449_1 := we1 && enable449_0
  enable449_1

/-- The extracted gate of byte 449 equals `we1 && addr1 == 449` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable449_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable449 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 449) := by
  unfold enable449
  bv_decide

/-- Byte 449's extracted gate opens at its own offset and only there. -/
theorem enable449_open :
    enable449 true (Metronome.Bank.addrOf ⟨449, by decide⟩) = true := by
  rw [enable449_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable449_spec
#print axioms enable449_open

/-- Gate enable of byte 452, extracted from `g_byte[452].g_used.u_cg`. -/
def enable452 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable452_0 := (addr1 == (452 : BitVec 9))
  let enable452_1 := we1 && enable452_0
  enable452_1

/-- The extracted gate of byte 452 equals `we1 && addr1 == 452` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable452_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable452 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 452) := by
  unfold enable452
  bv_decide

/-- Byte 452's extracted gate opens at its own offset and only there. -/
theorem enable452_open :
    enable452 true (Metronome.Bank.addrOf ⟨452, by decide⟩) = true := by
  rw [enable452_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable452_spec
#print axioms enable452_open

/-- Gate enable of byte 453, extracted from `g_byte[453].g_used.u_cg`. -/
def enable453 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable453_0 := (addr1 == (453 : BitVec 9))
  let enable453_1 := we1 && enable453_0
  enable453_1

/-- The extracted gate of byte 453 equals `we1 && addr1 == 453` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable453_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable453 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 453) := by
  unfold enable453
  bv_decide

/-- Byte 453's extracted gate opens at its own offset and only there. -/
theorem enable453_open :
    enable453 true (Metronome.Bank.addrOf ⟨453, by decide⟩) = true := by
  rw [enable453_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable453_spec
#print axioms enable453_open

/-- Gate enable of byte 454, extracted from `g_byte[454].g_used.u_cg`. -/
def enable454 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable454_0 := (addr1 == (454 : BitVec 9))
  let enable454_1 := we1 && enable454_0
  enable454_1

/-- The extracted gate of byte 454 equals `we1 && addr1 == 454` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable454_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable454 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 454) := by
  unfold enable454
  bv_decide

/-- Byte 454's extracted gate opens at its own offset and only there. -/
theorem enable454_open :
    enable454 true (Metronome.Bank.addrOf ⟨454, by decide⟩) = true := by
  rw [enable454_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable454_spec
#print axioms enable454_open

/-- Gate enable of byte 455, extracted from `g_byte[455].g_used.u_cg`. -/
def enable455 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable455_0 := (addr1 == (455 : BitVec 9))
  let enable455_1 := we1 && enable455_0
  enable455_1

/-- The extracted gate of byte 455 equals `we1 && addr1 == 455` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable455_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable455 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 455) := by
  unfold enable455
  bv_decide

/-- Byte 455's extracted gate opens at its own offset and only there. -/
theorem enable455_open :
    enable455 true (Metronome.Bank.addrOf ⟨455, by decide⟩) = true := by
  rw [enable455_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable455_spec
#print axioms enable455_open

/-- Gate enable of byte 464, extracted from `g_byte[464].g_used.u_cg`. -/
def enable464 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable464_0 := (addr1 == (464 : BitVec 9))
  let enable464_1 := we1 && enable464_0
  enable464_1

/-- The extracted gate of byte 464 equals `we1 && addr1 == 464` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable464_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable464 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 464) := by
  unfold enable464
  bv_decide

/-- Byte 464's extracted gate opens at its own offset and only there. -/
theorem enable464_open :
    enable464 true (Metronome.Bank.addrOf ⟨464, by decide⟩) = true := by
  rw [enable464_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable464_spec
#print axioms enable464_open

/-- Gate enable of byte 465, extracted from `g_byte[465].g_used.u_cg`. -/
def enable465 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable465_0 := (addr1 == (465 : BitVec 9))
  let enable465_1 := we1 && enable465_0
  enable465_1

/-- The extracted gate of byte 465 equals `we1 && addr1 == 465` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable465_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable465 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 465) := by
  unfold enable465
  bv_decide

/-- Byte 465's extracted gate opens at its own offset and only there. -/
theorem enable465_open :
    enable465 true (Metronome.Bank.addrOf ⟨465, by decide⟩) = true := by
  rw [enable465_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable465_spec
#print axioms enable465_open

/-- Gate enable of byte 468, extracted from `g_byte[468].g_used.u_cg`. -/
def enable468 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable468_0 := (addr1 == (468 : BitVec 9))
  let enable468_1 := we1 && enable468_0
  enable468_1

/-- The extracted gate of byte 468 equals `we1 && addr1 == 468` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable468_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable468 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 468) := by
  unfold enable468
  bv_decide

/-- Byte 468's extracted gate opens at its own offset and only there. -/
theorem enable468_open :
    enable468 true (Metronome.Bank.addrOf ⟨468, by decide⟩) = true := by
  rw [enable468_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable468_spec
#print axioms enable468_open

/-- Gate enable of byte 469, extracted from `g_byte[469].g_used.u_cg`. -/
def enable469 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable469_0 := (addr1 == (469 : BitVec 9))
  let enable469_1 := we1 && enable469_0
  enable469_1

/-- The extracted gate of byte 469 equals `we1 && addr1 == 469` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable469_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable469 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 469) := by
  unfold enable469
  bv_decide

/-- Byte 469's extracted gate opens at its own offset and only there. -/
theorem enable469_open :
    enable469 true (Metronome.Bank.addrOf ⟨469, by decide⟩) = true := by
  rw [enable469_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable469_spec
#print axioms enable469_open

/-- Gate enable of byte 470, extracted from `g_byte[470].g_used.u_cg`. -/
def enable470 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable470_0 := (addr1 == (470 : BitVec 9))
  let enable470_1 := we1 && enable470_0
  enable470_1

/-- The extracted gate of byte 470 equals `we1 && addr1 == 470` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable470_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable470 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 470) := by
  unfold enable470
  bv_decide

/-- Byte 470's extracted gate opens at its own offset and only there. -/
theorem enable470_open :
    enable470 true (Metronome.Bank.addrOf ⟨470, by decide⟩) = true := by
  rw [enable470_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable470_spec
#print axioms enable470_open

/-- Gate enable of byte 471, extracted from `g_byte[471].g_used.u_cg`. -/
def enable471 (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  let enable471_0 := (addr1 == (471 : BitVec 9))
  let enable471_1 := we1 && enable471_0
  enable471_1

/-- The extracted gate of byte 471 equals `we1 && addr1 == 471` at every one of
the 512 addresses, for either strobe value. -/
@[simp] theorem enable471_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable471 we1 addr1 = (we1 && addr1 == BitVec.ofNat 9 471) := by
  unfold enable471
  bv_decide

/-- Byte 471's extracted gate opens at its own offset and only there. -/
theorem enable471_open :
    enable471 true (Metronome.Bank.addrOf ⟨471, by decide⟩) = true := by
  rw [enable471_spec]
  simp [Metronome.Bank.addrOf]

-- The audit for this byte; `bank_check.py` records it and rejects `sorryAx`.
#print axioms enable471_spec
#print axioms enable471_open

/-! ## Mutual exclusion, the write contract and concrete witnesses

Every live byte has its own `enable{k}_spec` above: the extracted gate is the
arithmetic per-byte comparison at every address. Mutual exclusion follows from
that rule and from the offsets being distinct (`Metronome.Bank.gateOpen_exclusive`),
and the write contract follows from the rule plus the latch wiring that
`bank_check.py` checks structurally (`Metronome.Bank.write_exact`). -/

/-- At most one gate of the bank is enabled for any staged write word: the
extracted gates are instances of this arithmetic rule. -/
theorem gates_exclusive (k j : Fin cfgBytes) (h : k ≠ j) (we1 : Bool)
    (addr1 : BitVec 9) :
    (Metronome.Bank.gateOpen we1 addr1 k &&
      Metronome.Bank.gateOpen we1 addr1 j) = false :=
  Metronome.Bank.gateOpen_exclusive k j h we1 addr1

/-- The live witness's extracted gate is its specification gate at every
address. -/
theorem witness_gate_matches (we1 : Bool) (addr1 : BitVec 9) :
    enable0 we1 addr1 = Metronome.Bank.gateOpen we1 addr1 liveWitness := by
  rw [enable0_spec]
  rfl

/-- An issued write to any byte of the elaborated bank updates exactly that
byte's mask bits to `data1 & MASK`. -/
theorem bank_write_exact (s : Metronome.Bank.State) (k : Fin cfgBytes)
    (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.step s true (Metronome.Bank.addrOf k) data1) k =
      data1 &&& s.mask k :=
  (Metronome.Bank.write_exact s k data1).1

/-- ... and leaves every other byte unchanged. -/
theorem bank_write_others (s : Metronome.Bank.State) (k j : Fin cfgBytes)
    (h : j ≠ k) (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.step s true (Metronome.Bank.addrOf k) data1) j =
      Metronome.Bank.read s j :=
  (Metronome.Bank.write_exact s k data1).2 j h

/-- A transparency phase of any gate family that implements the arithmetic
per-byte rule is exactly the specified write step. `bank_check.py` proves the
hypothesis one live byte at a time; the `enable{k}_spec` theorems above are its
conjuncts. -/
theorem phase_eq_step (rtlEn : Fin cfgBytes → Bool → BitVec 9 → Bool)
    (hmatch : ∀ k we1 addr1,
      rtlEn k we1 addr1 = Metronome.Bank.gateOpen we1 addr1 k)
    (s : Metronome.Bank.State) (we1 : Bool) (addr1 : BitVec 9) (data1 : BitVec 8) :
    Metronome.Bank.phase s (fun k => rtlEn k we1 addr1) data1 =
      Metronome.Bank.step s we1 addr1 data1 :=
  Metronome.Bank.step_of_gates s rtlEn hmatch we1 addr1 data1

/-! ## Concrete witnesses on the elaborated mask -/

/-- The live witness offset has a non-zero mask byte, so it has latches. -/
theorem witness_live_mask : paramMask liveWitness ≠ 0 := by
  decide

/-- The hole witness offset has a zero mask byte. -/
theorem witness_hole_mask : paramMask holeWitness = 0 := by
  decide

/-- A write to the mask-zero witness offset changes nothing on the elaborated
mask. -/
theorem bank_hole_noop (we1 : Bool) (data1 : BitVec 8) :
    Metronome.Bank.read
        (Metronome.Bank.step maskState we1 (Metronome.Bank.addrOf holeWitness)
          data1) =
      Metronome.Bank.read maskState :=
  Metronome.Bank.write_mask_zero maskState holeWitness witness_hole_mask we1 data1

-- Axiom audit. The per-byte equalities use `bv_decide`; the audit below and the
-- per-byte audits above record exactly which axioms appear. `bank_check.py`
-- rejects any `sorryAx`.
#print axioms gates_exclusive
#print axioms witness_gate_matches
#print axioms bank_write_exact
#print axioms bank_write_others
#print axioms phase_eq_step
#print axioms witness_live_mask
#print axioms witness_hole_mask
#print axioms bank_hole_noop
