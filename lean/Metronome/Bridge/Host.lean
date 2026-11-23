import Metronome.Machine
import Metronome.HostCmd
import Metronome.HostRead

/-!
# Bridge: the host-link cut (`Metronome.HostCmd`) against `Machine.Host`

`Metronome.HostCmd` specifies the §9 SPI target's command/address/data state
machine (`phase`, `bitc`, `rx`, `isRd`, `addr`, `wr`, `wdata`, `rd`, `rack` and
the `cmd` history byte) and `HostRead` extends it with `tx`/`rackv`;
`hostcmd_check.py` / `hostread_check.py` prove the elaborated link implements
them.  `Metronome.Machine` states the same link in `Machine.hostNext`.

## What this file proves

* `pin_bridge` — the cut's `SR` (synchronised rising SCK with `CS_N` low) is the
  machine `PinView`'s `sckRise && !csn`, under the explicit `pinOf` map.
* `nbit_bridge` / `nbit_step` — the machine's bit counter `nbit` after the step is
  exactly the cut's `bitc`, for every sampled pin input.
* `byteIn_eq` — if the machine's shift register holds the cut's seven bits in
  its low seven, then the machine's completed byte `bv 8 ((rx % 128) * 2 + MOSI)`
  is exactly the cut's `byteIn = rx ++ MOSI`.
* `LinkRel` — the relation between the cut's link registers and the machine's
  (see the section comment below); `linkRel_reset` and `phase_step`, `nbit_step`,
  `rx_step`, `cmdZero_step`, `cmdNe_step`, `isRd_step`, `wr_step`, `wdata_step`,
  `rd_step`, `rack_step`, `addr_step` show it is preserved by one step;
  `linkRel_step` assembles them.
* `LinkRelR` — `LinkRel` extended with the `HostRead` response registers `tx`
  and `rackv` (`linkRelR_reset`, `tx_step`, `rackv_step`, `linkRelR_step`).  The
  `rackv` relation is conditional on the waiting acknowledgement (`rack`),
  because the machine keeps the read value in `ldD` for one cycle only
  (`rackv_witness`).
* `hw_bridge`, `read_req_bridge`, `miso_bridge`, `miso_pin_bridge` — the
  observable outputs agree: the host write (address, data) the machine issues,
  its read request, and MISO (`Machine.pinsOut`'s low bit = the cut's `tx[7]`).

No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace Metronome.Bridge.Host

/-- The cut's sampled pins as the machine's `PinView`, with the host pins in
the §2 positions (`SCK = ui_in[0]`, `CS_N = ui_in[1]`, `MOSI = ui_in[2]`) and
`sckRise` the rising edge of the synchronised SCK. -/
def pinOf (i : HostCmd.Input) : Machine.PinView :=
  { lvl := 0, prev := 0, sck := i.sck, csn := i.csN, mosi := i.mosi,
    sckRise := i.sck && !i.sckPrev }

/-- The link registers of the cut that have a direct machine counterpart
(`rx` keeps the low seven bits, `nbit = bitc`). -/
def absHost (s : HostCmd.State) : Machine.HostSt :=
  { rx := Machine.Util.bv 8 s.rx.toNat, nbit := s.bitc }

/-- A machine state carrying the cut's link registers; the other fields are the
machine's zero state, since the theorems below do not read them. -/
def absChip (s : HostCmd.State) : Machine.State :=
  { Machine.State.init with host := absHost s }

/-- The cut's `SR` is the machine's `sckRise && !csn`. -/
theorem pin_bridge (i : HostCmd.Input) :
    ((pinOf i).sckRise && !((pinOf i).csn)) = HostCmd.sr i := by
  rcases i with ⟨r, sc, sp, cs, mo, rd, hl⟩
  cases cs <;> cases sc <;> cases sp <;> simp [pinOf, HostCmd.sr]

/-- `bv n x.toNat` is `x`. -/
theorem bv_toNat {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv]

/-- The machine's `(nbit + 1) mod 8` (a `Nat`, reduced to three bits) is the
cut's `if bitc = 7 then 0 else bitc + 1`. -/
theorem bitc_succ (x : BitVec 3) :
    BitVec.ofNat 3 ((x.toNat + 1) % 8) = if x = 7 then 0 else x + 1 := by
  have h : BitVec.ofNat 3 ((x.toNat + 1) % 8) = x + 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add]
    simp
  rw [h]
  by_cases hx : x = 7
  · rw [ite_eq_left hx, hx]
    decide
  · rw [ite_eq_right hx]

/-- The machine's bit counter after the step is the cut's `bitc` (§9: the bit
index within the current byte; `CS_N` high clears it, each `SR` advances it,
the eighth wraps). -/
theorem nbit_bridge (s : HostCmd.State) (i : HostCmd.Input) (cv : Machine.CfgView)
    (served : Bool) (hreset : i.resetN = true) :
    (Machine.hostNext (absChip s) cv (pinOf i) served).1.nbit =
      HostCmd.bitcNext s i := by
  rcases i with ⟨r, sc, sp, cs, mo, rd, hl⟩
  have hrr : r = true := hreset
  cases cs <;> cases sc <;> cases sp <;>
  simp [Machine.hostNext, absChip, absHost, pinOf, HostCmd.bitcNext, HostCmd.sr,
    bitc_succ, hrr, bv_toNat, Machine.Util.bv]

/-- A one-bit vector's `toNat` is the Bool's 0/1. -/
theorem b2n_bit (b : Bool) :
    (if b then (1 : BitVec 1) else 0).toNat = Machine.Util.b2n b := by
  cases b <;> simp [Machine.Util.b2n]

/-- The completed byte: if the machine's `rx` holds the cut's seven bits in its
low seven, the machine's `bv 8 ((rx % 128) * 2 + MOSI)` is the cut's
`byteIn = rx ++ MOSI`.  This is the value the §9 command/address/data decode
uses. -/
theorem byteIn_eq (s : HostCmd.State) (m : Machine.HostSt)
    (hrx : m.rx.toNat % 128 = s.rx.toNat) (b : Bool) :
    Machine.Util.bv 8 ((m.rx.toNat % 128) * 2 + Machine.Util.b2n b) =
      s.rx ++ (if b then (1 : BitVec 1) else 0) := by
  rw [hrx]
  apply BitVec.eq_of_toNat_eq
  rw [Machine.Util.bv, BitVec.toNat_ofNat, BitVec.toNat_append, b2n_bit]
  have hlt : s.rx.toNat * 2 + Machine.Util.b2n b < 2 ^ 8 := by
    have h := s.rx.isLt
    cases b <;> simp [Machine.Util.b2n] <;> omega
  rw [Nat.mod_eq_of_lt hlt]
  have hb : Machine.Util.b2n b < 2 ^ 1 := by
    cases b <;> simp [Machine.Util.b2n]
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 1) hb s.rx.toNat
  rw [Nat.shiftLeft_eq]
  have h2 : s.rx.toNat * 2 ^ 1 = 2 ^ 1 * s.rx.toNat := Nat.mul_comm _ _
  rw [h2, ← hor]

/-! ## The relation between the cut and the machine link state

`phaseOf` is the cut's byte state as a function of the machine's `(nbyte, cmd)`:
the machine has no `IGN` state, it walks `nbyte = 1, 2, 3` with `cmd = 0` for a
transaction it ignores.  `LinkRel` relates every link register of the cut to the
machine's `HostSt` (plus the chip fields the machine's link step reads).
`wdata` is conditional because the machine tracks the shifting byte in `wData`
every cycle while the cut holds it until the strobe. -/

/-- The machine's data-RAM address test (§6.2 / §9: `DATA_BASE .. DATA_BASE + 2048`). -/
def ramAddr (a : Nat) : Bool :=
  Machine.Tables.DATA_BASE ≤ a && a < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES

/-- The cut's byte state as a function of the machine's `(nbyte, cmd)`. -/
def phaseOf (h : Machine.HostSt) : BitVec 3 :=
  if h.nbyte.toNat = 0 then HostCmd.ST_CMD
  else if h.cmd.toNat = 0 then HostCmd.ST_IGN
  else if h.nbyte.toNat = 1 then HostCmd.ST_AH
  else if h.nbyte.toNat = 2 then HostCmd.ST_AL
  else HostCmd.ST_DATA

/-- The link relation: the cut's `HostCmd.State` against the machine's host link
state in a chip state `m`.  The machine's `cmd` code is `0` exactly for a cut
command byte that is neither `0x02` nor `0x03` (the ignored transaction), and is
never `3`. -/
structure LinkRel (s : HostCmd.State) (m : Machine.State) : Prop where
  /-- `phase` is the machine's `(nbyte, cmd)`; `IGN` is `1 ≤ nbyte` with `cmd = 0`. -/
  phase : s.phase = phaseOf m.host
  /-- the bit count within the byte. -/
  bitc : s.bitc = m.host.nbit
  /-- the receive shift register holds the cut's seven bits. -/
  rx : s.rx.toNat = m.host.rx.toNat % 128
  /-- the command code is zero exactly for an ignored command. -/
  cmdZero : (m.host.cmd = 0) ↔ (s.cmd ≠ HostCmd.CMD_WRITE ∧ s.cmd ≠ HostCmd.CMD_READ)
  /-- the machine only ever latches the codes `0`, `1`, `2`. -/
  cmdNe : m.host.cmd ≠ 3
  /-- the read-command latch. -/
  isRd : (s.isRd = true) ↔ (m.host.cmd = 2)
  /-- the address register. -/
  addr : s.addr = m.host.addr
  /-- the registered write strobe. -/
  wr : s.wr = m.host.wPend
  /-- the write byte, while the strobe is up. -/
  wdata : s.wr = true → s.wdata = m.host.wData
  /-- the registered read request. -/
  rd : s.rd = m.host.rPend
  /-- the register-read acknowledgement pending. -/
  rack : s.rack = m.host.ldV

theorem bv2_cases (x : BitVec 2) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  bv_decide

theorem bv2_cases_ne (x : BitVec 2) (h : x ≠ 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases bv2_cases x with h' | h' | h' | h' <;> simp_all

theorem toNat_eq_two (c : BitVec 8) : c.toNat = 2 ↔ c = HostCmd.CMD_WRITE := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; decide
  · intro h; rw [h]; decide

theorem toNat_eq_three (c : BitVec 8) : c.toNat = 3 ↔ c = HostCmd.CMD_READ := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; decide
  · intro h; rw [h]; decide

theorem byte_ne_two (c : BitVec 8) : c.toNat ≠ 2 ↔ c ≠ HostCmd.CMD_WRITE :=
  not_congr (toNat_eq_two c)

theorem byte_ne_three (c : BitVec 8) : c.toNat ≠ 3 ↔ c ≠ HostCmd.CMD_READ :=
  not_congr (toNat_eq_three c)

theorem bv2_toNat_zero (x : BitVec 2) : x.toNat = 0 ↔ x = 0 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  · intro h; rw [h]; rfl

theorem bv2_zero_iff (x : BitVec 2) : (Machine.Util.bv 2 x.toNat = 0) ↔ x = 0 := by
  rw [bv_toNat]

@[simp] theorem bv2_toNat_toNat (x : BitVec 2) : (Machine.Util.bv 2 x.toNat).toNat = x.toNat := by
  rw [bv_toNat]

@[simp] theorem bv2_toNat_0 : (Machine.Util.bv 2 0).toNat = 0 := by decide
@[simp] theorem bv2_toNat_1 : (Machine.Util.bv 2 1).toNat = 1 := by decide
@[simp] theorem bv2_toNat_2 : (Machine.Util.bv 2 2).toNat = 2 := by decide
@[simp] theorem bv2_toNat_3 : (Machine.Util.bv 2 3).toNat = 3 := by decide

/-- The machine's command code at a completed command byte: zero exactly for an
ignored command. -/
@[simp] theorem cmdStep_toNat_zero (v : Nat) :
    ((Machine.Util.bv 2 (if v = 2 then 1 else if v = 3 then 2 else 0)).toNat = 0) ↔
      (v ≠ 2 ∧ v ≠ 3) := by
  rw [bv2_toNat_zero]
  by_cases h2 : v = 2
  · simp [h2, Machine.Util.bv]
  · by_cases h3 : v = 3
    · simp [h2, h3, Machine.Util.bv]
    · simp [h2, h3, Machine.Util.bv]

theorem cmdStep_zero (v : Nat) :
    (Machine.Util.bv 2 (if v = 2 then 1 else if v = 3 then 2 else 0) = 0) ↔
      (v ≠ 2 ∧ v ≠ 3) := by
  rw [← bv2_toNat_zero]
  exact cmdStep_toNat_zero v

theorem cmdStep_two (v : Nat) :
    (Machine.Util.bv 2 (if v = 2 then 1 else if v = 3 then 2 else 0) = 2) ↔ v = 3 := by
  by_cases h2 : v = 2
  · simp [h2, Machine.Util.bv]
  · by_cases h3 : v = 3
    · simp [h2, h3, Machine.Util.bv]
    · simp [h2, h3, Machine.Util.bv]

theorem cmdStep_ne_three (v : Nat) :
    Machine.Util.bv 2 (if v = 2 then 1 else if v = 3 then 2 else 0) ≠ 3 := by
  by_cases h2 : v = 2
  · simp [h2, Machine.Util.bv]
  · by_cases h3 : v = 3
    · simp [h2, h3, Machine.Util.bv]
    · simp [h2, h3, Machine.Util.bv]

/-- The machine's completed byte equals the cut's `byteIn`. -/
theorem v_bridge (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (hrel : LinkRel s m) :
    (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi =
      (HostCmd.byteIn s i).toNat := by
  have hlt : (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi < 256 := by
    have := Nat.mod_lt m.host.rx.toNat (by decide : 0 < 128)
    cases i.mosi <;> simp [Machine.Util.b2n] <;> omega
  have h : Machine.Util.bv 8 ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi) =
      HostCmd.byteIn s i := by
    simp only [HostCmd.byteIn]
    exact byteIn_eq s m.host hrel.rx.symm i.mosi
  rw [← h, Machine.Util.bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The ignored-command test on both sides. -/
theorem ign_iff (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input) (hrel : LinkRel s m) :
    ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 2 ∧
        (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 3) ↔
      ¬ (HostCmd.byteIn s i = HostCmd.CMD_WRITE ∨ HostCmd.byteIn s i = HostCmd.CMD_READ) := by
  rw [v_bridge s m i hrel]
  constructor
  · intro h hWR
    rcases hWR with hW | hR
    · exact h.1 (by rw [hW]; decide)
    · exact h.2 (by rw [hR]; decide)
  · intro h
    exact ⟨fun h2 => h (Or.inl ((toNat_eq_two _).mp h2)),
      fun h3 => h (Or.inr ((toNat_eq_three _).mp h3))⟩

/-- `(x <<< 1) ||| b` is the low seven bits of `x ++ b`. -/
theorem rxOr_toNat (x : BitVec 7) (b : Bool) :
    ((x <<< 1) ||| (if b then (1 : BitVec 7) else 0)).toNat =
      (2 * x.toNat + Machine.Util.b2n b) % 128 := by
  have hb2 : Machine.Util.b2n b < 2 ^ 1 := by cases b <;> simp [Machine.Util.b2n]
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 1) hb2 (x.toNat % 64)
  rw [show (2 : Nat) ^ 1 = 2 by decide] at hor
  have hb' : (if b then (1 : BitVec 7) else 0).toNat = Machine.Util.b2n b := by
    cases b <;> simp [Machine.Util.b2n]
  rw [BitVec.toNat_or, hb']
  have hs : (x <<< 1).toNat = (x.toNat % 64) * 2 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [show (2 : Nat) ^ 1 = 2 by decide, show (2 : Nat) ^ 7 = 128 by decide]
    omega
  rw [hs, Nat.mul_comm (x.toNat % 64) 2]
  rw [← hor]
  omega

/-- The cut's reset state is the machine's power-on state. -/
theorem linkRel_reset : LinkRel HostCmd.resetState Machine.State.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phaseOf, HostCmd.resetState, Machine.State.init]
  · rfl
  · rfl
  · simp [HostCmd.resetState, Machine.State.init]
  · simp [HostCmd.resetState, Machine.State.init]
  · simp [HostCmd.resetState, Machine.State.init]
  · rfl
  · rfl
  · intro h; exact absurd h (by simp [HostCmd.resetState])
  · rfl
  · rfl

/-! ## The machine's link registers as formulas

Each field of `Machine.hostNext`'s host state is characterised either by a
"hold" formula (no completed byte) or by a "complete" formula for the byte state
the machine was in.  These are the building blocks of the step proofs. -/

/-- Without a completed byte the machine's command code holds. -/
theorem cmd_hold (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView) (served : Bool)
    (hcomp : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false) :
    (Machine.hostNext m cv p served).1.cmd = Machine.Util.bv 2 m.host.cmd.toNat := by
  simp only [Machine.hostNext]
  by_cases hcs : p.csn
  · simp [hcs]
  · have hcond : p.sckRise = false ∨ ¬(m.host.nbit.toNat = 7) := by
      by_cases hs : p.sckRise = true
      · right
        have h1 : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false := hcomp
        rw [hs] at h1
        have hc : (m.host.nbit.toNat == 7) = false := by simpa [hcs] using h1
        simpa [beq_iff_eq] using hc
      · left
        cases hsp : p.sckRise <;> simp_all
    simp [hcs, hcond]

/-- The command code latched by a completed command byte. -/
theorem cmd_complete_zero (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 0) :
    (Machine.hostNext m cv p served).1.cmd =
      Machine.Util.bv 2 (if (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi = 2 then 1
        else if (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi = 3 then 2 else 0) := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

/-- A completed address or data byte leaves the command code alone. -/
theorem cmd_complete_keep (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte ≠ 0) :
    (Machine.hostNext m cv p served).1.cmd = Machine.Util.bv 2 m.host.cmd.toNat := by
  rcases bv2_cases m.host.nbyte with h | h | h | h
  · exact absurd h hnb
  · simp [Machine.hostNext, hcs, hsr, hbit, h]
  · simp [Machine.hostNext, hcs, hsr, hbit, h]
  · simp [Machine.hostNext, hcs, hsr, hbit, h]

/-- Without a completed byte the machine issues no host write. -/
theorem wP_hold (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView) (served : Bool)
    (hcomp : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false) :
    (Machine.hostNext m cv p served).1.wPend = false := by
  simp only [Machine.hostNext]
  by_cases hcs : p.csn
  · simp [hcs]
  · have hcond : p.sckRise = false ∨ ¬(m.host.nbit.toNat = 7) := by
      by_cases hs : p.sckRise = true
      · right
        have h1 : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false := hcomp
        rw [hs] at h1
        have hc : (m.host.nbit.toNat == 7) = false := by simpa [hcs] using h1
        simpa [beq_iff_eq] using hc
      · left
        cases hsp : p.sckRise <;> simp_all
    simp [hcs, hcond]

/-- Without a completed byte the machine issues no read request. -/
theorem rP_hold (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView) (served : Bool)
    (hcomp : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false) :
    (Machine.hostNext m cv p served).1.rPend = false := by
  simp only [Machine.hostNext]
  by_cases hcs : p.csn
  · simp [hcs]
  · have hcond : p.sckRise = false ∨ ¬(m.host.nbit.toNat = 7) := by
      by_cases hs : p.sckRise = true
      · right
        have h1 : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false := hcomp
        rw [hs] at h1
        have hc : (m.host.nbit.toNat == 7) = false := by simpa [hcs] using h1
        simpa [beq_iff_eq] using hc
      · left
        cases hsp : p.sckRise <;> simp_all
    simp [hcs, hcond]

/-- A completed data byte of a write transaction issues the host write. -/
theorem wP_complete_data (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 3) :
    (Machine.hostNext m cv p served).1.wPend = (m.host.cmd.toNat == 1) := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

/-- A completed data byte of a read transaction issues the read request. -/
theorem rP_complete_data (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 3) :
    (Machine.hostNext m cv p served).1.rPend = (m.host.cmd.toNat == 2) := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

/-- A completed address-low byte of a read transaction issues the read request. -/
theorem rP_complete_low (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 2) :
    (Machine.hostNext m cv p served).1.rPend = (m.host.cmd.toNat == 2) := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

theorem wP_complete_low (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 2) :
    (Machine.hostNext m cv p served).1.wPend = false := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

theorem wP_complete_high (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 1) :
    (Machine.hostNext m cv p served).1.wPend = false := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

theorem rP_complete_high (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 1) :
    (Machine.hostNext m cv p served).1.rPend = false := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

theorem wP_complete_zero (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 0) :
    (Machine.hostNext m cv p served).1.wPend = false := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

theorem rP_complete_zero (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 0) :
    (Machine.hostNext m cv p served).1.rPend = false := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb]

/-- The machine latches the shifting byte into `wData` every cycle. -/
theorem wData_eq (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView) (served : Bool) :
    (Machine.hostNext m cv p served).1.wData =
      Machine.Util.bv 8 ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi) := by
  simp [Machine.hostNext]

/-- The machine's test for a register (not data-RAM) read value. -/
def regRead (m : Machine.State) (cv : Machine.CfgView) : Bool :=
  match Machine.hostRead m cv m.host.addr.toNat with
  | .inl _ => true
  | .inr _ => false

/-- The machine's register-read load strobe: a read request to a register
address (not a data-RAM read) loads `TX`.  `Machine.hostRead` answers with a
register value (`.inl`) exactly outside the data RAM; the cut's `rdData` input is
the same test, named by `LinkRel`'s caller. -/
theorem ldV_eq (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView) (served : Bool) :
    (Machine.hostNext m cv p served).1.ldV = (m.host.rPend && regRead m cv) := by
  simp only [Machine.hostNext, regRead]
  by_cases hr : m.host.rPend
  · cases h : Machine.hostRead m cv m.host.addr.toNat <;> simp [hr, h]
  · simp [hr]

/-- Byte-append arithmetic: `hi ++ lo` as a 16-bit word. -/
theorem append_toNat (hi lo : BitVec 8) :
    (hi ++ lo).toNat = hi.toNat * 256 + lo.toNat := by
  have h2 : lo.toNat < 2 ^ 8 := by have := lo.isLt; simpa using this
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 8) h2 hi.toNat
  rw [BitVec.toNat_append]
  rw [show hi.toNat <<< 8 = 2 ^ 8 * hi.toNat by rw [Nat.shiftLeft_eq, Nat.mul_comm]]
  rw [← hor]
  rw [show (2 : Nat) ^ 8 = 256 by decide]
  omega

theorem append_byte (hi lo : BitVec 8) :
    hi ++ lo = Machine.Util.bv 16 (hi.toNat * 256 + lo.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat, Machine.Util.bv, BitVec.toNat_ofNat]
  have h1 : hi.toNat < 256 := by have := hi.isLt; omega
  have h2 : lo.toNat < 256 := by have := lo.isLt; omega
  rw [Nat.mod_eq_of_lt (by omega)]

theorem trunc_toNat (a : BitVec 16) : (BitVec.truncate 8 a).toNat = a.toNat % 256 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem shr8_toNat (a : BitVec 16) : (BitVec.truncate 8 (a >>> 8)).toNat = a.toNat / 256 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 8 = 256 by decide]
  have h := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

theorem bv16_add_one (a : BitVec 16) :
    BitVec.ofNat 16 ((a.toNat + 1) % 65536) = a + 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add]
  simp

/-- `bv 16` of the machine's increment path. -/
@[simp] theorem addr_if_bv (c : Prop) [Decidable c] (a : BitVec 16) :
    BitVec.ofNat 16 (if c then (a.toNat + 1) % 65536 else a.toNat) =
      (if c then a + 1 else a) := by
  by_cases h : c
  · simp [h, Machine.Util.bv, bv16_add_one]
  · simp [h, Machine.Util.bv, bv_toNat]

/-- The address register's increment path: no address byte completes. -/
theorem addr_incr (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hinc : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false) :
    (Machine.hostNext m cv p served).1.addr =
      if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr := by
  simp only [Machine.hostNext]
  rw [hinc]
  simp [Machine.Util.bv, addr_if_bv]

/-- The machine's address register after a completed command byte. -/
theorem addr_data (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 3) :
    (Machine.hostNext m cv p served).1.addr =
      if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb, Machine.Util.bv, addr_if_bv]

theorem addr_zero (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 0) :
    (Machine.hostNext m cv p served).1.addr =
      if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr := by
  simp [Machine.hostNext, hcs, hsr, hbit, hnb, Machine.Util.bv, addr_if_bv]

/-- The machine's address register after a completed address-high byte of a
transaction. -/
theorem addr_high (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 1) :
    (Machine.hostNext m cv p served).1.addr =
      (if m.host.cmd.toNat = 0 then
        (if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr)
       else Machine.Util.bv 16 (((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi) * 256 +
         m.host.addr.toNat % 256)) := by
  simp only [Machine.hostNext, hcs, hsr, hbit, hnb, ite_true, Bool.true_and]
  by_cases h0 : m.host.cmd.toNat = 0
  · simp [h0, Machine.Util.bv, addr_if_bv]
  · simp [h0, Machine.Util.bv]

/-- The machine's address register after a completed address-low byte of a
transaction. -/
theorem addr_low (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 2) :
    (Machine.hostNext m cv p served).1.addr =
      (if m.host.cmd.toNat = 0 then
        (if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr)
       else Machine.Util.bv 16 (m.host.addr.toNat / 256 * 256 +
         ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi))) := by
  simp only [Machine.hostNext, hcs, hsr, hbit, hnb, ite_true, Bool.true_and]
  by_cases h0 : m.host.cmd.toNat = 0
  · simp [h0, Machine.Util.bv, addr_if_bv]
  · simp [h0, Machine.Util.bv]

/-! ## Cut-side helpers -/

theorem sr_facts (i : HostCmd.Input) (h : HostCmd.sr i = true) :
    i.csN = false ∧ i.sck = true ∧ i.sckPrev = false := by
  rcases i with ⟨r, sc, sp, cs, mo, rd, hl⟩
  cases cs <;> cases sc <;> cases sp <;> simp_all [HostCmd.sr]

/-- With no completed byte the cut's command byte holds. -/
theorem cmdNext_hold (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (h : ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_CMD)) :
    (HostCmd.step s i).cmd = s.cmd := by
  rcases i with ⟨r, sc, sp, cs, mo, rd, hl⟩
  simp only [HostCmd.step, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr] at h ⊢
  simp_all

/-- At a completed command byte the cut latches the completed byte. -/
theorem cmdNext_complete (s : HostCmd.State) (i : HostCmd.Input) (hph : s.phase = HostCmd.ST_CMD)
    (hbitc : s.bitc = 7) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsck : i.sck = true) (hsp : i.sckPrev = false) :
    (HostCmd.step s i).cmd = HostCmd.byteIn s i :=
  (HostCmd.cmd_completion s i hph hbitc hreset hcs hsck hsp).2.2.1

theorem pin_csn (i : HostCmd.Input) (h : i.csN = false) : (pinOf i).csn = false := by
  simp [pinOf, h]

theorem pin_sckRise (i : HostCmd.Input) (hsck : i.sck = true) (hsp : i.sckPrev = false) :
    (pinOf i).sckRise = true := by
  simp [pinOf, hsck, hsp]

theorem phase_ne_cmd (h : Machine.HostSt) (hnb : h.nbyte ≠ 0) : phaseOf h ≠ HostCmd.ST_CMD := by
  rcases bv2_cases h.nbyte with h' | h' | h' | h'
  · exact absurd h' hnb
  · by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, h', h0]
  · by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, h', h0]
  · by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, h', h0]

theorem not_completing_cmd (s : HostCmd.State) (i : HostCmd.Input)
    (hph : s.phase ≠ HostCmd.ST_CMD) :
    ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_CMD) := by
  rintro ⟨-, hp⟩; exact hph hp

theorem not_completing_of_nbit (s : HostCmd.State) (i : HostCmd.Input)
    (hsr : HostCmd.sr i = true) (h7 : s.bitc ≠ 7) :
    ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_CMD) := by
  rintro ⟨hc, -⟩
  simp only [HostCmd.completing, hsr, Bool.true_and, beq_iff_eq] at hc
  exact h7 hc

theorem bv2_eq_three {x : BitVec 2} (h : Machine.Util.bv 2 x.toNat = 3) : x = 3 := by
  rw [bv_toNat] at h; exact h

theorem cmd_one_iff (x : BitVec 2) (h0 : x ≠ 0) (h3 : x ≠ 3) :
    (x.toNat == 1) = true ↔ ¬(x = 2) := by
  rcases bv2_cases x with h | h | h | h
  · exact absurd h h0
  · subst h; decide
  · subst h; decide
  · exact absurd h h3

theorem cmd_two_iff (x : BitVec 2) : (x.toNat == 2) = true ↔ x = 2 := by
  rcases bv2_cases x with h | h | h | h <;> subst h <;> decide

theorem bv2_ne_three (x : BitVec 2) : Machine.Util.bv 2 x.toNat ≠ 3 ↔ x ≠ 3 := by
  rw [bv_toNat]


/-- With `CS_N` high the machine returns to the command byte. -/
theorem phaseOf_csHigh (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = true) :
    phaseOf (Machine.hostNext m cv p served).1 = HostCmd.ST_CMD := by
  simp [Machine.hostNext, phaseOf, hcs]

/-- With no completed byte the machine's byte state and command code hold. -/
theorem phaseOf_hold (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcomp : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false) :
    phaseOf (Machine.hostNext m cv p served).1 =
      if p.csn then HostCmd.ST_CMD else phaseOf m.host := by
  simp only [Machine.hostNext, phaseOf]
  by_cases hcs : p.csn
  · simp [hcs]
  · have hcond : p.sckRise = false ∨ ¬(m.host.nbit.toNat = 7) := by
      by_cases hs : p.sckRise = true
      · right
        have h1 : (p.sckRise && !p.csn && (m.host.nbit.toNat == 7)) = false := hcomp
        rw [hs] at h1
        have hc : (m.host.nbit.toNat == 7) = false := by simpa [hcs] using h1
        simpa [beq_iff_eq] using hc
      · left
        cases hsp : p.sckRise <;> simp_all
    simp [hcs, hcond]

/-- The completed command byte. -/
theorem phaseOf_complete_0 (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 0) :
    phaseOf (Machine.hostNext m cv p served).1 =
      (if ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi ≠ 2 ∧
            (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n p.mosi ≠ 3)
        then HostCmd.ST_IGN else HostCmd.ST_AH) := by
  simp [Machine.hostNext, phaseOf, hcs, hsr, hbit, hnb]

/-- A completed address-high byte enters the address-low byte. -/
theorem phaseOf_complete_1 (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 1) :
    phaseOf (Machine.hostNext m cv p served).1 =
      (if m.host.cmd.toNat = 0 then HostCmd.ST_IGN else HostCmd.ST_AL) := by
  simp [Machine.hostNext, phaseOf, hcs, hsr, hbit, hnb]

/-- A completed address-low byte enters the data bytes. -/
theorem phaseOf_complete_2 (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 2) :
    phaseOf (Machine.hostNext m cv p served).1 =
      (if m.host.cmd.toNat = 0 then HostCmd.ST_IGN else HostCmd.ST_DATA) := by
  simp [Machine.hostNext, phaseOf, hcs, hsr, hbit, hnb]

/-- A completed data byte stays in the data bytes. -/
theorem phaseOf_complete_3 (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hsr : p.sckRise = true)
    (hbit : m.host.nbit.toNat = 7) (hnb : m.host.nbyte = 3) :
    phaseOf (Machine.hostNext m cv p served).1 =
      (if m.host.cmd.toNat = 0 then HostCmd.ST_IGN else HostCmd.ST_DATA) := by
  simp [Machine.hostNext, phaseOf, hcs, hsr, hbit, hnb]

/-- At a completed command byte of a write or read transaction the cut's next
byte state is the address high byte. -/
theorem phaseNext_cmd_ah (s : HostCmd.State) (i : HostCmd.Input)
    (hph : s.phase = HostCmd.ST_CMD) (hbitc : s.bitc = 7) (hreset : i.resetN = true)
    (hcs : i.csN = false) (hsck : i.sck = true) (hsp : i.sckPrev = false)
    (hd : HostCmd.byteIn s i = HostCmd.CMD_WRITE ∨ HostCmd.byteIn s i = HostCmd.CMD_READ) :
    HostCmd.phaseNext s i = HostCmd.ST_AH := by
  have h := (HostCmd.cmd_completion s i hph hbitc hreset hcs hsck hsp).1
  have hb : (HostCmd.byteIn s i == HostCmd.CMD_WRITE ||
      HostCmd.byteIn s i == HostCmd.CMD_READ) = true := by
    simpa [Bool.or_eq_true, beq_iff_eq] using hd
  have h' : HostCmd.phaseNext s i = (if (HostCmd.byteIn s i == HostCmd.CMD_WRITE ||
      HostCmd.byteIn s i == HostCmd.CMD_READ) then HostCmd.ST_AH else HostCmd.ST_IGN) := h
  rw [h', ite_eq_left hb]

/-- At a completed command byte that is neither `0x02` nor `0x03` the cut ignores
the rest of the transaction. -/
theorem phaseNext_cmd_ign (s : HostCmd.State) (i : HostCmd.Input)
    (hph : s.phase = HostCmd.ST_CMD) (hbitc : s.bitc = 7) (hreset : i.resetN = true)
    (hcs : i.csN = false) (hsck : i.sck = true) (hsp : i.sckPrev = false)
    (hd : ¬ (HostCmd.byteIn s i = HostCmd.CMD_WRITE ∨ HostCmd.byteIn s i = HostCmd.CMD_READ)) :
    HostCmd.phaseNext s i = HostCmd.ST_IGN := by
  have h := (HostCmd.cmd_completion s i hph hbitc hreset hcs hsck hsp).1
  have hb : (HostCmd.byteIn s i == HostCmd.CMD_WRITE ||
      HostCmd.byteIn s i == HostCmd.CMD_READ) = false := by
    rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
    exact ⟨fun hW => hd (Or.inl hW), fun hR => hd (Or.inr hR)⟩
  have h' : HostCmd.phaseNext s i = (if (HostCmd.byteIn s i == HostCmd.CMD_WRITE ||
      HostCmd.byteIn s i == HostCmd.CMD_READ) then HostCmd.ST_AH else HostCmd.ST_IGN) := h
  rw [h', ite_eq_right (by rw [hb]; decide)]

/-- With no completed byte the cut's byte state holds. -/
theorem phaseNext_hold (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (hcs : i.csN = false) (hnot : HostCmd.completing s i = false) :
    HostCmd.phaseNext s i = s.phase := by
  simp [HostCmd.phaseNext, hreset, hcs, hnot]

/-- **The byte state.**  Under `LinkRel` one step preserves the cut's `phase` as
the machine's `(nbyte, cmd)`: the machine's `IGN` is `1 ≤ nbyte` with `cmd = 0`. -/
theorem phase_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    HostCmd.phaseNext s i = phaseOf (Machine.hostNext m cv (pinOf i) served).1 := by
  cases hcsn : i.csN with
  | true =>
    rw [phaseOf_csHigh m cv (pinOf i) served (by simp [pinOf, hcsn])]
    simp [HostCmd.phaseNext, hreset, hcsn]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [phaseOf_hold m cv (pinOf i) served hcomp]
      simp [pinOf, hcsn]
      have hnot : HostCmd.completing s i = false := by simp [HostCmd.completing, hsr]
      rw [phaseNext_hold s i hreset hcsn hnot]
      rw [hrel.phase]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [phaseOf_complete_0 m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          have hpm : (pinOf i).mosi = i.mosi := by simp [pinOf]
          rw [hpm]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          by_cases hb : ((HostCmd.byteIn s i == HostCmd.CMD_WRITE) ||
              (HostCmd.byteIn s i == HostCmd.CMD_READ)) = true
          · have hdisj : HostCmd.byteIn s i = HostCmd.CMD_WRITE ∨
                HostCmd.byteIn s i = HostCmd.CMD_READ := by
              simpa [Bool.or_eq_true, beq_iff_eq] using hb
            rw [phaseNext_cmd_ah s i hph h7 hreset hcsn hsck hsp hdisj]
            have hconj : ¬ ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 2 ∧
                (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 3) :=
              fun h => (ign_iff s m i hrel).mp h hdisj
            simp [hconj]
          · have hnotdisj : ¬ (HostCmd.byteIn s i = HostCmd.CMD_WRITE ∨
                HostCmd.byteIn s i = HostCmd.CMD_READ) :=
              fun h => hb (by simpa [Bool.or_eq_true, beq_iff_eq] using h)
            rw [phaseNext_cmd_ign s i hph h7 hreset hcsn hsck hsp hnotdisj]
            have hconj : ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 2 ∧
                (m.host.rx.toNat % 128) * 2 + Machine.Util.b2n i.mosi ≠ 3) :=
              (ign_iff s m i hrel).mpr hnotdisj
            simp [hconj]
        · rw [phaseOf_complete_1 m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          by_cases h0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_left h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_IGN from by
              simpa [HostCmd.step] using ((HostCmd.ign_holds s i hph hcsn hreset).1)]
          · have hph : s.phase = HostCmd.ST_AH := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_right h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_AL from by
              simpa [HostCmd.step] using (HostCmd.ah_completion s i hph h7 hreset hcsn hsck hsp).1]
        · rw [phaseOf_complete_2 m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          by_cases h0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_left h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_IGN from by
              simpa [HostCmd.step] using ((HostCmd.ign_holds s i hph hcsn hreset).1)]
          · have hph : s.phase = HostCmd.ST_AL := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_right h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_DATA from by
              simpa [HostCmd.step] using (HostCmd.al_completion s i hph h7 hreset hcsn hsck hsp).1]
        · rw [phaseOf_complete_3 m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          by_cases h0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_left h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_IGN from by
              simpa [HostCmd.step] using ((HostCmd.ign_holds s i hph hcsn hreset).1)]
          · have hph : s.phase = HostCmd.ST_DATA := by
              rw [hrel.phase]; simp [phaseOf, hnb, h0]
            rw [ite_eq_right h0]
            rw [show HostCmd.phaseNext s i = HostCmd.ST_DATA from by
              simpa [HostCmd.step] using (HostCmd.data_completion s i hph h7 hreset hcsn hsck hsp).2.1]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [phaseOf_hold m cv (pinOf i) served hcomp]
        simp [pinOf, hcsn]
        have hnot : HostCmd.completing s i = false := by
          simp only [HostCmd.completing, hsr, Bool.true_and]
          exact beq_eq_false_iff_ne.mpr h7
        rw [phaseNext_hold s i hreset hcsn hnot]
        rw [hrel.phase]

theorem bitc_succ_iff (x : BitVec 3) :
    (if x = 7 then 0 else x + 1) = BitVec.ofNat 3 ((x.toNat + 1) % 8) := (bitc_succ x).symm

@[simp] theorem bv3_zero : Machine.Util.bv 3 0 = 0 := by decide

/-- **The bit counter.**  One step preserves `bitc = nbit`. -/
theorem nbit_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (HostCmd.step s i).bitc = (Machine.hostNext m cv (pinOf i) served).1.nbit := by
  have hb : m.host.nbit = s.bitc := hrel.bitc.symm
  have h1 : (Machine.hostNext m cv (pinOf i) served).1.nbit =
      (Machine.hostNext (absChip s) cv (pinOf i) served).1.nbit := by
    simp only [Machine.hostNext, hb, absChip, absHost]
  rw [h1, nbit_bridge s i cv served hreset]
  rfl

/-- **The receive register.**  One step preserves the low seven bits. -/
theorem rx_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (HostCmd.step s i).rx.toNat = (Machine.hostNext m cv (pinOf i) served).1.rx.toNat % 128 := by
  cases hcsn : i.csN with
  | true =>
    have hcut : (HostCmd.step s i).rx.toNat = s.rx.toNat := by
      simp [HostCmd.step, HostCmd.rxNext, HostCmd.sr, hreset, hcsn]
    rw [hcut]
    have hm : ((Machine.hostNext m cv (pinOf i) served).1.rx.toNat % 128) =
        m.host.rx.toNat % 128 := by
      simp only [Machine.hostNext]
      rw [ite_eq_right (by simp [pinOf, hcsn])]
    rw [hm]
    exact hrel.rx
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcut : (HostCmd.step s i).rx.toNat = s.rx.toNat := by
        simp [HostCmd.step, HostCmd.rxNext, hreset, hsr]
      rw [hcut]
      have hm : ((Machine.hostNext m cv (pinOf i) served).1.rx.toNat % 128) =
          m.host.rx.toNat % 128 := by
        simp only [Machine.hostNext]
        rw [ite_eq_right (by
          have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
          simp [hp])]
      rw [hm]
      exact hrel.rx
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      have hcut : (HostCmd.step s i).rx.toNat =
          (2 * s.rx.toNat + Machine.Util.b2n i.mosi) % 128 := by
        simp only [HostCmd.step, HostCmd.rxNext, hreset, hsr, hsck, hsp, Bool.not_false,
          Bool.not_true, ite_false, ite_true]
        exact rxOr_toNat s.rx i.mosi
      rw [hcut]
      have hm : ((Machine.hostNext m cv (pinOf i) served).1.rx.toNat % 128) =
          ((m.host.rx.toNat % 128) * 2 + Machine.Util.b2n (pinOf i).mosi) % 128 := by
        simp only [Machine.hostNext]
        rw [ite_eq_left (by simp [pinOf, hsck, hsp, hcsn])]
        simp [Machine.Util.bv, BitVec.toNat_ofNat]
      have hpm : (pinOf i).mosi = i.mosi := rfl
      rw [hm, ← hpm, hrel.rx, Nat.mul_comm (m.host.rx.toNat % 128) 2]
theorem cmdZero_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    ((Machine.hostNext m cv (pinOf i) served).1.cmd = 0) ↔
      ((HostCmd.step s i).cmd ≠ HostCmd.CMD_WRITE ∧ (HostCmd.step s i).cmd ≠ HostCmd.CMD_READ) := by
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    rw [cmd_hold m cv _ served hcomp, bv2_zero_iff, hrel.cmdZero]
    rw [cmdNext_hold s i hreset (by simp [HostCmd.completing, HostCmd.sr, hcsn])]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [cmd_hold m cv _ served hcomp, bv2_zero_iff, hrel.cmdZero]
      rw [cmdNext_hold s i hreset (by simp [HostCmd.completing, hsr])]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [cmd_complete_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          have hpm : (pinOf i).mosi = i.mosi := by simp [pinOf]
          rw [hpm, cmdStep_zero, v_bridge s m i hrel, byte_ne_two, byte_ne_three]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          rw [cmdNext_complete s i hph h7 hreset hcsn hsck hsp]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          rw [bv2_zero_iff, hrel.cmdZero]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          rw [cmdNext_hold s i hreset (not_completing_cmd s i hph)]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          rw [bv2_zero_iff, hrel.cmdZero]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          rw [cmdNext_hold s i hreset (not_completing_cmd s i hph)]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          rw [bv2_zero_iff, hrel.cmdZero]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          rw [cmdNext_hold s i hreset (not_completing_cmd s i hph)]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [cmd_hold m cv _ served hcomp, bv2_zero_iff, hrel.cmdZero]
        rw [cmdNext_hold s i hreset (not_completing_of_nbit s i hsr h7)]

/-- The machine only ever latches the command codes `0`, `1`, `2`. -/
theorem cmdNe_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (Machine.hostNext m cv (pinOf i) served).1.cmd ≠ 3 := by
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    rw [cmd_hold m cv _ served hcomp]
    exact fun h => hrel.cmdNe (bv2_eq_three h)
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [cmd_hold m cv _ served hcomp]
      intro h
      exact hrel.cmdNe (bv2_eq_three h)
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [cmd_complete_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          exact cmdStep_ne_three _
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          intro h
          exact hrel.cmdNe (bv2_eq_three h)
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          intro h
          exact hrel.cmdNe (bv2_eq_three h)
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit (by rw [hnb]; decide)]
          intro h
          exact hrel.cmdNe (bv2_eq_three h)
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [cmd_hold m cv _ served hcomp]
        intro h
        exact hrel.cmdNe (bv2_eq_three h)

/-- **The read-command latch.**  One step preserves `isRd ↔ cmd = 2`. -/
theorem isRdNext_hold (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (h : ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_CMD)) :
    (HostCmd.step s i).isRd = s.isRd := by
  rcases i with ⟨r, sc, sp, cs, mo, rd, hl⟩
  simp only [HostCmd.step, HostCmd.isRdNext, HostCmd.completing, HostCmd.sr] at h ⊢
  simp_all

theorem isRd_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    ((HostCmd.step s i).isRd = true) ↔ ((Machine.hostNext m cv (pinOf i) served).1.cmd = 2) := by
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    rw [cmd_hold m cv _ served hcomp, bv_toNat]
    have his : (HostCmd.step s i).isRd = s.isRd :=
      isRdNext_hold s i hreset (by simp [HostCmd.completing, HostCmd.sr, hcsn])
    rw [his, hrel.isRd]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [cmd_hold m cv _ served hcomp, bv_toNat]
      have his : (HostCmd.step s i).isRd = s.isRd :=
        isRdNext_hold s i hreset (by simp [HostCmd.completing, hsr])
      rw [his, hrel.isRd]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [cmd_complete_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          have hpm : (pinOf i).mosi = i.mosi := by simp [pinOf]
          rw [hpm, cmdStep_two, v_bridge s m i hrel, toNat_eq_three]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          rw [(HostCmd.cmd_completion s i hph h7 hreset hcsn hsck hsp).2.1]
          simp [beq_iff_eq]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit
            (by rw [hnb]; decide), bv_toNat]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          have his : (HostCmd.step s i).isRd = s.isRd :=
            isRdNext_hold s i hreset (not_completing_cmd s i hph)
          rw [his, hrel.isRd]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit
            (by rw [hnb]; decide), bv_toNat]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          have his : (HostCmd.step s i).isRd = s.isRd :=
            isRdNext_hold s i hreset (not_completing_cmd s i hph)
          rw [his, hrel.isRd]
        · rw [cmd_complete_keep m cv _ served hcsn (pin_sckRise i hsck hsp) hbit
            (by rw [hnb]; decide), bv_toNat]
          have hph : s.phase ≠ HostCmd.ST_CMD := by
            rw [hrel.phase]; exact phase_ne_cmd m.host (by rw [hnb]; decide)
          have his : (HostCmd.step s i).isRd = s.isRd :=
            isRdNext_hold s i hreset (not_completing_cmd s i hph)
          rw [his, hrel.isRd]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [cmd_hold m cv _ served hcomp, bv_toNat]
        have his : (HostCmd.step s i).isRd = s.isRd :=
          isRdNext_hold s i hreset (not_completing_of_nbit s i hsr h7)
        rw [his, hrel.isRd]

theorem phase_high_ne (h : Machine.HostSt) (hnb : h.nbyte = 1) : phaseOf h ≠ HostCmd.ST_DATA := by
  by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, hnb, h0]

theorem phase_high_ne_al (h : Machine.HostSt) (hnb : h.nbyte = 1) : phaseOf h ≠ HostCmd.ST_AL := by
  by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, hnb, h0]

theorem phase_low_ne (h : Machine.HostSt) (hnb : h.nbyte = 2) : phaseOf h ≠ HostCmd.ST_DATA := by
  by_cases h0 : h.cmd.toNat = 0 <;> simp [phaseOf, hnb, h0]

theorem wr_machine_eq (m : Machine.State) (s : HostCmd.State) (hrel : LinkRel s m)
    (hz : m.host.cmd ≠ 0) : (m.host.cmd.toNat == 1) = !s.isRd := by
  by_cases his : s.isRd = true
  · have h2 : m.host.cmd = 2 := hrel.isRd.mp his
    rw [h2, his]
    decide
  · have his' : s.isRd = false := by
      cases h : s.isRd with
      | false => rfl
      | true => exact absurd h his
    have h2 : m.host.cmd ≠ 2 := fun h => his (hrel.isRd.mpr h)
    rcases bv2_cases_ne m.host.cmd hrel.cmdNe with h | h | h
    · exact absurd h hz
    · rw [h, his']
      decide
    · exact absurd h h2

theorem rd_machine_eq (m : Machine.State) (s : HostCmd.State) (hrel : LinkRel s m) :
    (m.host.cmd.toNat == 2) = s.isRd := by
  by_cases his : s.isRd = true
  · have h2 : m.host.cmd = 2 := hrel.isRd.mp his
    rw [h2, his]
    decide
  · have his' : s.isRd = false := by
      cases h : s.isRd with
      | false => rfl
      | true => exact absurd h his
    have h2 : m.host.cmd ≠ 2 := fun h => his (hrel.isRd.mpr h)
    rcases bv2_cases_ne m.host.cmd hrel.cmdNe with h | h | h
    · rw [h, his']
      decide
    · rw [h, his']
      decide
    · exact absurd h h2

theorem bool_eq_iff (a b : Bool) : (a = b) ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp

/-- The cut's write strobe in terms of the byte state. -/
theorem wrNext_eq (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true) :
    (HostCmd.step s i).wr =
      (!i.csN && HostCmd.completing s i && (s.phase == HostCmd.ST_DATA) && !s.isRd) := by
  simp [HostCmd.step, HostCmd.wrNext, hreset]

/-- The cut's read request in terms of the byte state. -/
theorem rdNext_eq (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true) :
    (HostCmd.step s i).rd =
      (!i.csN && HostCmd.completing s i && (s.phase == HostCmd.ST_AL || s.phase == HostCmd.ST_DATA) &&
        s.isRd) := by
  simp [HostCmd.step, HostCmd.rdNext, hreset, Bool.and_assoc]

/-- **The write strobe.**  One step preserves `wr = wPend`. -/
theorem wr_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (HostCmd.step s i).wr = (Machine.hostNext m cv (pinOf i) served).1.wPend := by
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    rw [wP_hold m cv _ served hcomp, wrNext_eq s i hreset]
    simp [hcsn]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [wP_hold m cv _ served hcomp, wrNext_eq s i hreset]
      simp [HostCmd.completing, hsr, hcsn]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [wP_complete_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            wrNext_eq s i hreset]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          simp [HostCmd.completing, hsr, h7, hcsn, hph]
        · rw [wP_complete_high m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            wrNext_eq s i hreset]
          have hph : s.phase ≠ HostCmd.ST_DATA := by
            rw [hrel.phase]; exact phase_high_ne m.host hnb
          simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and, Bool.not_false]
          have hb : (s.phase == HostCmd.ST_DATA) = false := beq_eq_false_iff_ne.mpr hph
          rw [hb]
          simp
        · rw [wP_complete_low m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            wrNext_eq s i hreset]
          have hph : s.phase ≠ HostCmd.ST_DATA := by
            rw [hrel.phase]; exact phase_low_ne m.host hnb
          simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and, Bool.not_false]
          have hb : (s.phase == HostCmd.ST_DATA) = false := beq_eq_false_iff_ne.mpr hph
          rw [hb]
          simp
        · rw [wP_complete_data m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            wrNext_eq s i hreset]
          by_cases hc0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            simp [HostCmd.completing, hsr, h7, hcsn, hph, hc0]
          · have hph : s.phase = HostCmd.ST_DATA := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            have hz : m.host.cmd ≠ 0 := by
              intro h; exact hc0 (by rw [h]; rfl)
            have hlhs : (!i.csN && HostCmd.completing s i && (s.phase == HostCmd.ST_DATA) &&
                !s.isRd) = !s.isRd := by
              simp [hcsn, HostCmd.completing, hsr, h7, hph]
            rw [hlhs, wr_machine_eq m s hrel hz]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [wP_hold m cv _ served hcomp, wrNext_eq s i hreset]
        simp only [HostCmd.completing, hsr, Bool.true_and, hcsn, Bool.not_false]
        have hb : (s.bitc == 7) = false := beq_eq_false_iff_ne.mpr h7
        rw [hb]
        simp

/-- **The read request.**  One step preserves `rd = rPend`. -/
theorem rd_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (HostCmd.step s i).rd = (Machine.hostNext m cv (pinOf i) served).1.rPend := by
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    rw [rP_hold m cv _ served hcomp, rdNext_eq s i hreset]
    simp [hcsn]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      rw [rP_hold m cv _ served hcomp, rdNext_eq s i hreset]
      simp [HostCmd.completing, hsr, hcsn]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [rP_complete_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            rdNext_eq s i hreset]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and]
          have h1 : (s.phase == HostCmd.ST_AL) = false :=
            beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
          have h2 : (s.phase == HostCmd.ST_DATA) = false :=
            beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
          rw [h1, h2]
          simp
        · rw [rP_complete_high m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            rdNext_eq s i hreset]
          have hph : s.phase ≠ HostCmd.ST_AL := by
            rw [hrel.phase]; exact phase_high_ne_al m.host hnb
          have hph' : s.phase ≠ HostCmd.ST_DATA := by
            rw [hrel.phase]; exact phase_high_ne m.host hnb
          simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and]
          have h1 : (s.phase == HostCmd.ST_AL) = false := beq_eq_false_iff_ne.mpr hph
          have h2 : (s.phase == HostCmd.ST_DATA) = false := beq_eq_false_iff_ne.mpr hph'
          rw [h1, h2]
          simp
        · rw [rP_complete_low m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            rdNext_eq s i hreset]
          by_cases hc0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and]
            have h1 : (s.phase == HostCmd.ST_AL) = false :=
              beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
            have h2 : (s.phase == HostCmd.ST_DATA) = false :=
              beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
            rw [h1, h2]
            simp [hc0]
          · have hph : s.phase = HostCmd.ST_AL := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [rd_machine_eq m s hrel]
            cases his : s.isRd
            · simp [his]
            · simp [hph, hcsn, HostCmd.completing, hsr, h7]
        · rw [rP_complete_data m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb,
            rdNext_eq s i hreset]
          by_cases hc0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            simp only [HostCmd.completing, hsr, h7, hcsn, Bool.true_and]
            have h1 : (s.phase == HostCmd.ST_AL) = false :=
              beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
            have h2 : (s.phase == HostCmd.ST_DATA) = false :=
              beq_eq_false_iff_ne.mpr (by rw [hph]; decide)
            rw [h1, h2]
            simp [hc0]
          · have hph : s.phase = HostCmd.ST_DATA := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [rd_machine_eq m s hrel]
            cases his : s.isRd
            · simp [his]
            · simp [hph, hcsn, HostCmd.completing, hsr, h7]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        rw [rP_hold m cv _ served hcomp, rdNext_eq s i hreset]
        simp only [HostCmd.completing, hsr, Bool.true_and, hcsn, Bool.not_false]
        have hb : (s.bitc == 7) = false := beq_eq_false_iff_ne.mpr h7
        rw [hb]
        simp

/-- **The register-read acknowledgement.**  With `rdData` naming the machine's
data-RAM test, `rack = ldV`. -/
theorem rack_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m)
    (hreg : i.rdData = !regRead m cv) :
    (HostCmd.step s i).rack = (Machine.hostNext m cv (pinOf i) served).1.ldV := by
  have hcut : (HostCmd.step s i).rack = (s.rd && !i.rdData) := by
    simp [HostCmd.step, HostCmd.rackNext, hreset]
  rw [hcut, ldV_eq, hrel.rd, hreg]
  simp

/-- **The write byte.**  While the strobe is up, the byte the machine presents in
`wData` is the cut's `wdata`. -/
theorem wdata_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m) :
    (HostCmd.step s i).wr = true →
      (HostCmd.step s i).wdata = (Machine.hostNext m cv (pinOf i) served).1.wData := by
  intro hwr
  obtain ⟨hph, hbitc, hird, hres, hcs, hsck, hsp⟩ := HostCmd.wr_only_in_data s i hwr
  have hw : (HostCmd.step s i).wdata = HostCmd.byteIn s i := by
    have h := (HostCmd.data_completion s i hph hbitc hres hcs hsck hsp).2.2.1.2
    rw [h]
    simp [hird]
  rw [hw, wData_eq]
  exact (byteIn_eq s m.host hrel.rx.symm i.mosi).symm

/-- The address-set test of the cut at phase `ph` is false unless the byte
completes in that phase. -/
theorem addrSet_false (s : HostCmd.State) (i : HostCmd.Input) (ph : BitVec 3)
    (h : ¬ (HostCmd.completing s i = true ∧ s.phase = ph)) :
    (HostCmd.completing s i && (s.phase == ph)) = false := by
  rcases hb : HostCmd.completing s i with _ | _
  · show (false && (s.phase == ph)) = false
    rfl
  · have hp : ¬(s.phase = ph) := fun hp => h ⟨hb, hp⟩
    show (true && (s.phase == ph)) = false
    rw [Bool.true_and]
    exact beq_eq_false_iff_ne.mpr hp

/-- At a completed address byte the address-set test is true. -/
theorem addrSet_true (s : HostCmd.State) (i : HostCmd.Input) (ph : BitVec 3)
    (h : HostCmd.completing s i = true ∧ s.phase = ph) :
    (HostCmd.completing s i && (s.phase == ph)) = true := by
  rw [h.1]
  show (true && (s.phase == ph)) = true
  rw [Bool.true_and, h.2]
  simp

/-- The cut's address update with no address byte completing. -/
theorem addrNext_incr (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (hah : ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_AH))
    (hal : ¬ (HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_AL)) :
    (HostCmd.step s i).addr = HostCmd.addrInc s i := by
  simp only [HostCmd.step, HostCmd.addrNext, hreset]
  rw [ite_eq_right (by simp),
    ite_eq_right (by rw [addrSet_false s i HostCmd.ST_AH hah]; decide),
    ite_eq_right (by rw [addrSet_false s i HostCmd.ST_AL hal]; decide)]

/-- The cut's address update at a completed address-high byte. -/
theorem addrNext_ah (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (hah : HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_AH) :
    (HostCmd.step s i).addr = HostCmd.byteIn s i ++ (HostCmd.addrInc s i).truncate 8 := by
  simp only [HostCmd.step, HostCmd.addrNext, hreset]
  rw [ite_eq_right (by simp), ite_eq_left (by rw [addrSet_true s i HostCmd.ST_AH hah])]

/-- The cut's address update at a completed address-low byte. -/
theorem addrNext_al (s : HostCmd.State) (i : HostCmd.Input) (hreset : i.resetN = true)
    (hal : HostCmd.completing s i = true ∧ s.phase = HostCmd.ST_AL) :
    (HostCmd.step s i).addr = (HostCmd.addrInc s i >>> 8).truncate 8 ++ HostCmd.byteIn s i := by
  simp only [HostCmd.step, HostCmd.addrNext, hreset]
  rw [ite_eq_right (by simp),
    ite_eq_right (by rw [addrSet_false s i HostCmd.ST_AH (fun h => by
      rw [hal.2] at h
      exact absurd h.2 (by decide))]; decide),
    ite_eq_left (by rw [addrSet_true s i HostCmd.ST_AL hal])]

/-- **The address register.**  On a cycle with no exception (`hquiet`: no strobe
and no acknowledgement while a byte completes) the cut's address register steps
exactly as the machine's. -/
theorem addr_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m)
    (hland : (m.ramOwner == 4) = i.hland)
    (hquiet : HostCmd.completing s i = true →
      s.wr = false ∧ HostCmd.ackBit s i = false) :
    (HostCmd.step s i).addr = (Machine.hostNext m cv (pinOf i) served).1.addr := by
  have hinc : HostCmd.addrInc s i =
      if (m.host.wPend || (m.host.ldV || m.ramOwner == 4)) then m.host.addr + 1 else m.host.addr := by
    have hl : HostCmd.ackBit s i = (m.host.ldV || (m.ramOwner == 4)) := by
      simp [HostCmd.ackBit, hrel.rack, hland]
    simp only [HostCmd.addrInc, hrel.wr, hl, hrel.addr]
  have hincAddr : HostCmd.completing s i = true → HostCmd.addrInc s i = s.addr := by
    intro hc
    rw [hinc, hrel.addr]
    rw [show m.host.wPend = false from by rw [← hrel.wr]; exact (hquiet hc).1]
    rw [show (m.host.ldV || (m.ramOwner == 4)) = false from by
      rw [← hrel.rack, hland]
      exact (hquiet hc).2]
    simp
  cases hcsn : i.csN with
  | true =>
    have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
      simp [pinOf, hcsn]
    have hnc : HostCmd.completing s i = false := by simp [HostCmd.completing, HostCmd.sr, hcsn]
    rw [addrNext_incr s i hreset (by simp [hnc]) (by simp [hnc]),
      addr_incr m cv _ served hcomp, hinc]
  | false =>
    cases hsr : HostCmd.sr i with
    | false =>
      have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
        have hp : ((pinOf i).sckRise && !(pinOf i).csn) = false := by rw [pin_bridge i, hsr]
        simp [hp]
      have hnc : HostCmd.completing s i = false := by simp [HostCmd.completing, hsr]
      rw [addrNext_incr s i hreset (by simp [hnc]) (by simp [hnc]),
        addr_incr m cv _ served hcomp, hinc]
    | true =>
      have hsck : i.sck = true := (sr_facts i hsr).2.1
      have hsp : i.sckPrev = false := (sr_facts i hsr).2.2
      by_cases h7 : s.bitc = 7
      · have hbit : m.host.nbit.toNat = 7 := by
          rw [← hrel.bitc]; rw [h7]; rfl
        have hc : HostCmd.completing s i = true := by simp [HostCmd.completing, hsr, h7]
        have hinc' : HostCmd.addrInc s i = s.addr := hincAddr hc
        rcases bv2_cases m.host.nbyte with hnb | hnb | hnb | hnb
        · rw [addr_zero m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          have hph : s.phase = HostCmd.ST_CMD := by
            rw [hrel.phase]; simp [phaseOf, hnb]
          rw [addrNext_incr s i hreset
              (fun h => by rw [hph] at h; exact absurd h.2 (by decide))
              (fun h => by rw [hph] at h; exact absurd h.2 (by decide)),
            hinc]
        · rw [addr_high m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          by_cases hc0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [ite_eq_left hc0]
            rw [addrNext_incr s i hreset
                (fun h => by rw [hph] at h; exact absurd h.2 (by decide))
                (fun h => by rw [hph] at h; exact absurd h.2 (by decide)),
              hinc]
          · have hph : s.phase = HostCmd.ST_AH := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [ite_eq_right hc0]
            rw [addrNext_ah s i hreset ⟨hc, hph⟩, hinc', hrel.addr]
            simp only [pinOf]
            rw [append_byte, trunc_toNat, v_bridge s m i hrel]
        · rw [addr_low m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          by_cases hc0 : m.host.cmd.toNat = 0
          · have hph : s.phase = HostCmd.ST_IGN := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [ite_eq_left hc0]
            rw [addrNext_incr s i hreset
                (fun h => by rw [hph] at h; exact absurd h.2 (by decide))
                (fun h => by rw [hph] at h; exact absurd h.2 (by decide)),
              hinc]
          · have hph : s.phase = HostCmd.ST_AL := by
              rw [hrel.phase]; simp [phaseOf, hnb, hc0]
            rw [ite_eq_right hc0]
            rw [addrNext_al s i hreset ⟨hc, hph⟩, hinc', hrel.addr]
            simp only [pinOf]
            rw [append_byte, shr8_toNat, v_bridge s m i hrel]
        · rw [addr_data m cv _ served hcsn (pin_sckRise i hsck hsp) hbit hnb]
          have hne1 : s.phase ≠ HostCmd.ST_AH := by
            rw [hrel.phase]; by_cases h0 : m.host.cmd.toNat = 0 <;> simp [phaseOf, hnb, h0]
          have hne2 : s.phase ≠ HostCmd.ST_AL := by
            rw [hrel.phase]; by_cases h0 : m.host.cmd.toNat = 0 <;> simp [phaseOf, hnb, h0]
          rw [addrNext_incr s i hreset (fun h => hne1 h.2) (fun h => hne2 h.2), hinc]
      · have hbit : m.host.nbit.toNat ≠ 7 := by
          intro h
          exact h7 (by rw [hrel.bitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have hcomp : ((pinOf i).sckRise && !(pinOf i).csn && (m.host.nbit.toNat == 7)) = false := by
          simp [beq_iff_eq, hbit]
        have hnc : HostCmd.completing s i = false := by
          simp only [HostCmd.completing, hsr, Bool.true_and]
          exact beq_eq_false_iff_ne.mpr h7
        rw [addrNext_incr s i hreset (by simp [hnc]) (by simp [hnc]),
          addr_incr m cv _ served hcomp, hinc]

/-- **One step.**  `LinkRel` is preserved by one link step under the interface
hypotheses: `hland` (the cut's `hland` input is the machine's host RAM landing),
`hreg` (the cut's `rdData` input is the machine's register-read test) and
`hquiet` (no strobe/acknowledgement in a completing cycle). -/
theorem linkRel_step (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hreset : i.resetN = true) (hrel : LinkRel s m)
    (hland : (m.ramOwner == 4) = i.hland) (hreg : i.rdData = !regRead m cv)
    (hquiet : HostCmd.completing s i = true →
      s.wr = false ∧ HostCmd.ackBit s i = false) :
    LinkRel (HostCmd.step s i) { m with host := (Machine.hostNext m cv (pinOf i) served).1 } :=
  { phase := phase_step s m i cv served hreset hrel
    bitc := nbit_step s m i cv served hreset hrel
    rx := rx_step s m i cv served hreset hrel
    cmdZero := cmdZero_step s m i cv served hreset hrel
    cmdNe := cmdNe_step s m i cv served hreset hrel
    isRd := isRd_step s m i cv served hreset hrel
    addr := addr_step s m i cv served hreset hrel hland hquiet
    wr := wr_step s m i cv served hreset hrel
    wdata := wdata_step s m i cv served hreset hrel
    rd := rd_step s m i cv served hreset hrel
    rack := rack_step s m i cv served hreset hrel hreg }

/-! ## The observable outputs -/

/-- **The host write.**  The write the machine issues in a cycle is the cut's
`wr`/`addr`/`wdata` (§9: a completed data byte of a write transaction). -/
theorem hw_bridge (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hrel : LinkRel s m) :
    (Machine.hostNext m cv (pinOf i) served).2 =
      (if s.wr then
        some ⟨s.addr.toNat, s.wdata.toNat, Machine.hostLocate s.addr.toNat⟩
       else none) := by
  simp only [Machine.hostNext]
  by_cases hw : m.host.wPend
  · have hwr : s.wr = true := by rw [hrel.wr]; exact hw
    simp [hw, hwr, hrel.wdata hwr, hrel.addr]
  · have hwr : s.wr = false := by rw [hrel.wr]; cases hwv : m.host.wPend <;> simp_all
    simp [hw, hwr]

/-- The machine's test for a data-RAM read address. -/
def ramRead (m : Machine.State) (cv : Machine.CfgView) : Bool :=
  match Machine.hostRead m cv m.host.addr.toNat with
  | .inl _ => false
  | .inr _ => true

/-- **The read request.**  A read the cut issues to a data-RAM address becomes
the machine's host request at the same address (as a byte address in the RAM). -/
theorem read_req_bridge (s : HostCmd.State) (m : Machine.State) (i : HostCmd.Input)
    (cv : Machine.CfgView) (served : Bool) (hrel : LinkRel s m)
    (hpend : m.host.rPend = true) (hram : ramRead m cv = true) :
    ∃ a : Nat, Machine.hostRead m cv m.host.addr.toNat = .inr a ∧
      (Machine.hostNext m cv (pinOf i) served).1.req = Machine.HReq.read (Machine.Util.bv 11 a) := by
  cases h : Machine.hostRead m cv m.host.addr.toNat with
  | inl v =>
    simp [ramRead, h] at hram
  | inr v =>
    refine ⟨v, rfl, ?_⟩
    simp only [Machine.hostNext]
    rw [ite_eq_left hpend]
    simp [h]

/-! ## The read-response registers (`HostRead`: `tx`, `rackv`)

`Metronome.HostRead` extends the command machine with `tx` (the shift register
MISO is taken from) and `rackv` (the register-read value waiting for its slot).
`LinkRelR` adds the two registers to `LinkRel` and `linkRelR_step` shows the
relation survives one step; `miso_bridge` states the observable, the MISO pin
being `tx[7]`.

The machine keeps a register-read value in `ldD` for one cycle only (the cycle
that loads `TX`), while the cut samples `rdVal` every cycle.  The `rackv`
relation is therefore conditional on the waiting acknowledgement `rack`; that
is a representation difference, not a behavioural one, and `rackv_witness`
shows the unconditional equation is false.  The `TX` load/share equations
(`cut_tx_noshift`, `mach_tx_csLow`, `tx_shift_bridge`, `ackv_bridge`) are kept
separate so the shift and load cases are independent. -/

/-- The machine's register-read value, as the cut's `rdVal` input. -/
def regVal (m : Machine.State) (cv : Machine.CfgView) : BitVec 8 :=
  match Machine.hostRead m cv m.host.addr.toNat with
  | .inl x => Machine.Util.bv 8 x
  | .inr _ => 0

/-- The byte a data-RAM landing loads: the machine's RAM output register in the
lane it presents. -/
def ramByte (m : Machine.State) : BitVec 8 :=
  Machine.Util.bv 8 (Machine.Util.nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8)

/-- The link relation extended with the two response registers.  `cmd` is the
command-history byte of the `HostCmd` projection; no equation of the response
path reads it. -/
structure LinkRelR (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State) : Prop where
  /-- the command machine's relation on the shared registers. -/
  base : LinkRel (s.toHostCmd cmd) m
  /-- the transmit shift register MISO is taken from. -/
  tx : s.tx = m.host.tx
  /-- the waiting register-read value, while an acknowledgement waits. -/
  rackv : s.rack = true → s.rackv = m.host.ldD

/-- The `HostRead` step is the command machine's step on the shared registers
(no equation of the command machine reads the history byte `cmd`). -/
theorem toHostCmd_step (s : HostRead.State) (cmd : BitVec 8) (i : HostRead.Input) :
    (HostRead.step s i).toHostCmd (HostCmd.step (s.toHostCmd cmd) i.toHostCmd).cmd =
      HostCmd.step (s.toHostCmd cmd) i.toHostCmd := rfl

/-- The cut's reset state is the machine's power-on state. -/
theorem linkRelR_reset : LinkRelR HostRead.resetState 0 Machine.State.init :=
  { base := linkRel_reset
    tx := rfl
    rackv := by intro h; exact absurd h (by simp [HostRead.resetState]) }

/-- **The `rackv` relation is conditional.**  A cut state at `rackv = 0x5A` with
no acknowledgement waiting satisfies every other field against the machine's
power-on state, but the machine's `ldD` is 0: `rackv = ldD` cannot be asserted
outside the acknowledgement cycle.  `HostRead.rackv` samples `rd_val` every
cycle, `Machine.HostSt.ldD` only carries the value of the read request. -/
theorem rackv_witness :
    let s : HostRead.State := { HostRead.resetState with rackv := 0x5A }
    LinkRelR s 0 Machine.State.init ∧ ¬ s.rackv = Machine.State.init.host.ldD := by
  refine ⟨⟨linkRel_reset, rfl, ?_⟩, ?_⟩
  · intro h; exact absurd h (by simp [HostRead.resetState])
  · decide

/-- The machine's `TX` is cleared by `CS_N` high. -/
theorem mach_tx_csHigh (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = true) :
    (Machine.hostNext m cv p served).1.tx = 0 := by
  simp [Machine.hostNext, hcs]

/-- The machine's `TX` with `CS_N` low: shift while the bit count is below 7, a
landing loads the waiting byte, otherwise it holds. -/
theorem mach_tx_csLow (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) :
    (Machine.hostNext m cv p served).1.tx =
      (if p.sckRise && m.host.nbit.toNat < 7 then
        Machine.Util.bv 8 ((m.host.tx.toNat * 2) % 256)
       else if m.host.ldV || m.ramOwner == 4 then
        Machine.Util.bv 8 (if m.host.ldV then m.host.ldD.toNat
          else Machine.Util.nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8)
       else m.host.tx) := by
  simp [Machine.hostNext, hcs]

/-- The machine's `TX` on a shifting `SR` (`nbit < 7`). -/
theorem mach_tx_shift (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false) (hrise : p.sckRise = true)
    (hbit : m.host.nbit.toNat < 7) :
    (Machine.hostNext m cv p served).1.tx =
      Machine.Util.bv 8 ((m.host.tx.toNat * 2) % 256) := by
  rw [mach_tx_csLow m cv p served hcs]
  simp [hrise, hbit]

/-- The machine's `TX` with no shifting `SR`: a landing loads, otherwise it holds. -/
theorem mach_tx_noshift (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hcs : p.csn = false)
    (hns : ¬ ((p.sckRise && (m.host.nbit.toNat < 7)) = true)) :
    (Machine.hostNext m cv p served).1.tx =
      (if (m.host.ldV || m.ramOwner == 4) = true then
        Machine.Util.bv 8 (if m.host.ldV then m.host.ldD.toNat
          else Machine.Util.nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8)
       else m.host.tx) := by
  rw [mach_tx_csLow m cv p served hcs, ite_eq_right hns]

/-- The cut's `TX` with no shifting `SR`: a landing loads, otherwise it holds. -/
theorem cut_tx_noshift (s : HostRead.State) (i : HostRead.Input) (hreset : i.resetN = true)
    (hcs : i.csN = false) (hns : (HostRead.sr i && (s.bitc != 7)) = false) :
    (HostRead.step s i).tx = (if HostRead.ack s i then HostRead.ackv s i else s.tx) := by
  have hns' : ¬ ((HostRead.sr i && (s.bitc != 7)) = true) := by rw [hns]; simp
  show HostRead.txNext s i =
    (if HostRead.ack s i then HostRead.ackv s i else s.tx)
  unfold HostRead.txNext
  have hreset' : ¬ ((!i.resetN) = true) := by rw [hreset]; simp
  have hcs' : ¬ (i.csN = true) := by rw [hcs]; simp
  rw [ite_eq_right hreset', ite_eq_right hcs', ite_eq_right hns']

/-- The machine's `ldD` after a read request for a register value. -/
theorem ldD_bridge (m : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) (hpend : m.host.rPend = true) (x : Nat)
    (hx : Machine.hostRead m cv m.host.addr.toNat = .inl x) :
    (Machine.hostNext m cv p served).1.ldD = Machine.Util.bv 8 x := by
  simp [Machine.hostNext, hpend, hx]

/-- A register-read test of `true` names a register address. -/
theorem regRead_inl (m : Machine.State) (cv : Machine.CfgView)
    (h : regRead m cv = true) :
    ∃ x, Machine.hostRead m cv m.host.addr.toNat = .inl x := by
  cases hx : Machine.hostRead m cv m.host.addr.toNat with
  | inl x => exact ⟨x, rfl⟩
  | inr a => simp [regRead, hx] at h

/-- An `SR` shifts one zero into `TX`: the cut's shift is the machine's `bv`
equation. -/
theorem tx_shift_bridge (x : BitVec 8) :
    x <<< 1 = Machine.Util.bv 8 ((x.toNat * 2) % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Machine.Util.bv, BitVec.toNat_ofNat]
  omega

/-- The byte a landing loads: the waiting register read or the RAM byte, the
same on both sides (`register_read_response` of `HostRead` against
`Machine.hostNext`'s `loadByte`). -/
theorem ackv_bridge (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (i : HostRead.Input) (hrel : LinkRelR s cmd m) (hlandD : i.hlandD = ramByte m) :
    HostRead.ackv s i =
      Machine.Util.bv 8 (if m.host.ldV then m.host.ldD.toNat
        else Machine.Util.nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8) := by
  have hrack : s.rack = m.host.ldV := hrel.base.rack
  have hbyte : Machine.Util.bv 8
      (Machine.Util.nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8) = ramByte m := rfl
  cases hr : s.rack with
  | false =>
    have hlv : m.host.ldV = false := by rw [← hrack, hr]
    rw [HostRead.ack_value_ram s i hr, hlandD, hlv]
    simp [hbyte]
  | true =>
    have hlv : m.host.ldV = true := by rw [← hrack, hr]
    rw [HostRead.ack_value s i hr, hlv, hrel.rackv hr]
    simp [Machine.Util.bv]

/-- The cut's sampled pins as the machine's `PinView` (its `HostCmd` projection
carries the pins). -/
def pinOfR (i : HostRead.Input) : Machine.PinView := pinOf i.toHostCmd

/-- The cut's `SR` is the machine's `sckRise && !csn` at the sampled pins. -/
theorem sr_pin (i : HostRead.Input) :
    HostRead.sr i = ((pinOfR i).sckRise && !(pinOfR i).csn) :=
  (pin_bridge i.toHostCmd).symm

/-- The cut's acknowledgements and the machine's landing test coincide. -/
theorem ack_bridge (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (i : HostRead.Input) (hrel : LinkRelR s cmd m) (hland : (m.ramOwner == 4) = i.hland) :
    HostRead.ack s i = (m.host.ldV || (m.ramOwner == 4)) := by
  have hrack : s.rack = m.host.ldV := hrel.base.rack
  rw [HostRead.ack, hrack, hland]

/-- **The transmit register.**  One `HostRead` step leaves `TX` exactly as the
machine's link step does (SPEC_V2 §9: shift on the 1st..7th `SR`, a load on a
landing, hold otherwise, `CS_N` high clears). -/
theorem tx_step (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (i : HostRead.Input) (cv : Machine.CfgView) (served : Bool)
    (hreset : i.resetN = true) (hrel : LinkRelR s cmd m)
    (hland : (m.ramOwner == 4) = i.hland) (hlandD : i.hlandD = ramByte m) :
    (HostRead.step s i).tx = (Machine.hostNext m cv (pinOfR i) served).1.tx := by
  have hbitc : s.bitc = m.host.nbit := hrel.base.bitc
  cases hcsn : i.csN with
  | true =>
    rw [HostRead.tx_cs_high s i hreset hcsn,
      mach_tx_csHigh m cv (pinOfR i) served (by simp [pinOfR, pinOf, hcsn])]
  | false =>
    have hcs2 : (pinOfR i).csn = false := by simp [pinOfR, pinOf, hcsn]
    by_cases hrise : (pinOfR i).sckRise = true
    · have hsr : HostRead.sr i = true := by
        rw [sr_pin i, hrise]
        simp [pinOfR, pinOf, hcsn]
      by_cases hb7 : s.bitc = 7
      · -- the eighth `SR`: no shift, a landing (if any) wins
        have hn7 : m.host.nbit.toNat = 7 := by rw [← hbitc, hb7]; rfl
        have hns : ¬ (((pinOfR i).sckRise && (m.host.nbit.toNat < 7)) = true) := by
          rw [hn7]; simp
        have hnsC : (HostRead.sr i && (s.bitc != 7)) = false := by
          rw [show (s.bitc != 7) = false from by rw [hb7]; rfl]
          simp
        rw [mach_tx_noshift m cv (pinOfR i) served hcs2 hns,
          cut_tx_noshift s i hreset hcsn hnsC, ack_bridge s cmd m i hrel hland,
          ackv_bridge s cmd m i hrel hlandD]
        by_cases hl : (m.host.ldV || (m.ramOwner == 4)) = true <;>
          simp [hl, hrel.tx]
      · -- a shifting `SR`
        have hnb : m.host.nbit.toNat < 7 := by
          have hlt := m.host.nbit.isLt
          have hne : m.host.nbit.toNat ≠ 7 := by
            intro h
            exact hb7 (by rw [hbitc]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
          omega
        rw [HostRead.tx_shift s i hreset hcsn hsr hb7,
          mach_tx_shift m cv (pinOfR i) served hcs2 hrise hnb,
          hrel.tx, tx_shift_bridge]
    · -- no rising `SCK` edge: no shift, a landing (if any) wins
      have hriseF : (pinOfR i).sckRise = false := by
        cases hv : (pinOfR i).sckRise <;> simp_all
      have hsr : HostRead.sr i = false := by
        rw [sr_pin i, hriseF]
        simp
      have hns : ¬ (((pinOfR i).sckRise && (m.host.nbit.toNat < 7)) = true) := by
        rw [hriseF]; simp
      have hnsC : (HostRead.sr i && (s.bitc != 7)) = false := by rw [hsr]; simp
      rw [mach_tx_noshift m cv (pinOfR i) served hcs2 hns,
        cut_tx_noshift s i hreset hcsn hnsC, ack_bridge s cmd m i hrel hland,
        ackv_bridge s cmd m i hrel hlandD]
      by_cases hl : (m.host.ldV || (m.ramOwner == 4)) = true <;>
        simp [hl, hrel.tx]

/-- **The waiting register-read value.**  While the acknowledgement waits, the
cut's `rackv` is the machine's `ldD`; the machine's `ldD` carries the value of
the read request that set it. -/
theorem rackv_step (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (i : HostRead.Input) (cv : Machine.CfgView) (served : Bool)
    (hreset : i.resetN = true) (hrel : LinkRelR s cmd m)
    (hreg : i.rdData = !regRead m cv) (hval : i.rdVal = regVal m cv) :
    (HostRead.step s i).rack = true →
      (HostRead.step s i).rackv = (Machine.hostNext m cv (pinOfR i) served).1.ldD := by
  intro hr
  have hcutRack : (HostRead.step s i).rack = (s.rd && !i.rdData) :=
    HostRead.rack_set s i hreset
  have hrd : s.rd = true := by
    have h2 : (s.rd && !i.rdData) = true := by rw [← hcutRack]; exact hr
    cases hd : s.rd with
    | false => rw [hd] at h2; simp at h2
    | true => rfl
  have hregT : regRead m cv = true := by
    have h2 : (s.rd && !i.rdData) = true := by rw [← hcutRack]; exact hr
    have h3 : !i.rdData = true := by
      cases hd : s.rd <;> simp_all
    have h4 : i.rdData = false := by simpa using h3
    cases hrr : regRead m cv <;> simp_all
  obtain ⟨x, hx⟩ := regRead_inl m cv hregT
  have hpend : m.host.rPend = true := by rw [← hrel.base.rd]; exact hrd
  rw [HostRead.rackv_sample s i hreset, hval, ldD_bridge m cv (pinOfR i) served hpend x hx]
  simp [regVal, hx]

/-- **One step of the response path.**  `LinkRelR` is preserved by one link step
under the interface hypotheses already used by `linkRel_step` plus `hlandD`
(the cut's RAM landing byte is the machine's RAM output lane) and `hval` (the
cut's `rdVal` input is the machine's register read of this cycle). -/
theorem linkRelR_step (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (i : HostRead.Input) (cv : Machine.CfgView) (served : Bool)
    (hreset : i.resetN = true) (hrel : LinkRelR s cmd m)
    (hland : (m.ramOwner == 4) = i.hland) (hreg : i.rdData = !regRead m cv)
    (hlandD : i.hlandD = ramByte m) (hval : i.rdVal = regVal m cv)
    (hquiet : HostCmd.completing (s.toHostCmd cmd) i.toHostCmd = true →
      (s.toHostCmd cmd).wr = false ∧ HostCmd.ackBit (s.toHostCmd cmd) i.toHostCmd = false) :
    LinkRelR (HostRead.step s i) (HostCmd.step (s.toHostCmd cmd) i.toHostCmd).cmd
      { m with host := (Machine.hostNext m cv (pinOfR i) served).1 } :=
  { base := by
      rw [toHostCmd_step]
      exact linkRel_step (s.toHostCmd cmd) m i.toHostCmd cv served hreset hrel.base
        hland hreg hquiet
    tx := tx_step s cmd m i cv served hreset hrel hland hlandD
    rackv := rackv_step s cmd m i cv served hreset hrel hreg hval }

/-- The machine's `nbit` of `TX` is its `bit`, the extractor `pinsOut` uses. -/
theorem nbit_eq_bit_seven (x : BitVec 8) :
    Machine.Util.nbit x.toNat 7 = Machine.Util.bit x 7 := by
  unfold Machine.Util.nbit Machine.Util.bit
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rw [show (x.toNat / 2 ^ 7 % 2 == 1) = decide (x.toNat / 2 ^ 7 % 2 = 1) from by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]]

/-- The cut's RTL-shaped `bitAt` is the machine's `nbit`, at the bit MISO uses. -/
theorem bitAt_eq_nbit_seven (x : BitVec 8) :
    HostRead.bitAt x 7 = Machine.Util.nbit x.toNat 7 := by
  rw [Bool.eq_iff_iff, HostRead.bitAt, Machine.Util.nbit, bne_iff_ne, beq_iff_eq]
  rw [ne_eq, BitVec.toNat_eq]
  rw [show ((0 : BitVec 8)).toNat = 0 from rfl]
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  rw [show (1 : BitVec 8).toNat = 1 from rfl]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.shiftRight_eq_div_pow]
  constructor <;> intro h <;> omega

/-- The cut's `bitAt x 7` and the machine's `bit x 7` are the same bit. -/
theorem bit_seven_eq_bitAt (x : BitVec 8) :
    Machine.Util.bit x 7 = HostRead.bitAt x 7 := by
  rw [← nbit_eq_bit_seven, bitAt_eq_nbit_seven]

/-- The chip's `uo_out` low bit is `MISO = TX[7]`; the other terms of `uo_out`
are even. -/
theorem pinsOut_miso (m : Machine.State) :
    (Machine.pinsOut m).1 % 2 = Machine.Util.b2n (Machine.Util.bit m.host.tx 7) := by
  simp only [Machine.pinsOut, Machine.Util.b2n]
  by_cases hb : Machine.Util.bit m.host.tx 7 <;> simp [hb] <;> omega

/-- **MISO.**  The bit the chip drives on `uo_out[0]` is the cut's `tx[7]`
(SPEC_V2 §9: the target shifts `TX` out MSB first; `Machine.pinsOut`). -/
theorem miso_bridge (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (hrel : LinkRelR s cmd m) :
    Machine.Util.bit m.host.tx 7 = HostRead.bitAt s.tx 7 := by
  rw [← hrel.tx]
  exact bit_seven_eq_bitAt s.tx

/-- The same statement on the output pins. -/
theorem miso_pin_bridge (s : HostRead.State) (cmd : BitVec 8) (m : Machine.State)
    (hrel : LinkRelR s cmd m) :
    (Machine.pinsOut m).1 % 2 = Machine.Util.b2n (HostRead.bitAt s.tx 7) := by
  rw [pinsOut_miso, miso_bridge s cmd m hrel]

end Metronome.Bridge.Host
