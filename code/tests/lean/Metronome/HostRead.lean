import Metronome.HostCmd
import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Metronome host read path

An independent specification of the read path of `src/md2_host.v` (SPEC_V2 §9,
"Read response") and of the host register-read map (`rd_val` in
`src/project.v`, ISA_TABLES_V2 "Host address map").

`Metronome.HostCmd` models the command/address/data phase machine and stops at
the read request `rd` and the acknowledge latch `rack`.  This module extends
that machine with the two registers of the response path, `tx` (the shift
register MISO is taken from) and `rackv` (the register-read value waiting to be
loaded), keeps every command-machine equation by projection onto
`HostCmd.step`, and states the byte-level contract:

* a register read requested in cycle `R` loads `TX` at the end of cycle `R+1`
  with the `rd_val` sampled in `R` (`register_read_response`);
* during a data byte the eight `SR` edges shift `TX` out MSB first, one bit per
  `SR`, and the eighth leaves `TX` alone (`read_byte_msb`);
* the two cycles after a byte latch the request and take the next byte
  (`read_slot_step`, `read_slot`), so `read_burst_index` gives the k-th byte
  clocked out and the address it belongs to;
* a data-RAM landing loads `TX` with `hland_d` (`ram_landing_sending`,
  `ram_byte_msb`); the RAM service contract is an interface premise;
* the second half of the file is the register-read map: `rdValSpec` is a pure
  function of the 16-bit address and the named state signals, it reads zero
  outside the five register blocks, and it is bit-exact for every documented
  layout.  `read_no_write` states the machine-level side of "no host read has a
  side effect".

The generated cut (`hostread_check.py`, `HostReadEquivalence.lean.in`) proves
that the elaborated host link is this machine's transition, that the elaborated
`rd_val` mux is `rdValSpec` at every 16-bit address, and that the MISO pin
carries `tx[7]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
-- The boolean component proofs of the step lemmas share one generous simp set
-- (every hypothesis of the case), and the equation lemmas keep the full
-- signature of the equation they state; not every branch uses every argument.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Metronome.HostRead

/-! ## Sampled inputs and state -/

/-- Sampled host-link inputs.  `rdVal` is the host register-read value of this
cycle (`rd_val` in the chip top), `hland`/`hlandD` the data-RAM landing strobe
and byte. -/
structure Input where
  resetN : Bool
  sck : Bool
  sckPrev : Bool
  csN : Bool
  mosi : Bool
  rdData : Bool
  rdVal : BitVec 8
  hland : Bool
  hlandD : BitVec 8
  deriving DecidableEq, Repr

/-- The command-machine view of the sampled inputs. -/
def Input.toHostCmd (i : Input) : HostCmd.Input :=
  ⟨i.resetN, i.sck, i.sckPrev, i.csN, i.mosi, i.rdData, i.hland⟩

/-- The registers of the host link plus the two read-response registers.  The
first nine are `Metronome.HostCmd`'s; `tx` is the shift register MISO comes
from and `rackv` the register-read value waiting for its slot. -/
@[ext] structure State where
  phase : BitVec 3
  bitc : BitVec 3
  rx : BitVec 7
  isRd : Bool
  addr : BitVec 16
  wr : Bool
  wdata : BitVec 8
  rd : Bool
  rack : Bool
  tx : BitVec 8
  rackv : BitVec 8
  deriving DecidableEq, Repr

/-- The command-machine projection.  `cmd` is the host-command history
variable; no equation of the nine shared registers reads it. -/
def State.toHostCmd (s : State) (cmd : BitVec 8) : HostCmd.State :=
  ⟨s.phase, s.bitc, s.rx, s.isRd, s.addr, s.wr, s.wdata, s.rd, s.rack, cmd⟩

@[simp] theorem State.toHostCmd_phase (s : State) (c : BitVec 8) :
    (s.toHostCmd c).phase = s.phase := rfl

@[simp] theorem State.toHostCmd_bitc (s : State) (c : BitVec 8) :
    (s.toHostCmd c).bitc = s.bitc := rfl

@[simp] theorem State.toHostCmd_isRd (s : State) (c : BitVec 8) :
    (s.toHostCmd c).isRd = s.isRd := rfl

@[simp] theorem State.toHostCmd_addr (s : State) (c : BitVec 8) :
    (s.toHostCmd c).addr = s.addr := rfl

@[simp] theorem State.toHostCmd_wr (s : State) (c : BitVec 8) :
    (s.toHostCmd c).wr = s.wr := rfl

@[simp] theorem State.toHostCmd_wdata (s : State) (c : BitVec 8) :
    (s.toHostCmd c).wdata = s.wdata := rfl

@[simp] theorem State.toHostCmd_rd (s : State) (c : BitVec 8) :
    (s.toHostCmd c).rd = s.rd := rfl

@[simp] theorem State.toHostCmd_rack (s : State) (c : BitVec 8) :
    (s.toHostCmd c).rack = s.rack := rfl

@[simp] theorem Input.toHostCmd_resetN (i : Input) : i.toHostCmd.resetN = i.resetN := rfl

@[simp] theorem Input.toHostCmd_sck (i : Input) : i.toHostCmd.sck = i.sck := rfl

@[simp] theorem Input.toHostCmd_sckPrev (i : Input) : i.toHostCmd.sckPrev = i.sckPrev := rfl

@[simp] theorem Input.toHostCmd_csN (i : Input) : i.toHostCmd.csN = i.csN := rfl

@[simp] theorem Input.toHostCmd_rdData (i : Input) : i.toHostCmd.rdData = i.rdData := rfl

/-- The state left by a sampled reset edge. -/
def resetState : State := ⟨0, 0, 0, false, 0, false, 0, false, false, 0, 0⟩

/-! ## Combinational terms

`sr` is SPEC_V2 §9's synchronised rising edge; it is the command machine's own
definition, so the two cuts cannot drift apart. -/

def sr (i : Input) : Bool := HostCmd.sr i.toHostCmd

@[simp] theorem sr_eq (i : Input) : HostCmd.sr i.toHostCmd = sr i := rfl

/-- A response lands this cycle: a register-read value waits (`rack`) or a data
RAM byte arrives (`hland`). -/
def ack (s : State) (i : Input) : Bool := s.rack || i.hland

@[simp] theorem ack_eq (s : State) (i : Input) :
    HostCmd.ackBit (s.toHostCmd 0#8) i.toHostCmd = ack s i := rfl

/-- The byte a landing loads: the waiting register-read value wins over a data
RAM landing, which is the RTL's `ackv = rack ? rackv : hland_d`. -/
def ackv (s : State) (i : Input) : BitVec 8 := if s.rack then s.rackv else i.hlandD

/-! ## Next state

The nine shared equations are the command machine's; `tx` and `rackv` are the
read path's.  SPEC_V2 §9: on the 1st..7th `SR` of a byte `TX' = {TX[6:0], 0}`;
the 8th `SR` leaves `TX` alone; `CS_N` high clears `TX`; a landing loads `TX`,
and a load in the same cycle as a shifting `SR` is lost (the order of the RTL's
assignments). -/

def txNext (s : State) (i : Input) : BitVec 8 :=
  if !i.resetN then 0
  else if i.csN then 0
  else if sr i && s.bitc != 7 then s.tx <<< 1
  else if ack s i then ackv s i else s.tx

/-- `rackv` samples `rd_val` every cycle; a reset clears it. -/
def rackvNext (s : State) (i : Input) : BitVec 8 := if !i.resetN then 0 else i.rdVal

def phaseNext (s : State) (i : Input) : BitVec 3 :=
  HostCmd.phaseNext (s.toHostCmd 0#8) i.toHostCmd

def bitcNext (s : State) (i : Input) : BitVec 3 :=
  HostCmd.bitcNext (s.toHostCmd 0#8) i.toHostCmd

def rxNext (s : State) (i : Input) : BitVec 7 :=
  HostCmd.rxNext (s.toHostCmd 0#8) i.toHostCmd

def isRdNext (s : State) (i : Input) : Bool :=
  HostCmd.isRdNext (s.toHostCmd 0#8) i.toHostCmd

def addrNext (s : State) (i : Input) : BitVec 16 :=
  HostCmd.addrNext (s.toHostCmd 0#8) i.toHostCmd

def wrNext (s : State) (i : Input) : Bool :=
  HostCmd.wrNext (s.toHostCmd 0#8) i.toHostCmd

def wdataNext (s : State) (i : Input) : BitVec 8 :=
  HostCmd.wdataNext (s.toHostCmd 0#8) i.toHostCmd

def rdNext (s : State) (i : Input) : Bool :=
  HostCmd.rdNext (s.toHostCmd 0#8) i.toHostCmd

def rackNext (s : State) (i : Input) : Bool :=
  HostCmd.rackNext (s.toHostCmd 0#8) i.toHostCmd

def step (s : State) (i : Input) : State :=
  ⟨phaseNext s i, bitcNext s i, rxNext s i, isRdNext s i, addrNext s i,
   wrNext s i, wdataNext s i, rdNext s i, rackNext s i, txNext s i, rackvNext s i⟩

/-- The register state during cycle `n` of the sampled trace. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- Splitting a sampled trace at cycle `m`. -/
theorem stateAt_add (inputs : Nat → Input) (initial : State) (m n : Nat) :
    stateAt inputs initial (m + n) =
      stateAt (fun j => inputs (m + j)) (stateAt inputs initial m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      stateAt inputs initial (m + (n + 1))
          = stateAt inputs initial ((m + n) + 1) := by rw [Nat.add_succ]
      _ = step (stateAt inputs initial (m + n)) (inputs (m + n)) :=
            stateAt_succ inputs initial (m + n)
      _ = step (stateAt (fun j => inputs (m + j)) (stateAt inputs initial m) n)
              (inputs (m + n)) := by rw [ih]
      _ = step (stateAt (fun j => inputs (m + j)) (stateAt inputs initial m) n)
              ((fun j => inputs (m + j)) n) := rfl
      _ = stateAt (fun j => inputs (m + j)) (stateAt inputs initial m) (n + 1) :=
            (stateAt_succ (fun j => inputs (m + j)) (stateAt inputs initial m) n).symm

/-! ## One-step equations of the response registers -/

/-- `completing` is false away from the eighth edge of a byte. -/
theorem completing_false (t : State) (i : Input) (hbitc : t.bitc ≠ 7) :
    HostCmd.completing (t.toHostCmd 0#8) i.toHostCmd = false := by
  have hs : ((t.toHostCmd 0#8).bitc == 7) = false := beq_eq_false_iff_ne.mpr hbitc
  show (sr i && ((t.toHostCmd 0#8).bitc == 7)) = false
  rw [hs]
  simp

/-- `completing` is true on the eighth edge of a byte. -/
theorem completing_true (t : State) (i : Input) (hsr : sr i = true) (hbitc : t.bitc = 7) :
    HostCmd.completing (t.toHostCmd 0#8) i.toHostCmd = true := by
  have hs : ((t.toHostCmd 0#8).bitc == 7) = true := beq_iff_eq.mpr hbitc
  show (sr i && ((t.toHostCmd 0#8).bitc == 7)) = true
  rw [hs, hsr]
  rfl

/-- The response byte selected by a landing: a waiting register read wins. -/
theorem ack_value (s : State) (i : Input) (h : s.rack = true) : ackv s i = s.rackv := by
  simp [ackv, h]

/-- Without a waiting register read a landing is the data RAM byte. -/
theorem ack_value_ram (s : State) (i : Input) (h : s.rack = false) : ackv s i = i.hlandD := by
  simp [ackv, h]

/-- `TX` holds unless a reset, `CS_N` high, a shifting `SR` or a landing acts. -/
theorem tx_holds (s : State) (i : Input) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : sr i = false) (hack : ack s i = false) : (step s i).tx = s.tx := by
  show txNext s i = s.tx
  unfold txNext
  by_cases h7 : s.bitc = 7
  · rw [show (s.bitc != 7) = false from bne_eq_false_iff_eq.mpr h7]
    simp [hreset, hcs, hsr, hack]
  · rw [show (s.bitc != 7) = true from bne_iff_ne.mpr h7]
    simp [hreset, hcs, hsr, hack]

/-- A shifting `SR` (`bitc ≠ 7`) drops the top bit of `TX` and shifts in a zero;
a landing in the same cycle is lost. -/
theorem tx_shift (s : State) (i : Input) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : sr i = true) (hbitc : s.bitc ≠ 7) : (step s i).tx = s.tx <<< 1 := by
  show txNext s i = s.tx <<< 1
  unfold txNext
  rw [show (s.bitc != 7) = true from bne_iff_ne.mpr hbitc]
  simp [hreset, hcs, hsr]

/-- The eighth `SR` of a byte leaves `TX` alone. -/
theorem tx_eighth (s : State) (i : Input) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : sr i = true) (hbitc : s.bitc = 7) (hack : ack s i = false) :
    (step s i).tx = s.tx := by
  show txNext s i = s.tx
  unfold txNext
  rw [show (s.bitc != 7) = false from bne_eq_false_iff_eq.mpr hbitc]
  simp [hreset, hcs, hsr, hack]

/-- A landing loads `TX` when no shifting `SR` is in the cycle. -/
theorem tx_load (s : State) (i : Input) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hack : ack s i = true) (hkeep : sr i = false ∨ s.bitc = 7) :
    (step s i).tx = ackv s i := by
  show txNext s i = ackv s i
  unfold txNext
  rcases hkeep with hs | hb
  · simp [hreset, hcs, hack, hs]
  · rw [show (s.bitc != 7) = false from bne_eq_false_iff_eq.mpr hb]
    simp [hreset, hcs, hack]

/-- `CS_N` high clears `TX` (SPEC_V2 §9). -/
theorem tx_cs_high (s : State) (i : Input) (hreset : i.resetN = true) (hcs : i.csN = true) :
    (step s i).tx = 0 := by
  show txNext s i = 0
  unfold txNext
  simp [hreset, hcs]

/-- A reset edge clears the response path. -/
theorem tx_reset (s : State) (i : Input) (hreset : i.resetN = false) : (step s i).tx = 0 := by
  show txNext s i = 0
  unfold txNext
  simp [hreset]

/-- `rackv` samples the register-read value of this cycle. -/
theorem rackv_sample (s : State) (i : Input) (hreset : i.resetN = true) :
    (step s i).rackv = i.rdVal := by
  show rackvNext s i = i.rdVal
  unfold rackvNext
  simp [hreset]

/-- The register-read request slot: `rack' = rd & !rd_data`. -/
theorem rack_set (s : State) (i : Input) (hreset : i.resetN = true) :
    (step s i).rack = (s.rd && !i.rdData) := by
  show HostCmd.rackNext (s.toHostCmd 0#8) i.toHostCmd = (s.rd && !i.rdData)
  rw [HostCmd.rackNext]
  simp [hreset]

/-! ## A read transaction issues no write

SPEC_V2 §9: "No host read has a side effect."  At the machine level a read
transaction (`isRd`) never raises the write strobe and never loads the write
data register; `rdValSpec` is combinational.  The adapter additionally checks
that the elaborated `h_rd` net enters nothing but the data-RAM host request
slot. -/

theorem read_no_write (s : State) (i : Input) (h : s.isRd = true)
    (hreset : i.resetN = true) :
    (step s i).wr = false ∧ (step s i).wdata = s.wdata := by
  have hwr : (step s i).wr = false := HostCmd.isRd_no_wr _ _ h
  refine ⟨hwr, ?_⟩
  show HostCmd.wdataNext (s.toHostCmd 0#8) i.toHostCmd = s.wdata
  rw [HostCmd.wdataNext]
  simp [h, hreset]

/-- The command machine's address hold with this machine's state. -/
theorem addr_holds (s : State) (i : Input) (hwr : s.wr = false) (hack : ack s i = false)
    (hreset : i.resetN = true) (hah : s.phase ≠ HostCmd.ST_AH)
    (hal : s.phase ≠ HostCmd.ST_AL) : (step s i).addr = s.addr :=
  HostCmd.addr_holds _ _ hwr hack hreset hah hal

/-! ## The register read: `rd_val` of cycle `R` loads `TX` at the end of `R+1` -/

/-- SPEC_V2 §9 read response: a register read requested in cycle `R` (`rd`
high, not a data-RAM address) latches `rack` and the `rd_val` of cycle `R`, and
the next edge loads `TX` with that value.  `hkeep` is the RTL's "a load in the
same cycle as a shifting `SR` is lost": the loading edge is an idle cycle or the
completing (eighth) edge of the previous byte. -/
theorem register_read_response (inputs : Nat → Input) (initial : State) (R : Nat)
    (hd : (stateAt inputs initial R).rd = true)
    (hrdData : (inputs R).rdData = false)
    (hresetR : (inputs R).resetN = true) (hcsR : (inputs R).csN = false)
    (hresetL : (inputs (R + 1)).resetN = true) (hcsL : (inputs (R + 1)).csN = false)
    (hkeep : sr (inputs (R + 1)) = false ∨ (stateAt inputs initial (R + 1)).bitc = 7) :
    (stateAt inputs initial (R + 1)).rack = true ∧
      (stateAt inputs initial (R + 1)).rackv = (inputs R).rdVal ∧
      (stateAt inputs initial (R + 2)).tx = (inputs R).rdVal := by
  have e1 : stateAt inputs initial (R + 1) = step (stateAt inputs initial R) (inputs R) :=
    stateAt_succ _ _ R
  have e2 : stateAt inputs initial (R + 2) =
      step (stateAt inputs initial (R + 1)) (inputs (R + 1)) := stateAt_succ _ _ (R + 1)
  have hmiddle : (stateAt inputs initial (R + 1)).rack = true := by
    rw [e1, rack_set _ _ hresetR, hd, hrdData]
    rfl
  have hsample : (stateAt inputs initial (R + 1)).rackv = (inputs R).rdVal := by
    rw [e1]
    exact rackv_sample _ _ hresetR
  have hload : (stateAt inputs initial (R + 2)).tx = (inputs R).rdVal := by
    rw [e2, tx_load _ _ hresetL hcsL (by rw [ack, hmiddle]; rfl) hkeep,
      ack_value _ _ hmiddle, hsample]
  exact ⟨hmiddle, hsample, hload⟩

/-! ## Byte framing: eight `SR` edges shift `TX` out MSB first -/

/-- Bit `i` of `x`. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool := ((x >>> i) &&& (1 : BitVec w)) != 0

/-- `b` shifted left `n` times: the `TX` content after `n` shifted-out bits of
the byte `b`. -/
def shifted (b : BitVec 8) : Nat → BitVec 8
  | 0 => b
  | n + 1 => shifted b n <<< 1

@[simp] theorem shifted_zero (b : BitVec 8) : shifted b 0 = b := rfl

theorem shifted_succ (b : BitVec 8) (n : Nat) : shifted b (n + 1) = shifted b n <<< 1 := rfl

/-- Sample `n` of a byte still holds bit `7 - n` of it. -/
theorem shifted_bit (b : BitVec 8) :
    ∀ n : Fin 8, bitAt (shifted b n.val) 7 = bitAt b (7 - n.val)
  | ⟨0, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨1, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨2, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨3, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨4, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨5, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨6, _⟩ => by simp [shifted, bitAt] <;> bv_decide
  | ⟨7, _⟩ => by simp [shifted, bitAt] <;> bv_decide

/-- Partway through a data byte of a read transaction: `n` bits already sent,
`TX` still holding the unsent bits of `b`, address `a`, no strobe. -/
def SendingN (t : State) (a : BitVec 16) (b : BitVec 8) (n : Nat) : Prop :=
  t.phase = HostCmd.ST_DATA ∧ t.isRd = true ∧ t.bitc = BitVec.ofNat 3 n ∧
    t.tx = shifted b n ∧ t.addr = a ∧ t.wr = false ∧ t.rd = false ∧ t.rack = false

theorem SendingN.phase_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.phase = HostCmd.ST_DATA := h.1

theorem SendingN.isRd_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.isRd = true := h.2.1

theorem SendingN.bitc_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.bitc = BitVec.ofNat 3 n := h.2.2.1

theorem SendingN.tx_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.tx = shifted b n := h.2.2.2.1

theorem SendingN.addr_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.addr = a := h.2.2.2.2.1

theorem SendingN.wr_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.wr = false := h.2.2.2.2.2.1

theorem SendingN.rd_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.rd = false := h.2.2.2.2.2.2.1

theorem SendingN.rack_eq {t : State} {a : BitVec 16} {b : BitVec 8} {n : Nat}
    (h : SendingN t a b n) : t.rack = false := h.2.2.2.2.2.2.2

/-- The byte just clocked out: `TX` holds its last bit, the request for the
next one is issued and the slot is empty. -/
def AfterByte (t : State) (a : BitVec 16) (b : BitVec 8) : Prop :=
  t.phase = HostCmd.ST_DATA ∧ t.isRd = true ∧ t.bitc = 0 ∧ t.tx = shifted b 7 ∧
    t.addr = a ∧ t.wr = false ∧ t.rd = true ∧ t.rack = false

theorem AfterByte.phase_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.phase = HostCmd.ST_DATA := h.1

theorem AfterByte.isRd_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.isRd = true := h.2.1

theorem AfterByte.bitc_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.bitc = 0 := h.2.2.1

theorem AfterByte.tx_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.tx = shifted b 7 := h.2.2.2.1

theorem AfterByte.addr_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.addr = a := h.2.2.2.2.1

theorem AfterByte.wr_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.wr = false := h.2.2.2.2.2.1

theorem AfterByte.rd_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.rd = true := h.2.2.2.2.2.2.1

theorem AfterByte.rack_eq {t : State} {a : BitVec 16} {b : BitVec 8}
    (h : AfterByte t a b) : t.rack = false := h.2.2.2.2.2.2.2

/-- The start of a data byte of a read transaction. -/
def Sending (t : State) (a : BitVec 16) (b : BitVec 8) : Prop := SendingN t a b 0

/-- One shifting `SR` in the middle of a byte. -/
theorem sending_step (t : State) (i : Input) (a : BitVec 16) (b : BitVec 8)
    (n : Nat) (h : SendingN t a b n) (hreset : i.resetN = true)
    (hcs : i.csN = false) (hsr : sr i = true) (hack : ack t i = false)
    (hbitc : t.bitc ≠ 7) : SendingN (step t i) a b (n + 1) := by
  have hcomp := completing_false t i hbitc
  have hphase := h.phase_eq
  have hisrd := h.isRd_eq
  have hbitc0 := h.bitc_eq
  have hne : BitVec.ofNat 3 n ≠ 7 := by rw [← hbitc0]; exact hbitc
  have htx := h.tx_eq
  have haddr := h.addr_eq
  have hwr := h.wr_eq
  have hrd := h.rd_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (t.toHostCmd 0#8) i.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp [hreset, hcs, hcomp, hphase]
  · show HostCmd.isRdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.bitcNext (t.toHostCmd 0#8) i.toHostCmd = BitVec.ofNat 3 (n + 1)
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
    rw [BitVec.ofNat_add]
  · rw [tx_shift _ _ hreset hcs hsr hbitc, htx, shifted_succ]
  · rw [addr_holds t i hwr hack hreset (by rw [hphase]; decide) (by rw [hphase]; decide), haddr]
  · show HostCmd.wrNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rdNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rackNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rackNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption

/-- The eighth `SR` completes the byte. -/
theorem sending_finish (t : State) (i : Input) (a : BitVec 16) (b : BitVec 8)
    (h : SendingN t a b 7) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : sr i = true) (hack : ack t i = false) :
    AfterByte (step t i) a b := by
  have hb7 : t.bitc = 7 := by rw [h.bitc_eq]; rfl
  have hcomp := completing_true t i hsr hb7
  have hphase := h.phase_eq
  have hisrd := h.isRd_eq
  have htx := h.tx_eq
  have haddr := h.addr_eq
  have hwr := h.wr_eq
  have hrd := h.rd_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (t.toHostCmd 0#8) i.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp [hreset, hcs, hcomp, hphase]
  · show HostCmd.isRdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.bitcNext (t.toHostCmd 0#8) i.toHostCmd = 0
    have hbeq : ((t.toHostCmd 0#8).bitc == 7) = true := by
      simp only [State.toHostCmd_bitc]
      exact beq_iff_eq.mpr hb7
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · rw [show (step t i).tx = t.tx from tx_eighth _ _ hreset hcs hsr hb7 hack, htx]
  · rw [addr_holds t i hwr hack hreset (by rw [hphase]; decide) (by rw [hphase]; decide), haddr]
  · show HostCmd.wrNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.rdNext]
    simp [hreset, hcs, hsr, hcomp, hphase, hisrd]
  · show HostCmd.rackNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rackNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption

/-- The eight `SR` edges of one data byte, from a `Sending` state: the eight
MISO samples are the eight bits of the byte, MSB first, and the byte ends in an
`AfterByte` state. -/
theorem read_byte_msb (inputs : Nat → Input) (s : State) (a : BitVec 16) (b : BitVec 8)
    (h : Sending s a b)
    (hcyc : ∀ j, j < 8 →
      (inputs j).resetN = true ∧ (inputs j).csN = false ∧ sr (inputs j) = true)
    (hack : ∀ j, j < 8 → ack (stateAt inputs s j) (inputs j) = false) :
    (∀ j, j < 8 → bitAt (stateAt inputs s j).tx 7 = bitAt b (7 - j)) ∧
      AfterByte (stateAt inputs s 8) a b := by
  have e1 : stateAt inputs s 1 = step (stateAt inputs s 0) (inputs 0) := stateAt_succ _ _ 0
  have e2 : stateAt inputs s 2 = step (stateAt inputs s 1) (inputs 1) := stateAt_succ _ _ 1
  have e3 : stateAt inputs s 3 = step (stateAt inputs s 2) (inputs 2) := stateAt_succ _ _ 2
  have e4 : stateAt inputs s 4 = step (stateAt inputs s 3) (inputs 3) := stateAt_succ _ _ 3
  have e5 : stateAt inputs s 5 = step (stateAt inputs s 4) (inputs 4) := stateAt_succ _ _ 4
  have e6 : stateAt inputs s 6 = step (stateAt inputs s 5) (inputs 5) := stateAt_succ _ _ 5
  have e7 : stateAt inputs s 7 = step (stateAt inputs s 6) (inputs 6) := stateAt_succ _ _ 6
  have e8 : stateAt inputs s 8 = step (stateAt inputs s 7) (inputs 7) := stateAt_succ _ _ 7
  have h0 : SendingN (stateAt inputs s 0) a b 0 := h
  have h1 : SendingN (stateAt inputs s 1) a b 1 := by
    rw [e1]
    exact sending_step _ _ _ _ 0 h0 (hcyc 0 (by decide)).1 (hcyc 0 (by decide)).2.1
      (hcyc 0 (by decide)).2.2 (hack 0 (by decide)) (by rw [h0.bitc_eq]; decide)
  have h2 : SendingN (stateAt inputs s 2) a b 2 := by
    rw [e2]
    exact sending_step _ _ _ _ 1 h1 (hcyc 1 (by decide)).1 (hcyc 1 (by decide)).2.1
      (hcyc 1 (by decide)).2.2 (hack 1 (by decide)) (by rw [h1.bitc_eq]; decide)
  have h3 : SendingN (stateAt inputs s 3) a b 3 := by
    rw [e3]
    exact sending_step _ _ _ _ 2 h2 (hcyc 2 (by decide)).1 (hcyc 2 (by decide)).2.1
      (hcyc 2 (by decide)).2.2 (hack 2 (by decide)) (by rw [h2.bitc_eq]; decide)
  have h4 : SendingN (stateAt inputs s 4) a b 4 := by
    rw [e4]
    exact sending_step _ _ _ _ 3 h3 (hcyc 3 (by decide)).1 (hcyc 3 (by decide)).2.1
      (hcyc 3 (by decide)).2.2 (hack 3 (by decide)) (by rw [h3.bitc_eq]; decide)
  have h5 : SendingN (stateAt inputs s 5) a b 5 := by
    rw [e5]
    exact sending_step _ _ _ _ 4 h4 (hcyc 4 (by decide)).1 (hcyc 4 (by decide)).2.1
      (hcyc 4 (by decide)).2.2 (hack 4 (by decide)) (by rw [h4.bitc_eq]; decide)
  have h6 : SendingN (stateAt inputs s 6) a b 6 := by
    rw [e6]
    exact sending_step _ _ _ _ 5 h5 (hcyc 5 (by decide)).1 (hcyc 5 (by decide)).2.1
      (hcyc 5 (by decide)).2.2 (hack 5 (by decide)) (by rw [h5.bitc_eq]; decide)
  have h7 : SendingN (stateAt inputs s 7) a b 7 := by
    rw [e7]
    exact sending_step _ _ _ _ 6 h6 (hcyc 6 (by decide)).1 (hcyc 6 (by decide)).2.1
      (hcyc 6 (by decide)).2.2 (hack 6 (by decide)) (by rw [h6.bitc_eq]; decide)
  have hfin := sending_finish (stateAt inputs s 7) (inputs 7) a b h7
    (hcyc 7 (by decide)).1 (hcyc 7 (by decide)).2.1 (hcyc 7 (by decide)).2.2
    (hack 7 (by decide))
  refine ⟨?_, ?_⟩
  · intro j hj
    have htx : (stateAt inputs s j).tx = shifted b j :=
      match j, hj with
      | 0, _ => h0.tx_eq
      | 1, _ => h1.tx_eq
      | 2, _ => h2.tx_eq
      | 3, _ => h3.tx_eq
      | 4, _ => h4.tx_eq
      | 5, _ => h5.tx_eq
      | 6, _ => h6.tx_eq
      | 7, _ => h7.tx_eq
      | _ + 8, h => absurd h (by omega)
    rw [htx]
    exact shifted_bit b ⟨j, hj⟩
  · rw [e8]
    exact hfin

/-! ## The slot after a byte: request next cycle, byte two cycles later -/

/-- After the eighth `SR` the machine holds the read request (`rd`), the loaded
address and an empty response slot.  Two idle cycles latch `rack` and `rd_val`
and step the address, leaving the next data byte loaded. -/
theorem read_slot_step (t : State) (i8 i9 : Input) (a : BitVec 16) (b : BitVec 8)
    (h : AfterByte t a b)
    (h8r : i8.resetN = true) (h8c : i8.csN = false) (h8s : sr i8 = false)
    (h8h : i8.hland = false) (h8d : i8.rdData = false)
    (h9r : i9.resetN = true) (h9c : i9.csN = false) (h9s : sr i9 = false) :
    Sending (step (step t i8) i9) (a + 1) i8.rdVal := by
  obtain ⟨hphase, hisrd, hbitc, htx0, haddr, hwr, hrdA, hrack⟩ := h
  have hcomp : HostCmd.completing (t.toHostCmd 0#8) i8.toHostCmd = false := by
    show (sr i8 && ((t.toHostCmd 0#8).bitc == 7)) = false
    rw [show ((t.toHostCmd 0#8).bitc == 7) = false from
      beq_eq_false_iff_ne.mpr (by simp [hbitc])]
    simp
  have hrd8 : (step t i8).rd = false := by
    show HostCmd.rdNext (t.toHostCmd 0#8) i8.toHostCmd = false
    rw [HostCmd.rdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hrack8 : (step t i8).rack = true := by
    rw [rack_set _ _ h8r, hrdA, h8d]
    rfl
  have hrackv8 : (step t i8).rackv = i8.rdVal := rackv_sample _ _ h8r
  have haddr8 : (step t i8).addr = a := by
    have hnoack : ack t i8 = false := by rw [ack, hrack, h8h]; rfl
    rw [addr_holds t i8 hwr hnoack h8r (by rw [hphase]; decide)
      (by rw [hphase]; decide), haddr]
  have hphase8 : (step t i8).phase = HostCmd.ST_DATA := by
    show HostCmd.phaseNext (t.toHostCmd 0#8) i8.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hisrd8 : (step t i8).isRd = true := by
    show HostCmd.isRdNext (t.toHostCmd 0#8) i8.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hbitc8 : (step t i8).bitc = 0 := by
    show HostCmd.bitcNext (t.toHostCmd 0#8) i8.toHostCmd = 0
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hwr8 : (step t i8).wr = false := by
    show HostCmd.wrNext (t.toHostCmd 0#8) i8.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hcomp9 : HostCmd.completing ((step t i8).toHostCmd 0#8) i9.toHostCmd = false := by
    show (sr i9 && (((step t i8).toHostCmd 0#8).bitc == 7)) = false
    rw [show (((step t i8).toHostCmd 0#8).bitc == 7) = false from
      beq_eq_false_iff_ne.mpr (by simp [hbitc8])]
    simp
  have hphase9 : (step (step t i8) i9).phase = HostCmd.ST_DATA := by
    show HostCmd.phaseNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hisrd9 : (step (step t i8) i9).isRd = true := by
    show HostCmd.isRdNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hbitc9 : (step (step t i8) i9).bitc = 0 := by
    show HostCmd.bitcNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = 0
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have htx9 : (step (step t i8) i9).tx = i8.rdVal := by
    rw [tx_load _ _ h9r h9c (by rw [ack, hrack8]; rfl) (Or.inl h9s),
      ack_value _ _ hrack8, hrackv8]
  have haddr9 : (step (step t i8) i9).addr = a + 1 := by
    show HostCmd.addrNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = a + 1
    rw [HostCmd.addrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hwr9 : (step (step t i8) i9).wr = false := by
    show HostCmd.wrNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hrd9 : (step (step t i8) i9).rd = false := by
    show HostCmd.rdNext ((step t i8).toHostCmd 0#8) i9.toHostCmd = false
    rw [HostCmd.rdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  have hrack9 : (step (step t i8) i9).rack = false := by
    rw [rack_set _ _ h9r, hrd8]
    rfl
  exact ⟨hphase9, hisrd9, hbitc9, htx9, haddr9, hwr9, hrd9, hrack9⟩

/-- One data byte of a read burst plus the two idle cycles that follow it: the
eight samples, and the next data byte loaded with the `rd_val` of the request
cycle. -/
theorem read_slot (inputs : Nat → Input) (t : State) (a : BitVec 16) (b : BitVec 8)
    (h : Sending t a b)
    (hcyc : ∀ j, j < 10 → (inputs j).resetN = true ∧ (inputs j).csN = false)
    (hsr : ∀ j, j < 8 → sr (inputs j) = true)
    (hidle : ∀ j, 8 ≤ j → j < 10 → sr (inputs j) = false)
    (hack : ∀ j, j < 10 → ack (stateAt inputs t j) (inputs j) = false)
    (hland : (inputs 8).hland = false) (hrd : (inputs 8).rdData = false) :
    (∀ j, j < 8 → bitAt (stateAt inputs t j).tx 7 = bitAt b (7 - j)) ∧
      Sending (stateAt inputs t 10) (a + 1) ((inputs 8).rdVal) := by
  have hbyte := read_byte_msb inputs t a b h
    (fun j hj => ⟨(hcyc j (by omega)).1, (hcyc j (by omega)).2, hsr j hj⟩)
    (fun j hj => hack j (by omega))
  have hstep := read_slot_step (stateAt inputs t 8) (inputs 8) (inputs 9) a b hbyte.2
    (hcyc 8 (by omega)).1 (hcyc 8 (by omega)).2 (hidle 8 (by omega) (by omega)) hland hrd
    (hcyc 9 (by omega)).1 (hcyc 9 (by omega)).2 (hidle 9 (by omega) (by omega))
  refine ⟨hbyte.1, ?_⟩
  rw [show stateAt inputs t 10 = stateAt (fun j => inputs (8 + j)) (stateAt inputs t 8) 2 from
    stateAt_add inputs t 8 2]
  exact hstep

/-! ## The burst: byte `k` is the `rd_val` of the request two cycles earlier -/

/-- The byte clocked out in slot `k` of a read burst.  Slot 0 carries the byte
already in `TX` (the response to the request that opened the data phase); slot
`k+1` carries the `rd_val` sampled in the request cycle that slot `k` ended
with. -/
def sentByte (inputs : Nat → Input) (b0 : BitVec 8) (n0 : Nat) : Nat → BitVec 8
  | 0 => b0
  | k + 1 => (inputs (n0 + 10 * k + 8)).rdVal

/-- A clean read burst.  Each slot has eight `SR` edges and two idle cycles
(SCK at clk/10 or slower; SPEC_V2 §9 requires clk/16, which has more slack), no
acknowledgement lands during a slot, and the request cycle of each byte is not
a data-RAM address.  Then slot `k` starts at `a0 + k` and its eight samples are
the MSB-first bits of `sentByte k`. -/
theorem read_burst_index (inputs : Nat → Input) (initial : State) (n0 : Nat)
    (a0 : BitVec 16) (b0 : BitVec 8) (hstart : Sending (stateAt inputs initial n0) a0 b0)
    (hcyc : ∀ k j, j < 10 →
      (inputs (n0 + 10 * k + j)).resetN = true ∧ (inputs (n0 + 10 * k + j)).csN = false)
    (hsr : ∀ k j, j < 8 → sr (inputs (n0 + 10 * k + j)) = true)
    (hidle : ∀ k j, 8 ≤ j → j < 10 → sr (inputs (n0 + 10 * k + j)) = false)
    (hack : ∀ k j, j < 10 → ack (stateAt inputs initial (n0 + 10 * k + j))
      (inputs (n0 + 10 * k + j)) = false)
    (hlandl : ∀ k, (inputs (n0 + 10 * k + 8)).hland = false)
    (hrd : ∀ k, (inputs (n0 + 10 * k + 8)).rdData = false) :
    ∀ k, Sending (stateAt inputs initial (n0 + 10 * k))
        (a0 + BitVec.ofNat 16 k) (sentByte inputs b0 n0 k) ∧
      (∀ j, j < 8 → bitAt (stateAt inputs initial (n0 + 10 * k + j)).tx 7 =
        bitAt (sentByte inputs b0 n0 k) (7 - j)) := by
  intro k
  induction k with
  | zero =>
    have h := read_slot (fun j => inputs (n0 + 0 + j)) (stateAt inputs initial (n0 + 0)) a0 b0
      hstart
      (fun j hj => by simpa using hcyc 0 j (by omega))
      (fun j hj => by simpa using hsr 0 j hj)
      (fun j hj hj' => by simpa using hidle 0 j hj hj')
      (fun j hj => by
        rw [← stateAt_add inputs initial (n0 + 0) j]
        simpa using hack 0 j (by omega))
      (by simpa using hlandl 0) (by simpa using hrd 0)
    refine ⟨by simpa [sentByte] using hstart, fun j hj => ?_⟩
    have hb := h.1 j hj
    rw [← stateAt_add inputs initial (n0 + 0) j] at hb
    simpa [sentByte] using hb
  | succ k ih =>
    obtain ⟨ihsend, _ihbits⟩ := ih
    have h := read_slot (fun j => inputs (n0 + 10 * k + j))
      (stateAt inputs initial (n0 + 10 * k)) (a0 + BitVec.ofNat 16 k)
      (sentByte inputs b0 n0 k) ihsend
      (fun j hj => hcyc k j (by omega))
      (fun j hj => hsr k j hj)
      (fun j hj hj' => hidle k j hj hj')
      (fun j hj => by
        rw [← stateAt_add inputs initial (n0 + 10 * k) j]
        exact hack k j (by omega))
      (hlandl k) (hrd k)
    have hnext : Sending (stateAt inputs initial (n0 + 10 * (k + 1)))
        (a0 + BitVec.ofNat 16 (k + 1)) (sentByte inputs b0 n0 (k + 1)) := by
      have hsplit : stateAt inputs initial (n0 + 10 * (k + 1)) =
          stateAt (fun j => inputs (n0 + 10 * k + j))
            (stateAt inputs initial (n0 + 10 * k)) 10 := by
        rw [show n0 + 10 * (k + 1) = n0 + 10 * k + 10 from by omega]
        exact stateAt_add inputs initial (n0 + 10 * k) 10
      have haddr : (a0 + BitVec.ofNat 16 k) + 1 = a0 + BitVec.ofNat 16 (k + 1) := by
        rw [BitVec.add_assoc]
        congr 1
        exact (BitVec.ofNat_add k 1).symm
      rw [hsplit, ← haddr]
      exact h.2
    refine ⟨hnext, fun j hj => ?_⟩
    have hb := read_byte_msb (fun i => inputs (n0 + 10 * (k + 1) + i))
      (stateAt inputs initial (n0 + 10 * (k + 1))) _ _ hnext
      (fun i hi => ⟨(hcyc (k + 1) i (by omega)).1, (hcyc (k + 1) i (by omega)).2,
        hsr (k + 1) i hi⟩)
      (fun i hi => by
        rw [← stateAt_add inputs initial (n0 + 10 * (k + 1)) i]
        exact hack (k + 1) i (by omega))
    have hb1 := hb.1 j hj
    rw [← stateAt_add inputs initial (n0 + 10 * (k + 1)) j] at hb1
    exact hb1

/-! ## The data-RAM landing is the byte clocked out

SPEC_V2 §9: a data RAM read issued in `R` becomes a host request; served in
`s`, its byte loads `TX` at the end of `s+1`.  The service contract (the arbiter
delivers the byte of the requested address within the window before the next
`SR`) is an interface premise: `hland`/`hland_d` are inputs of this cut.  Here
we prove that a landing loads `TX` with `hland_d`, that `TX` holds it across the
idle cycles, and that the byte clocked out is `hland_d`. -/

/-- A data-RAM landing loads `TX` with `hland_d` and steps the address. -/
theorem ram_landing_sending (t : State) (i : Input) (a : BitVec 16) (b : BitVec 8)
    (c : BitVec 8) (h : Sending t a b) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hland : i.hland = true) (hd : i.hlandD = c) (hnosr : sr i = false) :
    Sending (step t i) (a + 1) c := by
  obtain ⟨hphase, hisrd, hbitc, htx0, haddr, hwr, hrdA, hrack⟩ := h
  have hcomp : HostCmd.completing (t.toHostCmd 0#8) i.toHostCmd = false := by
    show (sr i && ((t.toHostCmd 0#8).bitc == 7)) = false
    rw [show ((t.toHostCmd 0#8).bitc == 7) = false from
      beq_eq_false_iff_ne.mpr (by simp [hbitc])]
    simp
  have htx' : (step t i).tx = c := by
    rw [tx_load _ _ hreset hcs (by rw [ack, hrack, hland]; rfl) (Or.inl hnosr),
      ack_value_ram _ _ hrack, hd]
  refine ⟨?_, ?_, ?_, htx', ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (t.toHostCmd 0#8) i.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.isRdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.bitcNext (t.toHostCmd 0#8) i.toHostCmd = 0
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.addrNext (t.toHostCmd 0#8) i.toHostCmd = a + 1
    rw [HostCmd.addrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.wrNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rdNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rackNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rackNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption

/-- A `Sending` state is preserved across an idle cycle (no `SR`, no landing). -/
theorem sending_frame (t : State) (i : Input) (a : BitVec 16) (b : BitVec 8)
    (h : Sending t a b) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hnosr : sr i = false) (hnoack : ack t i = false) : Sending (step t i) a b := by
  obtain ⟨hphase, hisrd, hbitc, htx0, haddr, hwr, hrdA, hrack⟩ := h
  have hcomp : HostCmd.completing (t.toHostCmd 0#8) i.toHostCmd = false := by
    show (sr i && ((t.toHostCmd 0#8).bitc == 7)) = false
    rw [show ((t.toHostCmd 0#8).bitc == 7) = false from
      beq_eq_false_iff_ne.mpr (by simp [hbitc])]
    simp
  have htx' : (step t i).tx = b := by
    rw [tx_holds _ _ hreset hcs hnosr hnoack]
    exact htx0
  refine ⟨?_, ?_, ?_, htx', ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (t.toHostCmd 0#8) i.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.isRdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.bitcNext (t.toHostCmd 0#8) i.toHostCmd = 0
    rw [HostCmd.bitcNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.addrNext (t.toHostCmd 0#8) i.toHostCmd = a
    rw [HostCmd.addrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.wrNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.wrNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rdNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rdNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption
  · show HostCmd.rackNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rackNext]
    simp_all [HostCmd.addrInc, ack] <;> try assumption

/-- The state holds across a range of idle cycles. -/
theorem sending_frame_range (inputs : Nat → Input) (initial : State) (m n : Nat)
    (a : BitVec 16) (b : BitVec 8) (hmn : m ≤ n) (h : Sending (stateAt inputs initial m) a b)
    (hgap : ∀ j, m ≤ j → j < n → (inputs j).resetN = true ∧ (inputs j).csN = false ∧
      sr (inputs j) = false ∧ ack (stateAt inputs initial j) (inputs j) = false) :
    Sending (stateAt inputs initial n) a b := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have hs : Sending (stateAt inputs initial (m + d)) a b :=
      ih (by omega) (fun j hj hj' => hgap j hj (by omega))
    have e : stateAt inputs initial (m + (d + 1)) =
        step (stateAt inputs initial (m + d)) (inputs (m + d)) := by
      rw [show m + (d + 1) = (m + d) + 1 from by omega]
      exact stateAt_succ _ _ (m + d)
    rw [e]
    exact sending_frame _ _ _ _ hs (hgap (m + d) (by omega) (by omega)).1
      (hgap (m + d) (by omega) (by omega)).2.1
      (hgap (m + d) (by omega) (by omega)).2.2.1
      (hgap (m + d) (by omega) (by omega)).2.2.2

/-- The data-RAM byte lands within the service window, `TX` holds it, and the
byte clocked out is `hland_d`.  The RAM service contract is the premise that the
landing byte is the RAM byte of the requested address: `hland`/`hland_d` are
inputs of this cut, and `sending_frame_range` carries the loaded byte from the
landing cycle to the first `SR` of its slot. -/
theorem ram_byte_msb (inputs : Nat → Input) (initial : State) (L n0 : Nat)
    (a : BitVec 16) (b : BitVec 8) (c : BitVec 8)
    (hL : Sending (stateAt inputs initial L) a b)
    (hresetL : (inputs L).resetN = true) (hcsL : (inputs L).csN = false)
    (hland : (inputs L).hland = true) (hd : (inputs L).hlandD = c)
    (hnosr : sr (inputs L) = false) (hl : L + 1 ≤ n0)
    (hgap : ∀ j, L + 1 ≤ j → j < n0 → (inputs j).resetN = true ∧ (inputs j).csN = false ∧
      sr (inputs j) = false ∧ ack (stateAt inputs initial j) (inputs j) = false)
    (hcyc : ∀ j, j < 8 →
      (inputs (n0 + j)).resetN = true ∧ (inputs (n0 + j)).csN = false ∧
        sr (inputs (n0 + j)) = true)
    (hack : ∀ j, j < 8 → ack (stateAt inputs initial (n0 + j)) (inputs (n0 + j)) = false) :
    (∀ j, j < 8 → bitAt (stateAt inputs initial (n0 + j)).tx 7 = bitAt c (7 - j)) ∧
      (stateAt inputs initial (n0 + 8)).rd = true := by
  have hlanded : Sending (stateAt inputs initial (L + 1)) (a + 1) c := by
    have hs : stateAt inputs initial (L + 1) = step (stateAt inputs initial L) (inputs L) :=
      stateAt_succ _ _ L
    rw [hs]
    exact ram_landing_sending _ _ _ _ c hL hresetL hcsL hland hd hnosr
  have hheld : Sending (stateAt inputs initial n0) (a + 1) c :=
    sending_frame_range inputs initial (L + 1) n0 (a + 1) c hl hlanded hgap
  have hbyte := read_byte_msb (fun j => inputs (n0 + j)) (stateAt inputs initial n0)
    (a + 1) c hheld hcyc (fun j hj => by
      rw [← stateAt_add inputs initial n0 j]
      exact hack j hj)
  refine ⟨fun j hj => ?_, AfterByte.rd_eq hbyte.2⟩
  have hb := hbyte.1 j hj
  rw [← stateAt_add inputs initial n0 j] at hb
  exact hb

/-! ## The host register-read map (`rd_val`)

The five register blocks of ISA_TABLES_V2's host map, at 0x2400 (CTRL), 0x2410
(LRT), 0x2440 (TRT), 0x2450 (SRT) and 0x2460 (DBG).  Everything else -- program
memory, the data RAM, the configuration window and unmapped addresses -- reads
zero (SPEC_V2 §9: configuration registers are write-only and read 0, D14). -/

/-- Every host-visible state signal a read can observe, as a free input. -/
structure Regs where
  runG : Bool
  cwOverrun : Bool
  memhaz : Bool
  conflict : Bool
  irqen : BitVec 2
  inb : BitVec 8
  outb : BitVec 8
  outv : Bool
  inv : Bool
  lPh : BitVec 64
  lHeld : BitVec 4
  lFired : BitVec 12
  lSp : BitVec 4
  lRen : BitVec 4
  lArm : BitVec 4
  lRun : BitVec 4
  lComm : BitVec 16
  lStaged : BitVec 16
  lIn : BitVec 8
  lCap : BitVec 20
  lTapmiss : BitVec 4
  tPc : BitVec 48
  tOvr : BitVec 6
  tLate : BitVec 6
  tEn : BitVec 6
  tArmed : BitVec 6
  tRunning : BitVec 6
  tReady : BitVec 6
  sPos : BitVec 24
  sStarved : BitVec 2
  sBidx : BitVec 6
  freeze : Bool
  men : Bool
  replay : Bool
  cen : Bool
  misr : BitVec 32
  emask : BitVec 13
  rlv : BitVec 13
  accA : BitVec 8
  accN : Bool
  accC : Bool
  accZ : Bool
  fl : BitVec 16
  cRv : BitVec 2
  cXv : BitVec 2
  xt : BitVec 6
  cFpc : BitVec 16
  deriving DecidableEq, Repr

/-- `MD_VERSION` of `src/md2_defs.vh`, the low byte `ID` reads.  The adapter
requires the elaborated constant to be this value. -/
abbrev mdVersion : BitVec 8 := 2

/-- A one-bit value from a Boolean (the `{7'd0, flag}` shape). -/
def bv (b : Bool) : BitVec 1 := if b then 1 else 0

/-- `n` bits of `x` starting at bit `off`. -/
def sliceAt {w : Nat} (x : BitVec w) (off : Nat) (n : Nat) : BitVec n :=
  BitVec.setWidth n (x >>> off)

/-- `n` bits of `x` starting at the 32-bit bit offset `off`: the shape of the
elaborated dynamic part-selects, whose index is computed on a 32-bit bus. -/
def sliceOff {w : Nat} (x : BitVec w) (off : BitVec 32) (n : Nat) : BitVec n :=
  BitVec.setWidth n (x >>> off.toNat)

/-- A constant multiply on the 32-bit index bus, spelled as shifts and adds so
that the specification and the elaborated cells share one arithmetic shape.
The adapter requires every `$mul` in the `rd_val` cone to be this form. -/
def mulC (k : Nat) (x : BitVec 32) : BitVec 32 :=
  match k with
  | 2 => x <<< 1
  | 3 => x + (x <<< 1)
  | 4 => x <<< 2
  | 5 => x + (x <<< 2)
  | 8 => x <<< 3
  | 12 => (x <<< 2) + (x <<< 3)
  | 16 => x <<< 4
  | _ => x

/-- `ERRSUM`: bits 0..6 are any LATE, any OVR, any TAPMISS, any STARVED,
CONFLICT, MEMHAZ, CWOVR (ISA_TABLES_V2, CTRL 0x08). -/
def errSum (r : Regs) : BitVec 8 :=
  (0 : BitVec 1) ++ bv r.cwOverrun ++ bv r.memhaz ++ bv r.conflict ++
    bv (r.sStarved != 0) ++ bv (r.lTapmiss != 0) ++ bv (r.tOvr != 0) ++ bv (r.tLate != 0)

/-- CTRL block (0x2400, offset 0..0x0F). -/
def ctlVal (o : BitVec 16) (r : Regs) : BitVec 8 :=
  if o == 0 then (0 : BitVec 7) ++ bv r.runG
  else if o == 1 then (0 : BitVec 5) ++ bv r.cwOverrun ++ bv r.memhaz ++ bv r.conflict
  else if o == 2 then (0 : BitVec 6) ++ r.irqen
  else if o == 4 then r.inb
  else if o == 5 then r.outb
  else if o == 6 then (0 : BitVec 6) ++ bv r.outv ++ bv r.inv
  else if o == 7 then (0xA0 : BitVec 8) ||| mdVersion
  else if o == 8 then errSum r
  else 0

/-- LRT block (0x2410, four instances of eight bytes). -/
def lrtVal (o : BitVec 16) (r : Regs) : BitVec 8 :=
  let li : BitVec 2 := sliceAt o 3 2
  let k : BitVec 32 := BitVec.setWidth 32 li
  if o &&& 7 == 0 then sliceOff r.lPh (mulC 16 k) 8
  else if o &&& 7 == 1 then sliceOff r.lPh (mulC 16 k + 8) 8
  else if o &&& 7 == 2 then
    bv (bitAt r.lHeld li.toNat) ++ sliceOff r.lFired (mulC 3 k) 3 ++
      bv (bitAt r.lSp li.toNat) ++ bv (bitAt r.lRen li.toNat) ++
      bv (bitAt r.lArm li.toNat) ++ bv (bitAt r.lRun li.toNat)
  else if o &&& 7 == 3 then
    sliceOff r.lComm (mulC 4 k) 4 ++ sliceOff r.lStaged (mulC 4 k) 4
  else if o &&& 7 == 4 then
    (0 : BitVec 1) ++ sliceOff r.lIn (mulC 2 k) 2 ++ sliceOff r.lCap (mulC 5 k) 5
  else if o &&& 7 == 5 then
    (0 : BitVec 7) ++ bv (bitAt r.lTapmiss li.toNat)
  else 0

/-- TRT block (0x2440, six instances of two bytes). -/
def trtVal (o : BitVec 16) (r : Regs) : BitVec 8 :=
  let ti : BitVec 3 := sliceAt o 1 3
  let k : BitVec 32 := BitVec.setWidth 32 ti
  if o &&& 1 == 0 then sliceOff r.tPc (mulC 8 k) 8
  else if o &&& 1 == 1 then
    (0 : BitVec 2) ++ bv (bitAt r.tOvr ti.toNat) ++ bv (bitAt r.tLate ti.toNat) ++
      bv (bitAt r.tEn ti.toNat) ++ bv (bitAt r.tArmed ti.toNat) ++
      bv (bitAt r.tRunning ti.toNat) ++ bv (bitAt r.tReady ti.toNat)
  else 0

/-- SRT block (0x2450, two instances of four bytes). -/
def srtVal (o : BitVec 16) (r : Regs) : BitVec 8 :=
  let si : BitVec 1 := sliceAt o 2 1
  let k : BitVec 32 := BitVec.setWidth 32 si
  if o &&& 3 == 0 then sliceOff r.sPos (mulC 12 k) 8
  else if o &&& 3 == 1 then
    bv (bitAt r.sStarved si.toNat) ++ sliceOff r.sBidx (mulC 3 k) 3 ++
      sliceOff r.sPos (mulC 12 k + 8) 4
  else 0

/-- DBG block (0x2460, one instance of 0x20 bytes). -/
def dbgVal (o : BitVec 16) (r : Regs) : BitVec 8 :=
  if o == 0 then (0 : BitVec 7) ++ bv r.freeze
  else if o == 1 then (0 : BitVec 7) ++ bv r.men
  else if o == 2 then (0 : BitVec 6) ++ bv r.replay ++ bv r.cen
  else if o == 4 then sliceAt r.misr 0 8
  else if o == 5 then sliceAt r.misr 8 8
  else if o == 6 then sliceAt r.misr 16 8
  else if o == 7 then sliceAt r.misr 24 8
  else if o == 8 then sliceAt r.emask 0 8
  else if o == 9 then (0 : BitVec 3) ++ sliceAt r.emask 8 5
  else if o == 10 then r.accA
  else if o == 11 then (0 : BitVec 5) ++ bv r.accN ++ bv r.accC ++ bv r.accZ
  else if o == 12 then sliceAt r.fl 0 8
  else if o == 13 then sliceAt r.fl 8 8
  else if o == 14 then
    (0 : BitVec 3) ++ bv (bitAt r.cRv 0) ++ bv (bitAt r.cXv 0) ++ sliceAt r.xt 0 3
  else if o == 15 then
    (0 : BitVec 3) ++ bv (bitAt r.cRv 1) ++ bv (bitAt r.cXv 1) ++ sliceAt r.xt 3 3
  else if o == 16 then sliceAt r.cFpc 0 8
  else if o == 17 then sliceAt r.cFpc 8 8
  else if o == 18 then sliceAt r.rlv 0 8
  else if o == 19 then (0 : BitVec 3) ++ sliceAt r.rlv 8 5
  else 0

def inCtl (a : BitVec 16) : Bool := a - 0x2400 < 0x10
def inLrt (a : BitVec 16) : Bool := a - 0x2410 < 0x20
def inTrt (a : BitVec 16) : Bool := a - 0x2440 < 0x0C
def inSrt (a : BitVec 16) : Bool := a - 0x2450 < 0x08
def inDbg (a : BitVec 16) : Bool := a - 0x2460 < 0x20

/-- The address is inside one of the five register blocks. -/
def inRegBlock (a : BitVec 16) : Bool :=
  inCtl a || inLrt a || inTrt a || inSrt a || inDbg a

/-- The register-read value of the host map at `a` for the register state `r`.
This is the independent statement of `rd_val`. -/
def rdValSpec (a : BitVec 16) (r : Regs) : BitVec 8 :=
  if inCtl a then ctlVal (a - 0x2400) r
  else if inLrt a then lrtVal (a - 0x2410) r
  else if inTrt a then trtVal (a - 0x2440) r
  else if inSrt a then srtVal (a - 0x2450) r
  else if inDbg a then dbgVal (a - 0x2460) r
  else 0

/-- Outside the five register blocks every read returns zero: program memory,
the data RAM, the configuration window (write-only latches, D14) and unmapped
addresses. -/
theorem zero_outside (a : BitVec 16) (r : Regs) (h : inRegBlock a = false) :
    rdValSpec a r = 0 := by
  simp only [inRegBlock, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp [rdValSpec, h1, h2, h3, h4, h5]

theorem program_reads_zero (a : BitVec 16) (r : Regs) (h : a < 0x1000) :
    rdValSpec a r = 0 :=
  zero_outside a r (by simp only [inRegBlock, inCtl, inLrt, inTrt, inSrt, inDbg]; bv_decide)

theorem data_reads_zero (a : BitVec 16) (r : Regs) (h : a - 0x1000 < 0x800) :
    rdValSpec a r = 0 :=
  zero_outside a r (by simp only [inRegBlock, inCtl, inLrt, inTrt, inSrt, inDbg]; bv_decide)

theorem config_reads_zero (a : BitVec 16) (r : Regs) (h : a - 0x2000 < 0x1E0) :
    rdValSpec a r = 0 :=
  zero_outside a r (by simp only [inRegBlock, inCtl, inLrt, inTrt, inSrt, inDbg]; bv_decide)

/-- `ID` reads `0xA0 | MD_VERSION`, `0xA2` for this design. -/
theorem id_reads_version (r : Regs) : rdValSpec 0x2407 r = 0xA2 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, ctlVal, bv]

/-- `CTRL.STICKY` reads `{CWOVR, MEMHAZ, CONFLICT}` in bits 2..0. -/
theorem sticky_layout (r : Regs) :
    rdValSpec 0x2401 { r with cwOverrun := true, memhaz := false, conflict := false } = 0x04 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, ctlVal, bv]

/-- `CTRL.HOSTSTAT` reads `{OUTV, INV}` in bits 1..0. -/
theorem hoststat_layout (r : Regs) :
    rdValSpec 0x2406 { r with outv := true, inv := false } = 0x02 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, ctlVal, bv]

/-- `CTRL.ERRSUM` bit 6 is CWOVR and bit 0 any LATE. -/
theorem errsum_layout (r : Regs) :
    rdValSpec 0x2408 ({ r with cwOverrun := true, memhaz := false, conflict := false, sStarved := 0, lTapmiss := 0, tOvr := 0, tLate := 1 }) = 0x41 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, ctlVal, errSum, bv]

/-- `DBG.DBG` bit 0 is FREEZE. -/
theorem dbg_layout (r : Regs) :
    rdValSpec 0x2460 { r with freeze := true } = 0x01 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, dbgVal, bv]

/-- A hole inside the CTRL window (`DOORBELL`, offset 3) reads 0. -/
theorem doorbell_reads_zero (r : Regs) : rdValSpec 0x2403 r = 0 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, ctlVal]

/-- `LRT.CTL` reads `{HELD, FIRED, SYNC, REN, ARM, RUN}` of line `li`. -/
theorem lrt_ctl_layout (r : Regs) :
    rdValSpec 0x2412 ({ r with lHeld := 0, lFired := 5, lSp := 0, lRen := 0, lArm := 0, lRun := 0 }) = 0x50 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, lrtVal, sliceAt, bitAt,
    mulC, bv, sliceOff]

/-- `TRT.STAT` bit 5 is OVR for thread `ti`. -/
theorem trt_stat_layout (r : Regs) :
    rdValSpec 0x2441 ({ r with tOvr := 1, tLate := 0, tEn := 0, tArmed := 0, tRunning := 0, tReady := 0 }) = 0x20 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, trtVal, sliceAt, bitAt,
    mulC, bv, sliceOff]

/-- `SRT.POSH` reads `{STARVED, BIDX, POS[11:8]}` of stream `si`. -/
theorem srt_posh_layout (r : Regs) :
    rdValSpec 0x2455 ({ r with sStarved := 2, sBidx := 0, sPos := 0 }) = 0x80 := by
  simp [rdValSpec, inCtl, inLrt, inTrt, inSrt, inDbg, inRegBlock, srtVal, sliceAt, bitAt,
    mulC, bv, sliceOff]

end Metronome.HostRead
