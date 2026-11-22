import Metronome.SpiPins

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 5119a904ecf062f376f4ca6af796f4ae34ec1e12b899f602c5b868ce5ddd98d6
-- Synchronisers: the top-level registers `s1`, `s2`, `sp` of `tt_um_brentius_metronome`.
-- Host wiring: `u_host` gets `sck = s2[8]`, `sck_p = sp[8]`,
-- `cs_n = s2[9]`, `mosi = s2[10]` and `rst_n = rst_q`; the extraction checks
-- every one of those bit identities and rejects the design otherwise.

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.SpiPins

/-- The elaborated synchroniser transition of `tt_um_brentius_metronome`: the next value of the
registers `s1`, `s2`, `sp`. -/
def rtlStep (state : Sync) (input : Input) : Sync :=
  let spipins0 := if input.resetN then ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.lo 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hi 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) else (0 : BitVec 16)
  let spipins1 := if input.resetN then state.s1 else (0 : BitVec 16)
  let spipins2 := if input.resetN then state.s1 else (0 : BitVec 16)
  ⟨spipins0, spipins1, spipins2⟩

/-- The elaborated `u_host.sck` connection. -/
def hostSck (state : Sync) : Bool := ((BitVec.truncate 1 (BitVec.ushiftRight state.s2 8)) != 0)

/-- The elaborated `u_host.sck_p` connection. -/
def hostSckPrev (state : Sync) : Bool := ((BitVec.truncate 1 (BitVec.ushiftRight state.sp 8)) != 0)

/-- The elaborated `u_host.cs_n` connection. -/
def hostCsN (state : Sync) : Bool := ((BitVec.truncate 1 (BitVec.ushiftRight state.s2 9)) != 0)

/-- The elaborated `u_host.mosi` connection. -/
def hostMosi (state : Sync) : Bool := ((BitVec.truncate 1 (BitVec.ushiftRight state.s2 10)) != 0)

/-- The elaborated host-link input word: the four synchronised pin levels as the
`u_host` instance receives them, plus the free data-RAM inputs. -/
def hostWord (rst : Bool) (state : Sync) (rdData hland : Bool) : HostCmd.Input :=
  ⟨rst, hostSck state, hostSckPrev state, hostCsN state, hostMosi state, rdData, hland⟩

end Metronome.SpiPins

set_option linter.unusedSimpArgs false

namespace Metronome.SpiPins

/-! ## The extracted synchronisers are the specification

Each register equation is proved from its own cone: the generated `rtlStep` is
the elaborated next-state logic of `s1`, `s2`, `sp`, and the right-hand side is
`step`, the SPEC_V2 §2 equation.  Everything is symbolic in the register values
and the sampled input. -/

theorem rtlS1 (state : Sync) (input : Input) :
    (rtlStep state input).s1 = (step state input).s1 := by
  unfold rtlStep step
  by_cases h : input.resetN = true <;> simp [h, raw] <;> bv_decide

theorem rtlS2 (state : Sync) (input : Input) :
    (rtlStep state input).s2 = (step state input).s2 := by
  unfold rtlStep step
  by_cases h : input.resetN = true <;> simp [h]

theorem rtlSp (state : Sync) (input : Input) :
    (rtlStep state input).sp = (step state input).sp := by
  unfold rtlStep step
  by_cases h : input.resetN = true <;> simp [h]

/-- The elaborated synchroniser transition is SPEC_V2 §2's chain. -/
theorem rtlStep_eq_step (state : Sync) (input : Input) :
    rtlStep state input = step state input := by
  exact Sync.ext (rtlS1 state input) (rtlS2 state input) (rtlSp state input)

/-! ## The host-link wiring is the specification's input word

The extraction checks the `u_host` connections bit by bit (`sck = s2[8]`,
`sck_p = sp[8]`, `cs_n = s2[9]`, `mosi = s2[10]`, `rst_n = rst_q`); these
theorems prove that the resulting input word is `hostInput`'s. -/

theorem hostSck_eq (state : Sync) : hostSck state = sck state := by
  unfold hostSck sck bit
  bv_decide

theorem hostSckPrev_eq (state : Sync) : hostSckPrev state = sckPrev state := by
  unfold hostSckPrev sckPrev bit
  bv_decide

theorem hostCsN_eq (state : Sync) : hostCsN state = csN state := by
  unfold hostCsN csN bit
  bv_decide

theorem hostMosi_eq (state : Sync) : hostMosi state = mosi state := by
  unfold hostMosi mosi bit
  bv_decide

/-- The word the host link receives is `hostInput`'s word. -/
theorem hostWord_eq (rst : Bool) (state : Sync) (rdData hland : Bool) :
    hostWord rst state rdData hland = hostInput rst state rdData hland := by
  simp only [hostWord, hostInput, hostSck_eq, hostSckPrev_eq, hostCsN_eq, hostMosi_eq]

/-! ## The extracted synchroniser trace -/

/-- The synchroniser state of the elaborated transition during cycle `n`. -/
def rtlSyncAt (inputs : Nat → Input) (initial : Sync) (n : Nat) : Sync :=
  run (fun s i => rtlStep s i) inputs initial n

theorem rtlSyncAt_succ (inputs : Nat → Input) (initial : Sync) (n : Nat) :
    rtlSyncAt inputs initial (n + 1) = rtlStep (rtlSyncAt inputs initial n) (inputs n) := rfl

/-- The elaborated trace is the specification trace at every cycle. -/
theorem rtlSyncAt_eq (inputs : Nat → Input) (initial : Sync) (n : Nat) :
    rtlSyncAt inputs initial n = syncAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rtlSyncAt_succ, syncAt_succ, ih, rtlStep_eq_step]

/-- The host-link input trace of the pin trace, through the elaborated
synchronisers and wiring. -/
def rtlHostInputs (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) : Nat → HostCmd.Input :=
  fun n => hostWord (rst n) (rtlSyncAt (pinInputs raws rst) initial n) (rdData n) (hland n)

theorem rtlHostInputs_eq (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (n : Nat) :
    rtlHostInputs raws rst initial rdData hland n
      = hostInputs raws rst initial rdData hland n := by
  simp only [rtlHostInputs, hostInputs, rtlSyncAt_eq, hostWord_eq]

/-- Every SCK pin rise is exactly one `SR` in the elaborated trace, and no `SR`
happens without one. -/
theorem rtl_sr_pins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false) (m : Nat) :
    HostCmd.sr (rtlHostInputs raws rst initial rdData hland m) = pinRise raws m := by
  rw [rtlHostInputs_eq]
  exact sr_eq_pinRise raws rst initial rdData hland hinit hreset hcs m

/-- The host command machine's state through the elaborated trace is its state
through the specification trace. -/
theorem rtl_stateAt_eq (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (t : HostCmd.State) (n : Nat) :
    HostCmd.stateAt (rtlHostInputs raws rst initial rdData hland) t n
      = HostCmd.stateAt (hostInputs raws rst initial rdData hland) t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [HostCmd.stateAt_succ, HostCmd.stateAt_succ, ih, rtlHostInputs_eq]

/-- **The headline theorem at the RTL level.**  The elaborated synchronisers,
wired as the chip top wires them, turn a mode-0 SPI write transaction on the
pins into one host write strobe per data byte, with the clocked byte as data and
`{AH, AL} + j` as address, in the cycle after the byte's eighth rising edge. -/
theorem rtl_transaction_strobes (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (first period nbytes : Nat) (bytes : Nat → BitVec 8)
    (hp : 2 ≤ period) (hf : 3 ≤ first) (hnb : 3 ≤ nbytes)
    (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, pinRise raws (srAt first period k) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hbit : ∀ m k, m < nbytes → k < 8 →
      bit (raws (srAt first period (8 * m + k) - 2)) 10 = bit8 (bytes m) (7 - k))
    (hcmd : bytes 0 = HostCmd.CMD_WRITE)
    (hack : ∀ j, HostCmd.ackBit
      (HostCmd.stateAt (hostInputs raws rst initial rdData hland) HostCmd.resetState j)
      (hostInputs raws rst initial rdData hland j) = false) :
    ∀ j, j + 3 < nbytes →
      (HostCmd.stateAt (rtlHostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).wr = true ∧
      (HostCmd.stateAt (rtlHostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).addr =
        (bytes 1 ++ bytes 2) + (j : BitVec 16) ∧
      (HostCmd.stateAt (rtlHostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).wdata = bytes (3 + j) := by
  intro j hj
  simpa only [rtl_stateAt_eq] using
    (transaction_strobes raws rst initial rdData hland first period nbytes bytes hp hf hnb
      hinit hreset hcs hrise honly hbit hcmd hack j hj)

/-! ## Axiom audit

The audit below is read by `spipins_check.py`: a proof that used `sorryAx` is
rejected, and the remaining axioms are recorded with the evidence. -/

#print axioms rtlS1
#print axioms rtlS2
#print axioms rtlSp
#print axioms rtlStep_eq_step
#print axioms hostSck_eq
#print axioms hostSckPrev_eq
#print axioms hostCsN_eq
#print axioms hostMosi_eq
#print axioms hostWord_eq
#print axioms rtlSyncAt_eq
#print axioms rtlHostInputs_eq
#print axioms rtl_sr_pins
#print axioms rtl_stateAt_eq
#print axioms rtl_transaction_strobes

end Metronome.SpiPins
