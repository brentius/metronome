import Metronome.HostCmd

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 92ae050a81550a8fcdafc9fddc301fe87c9c4a9d8b53cb4507b96a96e8c6bf00
-- Host: the `md2_host` instance `tt_um_brentius_metronome.u_host`.  Every register of the
-- command machine is sampled; `cmd` is the history variable for the byte
-- completed in `ST_CMD`, defined from the same nets as the RTL `st`/`is_rd`
-- (6 gates, all of them in those two cones).

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.HostCmd

/-- The elaborated host-link transition.  `state.phase`, `state.bitc`, `state.rx`,
`state.isRd`, `state.addr`, `state.wr`, `state.wdata`, `state.rd` and
`state.rack` are the register values of this cycle. -/
def rtlStep (state : State) (input : Input) : State :=
  let hostcmd0 := !input.csN
  let hostcmd1 := hostcmd0 && input.sck
  let hostcmd2 := !input.sckPrev
  let hostcmd3 := hostcmd1 && hostcmd2
  let hostcmd4 := (state.bitc != (7 : BitVec 3))
  let hostcmd5 := ((byteIn state input) == (2 : BitVec 8))
  let hostcmd6 := ((byteIn state input) == (3 : BitVec 8))
  let hostcmd7 := hostcmd5 || hostcmd6
  let hostcmd8 := if hostcmd7 then (1 : BitVec 3) else (4 : BitVec 3)
  let hostcmd9 := (state.phase == (0 : BitVec 3))
  let hostcmd10 := (state.phase == (1 : BitVec 3))
  let hostcmd11 := (state.phase == (2 : BitVec 3))
  let hostcmd12 := (if hostcmd11 then (3 : BitVec 3) else (if hostcmd10 then (2 : BitVec 3) else (if hostcmd9 then hostcmd8 else state.phase)))
  let hostcmd13 := if hostcmd4 then state.phase else hostcmd12
  let hostcmd14 := if hostcmd3 then hostcmd13 else state.phase
  let hostcmd15 := if input.csN then (0 : BitVec 3) else hostcmd14
  let hostcmd16 := if input.resetN then hostcmd15 else (0 : BitVec 3)
  let hostcmd17 := (state.bitc + (1 : BitVec 3))
  let hostcmd18 := if hostcmd4 then hostcmd17 else (0 : BitVec 3)
  let hostcmd19 := if hostcmd3 then hostcmd18 else state.bitc
  let hostcmd20 := if input.csN then (0 : BitVec 3) else hostcmd19
  let hostcmd21 := if input.resetN then hostcmd20 else (0 : BitVec 3)
  let hostcmd22 := if hostcmd3 then (BitVec.truncate 7 (BitVec.ushiftRight (byteIn state input) 0)) else state.rx
  let hostcmd23 := if input.csN then state.rx else hostcmd22
  let hostcmd24 := if input.resetN then hostcmd23 else (0 : BitVec 7)
  let hostcmd25 := (state.phase == (0 : BitVec 3))
  let hostcmd26 := ((byteIn state input) == (3 : BitVec 8))
  let hostcmd27 := if hostcmd25 then hostcmd26 else state.isRd
  let hostcmd28 := if hostcmd4 then state.isRd else hostcmd27
  let hostcmd29 := if hostcmd3 then hostcmd28 else state.isRd
  let hostcmd30 := if input.csN then state.isRd else hostcmd29
  let hostcmd31 := if input.resetN then hostcmd30 else false
  let hostcmd32 := state.rack || input.hland
  let hostcmd33 := state.wr || hostcmd32
  let hostcmd34 := (state.addr + (1 : BitVec 16))
  let hostcmd35 := if hostcmd33 then hostcmd34 else state.addr
  let hostcmd36 := (state.phase == (1 : BitVec 3))
  let hostcmd37 := (state.phase == (2 : BitVec 3))
  let hostcmd38 := (if hostcmd37 then ((if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if input.mosi then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) else (if hostcmd36 then ((if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight hostcmd35 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if input.mosi then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.rx 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) else hostcmd35))
  let hostcmd39 := if hostcmd4 then hostcmd35 else hostcmd38
  let hostcmd40 := if hostcmd3 then hostcmd39 else hostcmd35
  let hostcmd41 := if input.csN then hostcmd35 else hostcmd40
  let hostcmd42 := if input.resetN then hostcmd41 else (0 : BitVec 16)
  let hostcmd43 := (state.phase == (3 : BitVec 3))
  let hostcmd44 := if state.isRd then false else true
  let hostcmd45 := if hostcmd43 then hostcmd44 else false
  let hostcmd46 := if hostcmd4 then false else hostcmd45
  let hostcmd47 := if hostcmd3 then hostcmd46 else false
  let hostcmd48 := if input.csN then false else hostcmd47
  let hostcmd49 := if input.resetN then hostcmd48 else false
  let hostcmd50 := (state.phase == (3 : BitVec 3))
  let hostcmd51 := if state.isRd then state.wdata else (byteIn state input)
  let hostcmd52 := if hostcmd50 then hostcmd51 else state.wdata
  let hostcmd53 := if hostcmd4 then state.wdata else hostcmd52
  let hostcmd54 := if hostcmd3 then hostcmd53 else state.wdata
  let hostcmd55 := if input.csN then state.wdata else hostcmd54
  let hostcmd56 := if input.resetN then hostcmd55 else (0 : BitVec 8)
  let hostcmd57 := (state.phase == (2 : BitVec 3))
  let hostcmd58 := if state.isRd then true else false
  let hostcmd59 := (state.phase == (3 : BitVec 3))
  let hostcmd60 := (if hostcmd59 then hostcmd58 else (if hostcmd57 then state.isRd else false))
  let hostcmd61 := if hostcmd4 then false else hostcmd60
  let hostcmd62 := if hostcmd3 then hostcmd61 else false
  let hostcmd63 := if input.csN then false else hostcmd62
  let hostcmd64 := if input.resetN then hostcmd63 else false
  let hostcmd65 := !input.rdData
  let hostcmd66 := state.rd && hostcmd65
  let hostcmd67 := if input.resetN then hostcmd66 else false
  let hostcmd68 := (state.phase == (0 : BitVec 3))
  ⟨hostcmd16, hostcmd21, hostcmd24, hostcmd31,
   hostcmd42, hostcmd49, hostcmd56, hostcmd64,
   hostcmd67, (if !input.resetN then (0 : BitVec 8) else if input.csN then state.cmd else if (hostcmd3 && !hostcmd4 && hostcmd68) then (byteIn state input) else state.cmd)⟩

end Metronome.HostCmd

namespace Metronome.HostCmd

set_option linter.unusedSimpArgs false

/-! ## The extracted transition is the specification -/

/-- The extracted next byte state is the specification's. -/
theorem rtlPhase (state : State) (input : Input) :
    (rtlStep state input).phase = (step state input).phase := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next bit count is the specification's. -/
theorem rtlBitc (state : State) (input : Input) :
    (rtlStep state input).bitc = (step state input).bitc := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next receive shift register is the specification's. -/
theorem rtlRx (state : State) (input : Input) :
    (rtlStep state input).rx = (step state input).rx := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next command latch is the specification's. -/
theorem rtlIsRd (state : State) (input : Input) :
    (rtlStep state input).isRd = (step state input).isRd := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next address register is the specification's. -/
theorem rtlAddr (state : State) (input : Input) :
    (rtlStep state input).addr = (step state input).addr := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next write strobe is the specification's. -/
theorem rtlWr (state : State) (input : Input) :
    (rtlStep state input).wr = (step state input).wr := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next write data is the specification's. -/
theorem rtlWdata (state : State) (input : Input) :
    (rtlStep state input).wdata = (step state input).wdata := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next read request is the specification's. -/
theorem rtlRd (state : State) (input : Input) :
    (rtlStep state input).rd = (step state input).rd := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted next read acknowledgement is the specification's. -/
theorem rtlRack (state : State) (input : Input) :
    (rtlStep state input).rack = (step state input).rack := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted command-byte history variable follows the specification. -/
theorem rtlCmd (state : State) (input : Input) :
    (rtlStep state input).cmd = (step state input).cmd := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc]
  bv_decide

/-- The extracted host-link transition matches the independent SPEC_V2 §9
specification for every state and input: all ten register values. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext,
    wdataNext, rdNext, rackNext, cmdNext, completing, sr, byteIn, ackBit, addrInc,
    State.mk.injEq]
  exact ⟨rtlPhase state input, rtlBitc state input, rtlRx state input,
    rtlIsRd state input, rtlAddr state input, rtlWr state input,
    rtlWdata state input, rtlRd state input, rtlRack state input, rtlCmd state input⟩

/-! ## Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-- A write strobe in cycle `n+1` of the extracted trace is in `ST_DATA` and is
not a read. -/
theorem rtl_trace_wr_only_in_data (inputs : Nat → Input) (initial : State) (n : Nat)
    (hwr : (rtlStateAt inputs initial (n + 1)).wr = true) :
    (rtlStateAt inputs initial (n + 1)).phase = ST_DATA ∧
      (rtlStateAt inputs initial (n + 1)).isRd = false := by
  simp only [rtlStateAt_eq] at hwr ⊢
  exact trace_wr_only_in_data inputs initial n hwr

/-- A read transaction of the extracted trace never issues a write strobe. -/
theorem rtl_trace_isRd_no_wr (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (rtlStateAt inputs initial n).isRd = true) :
    (rtlStateAt inputs initial (n + 1)).wr = false := by
  simp only [rtlStateAt_eq] at h ⊢
  rw [stateAt_succ]
  exact isRd_no_wr _ _ h

/-- A write strobe of the extracted trace belongs to a transaction whose command
byte is `0x02`, given the sampled reset that opened the trace. -/
theorem rtl_trace_wr_cmd (inputs : Nat → Input) (initial : State) (n : Nat)
    (reset : (inputs 0).resetN = false)
    (hwr : (rtlStateAt inputs initial (n + 1)).wr = true) :
    (rtlStateAt inputs initial (n + 1)).cmd = CMD_WRITE := by
  simp only [rtlStateAt_eq] at hwr ⊢
  exact trace_wr_cmd inputs initial n reset hwr

/-- A sampled `CS_N` high edge of the extracted trace returns to the command
byte. -/
theorem rtl_trace_cs_high (inputs : Nat → Input) (initial : State) (n : Nat)
    (hcs : (inputs n).csN = true) :
    (rtlStateAt inputs initial (n + 1)).phase = ST_CMD ∧
      (rtlStateAt inputs initial (n + 1)).bitc = 0 := by
  rw [rtlStateAt_eq]
  exact trace_cs_high inputs initial n hcs

/-- A strobe cycle of the extracted trace advances the address by one. -/
theorem rtl_trace_wr_addr_step (inputs : Nat → Input) (initial : State) (n : Nat)
    (hwr : (rtlStateAt inputs initial (n + 1)).wr = true)
    (hreset : (inputs (n + 1)).resetN = true) :
    (rtlStateAt inputs initial (n + 2)).addr =
      (rtlStateAt inputs initial (n + 1)).addr + 1 := by
  simp only [rtlStateAt_eq] at hwr ⊢
  exact trace_wr_addr_step inputs initial n hwr hreset

/-- One strobe cycle plus the following data byte of the extracted trace produce
the next strobe, one address higher. -/
theorem rtl_trace_next_data_strobe (inputs : Nat → Input) (s : State)
    (hphase : (rtlStateAt inputs s 0).phase = ST_DATA)
    (hisrd : (rtlStateAt inputs s 0).isRd = false)
    (hbitc : (rtlStateAt inputs s 0).bitc = 0)
    (hwr : (rtlStateAt inputs s 0).wr = true)
    (hcyc : ∀ j, j < 8 → (inputs j).resetN = true ∧ sr (inputs j) = true)
    (hack : ∀ j, 0 < j → j < 8 → ackBit (rtlStateAt inputs s j) (inputs j) = false) :
    (rtlStateAt inputs s 8).wr = true ∧ (rtlStateAt inputs s 8).addr = s.addr + 1 ∧
      (rtlStateAt inputs s 8).phase = ST_DATA ∧ (rtlStateAt inputs s 8).isRd = false ∧
      (rtlStateAt inputs s 8).bitc = 0 := by
  simp only [rtlStateAt_eq] at hphase hisrd hbitc hwr hack ⊢
  exact next_data_strobe inputs s hphase hisrd hbitc hwr hcyc hack

/-! ## The start of the write data bytes -/

/-- The completing `ST_AL` edge of the extracted trace enters the first data
byte with the loaded address. -/
theorem rtl_al_enters_byteStart (s : State) (input : Input)
    (hphase : s.phase = ST_AL) (hbitc : s.bitc = 7) (hisrd : s.isRd = false)
    (hreset : input.resetN = true) (hcs : input.csN = false)
    (hsck : input.sck = true) (hsp : input.sckPrev = false) :
    ByteStart (rtlStep s input)
      ((addrInc s input >>> 8).truncate 8 ++ byteIn s input) := by
  rw [rtlStep_eq_step]
  exact al_enters_byteStart s input hphase hbitc hisrd hreset hcs hsck hsp

/-- The first data-byte strobe of the extracted trace is at the loaded
address. -/
theorem rtl_first_data_strobe (inputs : Nat → Input) (s : State) (a : BitVec 16)
    (h : ByteStart s a)
    (hcyc : ∀ j, j < 8 → (inputs j).resetN = true ∧ sr (inputs j) = true)
    (hack : ∀ j, j < 8 → ackBit (rtlStateAt inputs s j) (inputs j) = false) :
    (rtlStateAt inputs s 8).wr = true ∧ (rtlStateAt inputs s 8).addr = a ∧
      (rtlStateAt inputs s 8).phase = ST_DATA ∧ (rtlStateAt inputs s 8).isRd = false ∧
      (rtlStateAt inputs s 8).bitc = 0 := by
  simp only [rtlStateAt_eq] at hack ⊢
  exact first_data_strobe inputs s a h hcyc hack

/-- A clean write burst of `k+1` data bytes on the extracted trace: strobe `j`
is at the loaded address plus `j`. -/
theorem rtl_data_strobe_index (inputs : Nat → Input) (s : State) (a : BitVec 16)
    (k : Nat) (h : ByteStart s a)
    (hcyc : ∀ j, j < 8 * (k + 1) → (inputs j).resetN = true ∧ sr (inputs j) = true)
    (hack : ∀ j, j < 8 * (k + 1) → ackBit (rtlStateAt inputs s j) (inputs j) = false) :
    (rtlStateAt inputs s (8 * (k + 1))).wr = true ∧
      (rtlStateAt inputs s (8 * (k + 1))).addr = a + (k : BitVec 16) ∧
      (rtlStateAt inputs s (8 * (k + 1))).phase = ST_DATA ∧
      (rtlStateAt inputs s (8 * (k + 1))).isRd = false ∧
      (rtlStateAt inputs s (8 * (k + 1))).bitc = 0 := by
  simp only [rtlStateAt_eq] at hack ⊢
  exact data_strobe_index inputs s a k h hcyc hack

/-- A write burst stated from the completing `ST_AL` edge of the extracted trace:
the loaded address is the base and strobe `j` is `base + j`. -/
theorem rtl_trace_al_burst_index (inputs : Nat → Input) (initial : State) (n k : Nat)
    (hphase : (rtlStateAt inputs initial n).phase = ST_AL)
    (hbitc : (rtlStateAt inputs initial n).bitc = 7)
    (hisrd : (rtlStateAt inputs initial n).isRd = false)
    (hreset : (inputs n).resetN = true) (hcs : (inputs n).csN = false)
    (hsck : (inputs n).sck = true) (hsp : (inputs n).sckPrev = false)
    (hcyc : ∀ j, j < 8 * (k + 1) →
      (inputs (n + 1 + j)).resetN = true ∧ sr (inputs (n + 1 + j)) = true)
    (hack : ∀ j, j < 8 * (k + 1) →
      ackBit (rtlStateAt inputs initial (n + 1 + j)) (inputs (n + 1 + j)) = false) :
    (rtlStateAt inputs initial (n + 1 + 8 * (k + 1))).wr = true ∧
      (rtlStateAt inputs initial (n + 1 + 8 * (k + 1))).addr =
        ((addrInc (rtlStateAt inputs initial n) (inputs n) >>> 8).truncate 8 ++
          byteIn (rtlStateAt inputs initial n) (inputs n)) + (k : BitVec 16) := by
  simp only [rtlStateAt_eq] at hphase hbitc hisrd hack ⊢
  exact trace_al_burst_index inputs initial n k hphase hbitc hisrd
    hreset hcs hsck hsp hcyc hack

/-! ## The `Metronome.Host` / `Metronome.Compose` composition on the extracted
trace -/

/-- The host cut's `wr`/`bitc` trace on the extracted host-link trace is exactly
the merged trace's `wr`/`bitc`, with `st`/`is_rd` supplied by the registers
instead of being free inputs. -/
theorem rtl_host_stateAt (inputs : Nat → Input) (initial : State) (n : Nat) :
    Host.stateAt (hostInputs inputs initial) (hostInitial initial) n =
      ⟨(rtlStateAt inputs initial n).wr, (rtlStateAt inputs initial n).bitc⟩ := by
  rw [rtlStateAt_eq]
  exact host_stateAt inputs initial n

/-- The configuration input trace whose `hostValid` comes from the extracted
`u_host.wr`. -/
def rtlConfigInputs (rest : Nat → Config.Input) (inCfg live : Nat → Bool)
    (inputs : Nat → Input) (initial : State) : Nat → Config.Input :=
  fun n => { rest n with
             hostValid := Compose.chipHostValid (rtlStateAt inputs initial n).wr
               (inCfg n) (live n) }

/-- Adjacent host writes are spaced on the extracted trace. -/
theorem rtl_spaced_of_hostcmd (rest : Nat → Config.Input) (inCfg live : Nat → Bool)
    (inputs : Nat → Input) (initial : State) (cleared : initial.wr = false) :
    Config.SpacedHost (rtlConfigInputs rest inCfg live inputs initial) := by
  have same : rtlConfigInputs rest inCfg live inputs initial =
      configInputs rest inCfg live inputs initial := by
    funext n
    simp only [rtlConfigInputs, configInputs, topHostValid, rtlStateAt_eq]
  rw [same]
  exact spaced_of_hostcmd rest inCfg live inputs initial cleared

/-- The configuration service contract of `Metronome.Config` with the host
`st`/`is_rd` inputs taken from the extracted `u_host` registers and the write
spacing premise discharged: `st` and `is_rd` are no longer free. -/
theorem rtl_config_host_service_from_hostcmd (rest : Nat → Config.Input)
    (inCfg live : Nat → Bool) (inputs : Nat → Input) (initial : State)
    (cfgInitial : Config.State) (n : Nat) (cleared : initial.wr = false)
    (reset : (rtlConfigInputs rest inCfg live inputs initial 0).resetN = false)
    (active : (rtlConfigInputs rest inCfg live inputs initial (n + 1)).resetN = true)
    (valid : (rtlConfigInputs rest inCfg live inputs initial (n + 1)).hostValid = true) :
    let ins := rtlConfigInputs rest inCfg live inputs initial
    let state := Config.stateAt ins cfgInitial (n + 1)
    let input := ins (n + 1)
    if state.previousWrite then
      (Config.step state input).bankWrite = false ∧
        ((ins (n + 2)).resetN = true →
          Config.HostIssued
            (Config.step (Config.stateAt ins cfgInitial (n + 2)) (ins (n + 2)))
            input.host)
    else Config.HostIssued (Config.step state input) input.host := by
  have same : rtlConfigInputs rest inCfg live inputs initial =
      configInputs rest inCfg live inputs initial := by
    funext n
    simp only [rtlConfigInputs, configInputs, topHostValid, rtlStateAt_eq]
  rw [same] at reset active valid ⊢
  exact config_host_service_from_hostcmd rest inCfg live inputs initial cfgInitial n
    cleared reset active valid

/-- A witness that the sampled-reset premise is needed: a power-up state that
already holds a `0x03` command byte and a full data bit count, with `CS_N` low
and a rising `SCK` edge, produces a write strobe in cycle 1 while `cmd` is
`0x03`.  `rtl_trace_wr_cmd` therefore cannot drop its reset hypothesis. -/
theorem rtl_cmd_premise_witness :
    let initial : State := ⟨ST_DATA, 7, 0, false, 0, false, 0, false, false, CMD_READ⟩
    let inputs : Nat → Input := fun _ => ⟨true, true, false, false, true, false, false⟩
    (stateAt inputs initial 1).wr = true ∧ (stateAt inputs initial 1).cmd = CMD_READ := by
  simp only [stateAt, Metronome.run, step, wrNext, cmdNext, completing, sr, ST_DATA,
    CMD_READ]
  decide

/-! ## Axiom audit

`hostcmd_check.py` records these records and rejects `sorryAx`.  The component
equalities use `bv_decide`; on the current design most of them are decided
without a native certificate, and the larger goals carry the same kind of
per-theorem native certificate axiom as the configuration-address decode and
latch-bank cuts. -/

#print axioms rtlWr
#print axioms rtlAddr
#print axioms rtlStep_eq_step
#print axioms rtlStateAt_eq
#print axioms rtl_trace_wr_cmd
#print axioms rtl_trace_next_data_strobe
#print axioms rtl_al_enters_byteStart
#print axioms rtl_first_data_strobe
#print axioms rtl_data_strobe_index
#print axioms rtl_trace_al_burst_index
#print axioms rtl_host_stateAt
#print axioms rtl_spaced_of_hostcmd
#print axioms rtl_config_host_service_from_hostcmd
#print axioms rtl_cmd_premise_witness

end Metronome.HostCmd
