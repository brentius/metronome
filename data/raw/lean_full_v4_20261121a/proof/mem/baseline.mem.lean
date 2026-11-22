import Metronome.Mem

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b
-- Arbiter: the `md2_mem` instance `tt_um_brentius_metronome.u_mem`; the data RAM is the
-- black-box macro behind `tt_um_brentius_metronome.u_dmem`.  The fifteen registers are sampled
-- as `state`, the seventeen inputs as `input`, and the SRAM word as
-- `input.ramWord`.  106 RTL cells, 116 emitted terms.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Metronome.Mem

/-- The elaborated arbiter transition. -/
def rtlStep (state : State) (input : Input) : State :=
  let mem0 := (input.pSel == (0 : BitVec 2))
  let mem1 := input.pWe && mem0
  let mem2 := (input.pSel == (1 : BitVec 2))
  let mem3 := input.pWe && mem2
  let mem4 := (input.pSel == (2 : BitVec 2))
  let mem5 := input.pWe && mem4
  let mem6 := (input.pSel == (3 : BitVec 2))
  let mem7 := input.pWe && mem6
  let mem8 := mem5 || mem7
  let mem9 := (state.ptr + (1 : BitVec 11))
  let mem10 := if mem8 then mem9 else state.ptr
  let mem11 := if mem3 then ((BitVec.truncate 3 (BitVec.ushiftRight input.pData 0)) ++ (BitVec.truncate 8 (BitVec.ushiftRight state.ptr 0))) else mem10
  let mem12 := if mem1 then ((BitVec.truncate 3 (BitVec.ushiftRight state.ptr 8)) ++ (BitVec.truncate 8 (BitVec.ushiftRight input.pData 0))) else mem11
  let mem13 := if input.resetN then mem12 else (0 : BitVec 11)
  let mem14 := (input.sReq != 0)
  let mem15 := !mem14
  let mem16 := (state.req != 0)
  let mem17 := mem15 && mem16
  let mem18 := !input.frz
  let mem19 := mem17 && mem18
  let mem20 := if mem19 then (0 : BitVec 2) else state.req
  let mem21 := if input.pWe then (1 : BitVec 2) else mem20
  let mem22 := if mem5 then (2 : BitVec 2) else mem21
  let mem23 := if input.resetN then mem22 else (0 : BitVec 2)
  let mem24 := if mem5 then state.ptr else state.reqAddr
  let mem25 := if input.resetN then mem24 else (0 : BitVec 11)
  let mem26 := if mem5 then input.pData else state.reqData
  let mem27 := if input.resetN then mem26 else (0 : BitVec 8)
  let mem28 := state.land && state.landRdy
  let mem29 := !input.frz
  let mem30 := mem28 && mem29
  let mem31 := if mem30 then true else state.rdy
  let mem32 := if input.pWe then false else mem31
  let mem33 := if input.resetN then mem32 else false
  let mem34 := !input.frzd
  let mem35 := state.land && mem34
  let mem36 := (mulC 8 (BitVec.setWidth 32 state.landLane))
  let mem37 := (BitVec.truncate 8 (BitVec.ushiftRight input.ramWord (mem36).toNat))
  let mem38 := if mem35 then mem37 else state.dat
  let mem39 := if input.resetN then mem38 else (0 : BitVec 8)
  let mem40 := (state.req == (1 : BitVec 2))
  let mem41 := mem19 && mem40
  let mem42 := if input.frz then state.land else mem41
  let mem43 := if input.resetN then mem42 else false
  let mem44 := if input.frz then state.landLane else (BitVec.truncate 2 (BitVec.ushiftRight state.ptr 0))
  let mem45 := if input.resetN then mem44 else (0 : BitVec 2)
  let mem46 := !input.pWe
  let mem47 := if input.frz then state.landRdy else mem46
  let mem48 := if input.resetN then mem47 else false
  let mem49 := (input.sReq != 0)
  let mem50 := !mem49
  let mem51 := (state.req == (0 : BitVec 2))
  let mem52 := mem50 && mem51
  let mem53 := input.frz || mem52
  let mem54 := mem53 && state.hostQ
  let mem55 := if mem54 then false else state.hostQ
  let mem56 := if input.hSet then true else mem55
  let mem57 := if input.resetN then mem56 else false
  let mem58 := if input.hSet then input.hWr else state.hostWr
  let mem59 := if input.resetN then mem58 else false
  let mem60 := if input.hSet then input.hAddr else state.hostAddr
  let mem61 := if input.resetN then mem60 else (0 : BitVec 11)
  let mem62 := if input.hSet then input.hData else state.hostData
  let mem63 := if input.resetN then mem62 else (0 : BitVec 8)
  let mem64 := !state.hostWr
  let mem65 := mem54 && mem64
  let mem66 := if input.resetN then mem65 else false
  let mem67 := if input.resetN then (BitVec.truncate 2 (BitVec.ushiftRight state.hostAddr 0)) else (0 : BitVec 2)
  { ptr := mem13,
    req := mem23,
    reqAddr := mem25,
    reqData := mem27,
    rdy := mem33,
    dat := mem39,
    land := mem43,
    landLane := mem45,
    landRdy := mem48,
    hostQ := mem57,
    hostWr := mem59,
    hostAddr := mem61,
    hostData := mem63,
    hLand := mem66,
    hLane := mem67 }

/-- The elaborated arbiter outputs (`s_gnt`, the RAM port, the hazard event and
the host landing byte); `p_rdy`, `p_dat` and `h_land` are state. -/
def rtlOuts (state : State) (input : Input) : Outs :=
  let mem_out0 := !input.frz
  let mem_out1 := ((BitVec.truncate 1 (BitVec.ushiftRight input.sReq 0)) != 0) && mem_out0
  let mem_out2 := !((BitVec.truncate 1 (BitVec.ushiftRight input.sReq 0)) != 0)
  let mem_out3 := mem_out2 && ((BitVec.truncate 1 (BitVec.ushiftRight input.sReq 1)) != 0)
  let mem_out4 := !input.frz
  let mem_out5 := mem_out3 && mem_out4
  let mem_out6 := mem_out1 && ((BitVec.truncate 1 (BitVec.ushiftRight input.sWe 0)) != 0)
  let mem_out7 := mem_out5 && ((BitVec.truncate 1 (BitVec.ushiftRight input.sWe 1)) != 0)
  let mem_out8 := mem_out6 || mem_out7
  let mem_out9 := (input.sReq != 0)
  let mem_out10 := !mem_out9
  let mem_out11 := (state.req != 0)
  let mem_out12 := mem_out10 && mem_out11
  let mem_out13 := !input.frz
  let mem_out14 := mem_out12 && mem_out13
  let mem_out15 := (state.req == (2 : BitVec 2))
  let mem_out16 := mem_out14 && mem_out15
  let mem_out17 := mem_out8 || mem_out16
  let mem_out18 := (input.sReq != 0)
  let mem_out19 := !mem_out18
  let mem_out20 := (state.req == (0 : BitVec 2))
  let mem_out21 := mem_out19 && mem_out20
  let mem_out22 := input.frz || mem_out21
  let mem_out23 := mem_out22 && state.hostQ
  let mem_out24 := mem_out23 && state.hostWr
  let mem_out25 := mem_out17 || mem_out24
  let mem_out26 := mem_out1 || mem_out5
  let mem_out27 := mem_out26 || mem_out14
  let mem_out28 := mem_out27 || mem_out23
  let mem_out29 := !mem_out25
  let mem_out30 := mem_out28 && mem_out29
  let mem_out31 := if mem_out15 then state.reqAddr else state.ptr
  let mem_out32 := if mem_out14 then mem_out31 else state.hostAddr
  let mem_out33 := if mem_out5 then (BitVec.truncate 11 (BitVec.ushiftRight input.sAddr 11)) else mem_out32
  let mem_out34 := if mem_out1 then (BitVec.truncate 11 (BitVec.ushiftRight input.sAddr 0)) else mem_out33
  let mem_out35 := mem_out1 && input.s0Word
  let mem_out36 := (BitVec.shiftLeft (1 : BitVec 4) ((BitVec.truncate 2 (BitVec.ushiftRight mem_out34 0))).toNat)
  let mem_out37 := if mem_out35 then (15 : BitVec 4) else mem_out36
  let mem_out38 := if mem_out14 then state.reqData else state.hostData
  let mem_out39 := if mem_out5 then (BitVec.truncate 8 (BitVec.ushiftRight input.sWd 8)) else mem_out38
  let mem_out40 := if mem_out1 then (BitVec.truncate 8 (BitVec.ushiftRight input.sWd 0)) else mem_out39
  let mem_out41 := if mem_out35 then input.s0WWord else ((((BitVec.truncate 8 (BitVec.ushiftRight mem_out40 0)) ++ (BitVec.truncate 8 (BitVec.ushiftRight mem_out40 0))) ++ (BitVec.truncate 8 (BitVec.ushiftRight mem_out40 0))) ++ (BitVec.truncate 8 (BitVec.ushiftRight mem_out40 0)))
  let mem_out42 := (state.req != 0)
  let mem_out43 := input.pWe && mem_out42
  let mem_out44 := !mem_out14
  let mem_out45 := mem_out43 && mem_out44
  let mem_out46 := (mulC 8 (BitVec.setWidth 32 state.hLane))
  let mem_out47 := (BitVec.truncate 8 (BitVec.ushiftRight input.ramWord (mem_out46).toNat))
  { sGnt := ((if mem_out5 then (1 : BitVec 1) else 0) ++ (if mem_out1 then (1 : BitVec 1) else 0)),
    mWe := mem_out25,
    mRen := mem_out30,
    mAddr := (BitVec.truncate 9 (BitVec.ushiftRight mem_out34 2)),
    mBe := mem_out37,
    mWd := mem_out41,
    haz := mem_out45,
    hLandD := mem_out47,
    pRdy := state.rdy,
    pDat := state.dat,
    hLand := state.hLand }

/-! ## The extracted transition is the specification

Each register and each combinational output is proved from its own cone: the
generated function is the elaborated next-state logic, the right-hand side is
`Metronome.Mem`'s independent statement of the specification.  `mem_unfold`
unfolds both sides and `bv_decide` bit-blasts the (small) residual goal. -/

local macro "mem_unfold" : tactic =>
  `(tactic| simp only [rtlStep, rtlOuts, step, outs, ptrNext, reqNext, reqAddrNext,
    reqDataNext, rdyNext, datNext, landNext, landLaneNext, landRdyNext, hostQNext,
    hostWrNext, hostAddrNext, hostDataNext, hLandNext, hLaneNext, mWe, mRen, mAddr,
    mBe, mWd, haz, hLandD, wholeWord, byteAddr, writeByte, grantS0, grantS1, grantP0,
    grantHost, s0Req, s1Req, streamReq, pending, writing, fetching, bit0, bit1, opAl,
    opAh, opW, opR, PS_AL, PS_AH, PS_W, PS_R, RQ_NONE, RQ_FETCH, RQ_WRITE, ptrHigh,
    ptrLow, addrLow, addrHigh, wordAddr, lane, oneHotLane, word4, mulC, byteAt,
    laneShift, BitVec.ushiftRight_zero])

/-- Unfold both sides, split the residual `if`s, and bit-blast each leaf.  The
specification and the RTL write the same equations in different but equivalent
shapes (the reset polarity, `&&` order, a concatenation built bit by bit), so
the proof discharges them case by case rather than by literal matching. -/
local macro "mem_decide" : tactic =>
  `(tactic| (mem_unfold; repeat' split <;> all_goals simp_all <;>
      all_goals try bv_decide))

/-- `PTR`: byte-address loads and the 11-bit wrap step. -/
theorem rtlPtr (state : State) (input : Input) :
    (rtlStep state input).ptr = ptrNext state input := by
  mem_decide

/-- `REQ`: request set, replace and serve-clear. -/
theorem rtlReq (state : State) (input : Input) :
    (rtlStep state input).req = reqNext state input := by
  mem_decide

/-- The write request's address latch. -/
theorem rtlReqAddr (state : State) (input : Input) :
    (rtlStep state input).reqAddr = reqAddrNext state input := by
  mem_decide

/-- The write request's data latch. -/
theorem rtlReqData (state : State) (input : Input) :
    (rtlStep state input).reqData = reqDataNext state input := by
  mem_decide

/-- `RDY`: cleared by a move, set by a landing, held while frozen. -/
theorem rtlRdy (state : State) (input : Input) :
    (rtlStep state input).rdy = rdyNext state input := by
  mem_decide

/-- `D`: the landing byte, captured once from the presented word. -/
theorem rtlDat (state : State) (input : Input) :
    (rtlStep state input).dat = datNext state input := by
  mem_decide

/-- The fetch-served record. -/
theorem rtlLand (state : State) (input : Input) :
    (rtlStep state input).land = landNext state input := by
  mem_decide

/-- The landing's byte lane. -/
theorem rtlLandLane (state : State) (input : Input) :
    (rtlStep state input).landLane = landLaneNext state input := by
  mem_decide

/-- Whether the landing may raise `RDY`. -/
theorem rtlLandRdy (state : State) (input : Input) :
    (rtlStep state input).landRdy = landRdyNext state input := by
  mem_decide

/-- The host request slot's occupancy: a new request overwrites, a served one
clears. -/
theorem rtlHostQ (state : State) (input : Input) :
    (rtlStep state input).hostQ = hostQNext state input := by
  mem_decide

/-- The host request's write flag. -/
theorem rtlHostWr (state : State) (input : Input) :
    (rtlStep state input).hostWr = hostWrNext state input := by
  mem_decide

/-- The host request's address. -/
theorem rtlHostAddr (state : State) (input : Input) :
    (rtlStep state input).hostAddr = hostAddrNext state input := by
  mem_decide

/-- The host request's write byte. -/
theorem rtlHostData (state : State) (input : Input) :
    (rtlStep state input).hostData = hostDataNext state input := by
  mem_decide

/-- The host landing strobe. -/
theorem rtlHLand (state : State) (input : Input) :
    (rtlStep state input).hLand = hLandNext state input := by
  mem_decide

/-- The host landing's byte lane. -/
theorem rtlHLane (state : State) (input : Input) :
    (rtlStep state input).hLane = hLaneNext state input := by
  mem_decide

/-- The extracted transition is the specification's, register by register. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input :=
  State.ext (rtlPtr state input) (rtlReq state input) (rtlReqAddr state input)
    (rtlReqData state input) (rtlRdy state input) (rtlDat state input)
    (rtlLand state input) (rtlLandLane state input) (rtlLandRdy state input)
    (rtlHostQ state input) (rtlHostWr state input) (rtlHostAddr state input)
    (rtlHostData state input) (rtlHLand state input) (rtlHLane state input)

/-! ## The extracted outputs are the specification's -/

/-- `s_gnt = {S1, S0}`. -/
theorem rtlSGnt (state : State) (input : Input) :
    (rtlOuts state input).sGnt = (outs state input).sGnt := by
  mem_decide

/-- The RAM write strobe. -/
theorem rtlMWe (state : State) (input : Input) :
    (rtlOuts state input).mWe = mWe state input := by
  mem_decide

/-- The RAM read strobe. -/
theorem rtlMRen (state : State) (input : Input) :
    (rtlOuts state input).mRen = mRen state input := by
  mem_decide

/-- The RAM word address `a[10:2]`. -/
theorem rtlMAddr (state : State) (input : Input) :
    (rtlOuts state input).mAddr = mAddr state input := by
  mem_decide

/-- The RAM byte-lane enables. -/
theorem rtlMBe (state : State) (input : Input) :
    (rtlOuts state input).mBe = mBe state input := by
  mem_decide

/-- The RAM write data. -/
theorem rtlMWd (state : State) (input : Input) :
    (rtlOuts state input).mWd = mWd state input := by
  mem_decide

/-- The `MEMHAZ` event. -/
theorem rtlHazEvent (state : State) (input : Input) :
    (rtlOuts state input).haz = haz state input := by
  mem_decide

/-- The host landing byte. -/
theorem rtlHLandD (state : State) (input : Input) :
    (rtlOuts state input).hLandD = hLandD state input := by
  mem_decide

/-- `P0.RDY` is the register `p_rdy`, with no extra logic. -/
theorem rtlPRdy (state : State) (input : Input) :
    (rtlOuts state input).pRdy = state.rdy := by
  mem_unfold

/-- `P0.D` is the register `p_dat`. -/
theorem rtlPDat (state : State) (input : Input) :
    (rtlOuts state input).pDat = state.dat := by
  mem_unfold

/-- `h_land` is the arbiter's landing register. -/
theorem rtlHLandOut (state : State) (input : Input) :
    (rtlOuts state input).hLand = state.hLand := by
  mem_unfold

/-- The extracted outputs are the specification's. -/
theorem rtlOuts_eq_outs (state : State) (input : Input) :
    rtlOuts state input = outs state input :=
  Outs.ext (rtlSGnt state input) (rtlMWe state input) (rtlMRen state input)
    (rtlMAddr state input) (rtlMBe state input) (rtlMWd state input)
    (rtlHazEvent state input) (rtlHLandD state input) (rtlPRdy state input)
    (rtlPDat state input) (rtlHLandOut state input)

/-! ## The RTL trace is the specification trace

Every theorem of `Metronome.Mem` is a statement about `stateAt`; this says the
elaborated transition's trace is that trace, so those theorems hold of the RTL.
The cut is unconditional (no well-formedness hypothesis: the equations are
total, and `stateAt_req_ne_three` shows the unused request code is unreachable).
-/

/-- The register state during cycle `n` of the elaborated transition. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => rtlStep (rtlStateAt inputs initial n) (inputs n)

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rtlStateAt, stateAt_succ, ih, rtlStep_eq_step]

/-- The elaborated transition's trace is the specification's, at every cycle. -/
theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  rtlStateAt_eq inputs initial n

/-- The elaborated outputs in cycle `n` are the specification's. -/
theorem rtl_trace_outputs (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlOuts (rtlStateAt inputs initial n) (inputs n) =
      outs (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlOuts_eq_outs]

/-! ## What the elaborated arbiter does -/

/-- At most one requester is served per cycle and the order is S0, S1, P0, host. -/
theorem rtl_trace_grants_exclusive (inputs : Nat → Input) (initial : State)
    (n : Nat) :
    (grantS0 (inputs n) && grantS1 (inputs n)) = false ∧
      (grantS0 (inputs n) && grantP0 (stateAt inputs initial n) (inputs n)) = false ∧
      (grantS0 (inputs n) && grantHost (stateAt inputs initial n) (inputs n)) = false ∧
      (grantS1 (inputs n) && grantP0 (stateAt inputs initial n) (inputs n)) = false ∧
      (grantS1 (inputs n) && grantHost (stateAt inputs initial n) (inputs n)) = false ∧
      (grantP0 (stateAt inputs initial n) (inputs n) &&
        grantHost (stateAt inputs initial n) (inputs n)) = false :=
  grants_exclusive (stateAt inputs initial n) (inputs n)

/-- Bounded wait: a pointer request visible in cycle `n` is served in `n` itself
when no stream requests and the machine is not frozen, so a request set at the
end of `n-1` is served in `n` (`rtl_trace_request_visible`). -/
theorem rtl_trace_p0_served (inputs : Nat → Input) (initial : State) (n : Nat)
    (hpending : pending (stateAt inputs initial n) = true)
    (hstream : streamReq (inputs n) = false) (hfrz : (inputs n).frz = false) :
    grantP0 (stateAt inputs initial n) (inputs n) = true :=
  grantP0_served (stateAt inputs initial n) (inputs n) hpending hstream hfrz

/-- The host is served in the cycle its request is visible when nobody else
wants the port, or in any frozen cycle. -/
theorem rtl_trace_host_served (inputs : Nat → Input) (initial : State) (n : Nat)
    (hhost : (stateAt inputs initial n).hostQ = true)
    (hfree : (inputs n).frz = true ∨
      (streamReq (inputs n) = false ∧ (stateAt inputs initial n).req = RQ_NONE)) :
    grantHost (stateAt inputs initial n) (inputs n) = true :=
  grantHost_served (stateAt inputs initial n) (inputs n) hhost hfree

/-- A pointer move leaves a request pending in the next cycle. -/
theorem rtl_trace_request_visible (inputs : Nat → Input) (initial : State) (n : Nat)
    (hreset : (inputs n).resetN = true)
    (hmove : opAl (inputs n) = true ∨ opAh (inputs n) = true ∨
      opW (inputs n) = true ∨ opR (inputs n) = true) :
    pending (rtlStateAt inputs initial (n + 1)) = true := by
  rw [rtlStateAt_eq]
  exact trace_request_visible inputs initial n hreset hmove

/-- The unused request code is unreachable from a sampled reset. -/
theorem rtl_trace_req_ne_three (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (n : Nat) :
    (rtlStateAt inputs initial (n + 1)).req ≠ 3 := by
  rw [rtlStateAt_eq]
  exact stateAt_req_ne_three inputs initial reset n

/-- A host read served in cycle `n` lands in `n+1`, in the served request's byte
lane, from the word the RAM presents in `n+1`: the landing premise of the host
read cut, in terms of the arbiter's RAM word input. -/
theorem rtl_trace_host_read_lands (inputs : Nat → Input) (initial : State) (n : Nat)
    (hreset : (inputs n).resetN = true)
    (hserved : grantHost (rtlStateAt inputs initial n) (inputs n) = true)
    (hread : (rtlStateAt inputs initial n).hostWr = false) :
    (rtlStateAt inputs initial (n + 1)).hLand = true ∧
      (rtlStateAt inputs initial (n + 1)).hLane =
        lane (rtlStateAt inputs initial n).hostAddr ∧
      hLandD (rtlStateAt inputs initial (n + 1)) (inputs (n + 1)) =
        byteAt (inputs (n + 1)).ramWord (lane (rtlStateAt inputs initial n).hostAddr) := by
  simp only [rtlStateAt_eq] at *
  exact trace_host_read_lands inputs initial n hreset hserved hread

/-- With the SRAM macro contract, that byte is the data-RAM byte at the served
address. -/
theorem rtl_trace_host_read_data (inputs : Nat → Input) (initial : State) (n : Nat)
    (ram : BitVec 9 → BitVec 32)
    (hram : RamContract ram (fun k => (inputs k).ramWord)
      (fun k => mAddr (rtlStateAt inputs initial k) (inputs k)))
    (hreset : (inputs n).resetN = true)
    (hserved : grantHost (rtlStateAt inputs initial n) (inputs n) = true)
    (hread : (rtlStateAt inputs initial n).hostWr = false) :
    hLandD (rtlStateAt inputs initial (n + 1)) (inputs (n + 1)) =
      byteAt (ram (mAddr (rtlStateAt inputs initial n) (inputs n)))
        (lane (rtlStateAt inputs initial n).hostAddr) := by
  simp only [rtlStateAt_eq] at *
  exact trace_host_read_data inputs initial n ram hram hreset hserved hread

/-- A pointer write served in cycle `n` writes the latched address and byte. -/
theorem rtl_trace_p0_write (inputs : Nat → Input) (initial : State) (n : Nat)
    (hserved : grantP0 (stateAt inputs initial n) (inputs n) = true)
    (hwrite : writing (stateAt inputs initial n) = true) :
    mWe (stateAt inputs initial n) (inputs n) = true ∧
      mAddr (stateAt inputs initial n) (inputs n) =
        wordAddr (stateAt inputs initial n).reqAddr ∧
      mBe (stateAt inputs initial n) (inputs n) =
        oneHotLane (lane (stateAt inputs initial n).reqAddr) ∧
      mWd (stateAt inputs initial n) (inputs n) =
        word4 (stateAt inputs initial n).reqData :=
  served_write_ports (stateAt inputs initial n) (inputs n) hserved hwrite

/-- A pointer fetch served in cycle `n` reads `PTR` and makes its byte visible
with `RDY` in cycle `n+2` (§6.2). -/
theorem rtl_trace_p0_read_lands (inputs : Nat → Input) (initial : State) (n : Nat)
    (hserved : grantP0 (rtlStateAt inputs initial n) (inputs n) = true)
    (hfetch : fetching (rtlStateAt inputs initial n) = true)
    (hreset : (inputs n).resetN = true) (hreset1 : (inputs (n + 1)).resetN = true)
    (hnofrz : (inputs n).frz = false) (hnopwe : (inputs n).pWe = false)
    (hnofrz1 : (inputs (n + 1)).frz = false)
    (hnopwe1 : (inputs (n + 1)).pWe = false)
    (hfrzd1 : (inputs (n + 1)).frzd = false) :
    (rtlStateAt inputs initial (n + 2)).rdy = true ∧
      (rtlStateAt inputs initial (n + 2)).dat =
        byteAt (inputs (n + 1)).ramWord (lane (rtlStateAt inputs initial n).ptr) := by
  simp only [rtlStateAt_eq] at *
  exact trace_p0_read_lands inputs initial n hserved hfetch hreset hreset1 hnofrz
    hnopwe hnofrz1 hnopwe1 hfrzd1

/-- A pointer move that replaces an unserved request raises `MEMHAZ` (§9a.2). -/
theorem rtl_trace_haz_replaced (inputs : Nat → Input) (initial : State) (n : Nat)
    (hpwe : (inputs n).pWe = true)
    (hpending : pending (stateAt inputs initial n) = true)
    (hnotserved : grantP0 (stateAt inputs initial n) (inputs n) = false) :
    haz (stateAt inputs initial n) (inputs n) = true :=
  haz_replaced (stateAt inputs initial n) (inputs n) hpwe hpending hnotserved

/-- A move in the cycle its request is served raises no hazard (§9a.2). -/
theorem rtl_trace_no_haz_when_served (inputs : Nat → Input) (initial : State)
    (n : Nat) (hserved : grantP0 (stateAt inputs initial n) (inputs n) = true) :
    haz (stateAt inputs initial n) (inputs n) = false :=
  no_haz_when_served (stateAt inputs initial n) (inputs n) hserved

/-- A frozen cycle serves only the host and the pointer holds (§12.3). -/
theorem rtl_trace_frozen (inputs : Nat → Input) (initial : State) (n : Nat)
    (hreset : (inputs n).resetN = true) (hfrz : (inputs n).frz = true)
    (hpwe : (inputs n).pWe = false) :
    grantS0 (inputs n) = false ∧ grantS1 (inputs n) = false ∧
      grantP0 (stateAt inputs initial n) (inputs n) = false ∧
      grantHost (stateAt inputs initial n) (inputs n) =
        (stateAt inputs initial n).hostQ ∧
      (rtlStateAt inputs initial (n + 1)).ptr = (rtlStateAt inputs initial n).ptr ∧
      (rtlStateAt inputs initial (n + 1)).req = (rtlStateAt inputs initial n).req ∧
      (rtlStateAt inputs initial (n + 1)).rdy = (rtlStateAt inputs initial n).rdy ∧
      mAddr (stateAt inputs initial n) (inputs n) = wordAddr (stateAt inputs initial n).hostAddr := by
  obtain ⟨h0, h1, hp, hgh, hptr, hreq, _hra, _hrd, hrdy, _hland, _hlane, _hlrdy,
    _hdat⟩ := frozen_holds (stateAt inputs initial n) (inputs n) hreset hfrz hpwe
  obtain ⟨_, _, hmaddr⟩ :=
    frozen_access_is_host (stateAt inputs initial n) (inputs n) hreset hfrz hpwe
  simp only [rtlStateAt_eq] at *
  rw [stateAt_succ]
  exact ⟨h0, h1, hp, hgh, hptr, hreq, hrdy, hmaddr⟩

/-- A served S0 edge-capture write covers all four lanes (§12.4). -/
theorem rtl_trace_s0_word_write (inputs : Nat → Input) (initial : State) (n : Nat)
    (hserved : grantS0 (inputs n) = true) (hword : (inputs n).s0Word = true) :
    mBe (stateAt inputs initial n) (inputs n) = 0xF ∧
      mWd (stateAt inputs initial n) (inputs n) = (inputs n).s0WWord :=
  s0_word_write (stateAt inputs initial n) (inputs n) hserved hword

/-! ## Axiom audit -/

#print axioms rtlStep_eq_step
#print axioms rtlOuts_eq_outs
#print axioms rtlStateAt_eq
#print axioms rtl_trace_host_read_lands
#print axioms rtl_trace_p0_read_lands
#print axioms rtl_trace_frozen

end Metronome.Mem
