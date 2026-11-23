/-
# ChipCut: the chip-top wiring and one cycle

Every cut input is built here from the product state and the pin input, using
the cut specs' own output functions (`Line.inSym`, `Line.cap`, `Stream.out`,
`Mem.grants`, `Units` outputs, `Glue.Sources`/`Guards`/`LineGuards`,
`Strobes.opg`, `Moves.pickWord`/`symMask`/`readsOf`, `Debug.Pins.*`,
`Debug.Ctrl.*`, `CoreCtl.freezeStep`, ...).

Two loops are broken the way the RTL breaks them:

* the unit/line/glue *inputs* depend on the move fabric, which depends on the
  cores' outputs, which depend on the guard and source vectors through the
  cores' *inputs*: the guard/source vectors are built first, from
  line/unit/stream/pointer/glue state, never from the move fabric;
* the streams' RAM requests feed the arbiter, whose grants feed the streams'
  `gnt` input; `Stream.req` does not read `gnt`, so a request-only input record
  (`streamReqIn`) is built first.

The host write decode uses the machine's `hwByte`/`hostLocate` map (checked
structurally by the `hostmap` cut) and the host read/response decode uses
`Bridge.Host.regRead`/`regVal`/`ramByte`; those interface functions are the
trusted chip-top glue, recorded as premises in `Proof.lean`.
-/

import Metronome.ChipCut.State

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Metronome.ChipCut

open Metronome

/-- `n` words of width `w`, item `0` in the low bits. -/
def packNs (w : Nat) : (n : Nat) → (Nat → BitVec w) → BitVec (w * n)
  | 0, _ => 0
  | n + 1, f => (f n ++ packNs w n f).cast (by rw [Nat.mul_succ, Nat.add_comm])

/-! ## Reset sample and host interface -/

/-- The reset sample of the chip's active branch (`rst_q && rst_n`). -/
def runRst (s : State) (pin : Machine.PinIn) : Bool := s.rst.rstQ && pin.rstn

/-- The host write the host link issues this cycle (§9). -/
def hwOf (s : State) : Option Machine.HostWr :=
  if s.hostCmd.wr then
    some ⟨s.hostCmd.addr.toNat, s.hostCmd.wdata.toNat,
      Machine.hostLocate s.hostCmd.addr.toNat⟩
  else none

/-- The host configuration write offered to the arbiter (§13.1). -/
def hostCfgOf (s : State) : Option (Nat × Nat) :=
  match hwOf s with
  | some w => if Machine.Config.isCfgAddr w.addr then some (w.addr, w.v) else none
  | none => none

/-- The arbiter's input: the bridge's `cfgIn` (the queue and the host
configuration write) with the RTL's freeze gate on `core_valid`
(`project.v` 145: `cw_pending & ~frz & cw_is_cfg`). -/
def arbIn (s : State) : Config.Input :=
  { Bridge.CfgWrite.cfgIn s.cq (hostCfgOf s) with
    coreValid := s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat &&
      !s.freeze.frz }

/-- One arbiter cycle; its grant/bank-write/next state drive the queue, the
bank and the debug runtime port. -/
def arbStep (s : State) : Config.Result :=
  Config.step s.arb (arbIn s)

/-- The RTL's `cw_drain` (`project.v` 139):
`cw_pending & ~frz & (~cw_is_cfg | cfg_core_issue)`.  It is *not* the arbiter's
`core_issue`: a pending write to a non-configuration address drains (as a
runtime write or with no effect) without the arbiter granting anything. -/
def cwDrain (s : State) : Bool :=
  s.cq.pending && !s.freeze.frz &&
    (!Machine.Config.isCfgAddr s.cq.pendingAddr.toNat || (arbStep s).coreIssue)

/-- A host-map byte write strobe. -/
def hwIsSome (s : State) (blk : String) (inst : Nat) (reg : String) : Bool :=
  (Machine.Util.hwAt (hwOf s) blk inst reg).isSome

/-- The host write data byte. -/
def hwData (s : State) : BitVec 8 := s.hostCmd.wdata

/-! ## Host-map window gates

The RTL decodes two windows with a 16-bit unsigned subtraction; these are the
`a_dat`/`in_data` (`project.v` 83-84) and `a_dbg`/`in_dbg` (107, 118) tests. -/

/-- `a_dat = ha - HA_DATA_BASE` (`project.v` 83). -/
def dataOff (a : BitVec 16) : BitVec 16 := a - 0x1000

/-- `in_data = (a_dat < HSPAN_DATA)` (`project.v` 84). -/
def inData (a : BitVec 16) : Bool := dataOff a < 0x0800

/-- `a_dbg = ha - HA_DBG_BASE` (`project.v` 118). -/
def dbgOff (a : BitVec 16) : BitVec 16 := a - 0x2460

/-- `in_dbg = (a_dbg < HSPAN_DBG)` (`project.v` 107). -/
def inDbg (a : BitVec 16) : Bool := dbgOff a < 0x0020

/-- `w_dbg = h_wr & in_dbg` (`project.v` 123), the host half of the `DBG`
byte strobes. -/
def hwDbg (s : State) : Bool := s.hostCmd.wr && inDbg s.hostCmd.addr

/-! ## Line configuration inverse -/

/-- Pack a machine `LineCfg` back into the cut's byte layout.  `absCfg` of this
is the machine configuration (a decode/encode round trip, stated as a premise in
`Proof.lean`). -/
def lineCfgOf (lc : Machine.LineCfg) : Line.Config where
  inc := BitVec.ofNat 16 lc.inc
  mod := BitVec.ofNat 16 lc.mod
  t0 := BitVec.ofNat 16 lc.t0
  t1 := BitVec.ofNat 16 lc.t1
  t2 := BitVec.ofNat 16 lc.t2
  pre := BitVec.ofNat 16 lc.pre
  wlo := BitVec.ofNat 16 lc.wlo
  whi := BitVec.ofNat 16 lc.whi
  edge := BitVec.ofNat 8 (lc.edgePin + 16 * lc.edgePol + (if lc.wen then 64 else 0) +
    (if lc.follow then 128 else 0))
  t0edge := BitVec.ofNat 8 (lc.t0Pin + 16 * lc.t0Pol + (if lc.t0src then 64 else 0))
  pins := BitVec.ofNat 8 (lc.pina + 16 * lc.pinb)
  snap := BitVec.ofNat 2 lc.snap
  lut0 := BitVec.ofNat 32 lc.lut0
  lut1 := BitVec.ofNat 32 lc.lut1
  hold := BitVec.ofNat 8 (lc.hpin + 16 * (if lc.hlvl then 1 else 0) + 32 * lc.htap +
    (if lc.hen then 128 else 0))

/-- The line's configuration window. -/
def lineCfg (s : State) (l : Nat) : Line.Config :=
  lineCfgOf ((Machine.cfgView s.cont.cfg).lines[l]!)

/-- The static part of a line input (configuration and pin vectors); the
`Input`-valued functions used by the guard/source builders read only these. -/
def lineStaticIn (s : State) (l : Nat) : Line.Input where
  resetN := s.rst.rstQ
  frz := s.freeze.frz
  cfg := lineCfg s l
  lvl := lvlVec s
  rise := riseVec s
  fall := fallVec s
  ctlWe := false
  ctlD := 0
  symWe := false
  symOp := 0
  symD := 0
  phWe := 0
  hCtlWe := false
  hStatWe := false
  hD := 0

/-! ## Stream view and the guard/source builders -/

/-- A minimal stream input for the stream's output functions and its RAM
request; the move/grant fields are dummies and none of those functions reads
them. -/
def streamViewIn (s : State) (k : Nat) : Stream.Input :=
  let cf := (Machine.cfgView s.cont.cfg).streams[k]!
  { resetN := s.rst.rstQ
    frz := s.freeze.frz
    frzd := s.freeze.frzd
    capEn := Strobes.capEn s.dbgCtrl.cen s.dbgCtrl.replay
    capPush := false
    capRec := 0
    replayEn := s.dbgCtrl.replay
    replayApply := false
    replayLate := false
    cfgMode := cf.rx
    cfgMsb := cf.msb
    cfgStart := BitVec.ofNat 11 cf.start
    cfgLen := BitVec.ofNat 12 cf.len
    cfgMark := BitVec.ofNat 12 cf.mark
    adv := false
    rxWe := false
    rxBit := false
    rewind := false
    flush := false
    clrStarved := false
    gnt := false
    rdata := s.cont.ramOut }


/-! ## Indexed access to the small component vectors

`Vector` indexing at a run-time `Nat` would need a proof or an `Inhabited`
instance.  These explicit selectors keep the wiring total. -/

def threadAt (s : State) : Nat → Thread.State
  | 0 => s.threads[0]
  | 1 => s.threads[1]
  | 2 => s.threads[2]
  | 3 => s.threads[3]
  | 4 => s.threads[4]
  | _ => s.threads[5]

def lineAt (s : State) : Nat → Line.State
  | 0 => s.lines[0]
  | 1 => s.lines[1]
  | 2 => s.lines[2]
  | _ => s.lines[3]

def streamAt (s : State) : Nat → Stream.State
  | 0 => s.streams[0]
  | _ => s.streams[1]

def cntAt (s : State) : Nat → Units.Counter.State
  | 0 => s.cnt[0]
  | 1 => s.cnt[1]
  | _ => s.cnt[2]

def shAt (s : State) : Nat → Units.Shifter.State
  | 0 => s.sh[0]
  | _ => s.sh[1]

def lfAt (s : State) : Nat → Units.Lfsr.State
  | 0 => s.lf[0]
  | _ => s.lf[1]

/-- The cycle's global source leaves (SPEC §6). -/
def sourcesOf (s : State) : Glue.Sources where
  fl := s.glue.fl
  pins := pinLvl s
  accA := s.acc.a
  accR := s.acc.r
  shD := (shAt s 1).dr ++ (shAt s 0).dr
  shO := (if Units.Shifter.out (shAt s 1) then (1 : BitVec 1) else 0) ++
    (if Units.Shifter.out (shAt s 0) then (1 : BitVec 1) else 0)
  cnV := ((cntAt s 2).v ++ (cntAt s 1).v) ++ (cntAt s 0).v
  lfS := (lfAt s 1).s ++ (lfAt s 0).s
  pDat := s.p0.dat
  sBit := (if Stream.bitOut false (streamAt s 1) (streamViewIn s 1) then (1 : BitVec 1) else 0) ++
    (if Stream.bitOut true (streamAt s 0) (streamViewIn s 0) then (1 : BitVec 1) else 0)
  sByte := Stream.byteOut false (streamAt s 1) (streamViewIn s 1) ++
    Stream.byteOut true (streamAt s 0) (streamViewIn s 0)
  inB := s.glue.inB

/-- The cycle's global guard leaves (SPEC §7). -/
def guardsOf (s : State) : Glue.Guards where
  fl := s.glue.fl
  shDone := (if Units.Shifter.done (shAt s 1) then (1 : BitVec 1) else 0) ++
    (if Units.Shifter.done (shAt s 0) then (1 : BitVec 1) else 0)
  shOut := (if Units.Shifter.out (shAt s 1) then (1 : BitVec 1) else 0) ++
    (if Units.Shifter.out (shAt s 0) then (1 : BitVec 1) else 0)
  cntZ := (if Units.Counter.zOut (cntAt s 2) then (1 : BitVec 1) else 0) ++
    ((if Units.Counter.zOut (cntAt s 1) then (1 : BitVec 1) else 0) ++
      (if Units.Counter.zOut (cntAt s 0) then (1 : BitVec 1) else 0))
  accZ := s.acc.z
  accC := s.acc.c
  accN := s.acc.n
  lfS := (lfAt s 1).s ++ (lfAt s 0).s
  inv := s.glue.inv
  outv := s.glue.outv
  pRdy := s.p0.rdy
  sEnd := (if Stream.gEnd (streamAt s 1) (streamViewIn s 1) then (1 : BitVec 1) else 0) ++
    (if Stream.gEnd (streamAt s 0) (streamViewIn s 0) then (1 : BitVec 1) else 0)
  sMark := (if Stream.gMark (streamAt s 1) (streamViewIn s 1) then (1 : BitVec 1) else 0) ++
    (if Stream.gMark (streamAt s 0) (streamViewIn s 0) then (1 : BitVec 1) else 0)
  sByte := (if Stream.gByte (streamAt s 1) (streamViewIn s 1) then (1 : BitVec 1) else 0) ++
    (if Stream.gByte (streamAt s 0) (streamViewIn s 0) then (1 : BitVec 1) else 0)
  sBit := (if Stream.bitOut false (streamAt s 1) (streamViewIn s 1) then (1 : BitVec 1) else 0) ++
    (if Stream.bitOut true (streamAt s 0) (streamViewIn s 0) then (1 : BitVec 1) else 0)
  pins := pinLvl s
  lRun := (if s.lines[3].run then (1 : BitVec 1) else 0) ++
    ((if s.lines[2].run then (1 : BitVec 1) else 0) ++
      ((if s.lines[1].run then (1 : BitVec 1) else 0) ++
        (if s.lines[0].run then (1 : BitVec 1) else 0)))

/-- The per-line guard bundles (`g_line`). -/
def lineGuardsOf (s : State) : Glue.LineGuards where
  inn := (Line.inSym s.lines[3] (lineStaticIn s 3)) ++
    ((Line.inSym s.lines[2] (lineStaticIn s 2)) ++
      ((Line.inSym s.lines[1] (lineStaticIn s 1)) ++ (Line.inSym s.lines[0] (lineStaticIn s 0))))
  sp := (if s.lines[3].sp then (1 : BitVec 1) else 0) ++
    ((if s.lines[2].sp then (1 : BitVec 1) else 0) ++
      ((if s.lines[1].sp then (1 : BitVec 1) else 0) ++ (if s.lines[0].sp then (1 : BitVec 1) else 0)))
  pinA := (if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
      ((Machine.cfgView s.cont.cfg).lines[3]!).pina then (1 : BitVec 1) else 0) ++
    ((if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
      ((Machine.cfgView s.cont.cfg).lines[2]!).pina then (1 : BitVec 1) else 0) ++
      ((if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[1]!).pina then (1 : BitVec 1) else 0) ++
        (if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
          ((Machine.cfgView s.cont.cfg).lines[0]!).pina then (1 : BitVec 1) else 0)))
  pinB := (if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
      ((Machine.cfgView s.cont.cfg).lines[3]!).pinb then (1 : BitVec 1) else 0) ++
    ((if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
      ((Machine.cfgView s.cont.cfg).lines[2]!).pinb then (1 : BitVec 1) else 0) ++
      ((if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[1]!).pinb then (1 : BitVec 1) else 0) ++
        (if (Machine.pinView (absChip s).sync (absChip s).dbg).pin
          ((Machine.cfgView s.cont.cfg).lines[0]!).pinb then (1 : BitVec 1) else 0)))

/-! ## Core inputs -/

/-- Core `c`'s input: the thread file, the guard/source vectors, the line-local
vectors and the program-memory output word. -/
def coreIn (s : State) (pin : Machine.PinIn) (c : Nat) : Core.Input where
  resetN := runRst s pin
  frz := s.freeze.frz
  runG := s.glue.runG
  rdata := s.cont.mout[c]!
  tReady := packBools 6 fun t => (threadAt s t).ready
  -- project.v 553: t_core[k] = tc[0], the raw CORE bit, for BOTH core instances; md2_core.v 157
  -- forms mine = C ? t_core : ~t_core (fixed 2026-11-21: was `core == c`, which inverted core 0's
  -- binding; found by the CoreUnits discharge, `coreOf_inverted`).
  tCore := packBools 6 fun t => (Machine.cfgView s.cont.cfg).threads[t]!.core == 1
  tLine := packNs 2 6 fun t => BitVec.ofNat 2 (Machine.cfgView s.cont.cfg).threads[t]!.line
  tPc := packNs 8 6 fun t => (threadAt s t).pc
  tW0c := packNs 6 6 fun t => BitVec.ofNat 6 (Machine.cfgView s.cont.cfg).threads[t]!.w0c
  tW1c := packNs 6 6 fun t => BitVec.ofNat 6 (Machine.cfgView s.cont.cfg).threads[t]!.w1c
  tW0h := packNs 8 6 fun t => BitVec.ofNat 8 (Machine.cfgView s.cont.cfg).threads[t]!.w0h
  tW1h := packNs 8 6 fun t => BitVec.ofNat 8 (Machine.cfgView s.cont.cfg).threads[t]!.w1h
  guards := packBools 64 fun k => Glue.guardAt k (guardsOf s)
  gLine := packBools 20 fun i =>
    Glue.bitAt (Glue.lineGuard (i / 5) (lineGuardsOf s)) (i % 5)
  srcs := pack8s 64 fun k => Glue.srcAt k (sourcesOf s)
  lIn := packNs 2 4 fun l => Line.inSym (lineAt s l) (lineStaticIn s l)
  lCap := packNs 5 4 fun l => Line.cap (lineAt s l)

/-! ## The move fabric -/

/-- The six-slot move-enable vector: slots 0..2 are core 0, 3..5 core 1. -/
def mvEn (s : State) (pin : Machine.PinIn) : BitVec 6 :=
  (Core.out true s.cores[1] (coreIn s pin 1)).mvEn ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvEn

/-- The six-slot destination vector. -/
def mvDst (s : State) (pin : Machine.PinIn) : BitVec 36 :=
  (Core.out true s.cores[1] (coreIn s pin 1)).mvDst ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvDst

/-- The six-slot write-data vector. -/
def mvDat (s : State) (pin : Machine.PinIn) : BitVec 48 :=
  (Core.out true s.cores[1] (coreIn s pin 1)).mvData ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvData

/-- The six-slot source vector, slot order `(core, move)`.  The `MEMHAZ` event
and the `HOST.IN` read are source-side (`c_src`), not destination-side. -/
def mvSrc (s : State) (pin : Machine.PinIn) : BitVec 36 :=
  (Core.out true s.cores[1] (coreIn s pin 1)).mvSrc ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvSrc

/-- The six-slot group vector (`DG_MAP` applied to the destinations). -/
def mvGrp (s : State) (pin : Machine.PinIn) : BitVec 30 := Moves.mapOf (mvDst s pin)

/-- The two cores' `XL`, slot order `(core, move)`. -/
def mvXl (s : State) : BitVec 4 := s.cores[1].xl ++ s.cores[0].xl

/-- The two cores' `XT`. -/
def mvXt (s : State) : BitVec 6 := s.cores[1].xt ++ s.cores[0].xt

/-- The six winner bits of the global move bundle. -/
def mvWin (s : State) (pin : Machine.PinIn) : BitVec 6 :=
  Moves.winBits (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s)

/-- One slot's *valid* bit (`mv_valid`): enabled and its destination has a
group.  The thread `STOP`/`LATE` inputs read this, not the winner bits. -/
def slotValid (s : State) (pin : Machine.PinIn) (q : Nat) : Bool :=
  Machine.Util.bit (Moves.validBits (mvEn s pin) (mvGrp s pin)) q

/-- The picked word of destination `D`'s write group (`pick(OPG)`). -/
def gw (s : State) (pin : Machine.PinIn) (D : BitVec 6) : CoreCtl.GroupWord :=
  Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable D))
    (mvDst s pin) (mvDat s pin)

/-- The strobe `OPG(G, D)`: the winner of `D`'s group writes `D`. -/
def strobe (s : State) (pin : Machine.PinIn) (D : BitVec 6) : Bool :=
  Strobes.opg (mvEn s pin) (mvGrp s pin) (mvDst s pin) (Moves.dgTable D) D

/-- The 15-bit word of the `L.SYM` winners that ran on `line`. -/
def symWord (s : State) (pin : Machine.PinIn) (l : Nat) : BitVec 15 :=
  Moves.hitOr (Moves.symMask (mvWin s pin) (mvGrp s pin) (mvXl s) (BitVec.ofNat 2 l))
    (mvDst s pin) (mvDat s pin)

/-! ## Line inputs -/

/-- A host-map byte index test: the strobe of byte `k` of a register. -/
def byteStrobe (o : Option (Nat × Nat)) (k : Nat) : Bool :=
  match o with
  | some (j, _) => j == k
  | none => false

/-- Line `l`'s full input. -/
def lineIn (s : State) (pin : Machine.PinIn) (l : Nat) : Line.Input where
  resetN := runRst s pin
  frz := s.freeze.frz
  cfg := lineCfg s l
  lvl := lvlVec s
  rise := riseVec s
  fall := fallVec s
  ctlWe := strobe s pin (BitVec.ofNat 6 (53 + l))
  ctlD := BitVec.ofNat 3 (gw s pin (BitVec.ofNat 6 (53 + l))).data.toNat
  symWe := Machine.Util.bit (symWord s pin l) 14
  symOp := Strobes.lineSop (BitVec.truncate 6 (BitVec.ushiftRight (symWord s pin l) 8))
  symD := BitVec.truncate 4 (symWord s pin l)
  -- RTL project.v 520: h_ph_we = {byte-1 strobe, byte-0 strobe} (bit 0 = byte 0).
  phWe := (if byteStrobe (Machine.Util.hwAt (hwOf s) "LRT" l "PHASE") 1 then
      (1 : BitVec 1) else 0) ++
    (if byteStrobe (Machine.Util.hwAt (hwOf s) "LRT" l "PHASE") 0 then
      (1 : BitVec 1) else 0)
  hCtlWe := hwIsSome s "LRT" l "CTL"
  hStatWe := hwIsSome s "LRT" l "STAT"
  hD := hwData s

/-! ## Data-RAM and stream inputs -/

/-- The streams' request words, from the state and the configuration only (no
`gnt`). -/
def streamReq (s : State) (k : Nat) : Stream.Out :=
  -- project.v 461: md2_stream #(.CAP(k == 0 ? 1 : 0)); only S0 has capture/replay (fixed 2026-11-21:
  -- was `true` for every stream; found by the GuardSrc wiring task, `guards_false`/`srcs_false`).
  Stream.out (k == 0) (streamAt s k) (streamViewIn s k)

/-- The two stream request bits, `S0` in bit 0. -/
def sReqV (s : State) : BitVec 2 :=
  (if (streamReq s 1).req then (1 : BitVec 1) else 0) ++
    (if (streamReq s 0).req then (1 : BitVec 1) else 0)

/-- The two stream write bits, `S0` in bit 0. -/
def sWeV (s : State) : BitVec 2 :=
  (if (streamReq s 1).reqWe then (1 : BitVec 1) else 0) ++
    (if (streamReq s 0).reqWe then (1 : BitVec 1) else 0)

/-- The two stream byte addresses, `S0` in the low half. -/
def sAddrV (s : State) : BitVec 22 := (streamReq s 1).reqAddr ++ (streamReq s 0).reqAddr

/-- The two stream write bytes, `S0` in the low half. -/
def sWdV (s : State) : BitVec 16 := (streamReq s 1).reqWdata ++ (streamReq s 0).reqWdata

/-- The data-RAM arbiter input. -/
def memIn (s : State) (pin : Machine.PinIn) : Mem.Input where
  resetN := runRst s pin
  frz := s.freeze.frz
  frzd := s.freeze.frzd
  sReq := sReqV s
  sWe := sWeV s
  sAddr := sAddrV s
  sWd := sWdV s
  s0Word := (streamReq s 0).reqWord
  s0WWord := (streamReq s 0).reqWword
  pWe := (gw s pin 43).we
  pSel := Strobes.p0Sel (gw s pin 43).dst
  pData := (gw s pin 43).data
  hSet := (s.hostCmd.wr || s.hostCmd.rd) && inData s.hostCmd.addr
  hWr := s.hostCmd.wr
  hAddr := HostMap.dataAddr s.hostCmd.addr
  hData := hwData s
  ramWord := s.cont.ramOut

/-- The RAM grant of stream `k` (`S0` and `S1` priorities). -/
def streamGnt (s : State) (pin : Machine.PinIn) (k : Nat) : Bool :=
  if k == 0 then Mem.grantS0 (memIn s pin) else Mem.grantS1 (memIn s pin)

/-- The host's `RAM` landing. -/
def hostLand (s : State) : Bool := s.cont.ramOwner == 4

/-- The record a capture event stores: `{DC, PIN[12:0]}`. -/
def captureRecord (s : State) : BitVec 32 := s.dbgCtrl.dc ++ pinLvl s

/-- The full stream input. -/
def streamIn (s : State) (pin : Machine.PinIn) (k : Nat) : Stream.Input where
  resetN := runRst s pin
  frz := s.freeze.frz
  frzd := s.freeze.frzd
  capEn := Strobes.capEn s.dbgCtrl.cen s.dbgCtrl.replay
  capPush := Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s) (fallVec s)
    s.dbgCtrl.emask
  capRec := captureRecord s
  replayEn := s.dbgCtrl.replay
  replayApply := Debug.Ctrl.apply s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
    (streamAt s 0).wb
  replayLate := Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
    (streamAt s 0).wb
  cfgMode := ((Machine.cfgView s.cont.cfg).streams[k]!).rx
  cfgMsb := ((Machine.cfgView s.cont.cfg).streams[k]!).msb
  cfgStart := BitVec.ofNat 11 ((Machine.cfgView s.cont.cfg).streams[k]!).start
  cfgLen := BitVec.ofNat 12 ((Machine.cfgView s.cont.cfg).streams[k]!).len
  cfgMark := BitVec.ofNat 12 ((Machine.cfgView s.cont.cfg).streams[k]!).mark
  adv := strobe s pin (BitVec.ofNat 6 (47 + k))
  rxWe := strobe s pin (BitVec.ofNat 6 (49 + k))
  rxBit := Machine.Util.bit (gw s pin (BitVec.ofNat 6 (47 + k))).data 0
  rewind := (Strobes.streamCtlOf (gw s pin (BitVec.ofNat 6 (51 + k))).data
    (strobe s pin (BitVec.ofNat 6 (51 + k))) (hwIsSome s "SRT" k "CTL") (hwData s)).rewind
  flush := (Strobes.streamCtlOf (gw s pin (BitVec.ofNat 6 (51 + k))).data
    (strobe s pin (BitVec.ofNat 6 (51 + k))) (hwIsSome s "SRT" k "CTL") (hwData s)).flush
  clrStarved := (Strobes.streamCtlOf (gw s pin (BitVec.ofNat 6 (51 + k))).data
    (strobe s pin (BitVec.ofNat 6 (51 + k))) (hwIsSome s "SRT" k "CTL") (hwData s)).clrStarved
  gnt := streamGnt s pin k
  rdata := s.cont.ramOut

/-! ## Host-link inputs -/

/-- The host-command input: the sampled pins, the "not a register read" test and
the host RAM landing. -/
def hostCmdIn (s : State) (pin : Machine.PinIn) : HostCmd.Input where
  resetN := runRst s pin
  sck := SpiPins.sck s.sync
  sckPrev := SpiPins.sckPrev s.sync
  csN := SpiPins.csN s.sync
  mosi := SpiPins.mosi s.sync
  rdData := !Bridge.Host.regRead (absChip s) (Machine.cfgView s.cont.cfg)
  hland := hostLand s

/-- The host-read input: the command pins plus the read value and the RAM
landing byte. -/
def hostReadIn (s : State) (pin : Machine.PinIn) : HostRead.Input where
  resetN := runRst s pin
  sck := SpiPins.sck s.sync
  sckPrev := SpiPins.sckPrev s.sync
  csN := SpiPins.csN s.sync
  mosi := SpiPins.mosi s.sync
  rdData := !Bridge.Host.regRead (absChip s) (Machine.cfgView s.cont.cfg)
  rdVal := Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg)
  hland := hostLand s
  hlandD := Bridge.Host.ramByte (absChip s)

/-- The host-link write view. -/
def hostWrIn (s : State) (pin : Machine.PinIn) : Host.Input where
  resetN := runRst s pin
  sck := SpiPins.sck s.sync
  sckPrev := SpiPins.sckPrev s.sync
  csN := SpiPins.csN s.sync
  st := s.hostCmd.phase
  isRd := s.hostCmd.isRd

/-! ## Configuration queue, arbiter and debug inputs -/

/-- The picked `CW` word (`CW.AL`, `CW.AH`, `CW.D`). -/
def cwWord (s : State) (pin : Machine.PinIn) : BitVec 15 :=
  CoreCtl.GroupWord.pack (gw s pin 58)

/-- The host register-write strobe of `CTRL.STICKY` bit `k`. -/
def stickyClear (s : State) (k : Nat) : Bool :=
  match Machine.Util.hwAt (hwOf s) "CTRL" 0 "STICKY" with
  | some (j, v) => j == 0 && Machine.Util.nbit v k
  | none => false

/-- The core-queue input. -/
def cqIn (s : State) (pin : Machine.PinIn) : CoreQueue.Input where
  resetN := runRst s pin
  cw := cwWord s pin
  frz := s.freeze.frz
  coreIssue := (arbStep s).coreIssue
  isCfg := Machine.Config.isCfgAddr s.cq.pendingAddr.toNat
  clearSticky := stickyClear s 2
  hostData := hwData s

/-- The debug capture/replay input.  The combined host-or-drain byte strobes are
the RTL's `d_wr_*` (`project.v` 666-670): a host write inside the `DBG` window
at the byte's `a_dbg` offset, or a *drained* pending core write at that offset
(`cw_drain`, not the arbiter's `core_issue`, and gated by `!frz`). -/
def dbgCtrlIn (s : State) (pin : Machine.PinIn) : Debug.Ctrl.Input where
  resetN := runRst s pin
  frz := s.freeze.frz
  hEctl := hwIsSome s "DBG" 0 "ECTL"
  dWrEctl := Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
    (s.cq.pendingAddr) Strobes.hoDbgEctl
  -- RTL project.v 662: `h_em0 = w_dbg & (o_dbg == HO_DBG_EMASK)` (byte 0 only).
  hEm0 := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0
  dWrEm0 := Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
    (s.cq.pendingAddr) Strobes.hoDbgEmask
  hEm1 := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1
  dWrEm1 := Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
    (s.cq.pendingAddr) Strobes.hoDbgEmaskPlus1
  -- RTL project.v 664: `h_rlv0 = w_dbg & (o_dbg == HO_DBG_RLV)` (byte 0 only).
  hRlv0 := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0
  dWrRlv0 := Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
    (s.cq.pendingAddr) Strobes.hoDbgRlv
  hRlv1 := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1
  dWrRlv1 := Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
    (s.cq.pendingAddr) Strobes.hoDbgRlvPlus1
  hWd := hwData s
  cwData := s.cq.pendingData
  -- RTL project.v 438/465: `s_replay_valid[k]` is stream k's (bit 0 = S0, read at 442).
  replayValid := (if (streamAt s 1).wv then (1 : BitVec 1) else 0) ++
    (if (streamAt s 0).wv then (1 : BitVec 1) else 0)
  replayWord := (streamAt s 0).wb
  rise := riseVec s
  fall := fallVec s

/-- The debug digest input. -/
def dbgDigestIn (s : State) (pin : Machine.PinIn) : Debug.Digest.Input where
  resetN := runRst s pin
  dWrMctl := hwIsSome s "DBG" 0 "MCTL"
  hWd := hwData s
  frz := s.freeze.frz
  oEe := s.oenPins
  oOut := s.outPins

/-- The freeze register input. -/
def freezeIn (s : State) (pin : Machine.PinIn) : CoreCtl.FreezeInput where
  resetN := runRst s pin
  dbgWrite := hwIsSome s "DBG" 0 "DBG"
  data := hwData s

/-! ## Unit inputs -/

/-- Counter `k`'s input (`LO`/`HI`/`DEC` from its group). -/
def cntIn (s : State) (pin : Machine.PinIn) (k : Nat) : Units.Counter.Input where
  resetN := runRst s pin
  we := strobe s pin (BitVec.ofNat 6 (24 + k)) || strobe s pin (BitVec.ofNat 6 (27 + k)) ||
    strobe s pin (BitVec.ofNat 6 (30 + k))
  sel := Strobes.counterSel (strobe s pin (BitVec.ofNat 6 (24 + k)))
    (strobe s pin (BitVec.ofNat 6 (27 + k)))
  d := (gw s pin (BitVec.ofNat 6 (24 + k))).data

/-- Shifter `k`'s input (`LD`/`SH`/`CFG` from its group). -/
def shIn (s : State) (pin : Machine.PinIn) (k : Nat) : Units.Shifter.Input where
  resetN := runRst s pin
  -- RTL project.v 396: `.we(w[14])` of the SHk group word, independent of `SHk.CFG`
  -- (README units top wiring: `we == g_sh[k].w[14]`).
  we := (gw s pin (BitVec.ofNat 6 (18 + k))).we
  sel := Strobes.shifterSel (strobe s pin (BitVec.ofNat 6 (20 + k))) == 1
  d := (gw s pin (BitVec.ofNat 6 (18 + k))).data
  cfgWe := strobe s pin (BitVec.ofNat 6 (22 + k))
  cfgD := BitVec.truncate 5 (gw s pin (BitVec.ofNat 6 (22 + k))).data

/-- LFSR `k`'s input (`ST`/`B0..B3` from its group). -/
def lfIn (s : State) (pin : Machine.PinIn) (k : Nat) : Units.Lfsr.Input where
  resetN := runRst s pin
  we := (gw s pin (BitVec.ofNat 6 (33 + k))).we
  sel := Strobes.lfsrSel (strobe s pin (BitVec.ofNat 6 (33 + k)))
    (strobe s pin (BitVec.ofNat 6 (35 + 4 * k)))
    (strobe s pin (BitVec.ofNat 6 (36 + 4 * k)))
    (strobe s pin (BitVec.ofNat 6 (37 + 4 * k)))
  d := (gw s pin (BitVec.ofNat 6 (33 + k))).data
  poly := BitVec.ofNat 32 (s.cont.cfg.poly k)

/-- The accumulator input: the ACC group's winner mask, all six slots' op
codes and data, and the four scratch register groups. -/
def accIn (s : State) (pin : Machine.PinIn) : Units.Acc.Input where
  resetN := runRst s pin
  hit := Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 7)
  sel := packNs 3 6 fun m => Units.Acc.opCodeOf (BitVec.truncate 6 (BitVec.ushiftRight (mvDst s pin) (6 * m)))
  d := mvDat s pin
  rWe := packBools 4 fun k => (gw s pin (BitVec.ofNat 6 (14 + k))).we
  rD := packNs 8 4 fun k => (gw s pin (BitVec.ofNat 6 (14 + k))).data

/-! ## Glue, output pins and the sticky errors -/

/-- The picked `FLAGS` word `{we, dst, data}`. -/
def flagsWord (s : State) (pin : Machine.PinIn) : BitVec 15 := CoreCtl.GroupWord.pack (gw s pin 5)

/-- The picked `HOST.OUT` word. -/
def houtWord (s : State) (pin : Machine.PinIn) : BitVec 15 := CoreCtl.GroupWord.pack (gw s pin 57)

/-- The glue input. -/
def glueIn (s : State) (pin : Machine.PinIn) : Glue.GlueInput where
  resetN := runRst s pin
  frz := s.freeze.frz
  wrRun := hwIsSome s "CTRL" 0 "RUN"
  wrIrqEn := hwIsSome s "CTRL" 0 "IRQEN"
  wrDb := hwIsSome s "CTRL" 0 "DOORBELL"
  wrHin := hwIsSome s "CTRL" 0 "HOSTIN"
  wrHst := hwIsSome s "CTRL" 0 "HOSTSTAT"
  wFlags := flagsWord s pin
  wHout := houtWord s pin
  hWd := hwData s
  rdHin := Moves.readsOf (mvEn s pin) (mvSrc s pin) Moves.srcHostIn
  conflict := s.conflict
  memhaz := s.memhaz
  cwOverrun := s.cq.overrun
  tLate := packBools 6 fun t => (threadAt s t).late
  tOvr := packBools 6 fun t => (threadAt s t).ovr
  lTapmiss := packBools 4 fun l => (lineAt s l).tapmiss
  sStarved := packBools 2 fun k => (streamAt s k).starved

/-- The cut `OutCfg` of output pin `o`, built from the machine's decoded output
configuration and the line state (the packing `Bridge.Glue.outCfgOf` proves). -/
def outCfgOf (s : State) (o : Nat) : Glue.OutCfg :=
  let oc := (Machine.cfgView s.cont.cfg).outs[o]!
  { bind := BitVec.ofNat 8 (oc.line + 4 * (if oc.bound then 1 else 0) + 8 * oc.live)
    sel := BitVec.ofNat 8 (oc.sel0 + 4 * oc.sel1 + 16 * oc.sel2)
    lut := BitVec.ofNat 32 oc.lut
    oe := BitVec.ofNat 32 oc.oe
    comm := packNs 4 4 fun l => (lineAt s l).committed
    pinA := packBools 4 fun l =>
      (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pina
    pinB := packBools 4 fun l =>
      (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pinb
    seg := packNs 2 4 fun l => Line.seg (lineAt s l) }

/-- The next `OUT` register. -/
def outNextPins (s : State) (pin : Machine.PinIn) : BitVec 14 :=
  BitVec.ofNat 14 (Machine.Util.packBits ((List.range 14).map fun o =>
    Glue.outNext (outCfgOf s o) (Machine.Util.bit s.outPins o) (runRst s pin) s.freeze.frz))

/-- The next `OEN` register. -/
def oenNextPins (s : State) (pin : Machine.PinIn) : BitVec 8 :=
  BitVec.ofNat 8 (Machine.Util.packBits ((List.range 8).map fun o =>
    Glue.oeNext (outCfgOf s o) (Machine.Util.bit s.oenPins o) (runRst s pin) s.freeze.frz))

/-! ## Pin projection -/

/-- The chip's driven pins as the machine's `pinsOut` triple:
`(uo_out, uio_out, uio_oe)` = `({OUT[13:8], IRQ, MISO}, OUT[7:0], OEN)`
(`project.v` 818-820; MISO is `TX[7]`). -/
def pinsOf (s : State) : Nat × Nat × Nat :=
  let o := s.outPins.toNat
  ((o >>> 8) * 4 + Machine.Util.b2n s.glue.irq * 2 + Machine.Util.b2n (Machine.Util.bit s.hostRead.tx 7),
    o % 256, s.oenPins.toNat)

end Metronome.ChipCut
