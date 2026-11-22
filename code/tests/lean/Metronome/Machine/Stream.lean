import Metronome.Machine.Memory

/-! §6.3 Streams (transmit, receive, guards, control); §12.4 edge capture into S0; §13.2 edge replay from S0;
§12.3 freeze and landing exception. -/

namespace Metronome.Machine

open Util Tables

/-- §6.3 / §12.4 / §13.2 Stream mode: 0 transmit, 1 receive (by `MODE`); for S0, 2 capture (`CEN`, §12.4) and
3 replay (`RPL`, which takes priority over `CEN`, §13.2). -- AMBIG(8) capture and replay replace the whole 6.3 data
path of S0 (no transmit prefetch, no receive), not only the bit paths. -/
def streamMode (c : StreamCfg) (k : Nat) (d : DbgSt) : Nat :=
  if k == 0 && d.rpl then 3 else if k == 0 && d.cen then 2 else if c.rx then 1 else 0

/-- §6.3 `END = (POS == LEN)`. -/
def streamEnd (c : StreamCfg) (s : StreamSt) : Bool := s.pos.toNat == c.len

/-- §6.3 `b = MSB ? 7 - BIDX : BIDX`. -/
def streamB (c : StreamCfg) (s : StreamSt) : Nat := if c.msb then 7 - s.bidx.toNat else s.bidx.toNat

/-- §6.3 `LB` = lane `BA[1:0]` of `WB`. -/
def streamLB (s : StreamSt) : Nat := nbits s.wb.toNat (8 * (s.ba.toNat % 4)) 8

/-- §6.3 / §12.4 `Sk.BIT` (source and guard): transmit `CV && !END && CUR[b]`; 0 in receive mode; 0 for a capture
stream (§12.4) -- AMBIG(12) and for a replay stream. -/
def streamBit (c : StreamCfg) (k : Nat) (d : DbgSt) (s : StreamSt) : Bool :=
  streamMode c k d == 0 && s.cv && !streamEnd c s && bit s.cur (streamB c s)

/-- §6.3 / §12.4 Source `Sk.BYTE`: `CUR` in transmit mode, `PEND` in receive mode; a capture or replay stream reads
as 6.3 says for its `MODE`. -/
def streamByte (c : StreamCfg) (s : StreamSt) : Nat := if c.rx then s.pend.toNat else s.cur.toNat

/-- §6.3 Guard `Sk.MARK = (POS == MARK) && (BIDX == 0)`. -/
def streamMark (c : StreamCfg) (s : StreamSt) : Bool := s.pos.toNat == c.mark && s.bidx.toNat == 0

/-- §6.3 Guard `Sk.BYTE = (BIDX == 0)`. -/
def streamAtByte (s : StreamSt) : Bool := s.bidx.toNat == 0

/-- §6.2 / §6.3 / §12.4 / §13.2 The stream's RAM request: transmit and replay read word `BA[10:2]` while `RQ`;
receive writes `PEND` to byte `BA` while `PV`; capture writes `WB` to word `BA[10:2]` while `PV`. -/
def streamReq (mode : Nat) (s : StreamSt) : RamReq :=
  match mode with
  | 1 => if s.pv then .wrByte s.ba.toNat s.pend.toNat else .none
  | 2 => if s.pv then .wrWord (s.ba.toNat / 4) s.wb.toNat else .none
  | _ => if s.rq then .rd (s.ba.toNat / 4) 0 else .none

/-- §13.2 `apply = RPL && WV && DC + 1 >= WB.DC` (`WB.DC = WB[31:13]`) and `late = apply && DC + 1 > WB.DC`.
Neither occurs in a frozen cycle (§12.3; -- AMBIG(13)). -/
def replayApply (d : DbgSt) (s : StreamSt) (frozen : Bool) : Bool × Bool :=
  let wbdc := s.wb.toNat >>> 13
  let ap := !frozen && d.rpl && s.wv && d.dc.toNat + 1 ≥ wbdc
  (ap, ap && d.dc.toNat + 1 > wbdc)

/-- §6.3 / §12.4 Inputs to a stream in cycle t. -/
structure StreamIn where
  /-- winning move to `Sk.ADV` -/
  adv : Bool := false
  /-- winning move to `Sk.RX`, bus value -/
  rx : Option Nat := none
  /-- winning move to `Sk.CTL`, bus value -/
  ctlMove : Option Nat := none
  /-- host write of the stream's `CTL` -/
  hCtl : Option Nat := none
  /-- the arbiter serves this stream (`g`) -/
  served : Bool := false
  /-- the RAM output holds this stream's word read in t-1 -/
  landNow : Bool := false
  ramOut : Nat := 0
  /-- §12.4 edge event and record -/
  cev : Bool := false
  record : Nat := 0
  /-- §13.2 replay apply and late -/
  apply : Bool := false
  late : Bool := false

namespace Util
/-- Stream next state before the rewind override, and the starve event of the cycle. -/
def streamAuto (c : StreamCfg) (mode : Nat) (s : StreamSt) (i : StreamIn) (flushReq : Bool) : StreamSt × Bool :=
  let en := streamEnd c s
  let g := i.served
  match mode with
  | 0 =>
    -- §6.3 transmit
    let adv := i.adv && !en
    let s1 := if s.ld then { s with wb := if i.landNow then bv 32 i.ramOut else s.wb, wv := true, ld := false }
      else s
    let s2 := if s.rq && g then { s1 with rq := false, ld := true }
      else if !s.wv && !s.rq && !s.ld then { s1 with rq := true } else s1
    let st1 := adv && !s.cv
    let lastLane := s.ba.toNat % 4 == 3
    if !s.cv && s.wv then
      ({ s2 with cur := bv 8 (streamLB s), cv := true, ba := s.ba + 1, wv := if lastLane then false else s2.wv }, st1)
    else if adv && s.cv then
      if s.bidx.toNat != 7 then ({ s2 with bidx := s.bidx + 1 }, st1)
      else
        let s3 := { s2 with pos := s.pos + 1, bidx := 0 }
        if s.wv then
          ({ s3 with cur := bv 8 (streamLB s), ba := s.ba + 1, wv := if lastLane then false else s3.wv }, st1)
        else ({ s3 with cv := false }, true)
    else (s2, st1)
  | 1 =>
    -- §6.3 receive
    let bitin := i.rx.isSome && !en
    let bus0 := nbit (i.rx.getD 0) 0
    let flush := flushReq && !en
    let b := streamB c s
    let nsh := s.cur.toNat ||| (if bitin && bus0 then 2 ^ b else 0)
    let done := (bitin && s.bidx.toNat == 7) || (flush && (s.bidx.toNat != 0 || bitin))
    let s1 := if s.pv && g then { s with pv := false, ba := s.ba + 1 } else s
    let s2 := if bitin && !done then { s1 with cur := bv 8 nsh, bidx := s.bidx + 1 } else s1
    if done then
      let s3 := { s2 with cur := 0, bidx := 0, pos := s.pos + 1 }
      if s.pv && !g then (s3, true) else ({ s3 with pend := bv 8 nsh, pv := true }, false)
    else (s2, false)
  | 2 =>
    -- §12.4 capture
    let push := i.cev && !en
    let s1 := if s.pv && g then { s with pv := false, ba := s.ba + 4 } else s
    if push then
      if s.pv && !g then (s1, true) else ({ s1 with wb := bv 32 i.record, pv := true, pos := s.pos + 4 }, false)
    else (s1, false)
  | _ =>
    -- §13.2 replay -- AMBIG(10) POS and BA advance by 4 when the read is served; -- AMBIG(11) buffer order
    let (wb1, wv1, nb1, nv1) := if i.apply then (s.nb, s.nv, s.nb, false) else (s.wb, s.wv, s.nb, s.nv)
    let s1 := { s with wb := wb1, wv := wv1, nb := nb1, nv := nv1 }
    let s2 :=
      if s.ld then
        let word := if i.landNow then bv 32 i.ramOut else (if s.wv then s.nb else s.wb)
        let s' := if !s1.wv then { s1 with wb := word, wv := true } else { s1 with nb := word, nv := true }
        { s' with ld := false }
      else s1
    let s3 := if s.rq && g then { s2 with rq := false, ld := true, pos := s.pos + 4, ba := s.ba + 4 }
      else if !en && !s.rq && !s.ld && !(s.wv && s.nv) then { s2 with rq := true } else s2
    (s3, i.late)
end Util

/-- §6.3, §12.3, §12.4, §13.2 Stream next state.

* Control: a move to `Sk.CTL` or a host write of `CTL` makes a request (both combine). Bit 0 rewinds:
  `POS' = 0, BIDX' = 0, BA' = START, CUR' = 0, CV' = WV' = RQ' = LD' = PV' = 0`, overriding every other update
  (-- AMBIG(14) also `NV' = 0`); `PEND`, `STARVED` unchanged. Bit 1 flushes (receive only; a host flush is ignored
  while frozen, §12.3). Host bit 7 clears `STARVED` unless a starve event occurs in the same cycle.
* §12.3: in a frozen cycle there is no autonomous update and no service, but a word read in the last unfrozen cycle
  is captured from the RAM output (`WB`, or for a replay stream the free buffer slot).
* -- AMBIG(15) `MODE` and `MSB` are used live (9a.13 leaves a change without rewind unspecified). -/
def streamNext (c : StreamCfg) (mode : Nat) (s : StreamSt) (i : StreamIn) (frozen : Bool) : StreamSt :=
  let mctl := i.ctlMove.getD 0
  let hctl := i.hCtl.getD 0
  let rewind := nbit mctl 0 || nbit hctl 0
  let flushReq := nbit mctl 1 || (!frozen && nbit hctl 1)
  let clr := nbit hctl 7
  let (s1, ev) :=
    if frozen then
      let s' := if s.ld && i.landNow then
          (if mode == 3 && s.wv then { s with nb := bv 32 i.ramOut } else { s with wb := bv 32 i.ramOut })
        else s
      (s', false)
    else streamAuto c mode s i flushReq
  let s2 := { s1 with starved := (s.starved && !clr) || ev }
  if rewind then
    { s2 with pos := 0, bidx := 0, ba := bv 11 c.start, cur := 0, cv := false, wv := false, rq := false,
              ld := false, pv := false, nv := false }
  else s2

end Metronome.Machine
