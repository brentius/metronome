import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Streams `S0`, `S1` (SPEC_V2 §6.3, §12.3, §12.4, §13.2)

An independent specification of the stream datapath in `src/md2_stream.v`, written
from the SPEC text.  One module covers both elaborated variants: the `CAP`
parameter of the RTL becomes the `cap : Bool` argument, so `cap = true` is S0
(`CAP = 1`, edge capture and edge replay) and `cap = false` is S1 (`CAP = 0`).

## What SPEC_V2 says (the equations below)

§6.3 names the state `POS` (12), `BIDX` (3), `BA` (11), `CUR` (8), `CV`, `WB`
(32), `WV`, `RQ`, `LD`, `PEND` (8), `PV` and the sticky `STARVED`, and fixes the
common definitions: `END = (POS == LEN)`; `b = MSB ? 7 - BIDX : BIDX`; `LB` is
lane `BA[1:0]` of `WB`; the stream requests a read of word `BA[10:2]` while `RQ`
(transmit) and a one-byte write of `PEND` to byte `BA` while `PV` (receive).

Transmit (`MODE = 0`, `adv` = an enabled move to `Sk.ADV` and `!END`):

```
if LD:   WB' = word read in t-1;  WV' = 1;  LD' = 0
if RQ && g:  RQ' = 0;  LD' = 1
elif !WV && !RQ && !LD:  RQ' = 1
if adv && !CV:  STARVED' = 1                          (the advance is ignored)
if !CV && WV:   CUR' = LB;  CV' = 1;  BA' = BA + 1;  if BA[1:0] == 3: WV' = 0
elif adv && CV:
    if BIDX != 7:  BIDX' = BIDX + 1
    else:          POS' = POS + 1;  BIDX' = 0
                   if WV:  CUR' = LB;  BA' = BA + 1;  if BA[1:0] == 3: WV' = 0
                   else:   CV' = 0;  STARVED' = 1
```

`Sk.BIT` is `CV && !END && CUR[b]`; source `Sk.BYTE` reads `CUR`.

Receive (`MODE = 1`): `bitin` = an enabled move to `Sk.RX` and `!END`, `flush` =
a flush request and `!END`:

```
NSH  = CUR | ((bitin && bus[0]) << b)
done = (bitin && BIDX == 7) || (flush && (BIDX != 0 || bitin))
if PV && g:  PV' = 0;  BA' = BA + 1
if bitin && !done:  CUR' = NSH;  BIDX' = BIDX + 1
if done:  CUR' = 0;  BIDX' = 0;  POS' = POS + 1
          if PV && !g:  STARVED' = 1                  (the byte is dropped)
          else:         PEND' = NSH;  PV' = 1
```

`Sk.BIT` is 0 in receive mode; source `Sk.BYTE` reads `PEND`.  Guards:
`Sk.END = END`; `Sk.MARK = (POS == MARK) && (BIDX == 0)`; `Sk.BYTE = (BIDX == 0)`.

Control: bit 0 **rewinds** at the end of the cycle with `POS' = 0, BIDX' = 0,
BA' = START, CUR' = 0, CV' = WV' = RQ' = LD' = PV' = 0`, overriding every other
update of these.  A request served in a rewind cycle still accesses the RAM.
Bit 1 flushes (receive only).  Host `CTL` bit 7 clears `STARVED`, unless a starve
event occurs in the same cycle.  Reset leaves each stream rewound at address 0.
`MODE`, `MSB` and `START` changes take effect at the next rewind (§9a.13: a
change without a rewind leaves the stream unspecified); `LEN` and `MARK` are used
live.

§12.3 makes a cycle with `FRZ = 1` frozen: "streams and the pointer make no
autonomous update and are not served", rewind and the `STARVED` clear still act,
and a host stream flush is ignored.  The landing exception captures a word read
in the last unfrozen cycle `s` into `WB` at the end of `s+1` even if `s+1` is
frozen, while `LD` and `WV` update in the first unfrozen cycle.  `FRZD` is
`FRZ` of the previous cycle, so the capture happens once (`!FRZD`).

§12.4 adds edge capture to S0.  With `CEN` set the transmit and receive bit paths
are disabled, `S0.BIT` reads 0 and a pushed record is written as one word:
`push = cev && !END`; `if PV && g: PV' = 0; BA' = BA + 4`; `if push: if PV && !g:
STARVED' = 1 (record dropped) else WB' = rec; PV' = 1; POS' = POS + 4`.  While
`PV` the stream requests a one-word write of `WB` at word `BA[10:2]`.

§13.2 turns S0 into a replay stream with `ECTL.RPL`, which takes priority over
`CEN`.  S0 reads whole words from `START` into a two-deep buffer (`WB`, then
`NB`); "a read is requested when the stream is not at END, no read is in flight
and the buffer is not full", and `POS` advances by 4 per word read.  `apply` and
`late` are computed outside the stream module from the replay timer `DC` and the
record's own `DC` field; `apply` shifts `NB` into `WB` and `late` sets `STARVED`
(§13.2's `late: apply && DC + 1 > WB.DC`).  "No read is in flight" is read as
`!RQ && !LD`: `RQ` is the request and `LD` the landing half of the §6.2 read
handshake, exactly as §6.3 writes it for transmit (`elif !WV && !RQ && !LD`).

## What the cut leaves free

`g` (`gnt`), the RAM read word (`rdata`) and its timing (§6.2: a word read in
cycle `s` is at the RAM output in `s+1`, and the requester loads it at the end of
`s+1`) are per-cycle inputs: the arbiter, the RAM macro and the one-cycle read
latency are outside this module cut.  The replay timer, `RLV` and the
`apply`/`late` comparisons of §13.2 are outside it too, as are the capture
counter `DC`, `EMASK` and the `cev` edge detect of §12.4.  `FRZ`/`FRZD` are
sampled inputs; the freeze register's own next state is §12.3 and is a separate
cut.

## Encodings

`bitAt` is `x[b]` of SPEC_V2 §6.3 (`CUR[b]`, a one-bit part-select); `LB` is the
lane select `WB[8*BA[1:0] +: 8]`.  `b` is a three-bit vector, so `7 - BIDX` is
its bitwise complement — the same value, and the form the RTL uses.  `PEND` and
`STARVED` are plain registers in the RTL, so reset drives them low.

## Cycle boundary

`stateAt inputs initial n` is the register state during cycle `n`, after `n`
sampled edges (the same convention as `Metronome.HostCmd`).  A reset edge in
cycle `n` leaves `resetState` for cycle `n+1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Metronome.Stream

/-! ## State, inputs, outputs -/

/-- Stream state of SPEC_V2 §6.3 plus the §13.2 replay buffer slot `NB`, `NV`.

`NB`/`NV` are the second slot of the two-deep replay buffer.  A `CAP = 0`
stream has no second slot in the RTL, so with `cap = false` the specification
carries both fields unchanged: they are inert, not part of that machine. -/
structure State where
  /-- `POS`, in bytes, compared with the live `LEN` and `MARK`. -/
  pos : BitVec 12
  /-- `BIDX`, the bit index inside the current byte. -/
  bidx : BitVec 3
  /-- `BA`, the byte address of the current word (transmit) or next write. -/
  ba : BitVec 11
  /-- `CUR`, the current transmit byte or the receive assembly register. -/
  cur : BitVec 8
  /-- `CV`, `CUR` holds a byte. -/
  cv : Bool
  /-- `WB`, the lookahead word (transmit, replay) or the pending record. -/
  wb : BitVec 32
  /-- `WV`, `WB` holds a word. -/
  wv : Bool
  /-- `RQ`, a read of `BA[10:2]` is requested. -/
  rq : Bool
  /-- `LD`, the word of last cycle's served read is landing this cycle. -/
  ld : Bool
  /-- `PEND`, the completed receive byte waiting for its RAM write. -/
  pend : BitVec 8
  /-- `PV`, `PEND` (receive) or `WB` (capture) is waiting for its write. -/
  pv : Bool
  /-- Sticky `STARVED`, cleared by the host `CTL` bit 7. -/
  starved : Bool
  /-- `NB`, the second replay buffer slot (§13.2). -/
  nb : BitVec 32
  /-- `NV`, `NB` holds a word. -/
  nv : Bool
  deriving DecidableEq, Repr

/-- The state left by a reset edge (`rst_n` low at the clock). -/
def resetState : State :=
  ⟨0, 0, 0, 0, false, 0, false, false, false, 0, false, false, 0, false⟩

/-- Sampled stream inputs.  `cfgMode`/`cfgMsb`/`cfgStart`/`cfgLen`/`cfgMark` are
the configuration bytes, `gnt` the arbiter grant and `rdata` the RAM read word
of §6.2 (the word read in the previous cycle).  The capture inputs are §12.4's
gated edge event, and the replay inputs are §13.2's `apply`/`late`, which the
chip top computes from the replay timer and the record. -/
structure Input where
  resetN : Bool
  frz : Bool
  frzd : Bool
  capEn : Bool
  capPush : Bool
  capRec : BitVec 32
  replayEn : Bool
  replayApply : Bool
  replayLate : Bool
  cfgMode : Bool
  cfgMsb : Bool
  cfgStart : BitVec 11
  cfgLen : BitVec 12
  cfgMark : BitVec 12
  adv : Bool
  rxWe : Bool
  rxBit : Bool
  rewind : Bool
  flush : Bool
  clrStarved : Bool
  gnt : Bool
  rdata : BitVec 32
  deriving DecidableEq, Repr

/-- The combinational outputs of §6.3, §12.4 and §13.2. -/
structure Out where
  /-- `Sk.BIT`. -/
  bit : Bool
  /-- Source `Sk.BYTE`. -/
  byteOut : BitVec 8
  /-- Guard `Sk.END`. -/
  gEnd : Bool
  /-- Guard `Sk.MARK`. -/
  gMark : Bool
  /-- Guard `Sk.BYTE`. -/
  gByte : Bool
  /-- A RAM request this cycle (read or write). -/
  req : Bool
  /-- The request is a write (`PV` receive byte or `CEN` record). -/
  reqWe : Bool
  /-- The requested byte address `BA`. -/
  reqAddr : BitVec 11
  /-- The write byte `PEND`. -/
  reqWdata : BitVec 8
  /-- The request is a whole-word write of `reqWword` (§12.4). -/
  reqWord : Bool
  /-- The write word `WB` (§12.4). -/
  reqWword : BitVec 32
  /-- `RLV` may be updated from `replayWord` this cycle (§13.2). -/
  replayValid : Bool
  /-- The record `WB` the replay level is taken from (§13.2). -/
  replayWord : BitVec 32
  deriving DecidableEq, Repr

/-! ## Combinational terms -/

/-- `x[b]`: one bit of a byte (SPEC_V2 §6.3's `CUR[b]`). -/
def bitAt (x : BitVec 8) (n : BitVec 3) : Bool := ((x >>> n.toNat) &&& 1) != 0

/-- `CEN`: the §12.4 capture mode, off while §13.2's `RPL` is on. -/
def cen (cap : Bool) (i : Input) : Bool := cap && i.capEn && !(cap && i.replayEn)

/-- `RPL`: §13.2's replay mode (takes priority over `CEN`). -/
def rpl (cap : Bool) (i : Input) : Bool := cap && i.replayEn

/-- Transmit mode: `MODE = 0` and neither capture nor replay. -/
def txMode (cap : Bool) (i : Input) : Bool := !i.cfgMode && !cen cap i && !rpl cap i

/-- Receive mode: `MODE = 1` and neither capture nor replay. -/
def rxMode (cap : Bool) (i : Input) : Bool := i.cfgMode && !cen cap i && !rpl cap i

/-! ### Reading the mode flags apart

These are the primitive facts the transition theorems need, so that every branch
condition of the specification reduces to a `Bool` literal. -/

theorem cen_facts (cap : Bool) (i : Input) (h : cen cap i = true) :
    cap = true ∧ i.capEn = true ∧ i.replayEn = false := by
  simp only [cen] at h
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

theorem rpl_facts (cap : Bool) (i : Input) (h : rpl cap i = true) :
    cap = true ∧ i.replayEn = true := by
  simp only [rpl] at h
  refine ⟨?_, ?_⟩ <;> bv_decide

theorem txMode_facts (cap : Bool) (i : Input) (h : txMode cap i = true) :
    i.cfgMode = false ∧ cen cap i = false ∧ rpl cap i = false := by
  simp only [txMode] at h
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

theorem rxMode_facts (cap : Bool) (i : Input) (h : rxMode cap i = true) :
    i.cfgMode = true ∧ cen cap i = false ∧ rpl cap i = false := by
  simp only [rxMode] at h
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-- `END = (POS == LEN)`, with the live `LEN`. -/
def endC (s : State) (i : Input) : Bool := s.pos == i.cfgLen

/-- `BIDX == 7`. -/
def last (s : State) : Bool := s.bidx == 7

/-- `b = MSB ? 7 - BIDX : BIDX`. -/
def bsel (s : State) (i : Input) : BitVec 3 := if i.cfgMsb then ~~~s.bidx else s.bidx

/-- `BA[1:0]`, the byte lane of `BA`. -/
def lane (s : State) : BitVec 2 := BitVec.truncate 2 s.ba

/-- `LB`: lane `BA[1:0]` of `WB` (little-endian). -/
def lb (s : State) (_i : Input) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.ushiftRight s.wb (8 * (BitVec.truncate 2 s.ba).toNat))

/-- `adv`: an enabled move to `Sk.ADV` and `!END`. -/
def advT (cap : Bool) (s : State) (i : Input) : Bool :=
  txMode cap i && i.adv && !endC s i

/-- `bitin`: an enabled move to `Sk.RX` and `!END`. -/
def bitin (cap : Bool) (s : State) (i : Input) : Bool :=
  rxMode cap i && i.rxWe && !endC s i

/-- The receive flush request, and `!END`.  §12.3: a host stream flush is
ignored while frozen, so `FRZ` gates it. -/
def fl (cap : Bool) (s : State) (i : Input) : Bool :=
  rxMode cap i && i.flush && !endC s i && !i.frz

/-- `push` of §12.4: a capture edge event and `!END`. -/
def push (cap : Bool) (s : State) (i : Input) : Bool :=
  cen cap i && i.capPush && !endC s i

/-- `NSH = CUR | ((bitin && bus[0]) << b)`. -/
def nsh (cap : Bool) (s : State) (i : Input) : BitVec 8 :=
  s.cur ||| (if bitin cap s i && i.rxBit then
               (1 : BitVec 8) <<< (bsel s i).toNat else 0)

/-- `done = (bitin && BIDX == 7) || (flush && (BIDX != 0 || bitin))`. -/
def done (cap : Bool) (s : State) (i : Input) : Bool :=
  (bitin cap s i && last s) || (fl cap s i && (s.bidx != 0 || bitin cap s i))

/-- The buffer is full after a possible `apply` shift: §13.2 shifts `NB` into
`WB`, so the occupancy test is `NV` when applying and `WV` otherwise. -/
def occupied (s : State) (i : Input) : Bool :=
  (i.replayApply && s.nv) || (!i.replayApply && s.wv)

/-- The landing word: §12.3's landing exception takes it from `NB` when the
previous cycle was frozen, because a host read may have replaced the RAM output. -/
def landing (s : State) (i : Input) : BitVec 32 := if i.frzd then s.nb else i.rdata

/-- A transmit starve event: an advance without a byte, or a byte end with no
next byte (§6.3's `STARVED' = 1` rows). -/
def starveTx (cap : Bool) (s : State) (i : Input) : Bool :=
  advT cap s i && (!s.cv || (last s && !s.wv))

/-- A receive or capture starve event: a completed byte or a pushed record while
`PV` and the arbiter does not serve the stream (§6.3, §12.4). -/
def starveRx (cap : Bool) (s : State) (i : Input) : Bool :=
  (rxMode cap i && done cap s i && s.pv && !i.gnt) ||
    (push cap s i && s.pv && !i.gnt)

/-- Every starve event of the cycle, including §13.2's `late`. -/
def starveEvent (cap : Bool) (s : State) (i : Input) : Bool :=
  starveTx cap s i || starveRx cap s i || (rpl cap i && i.replayLate)

/-! ## Next state -/

/-- `POS'`. -/
def posNext (cap : Bool) (s : State) (i : Input) : BitVec 12 :=
  if !i.resetN then 0
  else if i.rewind then 0
  else if i.frz then s.pos
  else if rpl cap i then (if s.rq && i.gnt then s.pos + 4 else s.pos)
  else if cen cap i then
    (if push cap s i && !(s.pv && !i.gnt) then s.pos + 4 else s.pos)
  else if txMode cap i then
    (if advT cap s i && s.cv && last s then s.pos + 1 else s.pos)
  else if done cap s i then s.pos + 1 else s.pos

/-- `BIDX'`. -/
def bidxNext (cap : Bool) (s : State) (i : Input) : BitVec 3 :=
  if !i.resetN then 0
  else if i.rewind then 0
  else if i.frz then s.bidx
  else if rpl cap i || cen cap i then s.bidx
  else if txMode cap i then
    (if advT cap s i && s.cv then (if last s then 0 else s.bidx + 1) else s.bidx)
  else if done cap s i then 0 else if bitin cap s i then s.bidx + 1 else s.bidx

/-- `BA'`. -/
def baNext (cap : Bool) (s : State) (i : Input) : BitVec 11 :=
  if !i.resetN then 0
  else if i.rewind then i.cfgStart
  else if i.frz then s.ba
  else if rpl cap i then (if s.rq && i.gnt then s.ba + 4 else s.ba)
  else if cen cap i then (if s.pv && i.gnt then s.ba + 4 else s.ba)
  else if txMode cap i then
    (if (!s.cv && s.wv) || (advT cap s i && s.cv && last s && s.wv) then s.ba + 1
     else s.ba)
  else if s.pv && i.gnt then s.ba + 1 else s.ba

/-- `CUR'`. -/
def curNext (cap : Bool) (s : State) (i : Input) : BitVec 8 :=
  if !i.resetN then 0
  else if i.rewind then 0
  else if i.frz then s.cur
  else if rpl cap i || cen cap i then s.cur
  else if txMode cap i then
    (if (!s.cv && s.wv) || (advT cap s i && s.cv && last s && s.wv) then lb s i
     else s.cur)
  else if done cap s i then 0
  else if bitin cap s i then nsh cap s i else s.cur

/-- `CV'`. -/
def cvNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.rewind then false
  else if i.frz then s.cv
  else if rpl cap i || cen cap i then s.cv
  else if txMode cap i then
    (if !s.cv && s.wv then true
     else if advT cap s i && s.cv && last s && !s.wv then false else s.cv)
  else s.cv

/-- `WB'`.  The rules are §6.3's lookahead load, §12.3's landing exception,
§12.4's record and §13.2's two-deep buffer, written in the RTL's assignment
order: the landing and the record are independent assignments of the always
block, so they appear before the mode branch.  At a reachable state at most one
rule applies, except that the frozen landing and the record both need `!FRZ`. -/
def wbNext (cap : Bool) (s : State) (i : Input) : BitVec 32 :=
  if !i.resetN then 0
  else if txMode cap i && s.ld && !i.frzd then i.rdata
  else if cen cap i && push cap s i && !(s.pv && !i.gnt) && !i.frz then i.capRec
  else if i.frz then s.wb
  else if rpl cap i then
    (if s.ld && !occupied s i then landing s i
     else if i.replayApply then s.nb else s.wb)
  else s.wb

/-- `WV'`.  §6.3 sets it on the landing `LD`, clears it when the last lane
(`BA[1:0] == 3`) of the word has been consumed, and §13.2's `apply` shifts `NV`
in; a rewind clears it. -/
def wvNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.rewind then false
  else if i.frz then s.wv
  else if rpl cap i && s.ld && !occupied s i then true
  else if rpl cap i && i.replayApply then s.nv
  else if txMode cap i then
    (if ((!s.cv && s.wv) || (advT cap s i && s.cv && last s && s.wv)) &&
        (BitVec.truncate 2 s.ba == 3) then false
     else if s.ld then true else s.wv)
  else s.wv

/-- `RQ'`.  §13.2: a replay read is requested when the stream is not at `END`,
no read is in flight and the buffer is not full. -/
def rqNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.rewind then false
  else if i.frz then s.rq
  else if rpl cap i then
    (if s.rq && i.gnt then false
     else if !s.rq && !s.ld && !endC s i && !(s.wv && s.nv) then true else s.rq)
  else if cen cap i then s.rq
  else if txMode cap i then
    (if s.rq && i.gnt then false
     else if !s.wv && !s.rq && !s.ld then true else s.rq)
  else s.rq

/-- `LD'`. -/
def ldNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.rewind then false
  else if i.frz then s.ld
  else if rpl cap i then
    (if s.rq && i.gnt then true else if s.ld then false else s.ld)
  else if cen cap i then s.ld
  else if txMode cap i then
    (if s.rq && i.gnt then true else if s.ld then false else s.ld)
  else s.ld

/-- `PEND'`. -/
def pendNext (cap : Bool) (s : State) (i : Input) : BitVec 8 :=
  if !i.resetN then 0
  else if i.frz then s.pend
  else if rpl cap i || cen cap i || txMode cap i then s.pend
  else if done cap s i then (if s.pv && !i.gnt then s.pend else nsh cap s i)
  else s.pend

/-- `PV'`. -/
def pvNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.rewind then false
  else if i.frz then s.pv
  else if rpl cap i then s.pv
  else if cen cap i then
    (if push cap s i && !(s.pv && !i.gnt) then true
     else if s.pv && i.gnt then false else s.pv)
  else if txMode cap i then s.pv
  else if done cap s i then (if s.pv && !i.gnt then s.pv else true)
  else if s.pv && i.gnt then false else s.pv

/-- `STARVED'`: the cycle's starve events, or the sticky flag unless the host
`CTL` bit 7 clears it (a simultaneous event keeps it set). -/
def starvedNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else starveEvent cap s i || (s.starved && !i.clrStarved)

/-- `NB'`: the second replay slot takes the landing word when `WB` still holds a
word after a possible `apply` shift (§13.2's two-deep buffer), and a frozen
landing (§12.3) is preserved there. -/
def nbNext (cap : Bool) (s : State) (i : Input) : BitVec 32 :=
  if cap && !i.resetN then 0
  else if rpl cap i && s.ld && !i.frzd && i.frz then i.rdata
  else if rpl cap i && s.ld && !i.frzd && occupied s i then i.rdata
  else s.nb

/-- `NV'`. -/
def nvNext (cap : Bool) (s : State) (i : Input) : Bool :=
  if cap && !i.resetN then false
  else if cap && i.rewind then false
  else if i.frz then s.nv
  else if rpl cap i && s.ld && occupied s i then true
  else if rpl cap i && i.replayApply then false
  else s.nv

/-- The specified stream transition. -/
def step (cap : Bool) (s : State) (i : Input) : State :=
  ⟨posNext cap s i, bidxNext cap s i, baNext cap s i, curNext cap s i,
   cvNext cap s i, wbNext cap s i, wvNext cap s i, rqNext cap s i,
   ldNext cap s i, pendNext cap s i, pvNext cap s i, starvedNext cap s i,
   nbNext cap s i, nvNext cap s i⟩

/-! ## Combinational outputs -/

/-- `Sk.BIT` is `CV && !END && CUR[b]`, and 0 in receive mode (§6.3) and while
capturing or replaying (§12.4, §13.2). -/
def bitOut (cap : Bool) (s : State) (i : Input) : Bool :=
  txMode cap i && s.cv && !endC s i && bitAt s.cur (bsel s i)

/-- Source `Sk.BYTE`: `CUR` in transmit, `PEND` in receive (§6.3), by `MODE`
(§12.4). -/
def byteOut (_cap : Bool) (s : State) (i : Input) : BitVec 8 :=
  if i.cfgMode then s.pend else s.cur

/-- Guard `Sk.END`. -/
def gEnd (s : State) (i : Input) : Bool := endC s i

/-- Guard `Sk.MARK = (POS == MARK) && (BIDX == 0)`, with the live `MARK`. -/
def gMark (s : State) (i : Input) : Bool := (s.pos == i.cfgMark) && (s.bidx == 0)

/-- Guard `Sk.BYTE = (BIDX == 0)`. -/
def gByte (s : State) (_i : Input) : Bool := s.bidx == 0

/-- The RAM request of §6.3, §12.4 and §13.2: a read while `RQ` (transmit,
replay), a one-byte write while `PV` (receive), a one-word write while `PV`
(capture). -/
def req (cap : Bool) (s : State) (i : Input) : Bool :=
  if rpl cap i then s.rq else if i.cfgMode || cen cap i then s.pv else s.rq

/-- The request is a write. -/
def reqWe (cap : Bool) (_s : State) (i : Input) : Bool :=
  (i.cfgMode || cen cap i) && !rpl cap i

/-- The requested byte address `BA`. -/
def reqAddr (_cap : Bool) (s : State) (_i : Input) : BitVec 11 := s.ba

/-- The write byte `PEND`. -/
def reqWdata (_cap : Bool) (s : State) (_i : Input) : BitVec 8 := s.pend

/-- A whole-word write (§12.4 only). -/
def reqWord (cap : Bool) (_s : State) (i : Input) : Bool := cen cap i

/-- The write word `WB`. -/
def reqWword (_cap : Bool) (s : State) (_i : Input) : BitVec 32 := s.wb

/-- `RLV` may be updated this cycle (§13.2: `RPL && WV`). -/
def replayValid (cap : Bool) (s : State) (i : Input) : Bool := rpl cap i && s.wv

/-- The record the replay level comes from; a `CAP = 0` stream has none. -/
def replayWord (cap : Bool) (s : State) (_i : Input) : BitVec 32 :=
  if cap then s.wb else 0

/-- The specified outputs of the cycle. -/
def out (cap : Bool) (s : State) (i : Input) : Out :=
  ⟨bitOut cap s i, byteOut cap s i, gEnd s i, gMark s i, gByte s i,
   req cap s i, reqWe cap s i, reqAddr cap s i, reqWdata cap s i,
   reqWord cap s i, reqWword cap s i, replayValid cap s i, replayWord cap s i⟩

/-! ### A `Bool` `if` and the transition theorems' unfolding set

The `if` of a `Bool`-valued equation elaborates to `cond`, which `bv_decide`
cannot translate; `cond_eq_ite` turns it into the propositional `ite` it can. -/

universe u

theorem cond_eq_ite {α : Sort u} (c : Bool) (x y : α) :
    cond c x y = (if c = true then x else y) := by
  cases c <;> rfl

/-! Every definition of the specification, so that the branch conditions of the
equations reduce to `Bool` atoms over the state and input fields. -/
macro "stream_simp" : tactic =>
  `(tactic| simp only [step, posNext, bidxNext, baNext, curNext, cvNext, wbNext,
    wvNext, rqNext, ldNext, pendNext, pvNext, starvedNext, nbNext, nvNext,
    advT, starveTx, starveRx, starveEvent, push, done, bitin, fl, endC, last,
    txMode, rxMode, cen, rpl, occupied, landing, lb, bsel, nsh, bitAt, bitOut, out,
    bitOut, byteOut, bitOut, gEnd, gMark, gByte, req, reqWe, reqAddr, reqWdata, reqWord,
    reqWword, replayValid, replayWord, State.mk.injEq, Out.mk.injEq, cond_eq_ite] at *)

/-- Unfold the equations and close the goal: `simp` for the propositional
residue, `bv_decide` for the bitvector identities. -/
macro "stream_close" : tactic =>
  `(tactic| stream_simp <;> (try simp) <;> bv_decide)

/-! ## Reset and rewind -/

/-- A sampled reset edge leaves `resetState`, whatever the prior values do.  The
two §13.2 buffer fields are gated: a `CAP = 0` stream has no such registers, so
with `cap = false` the specification carries them unchanged rather than reset. -/
theorem reset_step (cap : Bool) (s : State) (i : Input) (h : i.resetN = false)
    (hcap : cap = true) : step cap s i = resetState := by
  simp only [step, resetState, posNext, bidxNext, baNext, curNext, cvNext,
    wbNext, wvNext, rqNext, ldNext, pendNext, pvNext, starvedNext, nbNext,
    nvNext, State.mk.injEq] at h hcap ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem rewind_pos (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).pos = 0 := by
  stream_close

theorem rewind_bidx (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).bidx = 0 := by
  stream_close

theorem rewind_ba (cap : Bool) (s : State) (i : Input) (h : i.rewind = true)
    (hreset : i.resetN = true) : (step cap s i).ba = i.cfgStart := by
  stream_close

theorem rewind_cur (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).cur = 0 := by
  stream_close

theorem rewind_cv (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).cv = false := by
  stream_close

theorem rewind_wv (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).wv = false := by
  stream_close

theorem rewind_rq (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).rq = false := by
  stream_close

theorem rewind_ld (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).ld = false := by
  stream_close

theorem rewind_pv (cap : Bool) (s : State) (i : Input) (h : i.rewind = true) :
    (step cap s i).pv = false := by
  stream_close

/-- Rewind overrides every other update of `POS`, `BIDX`, `BA`, `CUR`, `CV`,
`WV`, `RQ`, `LD` and `PV` (§6.3), whatever the mode, the freeze, the arbiter
grant or the moves do in the same cycle.  A sampled reset edge has priority over
a rewind in the same cycle, so it is excluded. -/
theorem rewind_overrides (cap : Bool) (s : State) (i : Input) (h : i.rewind = true)
    (hreset : i.resetN = true) :
    (step cap s i).pos = 0 ∧ (step cap s i).bidx = 0 ∧
      (step cap s i).ba = i.cfgStart ∧ (step cap s i).cur = 0 ∧
      (step cap s i).cv = false ∧ (step cap s i).wv = false ∧
      (step cap s i).rq = false ∧ (step cap s i).ld = false ∧
      (step cap s i).pv = false :=
  ⟨rewind_pos cap s i h, rewind_bidx cap s i h,
   rewind_ba cap s i h hreset, rewind_cur cap s i h,
   rewind_cv cap s i h, rewind_wv cap s i h,
   rewind_rq cap s i h, rewind_ld cap s i h,
   rewind_pv cap s i h⟩

/-- A rewind clears the second replay slot's flag with the rest of the buffer
(§13.2's two-deep buffer), as the RTL's rewind assignment does. -/
theorem rewind_nv (cap : Bool) (s : State) (i : Input) (h : i.rewind = true)
    (hcap : cap = true) : (step cap s i).nv = false := by
  stream_close

/-- A rewind does not suppress a same-cycle `PEND` load: §6.3's rewind list does
not include `PEND`, so a byte completed in a rewind cycle still lands. -/
theorem rewind_pend_lands (cap : Bool) (s : State) (i : Input)
    (hreset : i.resetN = true)
    (hmode : rxMode cap i = true) (hdone : done cap s i = true)
    (hfrz : i.frz = false) (hland : (s.pv && !i.gnt) = false) :
    (step cap s i).pend = nsh cap s i := by
  obtain ⟨h1, h2, h3⟩ := rxMode_facts cap i hmode
  stream_close

/-! ## Transmit -/

/-- The transmit source bit is `CUR[b]` with `b = MSB ? 7 - BIDX : BIDX`, and 0
otherwise. -/
theorem bit_out_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).bit = (txMode cap i && s.cv && !endC s i && bitAt s.cur (bsel s i)) := by
  stream_simp

/-- In transmit mode with a byte present and not at `END`, `Sk.BIT` is bit `b` of
`CUR`; `b` is `7 - BIDX` (`~~~BIDX`) when `MSB` is set and `BIDX` otherwise. -/
theorem bit_is_cur_bit (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) (hcv : s.cv = true) (hend : endC s i = false) :
    (out cap s i).bit = bitAt s.cur (bsel s i) ∧
      (i.cfgMsb = true → bsel s i = ~~~s.bidx) ∧
      (i.cfgMsb = false → bsel s i = s.bidx) := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  refine ⟨?_, ?_, ?_⟩
  · stream_close
  · stream_close
  · stream_close

/-- The bit paths are disabled in receive mode: `Sk.BIT` is 0. -/
theorem bit_zero_receive (cap : Bool) (s : State) (i : Input) (h : i.cfgMode = true) :
    (out cap s i).bit = false := by
  stream_close

/-- `Sk.BIT` is 0 while capturing or replaying (§12.4, §13.2). -/
theorem bit_zero_capture (cap : Bool) (s : State) (i : Input)
    (h : cen cap i = true ∨ rpl cap i = true) : (out cap s i).bit = false := by
  rcases h with h | h
  · obtain ⟨h1, h2, h3⟩ := cen_facts cap i h
    stream_close
  · obtain ⟨h1, h2⟩ := rpl_facts cap i h
    stream_close

/-- An advance with no byte is ignored — it does not move `POS`, `BIDX`, `BA` or
`CUR` when no byte is waiting in `WB` — and it sets `STARVED` (§6.3's
`if adv && !CV: STARVED' = 1`, "the advance is ignored"). -/
theorem adv_without_cur (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) (hcv : s.cv = false) (hadv : i.adv = true)
    (hend : endC s i = false) (hfrz : i.frz = false) (hrew : i.rewind = false)
    (hreset : i.resetN = true) (hwv : s.wv = false) :
    (step cap s i).pos = s.pos ∧ (step cap s i).bidx = s.bidx ∧
      (step cap s i).ba = s.ba ∧ (step cap s i).cur = s.cur ∧
      (step cap s i).starved = true := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- A byte end with no buffered next word clears `CV` and sets `STARVED`
(§6.3's last transmit row). -/
theorem byte_end_without_word_starves (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) (hcv : s.cv = true) (hadv : i.adv = true)
    (hend : endC s i = false) (hlast : last s = true) (hwv : s.wv = false)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true) :
    (step cap s i).cv = false ∧ (step cap s i).pos = s.pos + 1 ∧
      (step cap s i).bidx = 0 ∧ (step cap s i).starved = true := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- A transmit advance inside a byte increments `BIDX` and leaves `POS` and `CUR`
alone. -/
theorem advance_inside_byte (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) (hcv : s.cv = true) (hadv : i.adv = true)
    (hend : endC s i = false) (hnlast : last s = false) (hfrz : i.frz = false)
    (hrew : i.rewind = false) (hreset : i.resetN = true) :
    (step cap s i).bidx = s.bidx + 1 ∧ (step cap s i).pos = s.pos ∧
      (step cap s i).cur = s.cur := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  refine ⟨?_, ?_, ?_⟩ <;> (stream_close)

/-- A served transmit read sets `RQ' = 0` and `LD' = 1` (§6.3's second row). -/
theorem served_read_lands_next (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) (hrq : s.rq = true) (hg : i.gnt = true)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true) :
    (step cap s i).rq = false ∧ (step cap s i).ld = true := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  refine ⟨?_, ?_⟩ <;> (stream_close)

/-! ## Receive -/

/-- A completed receive byte lands in `PEND` with `PV' = 1`, unless a previous
byte is still waiting and the arbiter does not serve the stream; `CUR` and `BIDX`
restart and `POS` advances by one (§6.3). -/
theorem received_byte_lands (cap : Bool) (s : State) (i : Input)
    (hmode : rxMode cap i = true) (hdone : done cap s i = true)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hland : (s.pv && !i.gnt) = false) :
    (step cap s i).pend = nsh cap s i ∧ (step cap s i).pv = true ∧
      (step cap s i).cur = 0 ∧ (step cap s i).bidx = 0 ∧
      (step cap s i).pos = s.pos + 1 := by
  obtain ⟨h1, h2, h3⟩ := rxMode_facts cap i hmode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- A completed receive byte is dropped — `PEND` holds, `PV` stays set and
`STARVED` is set — when a previous byte still waits and the arbiter does not
serve the stream in this cycle (§6.3's `if PV && !g: STARVED' = 1`). -/
theorem received_byte_dropped (cap : Bool) (s : State) (i : Input)
    (hmode : rxMode cap i = true) (hdone : done cap s i = true)
    (hpv : s.pv = true) (hg : i.gnt = false)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true) :
    (step cap s i).pend = s.pend ∧ (step cap s i).pv = true ∧
      (step cap s i).starved = true := by
  obtain ⟨h1, h2, h3⟩ := rxMode_facts cap i hmode
  refine ⟨?_, ?_, ?_⟩ <;> (stream_close)

/-- The receive path writes at most the one bit `b` of this cycle's `bitin`: the
assembly register never gains an unfilled bit, which is why a flushed byte has
zeros in the positions it never received (§6.3: "Unfilled bits of a flushed byte
are 0"). -/
theorem nsh_writes_one_bit (cap : Bool) (s : State) (i : Input) (j : BitVec 3) :
    bitAt (nsh cap s i) j =
      (bitAt s.cur j || (bitin cap s i && i.rxBit && j = bsel s i)) := by
  stream_close

/-- The mask of the bit positions the receive path has written after `k` bits
have arrived: positions `0..k-1` of `b` (LSB-first) or the mirrored positions
(MSB-first). -/
def writtenMask (msb : Bool) : Nat → BitVec 8
  | 0 => 0
  | k + 1 => writtenMask msb k ||| ((1 : BitVec 8) <<< (if msb then 7 - k else k))

/-- The assembly register has no bit set outside the positions the receive path
has already written: `BIDX` bits arrived, at `b(0) .. b(BIDX-1)`. -/
def PadOK (msb : Bool) (cur : BitVec 8) (bidx : BitVec 3) : Prop :=
  cur &&& ~~~(writtenMask msb bidx.toNat) = 0

/-- A byte that has not received a bit yet is zero everywhere: `done` restarts
the assembly register at 0 and reset clears it. -/
theorem padOK_zero (msb : Bool) (bidx : BitVec 3) : PadOK msb 0 bidx := by
  simp only [PadOK]
  generalize writtenMask msb bidx.toNat = m
  bv_decide

/-- Receiving one bit keeps the padding invariant: the new bit is written at
`b(BIDX)` and no other position changes. -/
theorem padOK_bit (msb : Bool) (k : Nat) (cur : BitVec 8) (bit : Bool)
    (h : cur &&& ~~~(writtenMask msb k) = 0) :
    (cur ||| (if bit then (1 : BitVec 8) <<< (if msb then 7 - k else k) else 0)) &&&
      ~~~(writtenMask msb (k + 1)) = 0 := by
  simp only [writtenMask]
  generalize writtenMask msb k = m at h ⊢
  bv_decide

/-- A flush completes the partial byte: the flushed byte is exactly the assembly
register, so every position the receive path never wrote is 0 (`PadOK`), `PEND`
takes it and `BIDX` clears (§6.3: "read `BIDX` before a flush, which clears
it"). -/
theorem flush_lands_cur (cap : Bool) (s : State) (i : Input)
    (hfl : fl cap s i = true) (hbitin : bitin cap s i = false)
    (hnb : s.bidx ≠ 0) (hrew : i.rewind = false)
    (hreset : i.resetN = true) (hland : (s.pv && !i.gnt) = false) :
    (step cap s i).pend = s.cur ∧ (step cap s i).bidx = 0 ∧
      (step cap s i).cur = 0 ∧ (step cap s i).pos = s.pos + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- The flushed byte carries no bit outside the positions written so far: the
zero padding of §6.3, stated on the invariant above. -/
theorem flush_pads_zeros (cap : Bool) (s : State) (i : Input)
    (hfl : fl cap s i = true) (hbitin : bitin cap s i = false)
    (hnb : s.bidx ≠ 0) (hrew : i.rewind = false)
    (hreset : i.resetN = true) (hland : (s.pv && !i.gnt) = false)
    (hpad : PadOK i.cfgMsb s.cur s.bidx) :
    (step cap s i).pend &&& ~~~(writtenMask i.cfgMsb s.bidx.toNat) = 0 := by
  have hcur := (flush_lands_cur cap s i hfl hbitin hnb hrew hreset hland).1
  simp only [PadOK] at hpad
  rw [hcur]
  exact hpad

/-- In a frozen cycle a receive completion or flush does not update the stream:
`POS`, `BIDX`, `BA`, `CUR`, `CV`, `PEND`, `PV`, `WV` and `RQ` hold (§12.3:
"streams ... make no autonomous update and are not served"; a host stream flush
is ignored while frozen).  Rewind and the `STARVED` clear still act, so they are
hypotheses here. -/
theorem frozen_holds (cap : Bool) (s : State) (i : Input) (hfrz : i.frz = true)
    (hreset : i.resetN = true) (hrew : i.rewind = false) :
    (step cap s i).pos = s.pos ∧ (step cap s i).bidx = s.bidx ∧
      (step cap s i).ba = s.ba ∧ (step cap s i).cur = s.cur ∧
      (step cap s i).cv = s.cv ∧ (step cap s i).pend = s.pend ∧
      (step cap s i).pv = s.pv ∧ (step cap s i).wv = s.wv ∧
      (step cap s i).rq = s.rq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-! ## Requests: writes only in receive mode -/

/-- A write request exists only in receive mode or in §12.4's capture mode:
transmit and replay request reads, and a capture stream's write is a whole word. -/
theorem write_only_in_receive (cap : Bool) (s : State) (i : Input)
    (h : reqWe cap s i = true) :
    (i.cfgMode = true ∨ cen cap i = true) ∧ rpl cap i = false := by
  stream_close

/-- Transmit mode never writes: its request is a read of `BA[10:2]`. -/
theorem transmit_no_write (cap : Bool) (s : State) (i : Input)
    (hmode : txMode cap i = true) : reqWe cap s i = false := by
  obtain ⟨h1, h2, h3⟩ := txMode_facts cap i hmode
  stream_close

/-- The request lines are the specified ones: `BA`, `PEND`, `WB` and the
read/write and word flags of §6.3, §12.4 and §13.2. -/
theorem req_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).req = req cap s i ∧ (out cap s i).reqWe = reqWe cap s i ∧
      (out cap s i).reqAddr = s.ba ∧ (out cap s i).reqWdata = s.pend ∧
      (out cap s i).reqWord = cen cap i ∧ (out cap s i).reqWword = s.wb := by
  stream_close

/-- A one-byte write request (receive, not capture) presents `PEND` at byte `BA`
while `PV`, and is not a whole-word write: only the capture mode writes words. -/
theorem byte_write_is_pend_at_ba (cap : Bool) (s : State) (i : Input)
    (h : reqWe cap s i = true) (hcen : cen cap i = false) :
    (out cap s i).req = s.pv ∧ (out cap s i).reqWdata = s.pend ∧
      (out cap s i).reqAddr = s.ba ∧ (out cap s i).reqWord = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> stream_close

/-! ## Guards -/

/-- `Sk.END` compares `POS` with the live `LEN`. -/
theorem gEnd_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).gEnd = (s.pos == i.cfgLen) := by
  stream_simp

/-- `Sk.MARK` compares `POS` with the live `MARK` and requires `BIDX == 0`. -/
theorem gMark_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).gMark = ((s.pos == i.cfgMark) && (s.bidx == 0)) := by
  stream_simp

/-- `Sk.BYTE` is `BIDX == 0`. -/
theorem gByte_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).gByte = (s.bidx == 0) := by
  stream_simp

/-- `Sk.END` is true exactly at the live length, so it is `MARK`'s comparison
only when `LEN = MARK`. -/
theorem gEnd_of_pos (cap : Bool) (s : State) (i : Input)
    (h : s.pos = i.cfgLen) : (out cap s i).gEnd = true := by
  rw [gEnd_spec, h]
  simp

/-- `Sk.BYTE` is true exactly at a byte boundary. -/
theorem gByte_of_bidx (cap : Bool) (s : State) (i : Input)
    (h : s.bidx = 0) : (out cap s i).gByte = true := by
  rw [gByte_spec, h]
  simp

/-! ## Edge capture (§12.4) -/

/-- A pushed record lands in `WB`, sets `PV` and advances `POS` by 4, unless a
previous record waits and the arbiter does not serve the stream (§12.4). -/
theorem capture_push_lands (cap : Bool) (s : State) (i : Input)
    (hcap : cen cap i = true) (hpush : push cap s i = true)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hland : (s.pv && !i.gnt) = false) :
    (step cap s i).wb = i.capRec ∧ (step cap s i).pv = true ∧
      (step cap s i).pos = s.pos + 4 := by
  obtain ⟨h1, h2, h3⟩ := cen_facts cap i hcap
  refine ⟨?_, ?_, ?_⟩ <;> (stream_close)

/-- A record pushed while a previous one waits and the arbiter does not serve the
stream is dropped: `WB`, `POS` and `PV` hold and `STARVED` is set (§12.4). -/
theorem capture_push_dropped (cap : Bool) (s : State) (i : Input)
    (hcap : cen cap i = true) (hpush : push cap s i = true) (hpv : s.pv = true)
    (hg : i.gnt = false) (hfrz : i.frz = false) (hrew : i.rewind = false)
    (hreset : i.resetN = true) :
    (step cap s i).wb = s.wb ∧ (step cap s i).pos = s.pos ∧
      (step cap s i).pv = true ∧ (step cap s i).starved = true := by
  obtain ⟨h1, h2, h3⟩ := cen_facts cap i hcap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- A served record write clears `PV` and advances `BA` by 4 (a whole word). -/
theorem capture_write_served (cap : Bool) (s : State) (i : Input)
    (hcap : cen cap i = true) (hpv : s.pv = true) (hg : i.gnt = true)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hpush : push cap s i = false) :
    (step cap s i).ba = s.ba + 4 ∧ (step cap s i).pv = false := by
  obtain ⟨h1, h2, h3⟩ := cen_facts cap i hcap
  refine ⟨?_, ?_⟩ <;> (stream_close)

/-- Capture mode is a whole-word write port: `reqWord` and `reqWe` are set while
`CEN`. -/
theorem capture_word_request (cap : Bool) (s : State) (i : Input)
    (hcap : cen cap i = true) :
    (out cap s i).reqWord = true ∧ (out cap s i).reqWe = true := by
  obtain ⟨h1, h2, h3⟩ := cen_facts cap i hcap
  refine ⟨?_, ?_⟩ <;> (stream_close)

/-! ## Edge replay (§13.2) -/

/-- An `apply` shifts the second buffer slot into the first (§13.2:
`WB' = NB, WV' = NV, NV' = 0`). -/
theorem replay_apply_shifts (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (happly : i.replayApply = true)
    (hld : s.ld = false) (hfrz : i.frz = false) (hrew : i.rewind = false)
    (hreset : i.resetN = true) :
    (step cap s i).wb = s.nb ∧ (step cap s i).wv = s.nv ∧
      (step cap s i).nv = false := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  refine ⟨?_, ?_, ?_⟩ <;> (stream_close)

/-- A landing fills the first buffer slot when it is empty after a possible
`apply` shift (§13.2's two-deep buffer, §6.3's `if LD: WB' = word read in
t-1`), and the read handshake completes. -/
theorem replay_landing (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (hld : s.ld = true) (hfrz : i.frz = false)
    (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hempty : occupied s i = false) (hserved : (s.rq && i.gnt) = false) :
    (step cap s i).wb = landing s i ∧ (step cap s i).wv = true ∧
      (step cap s i).ld = false := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  refine ⟨?_, ?_, ?_⟩ <;> (stream_close)

/-- A landing into a full buffer goes to the second slot and `NV` becomes set. -/
theorem replay_landing_second (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (hld : s.ld = true) (hfrz : i.frz = false)
    (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hfull : occupied s i = true) (hfrzd : i.frzd = false) :
    (step cap s i).nb = i.rdata ∧ (step cap s i).nv = true := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  refine ⟨?_, ?_⟩ <;> (stream_close)

/-- A replay read is served: `RQ` clears, `LD` sets, and `BA` and `POS` advance
by 4 — one whole word (§13.2: "`POS` advances by 4 per word read"). -/
theorem replay_read_served (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (hrq : s.rq = true) (hg : i.gnt = true)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true)
    (hld : s.ld = false) :
    (step cap s i).rq = false ∧ (step cap s i).ld = true ∧
      (step cap s i).pos = s.pos + 4 ∧ (step cap s i).ba = s.ba + 4 := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (stream_close)

/-- A replay read is requested exactly when the stream is not at `END`, no read
is in flight (`RQ` or `LD`) and the buffer is not full. -/
theorem replay_request_rule (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (hrq : s.rq = false)
    (hfrz : i.frz = false) (hrew : i.rewind = false) (hreset : i.resetN = true) :
    (step cap s i).rq = (!s.ld && !endC s i && !(s.wv && s.nv)) := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  stream_close

/-- §13.2's `late` sets `STARVED` in a replay cycle. -/
theorem replay_late_starves (cap : Bool) (s : State) (i : Input)
    (hrpl : rpl cap i = true) (hlate : i.replayLate = true)
    (hreset : i.resetN = true) : (step cap s i).starved = true := by
  obtain ⟨h1, h2⟩ := rpl_facts cap i hrpl
  stream_close

/-- The replay record presentation: `RLV` is updated from `WB` exactly while
replaying and holding a word (§13.2's `apply: RLV' = (RLV & ~EMASK) | (WB[12:0] &
EMASK)`), and a `CAP = 0` stream presents nothing. -/
theorem replay_valid_spec (cap : Bool) (s : State) (i : Input) :
    (out cap s i).replayValid = (rpl cap i && s.wv) ∧
      (out cap s i).replayWord = (if cap then s.wb else 0) := by
  stream_close

/-! ## The sticky `STARVED` flag -/

/-- `STARVED` stays set until a cycle clears it (host `CTL` bit 7). -/
theorem starved_sticky (cap : Bool) (s : State) (i : Input)
    (h : s.starved = true) (hclr : i.clrStarved = false) (hreset : i.resetN = true) :
    (step cap s i).starved = true := by
  stream_close

/-- The host clear works when no starve event occurs in the same cycle (§6.3). -/
theorem starved_clear (cap : Bool) (s : State) (i : Input)
    (hclr : i.clrStarved = true) (hnoev : starveEvent cap s i = false)
    (hreset : i.resetN = true) : (step cap s i).starved = false := by
  stream_close

/-- A starve event and a simultaneous host clear leave the flag set: "a sticky
flag set in the same cycle as a host clear stays set" (§9). -/
theorem starved_event_beats_clear (cap : Bool) (s : State) (i : Input)
    (hev : starveEvent cap s i = true) (hreset : i.resetN = true) :
    (step cap s i).starved = true := by
  stream_close

/-! ## Traces -/

/-- The specified state during cycle `n`. -/
def stateAt (cap : Bool) (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step cap s i) inputs initial n

theorem stateAt_succ (cap : Bool) (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt cap inputs initial (n + 1) = step cap (stateAt cap inputs initial n) (inputs n) :=
  rfl

/-- A reset edge in cycle `n` leaves the reset state. -/
theorem trace_reset (cap : Bool) (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).resetN = false) (hcap : cap = true) :
    stateAt cap inputs initial (n + 1) = resetState := by
  rw [stateAt_succ]
  exact reset_step cap _ _ h hcap

/-- A rewind in cycle `n` rewinds the stream whatever else happens in it. -/
theorem trace_rewind (cap : Bool) (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rewind = true) (hreset : (inputs n).resetN = true) :
    (stateAt cap inputs initial (n + 1)).pos = 0 ∧
      (stateAt cap inputs initial (n + 1)).bidx = 0 ∧
      (stateAt cap inputs initial (n + 1)).ba = (inputs n).cfgStart ∧
      (stateAt cap inputs initial (n + 1)).cur = 0 ∧
      (stateAt cap inputs initial (n + 1)).cv = false ∧
      (stateAt cap inputs initial (n + 1)).wv = false ∧
      (stateAt cap inputs initial (n + 1)).rq = false ∧
      (stateAt cap inputs initial (n + 1)).ld = false ∧
      (stateAt cap inputs initial (n + 1)).pv = false := by
  rw [stateAt_succ]
  exact rewind_overrides cap _ _ h hreset

/-- `STARVED`, once set in cycle `n+1`, stays set through every later cycle until
one clears it (host `CTL` bit 7). -/
theorem trace_starved_persists (cap : Bool) (inputs : Nat → Input) (initial : State)
    (n m : Nat) (hnm : n ≤ m)
    (hset : (stateAt cap inputs initial (n + 1)).starved = true)
    (hclear : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).clrStarved = false)
    (hreset : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).resetN = true) :
    (stateAt cap inputs initial (m + 1)).starved = true := by
  induction m with
  | zero =>
    have hn : n = 0 := Nat.le_zero.mp hnm
    subst hn
    exact hset
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hle : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hprev : (stateAt cap inputs initial (m + 1)).starved = true :=
        ih hle (fun j h1 h2 => hclear j h1 (Nat.le_succ_of_le h2))
          (fun j h1 h2 => hreset j h1 (Nat.le_succ_of_le h2))
      rw [stateAt_succ]
      exact starved_sticky cap _ (inputs (m + 1)) hprev
        (hclear (m + 1) (by omega) (by omega)) (hreset (m + 1) (by omega) (by omega))
    · have hn : n = m + 1 := by omega
      subst hn
      exact hset

end Metronome.Stream
