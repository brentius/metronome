import Metronome.Machine.Pins

/-! §3 Lines: beat generator (3.2), hold (3.2a), follower mode (3.3), taps (3.4), capture and snapshot (3.5),
output symbol and commit (3.6); §12.3 freeze effects on lines. -/

namespace Metronome.Machine

open Util Tables

/-- §3.2 / §3.2a / §3.4 Combinational values of one line in cycle t. Tap vectors are indexed by tap k = 0..2. -/
structure LineComb where
  edge : Bool
  e0 : Bool
  inwin : Bool
  start : Bool
  accept : Bool
  n : Nat
  nx : Nat
  over : Bool
  want : Bool
  hold : Bool
  adv : Bool
  wrap : Bool
  beat : Bool
  en : Vector Bool 3
  cross : Vector Bool 3
  next : Vector Bool 3
  cur : Vector Bool 3
  tap : Vector Bool 3
deriving Repr, Inhabited

namespace Util
/-- Tap phase `Tk`. -/
@[inline] def tapT (c : LineCfg) (k : Nat) : Nat := if k == 0 then c.t0 else if k == 1 then c.t1 else c.t2
/-- §3.4 tap k is a phase tap (k = 1, 2, or k = 0 with `T0SRC = 0`). -/
@[inline] def isPhaseTap (c : LineCfg) (k : Nat) : Bool := k != 0 || !c.t0src
end Util

/-- §3.4 Tap k is **enabled** if `Tk < MOD`, or, for tap 0 with `T0SRC = 1`, if `T0EDGE.polarity != 0`. -/
def tapEnabled (c : LineCfg) (k : Nat) : Bool :=
  if k == 0 && c.t0src then c.t0Pol != 0 else tapT c k < c.mod

/-- §3.4 Phase-tap crossing for a given `adv`:
`adv && ((n >= MOD) ? (Tk > PH || Tk <= nx) : (PH < Tk && Tk <= nx))`. -/
def phaseCross (c : LineCfg) (ph n nx : Nat) (adv : Bool) (k : Nat) : Bool :=
  let t := tapT c k
  adv && (if n ≥ c.mod then (t > ph || t ≤ nx) else (ph < t && t ≤ nx))

/-- §3.5 Input symbol `IN = {LUT1[{REM, SN}], LUT0[{REM, SN}]}` (combinational from `REM` and `SN`). -/
def inSym (c : LineCfg) (st : LineSt) : Nat :=
  let idx := b2n st.rem * 16 + st.sn.toNat
  b2n (nbit c.lut1 idx) * 2 + b2n (nbit c.lut0 idx)

/-- §3.4 `SEG = popcount(FIRED)` (2 bits). -- AMBIG(9) not masked by the enabled taps. -/
def seg (st : LineSt) : Nat := popcount st.fired.toNat % 4

/-- §3.2, §3.2a, §3.3, §3.4 and §12.3: the line's combinational values in cycle t. In a frozen cycle `edge = e0 = 0`
and `adv = 0`. -/
def lineComb (c : LineCfg) (st : LineSt) (p : PinView) (frozen : Bool) : LineComb :=
  let ph := st.ph.toNat
  -- §3.2 / §12.3
  let edge := !frozen && p.edgeSel c.edgePin c.edgePol
  let e0 := !frozen && p.edgeSel c.t0Pin c.t0Pol
  let inwin := if c.wlo ≤ c.whi then (c.wlo ≤ ph && ph ≤ c.whi) else (ph ≥ c.wlo || ph ≤ c.whi)
  let start := edge && st.arm && !st.run
  let accept := edge && st.run && st.ren && (!c.wen || inwin)
  -- §3.2 / 9a.6: 17-bit sum reduced once, stored in 16 bits
  let n := ph + c.inc
  let over := n ≥ c.mod
  let nx := (if over then n - c.mod else n) % 65536
  -- §3.2a hold: k = HTAP must be an enabled phase tap
  let k := c.htap
  let holdOk := c.hen && k != 3 && tapEnabled c k && isPhaseTap c k
  let want := st.run && !accept && holdOk && phaseCross c ph n nx true k
  let hold := c.hen && want && (p.pin c.hpin != c.hlvl)
  -- §3.2
  let adv := !frozen && st.run && !accept && !hold
  let wrap := adv && over
  let beat := if c.follow then accept else wrap
  -- §3.4
  let en := Vector.ofFn (n := 3) fun i => tapEnabled c i.val
  let cross := Vector.ofFn (n := 3) fun i =>
    let k := i.val
    en[k]! && (if isPhaseTap c k then phaseCross c ph n nx adv k else st.run && e0)
  let next := Vector.ofFn (n := 3) fun i =>
    let k := i.val
    cross[k]! && beat && (if isPhaseTap c k then over && tapT c k ≤ nx else true)
  let cur := Vector.ofFn (n := 3) fun i => cross[i.val]! && !next[i.val]!
  let tap := Vector.ofFn (n := 3) fun i => (cur[i.val]! && !bit st.fired i.val) || next[i.val]!
  { edge, e0, inwin, start, accept, n, nx, over, want, hold, adv, wrap, beat, en, cross, next, cur, tap }

/-- §3.6 A winning write to the line's symbol write group: `op` 1 = `L.SYM`, 2 = `L.DBIT`, 3 = `L.XOR`. -/
structure SymWrite where
  op : Nat
  v : Nat
deriving Repr, Inhabited

/-- §3.6 `STAGED'` after the winning symbol write:
`L.SYM: bus[3:0]`; `L.DBIT: {STAGED[3:1], bus[0]}`; `L.XOR: STAGED ^ bus[3:0]`. -/
def stagedNext (st : LineSt) (w : Option SymWrite) : BitVec 4 :=
  match w with
  | some ⟨1, v⟩ => bv 4 v
  | some ⟨2, v⟩ => bv 4 ((st.staged.toNat / 2) * 2 + v % 2)
  | some ⟨3, v⟩ => st.staged ^^^ bv 4 v
  | _ => st.staged

/-- §3.2 / §3.6 / §9 Inputs to a line's next state from moves and the host in cycle t. -/
structure LineIn where
  sym : Option SymWrite := none
  ctlMove : Option Nat := none
  hPhase : Option (Nat × Nat) := none
  hCtl : Option Nat := none
  hTapmissClr : Bool := false
deriving Repr, Inhabited

/-- §3.2 – §3.6, §3.2a, §9 (line runtime host writes), §12.3: next state of a line.

* `RUN' = RUN || start; ARM' = ARM && !start`; a move to `Lk.CTL` sets `RUN, ARM, REN` from bus bits 0..2; a host
  write of `CTL` does the same with priority over the move (§3.2).
* `PH' = (start || accept) ? PRE : (adv ? nx : PH)`; a host write of a `PHASE` byte replaces that byte
  (-- AMBIG(7) the other byte follows the generator).
* `SC`, `SP` per `FOLLOW` (§3.2); `HELD' = hold` (§3.2a), held in a frozen cycle (§12.3).
* `FIRED`, `FIRST`, `TAPMISS` (§3.4); capture and snapshot (§3.5); `STAGED`, `COMMITTED` (§3.6). -/
def lineNext (c : LineCfg) (st : LineSt) (cb : LineComb) (p : PinView) (i : LineIn) (frozen : Bool) : LineSt :=
  -- §3.2 RUN/ARM/REN with move and host overrides
  let run0 := st.run || cb.start
  let arm0 := st.arm && !cb.start
  let (run1, arm1, ren1) := match i.ctlMove with
    | some v => (nbit v 0, nbit v 1, nbit v 2)
    | none => (run0, arm0, st.ren)
  let (run', arm', ren') := match i.hCtl with
    | some v => (nbit v 0, nbit v 1, nbit v 2)
    | none => (run1, arm1, ren1)
  -- §3.2 phase
  let ph0 : Nat := if cb.start || cb.accept then c.pre else if cb.adv then cb.nx else st.ph.toNat
  let ph' : BitVec 16 := match i.hPhase with
    | some (k, v) => setByte (bv 16 ph0) k v
    | none => bv 16 ph0
  -- §3.2 SYNC
  let (sc', sp') :=
    if c.follow then (false, if cb.beat then true else if cb.wrap then false else st.sp)
    else (if cb.accept then true else if cb.beat then false else st.sc, if cb.beat then st.sc else st.sp)
  -- §3.6
  let staged' := stagedNext st i.sym
  let starting := run' && !st.run
  let committed' := if cb.beat || starting then staged' else st.committed
  -- §3.4 fired bits and FIRST
  let (fired', first') :=
    if starting then
      (bv 3 (packBits ((List.range 3).map fun k =>
        tapEnabled c k && isPhaseTap c k && tapT c k ≤ ph'.toNat)), true)
    else if cb.beat then
      (bv 3 (packBits ((List.range 3).map fun k => cb.next[k]!)), false)
    else
      (bv 3 (packBits ((List.range 3).map fun k => bit st.fired k || cb.cur[k]!)), st.first)
  let miss := cb.beat && (List.range 3).any fun k =>
    cb.en[k]! && !bit st.fired k && !cb.cur[k]! && !(k == 0 && c.t0src && st.first)
  let tapmiss' := (st.tapmiss && !i.hTapmissClr) || miss
  -- §3.5 capture
  let pa := p.pin c.pina
  let pb := p.pin c.pinb
  let w0 := st.w
  let w1 := if cb.tap[0]! then setBit w0 0 pa else w0
  let w2 := if cb.tap[1]! then setBit (setBit w1 1 pa) 3 pb else w1
  let w' := if cb.tap[2]! then setBit w2 2 pa else w2
  -- §3.5 snapshot
  let snap := if c.snap == 3 then cb.beat else cb.tap[c.snap]!
  let sn' := if snap then w' else st.sn
  let rem' := if snap then nbit (inSym c st) 1 else st.rem
  { ph := ph', run := run', arm := arm', ren := ren', held := if frozen then st.held else cb.hold,
    first := first', sc := sc', sp := sp', fired := fired', w := w', sn := sn', rem := rem',
    staged := staged', committed := committed', tapmiss := tapmiss' }

end Metronome.Machine
