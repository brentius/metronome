import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Line `l = 0..3`: beat generator, taps, capture and output symbol

An independent specification of `src/md2_line.v`, written from
[SPEC_V2 §3](../../../wiki/SPEC_V2.md#3-lines-l--03) (§3.1 configuration and
state, §3.2 beat generator, §3.2a hold, §3.3 follower mode and edge-sourced
tap 0, §3.4 taps/fired/`TAPMISS`, §3.5 capture/snapshot/input symbol, §3.6
output symbol and commit), §12.1 (`LIVE`/`PINA`/`PINB` pins of a line) and
§12.3 (freeze), plus the module header's precedence comment of `md2_line.v`:
the generator, then a move to `Lk.CTL`, then a host write of `PHASE`, `CTL` or
`STAT`.

The specification is split into the same sub-machines the RTL names so that
each register equation can be proved on its own: the beat generator
(`edge`, `e0`, `inwin`, `start`, `accept`, `adv`, `wrap`, `beat`, `hold`), the
three taps (`cross*`, `next*`, `cur*`, `tap*`, `en*`), capture
(`wNext`, `snap`, `inSym`) and commit (`stagedNext`, `committedNext`).

## Cycle boundary and the state

`stateAt inputs initial n` is the register state during cycle `n`, before the
sampled rising edge at the end of that cycle; `step` is that edge.  A sampled
reset edge (`rst_n` low) clears every register, as the synchronous reset branch
of `md2_line.v` does.

## Configuration

`cfg` is the line's 32-byte host-map window (`machine.LINE_REGS` in
`code/md2/machine.json`, `HO_LINE_*` in `src/md2_map.vh`).  This cut takes the
window's content as free per-cycle input: the configuration latch bank, its
write stage and the host map are the configuration cuts' business.  `Config`
keeps the bytes as the window stores them and decodes the documented bit fields
in `Config.*`; `line_check.py` checks that the elaborated field nets are exactly
those window bytes.

## What is deliberately not here

The winning move, the host-write enable, the pin synchronisers and the
configuration latches are inputs of this module (`ctl_*`, `sym_*`, `h_*`,
`lvl`, `rise`, `fall`, `frz`).  The move pick (`pick(...)` in `project.v`) and
the `w_lrt & i_lrt == k & o_lrt == offset` enable decode are checked at the chip
top only structurally; their own semantics are the core-control and host-map
cuts' business.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Metronome.Line

/-! ## Window slicing helpers

The specification spells a slice and an indexed bit exactly the way the
elaborated RTL does (`BitVec.truncate` of a shifted bus, `&&& 1` of a shifted
bus), so that the extracted transition and the specification are the same term
and the per-register proofs are definitional unfoldings rather than
bit-blasting.  The names below give them the SPEC_V2 meanings. -/

/-- Bits `start .. start+w-1` of a bus, the RTL's `v[start +: w]` and the SPEC's
window byte field. -/
def slice {n : Nat} (start w : Nat) (v : BitVec n) : BitVec w :=
  BitVec.truncate w (BitVec.ushiftRight v start)

/-- Bit `i` of a bound bus as a Boolean: the RTL's one-bit read `v[i]`. -/
def bitAt {n : Nat} (i : Nat) (v : BitVec n) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight v i)) != 0)

/-- The indexed bit selection `v[i]` of a whole input bus (the RTL's `$shiftx`
of `PINS` selectors into `lvl`/`rise`/`fall`/`LUT*`). -/
def sel {n : Nat} (i : Nat) (v : BitVec n) : Bool :=
  (((BitVec.ushiftRight v i) &&& (1 : BitVec n)) != 0)

/-- Pack three independent bits, most significant first (`{b2, b1, b0}`). -/
def pack3 (b2 b1 b0 : Bool) : BitVec 3 :=
  ((if b2 then (1 : BitVec 1) else 0) ++ (if b1 then (1 : BitVec 1) else 0)) ++
    (if b0 then (1 : BitVec 1) else 0)

/-- Pack four independent bits, most significant first. -/
def pack4 (b3 b2 b1 b0 : Bool) : BitVec 4 :=
  (((if b3 then (1 : BitVec 1) else 0) ++ (if b2 then (1 : BitVec 1) else 0)) ++
    (if b1 then (1 : BitVec 1) else 0)) ++ (if b0 then (1 : BitVec 1) else 0)

/-- Repacking the three bits of a 3-bit bus gives the bus back. -/
theorem pack3_bits (v : BitVec 3) : pack3 (bitAt 2 v) (bitAt 1 v) (bitAt 0 v) = v := by
  simp [pack3, bitAt]
  bv_decide

/-- Repacking the four bits of a 4-bit bus gives the bus back. -/
theorem pack4_bits (v : BitVec 4) : pack4 (bitAt 3 v) (bitAt 2 v) (bitAt 1 v) (bitAt 0 v) = v := by
  simp [pack4, bitAt]
  bv_decide

/-- Three clear bits pack to zero. -/
theorem pack3_false : pack3 false false false = (0 : BitVec 3) := by decide

/-- Selecting a bit of the zero bus gives `false`. -/
theorem sel_zero (i : Nat) : sel i (0 : BitVec 3) = false := by
  simp [sel]

/-- Any bit of the zero bus is clear. -/
theorem bitAt_zero {n : Nat} (i : Nat) : bitAt i (0 : BitVec n) = false := by
  simp [bitAt]

/-- Any bit of the three-bit zero bus is clear (the tap-bit vector case). -/
theorem bitAt_zero3 (i : Nat) : bitAt i (BitVec.ofNat 3 0) = false := by
  simp [bitAt]

/-- Yosys lowers `x = d; if (b) x = e;` to `b ? (b ? e : 0) : d`. -/
theorem ite_ite_zero {w : Nat} (b : Bool) (x y : BitVec w) :
    (if b then (if b then x else 0) else y) = if b then x else y := by
  cases b <;> rfl

/-- The one-bit form of `ite_ite_zero`. -/
theorem ite_ite_false (b : Bool) (x y : Bool) :
    (if b then (if b then x else false) else y) = if b then x else y := by
  cases b <;> rfl

/-! ## §3.1 Configuration

The 32-byte window of `machine.LINE_REGS`: `INC MOD T0 T1 T2 PRE WLO WHI`
(2 bytes each), `EDGE` (pin 3:0, polarity 5:4, `WEN` 6, `FOLLOW` 7), `T0EDGE`
(pin 3:0, polarity 5:4, `T0SRC` 6), `PINS` (`PINA` 3:0, `PINB` 7:4), `SNAP`
(1:0), `LUT0`/`LUT1` (4 bytes each) and `HOLD` (`HPIN` 3:0, `HLVL` 4, `HTAP`
6:5, `HEN` 7). -/

structure Config where
  /-- Phase increment per cycle. -/
  inc : BitVec 16
  /-- Phase modulus. -/
  mod : BitVec 16
  /-- Phase tap 0. -/
  t0 : BitVec 16
  /-- Phase tap 1. -/
  t1 : BitVec 16
  /-- Phase tap 2. -/
  t2 : BitVec 16
  /-- Phase loaded on a start or an accepted edge. -/
  pre : BitVec 16
  /-- Accepted-edge window low. -/
  wlo : BitVec 16
  /-- Accepted-edge window high. -/
  whi : BitVec 16
  /-- `{FOLLOW, WEN, polarity, pin}` of the boundary edge. -/
  edge : BitVec 8
  /-- `{T0SRC, polarity, pin}` of the edge-sourced tap 0. -/
  t0edge : BitVec 8
  /-- `{PINB, PINA}` capture pin selects. -/
  pins : BitVec 8
  /-- Snapshot point: 0..2 tap `k`, 3 the boundary. -/
  snap : BitVec 2
  /-- Input symbol table 0, indexed by `{REM, SN}`. -/
  lut0 : BitVec 32
  /-- Input symbol table 1. -/
  lut1 : BitVec 32
  /-- Hold: `{HEN, HTAP, HLVL, HPIN}`. -/
  hold : BitVec 8
  deriving DecidableEq, Repr

/-- `EDGE.pin` (§3.1). -/
def Config.edgePin (c : Config) : BitVec 4 := slice 0 4 c.edge

/-- `EDGE.polarity`: 0 none, 1 rise, 2 fall, 3 both. -/
def Config.edgePol (c : Config) : BitVec 2 := slice 4 2 c.edge

/-- `EDGE.WEN`: the accepted edge is windowed by `WLO..WHI`. -/
def Config.wen (c : Config) : Bool := bitAt 6 c.edge

/-- `EDGE.FOLLOW`: the boundary is an accepted edge (§3.3). -/
def Config.follow (c : Config) : Bool := bitAt 7 c.edge

/-- `T0EDGE.pin`. -/
def Config.t0Pin (c : Config) : BitVec 4 := slice 0 4 c.t0edge

/-- `T0EDGE.polarity`. -/
def Config.t0Pol (c : Config) : BitVec 2 := slice 4 2 c.t0edge

/-- `T0EDGE.T0SRC`: tap 0 fires on the edge `e0`, not at phase `T0`. -/
def Config.t0src (c : Config) : Bool := bitAt 6 c.t0edge

/-- `PINS.PINA`: the capture pin for `A0`, `A1`, `A2` and the `LIVE` input. -/
def Config.pinaSel (c : Config) : BitVec 4 := slice 0 4 c.pins

/-- `PINS.PINB`: the capture pin for `B1`. -/
def Config.pinbSel (c : Config) : BitVec 4 := slice 4 4 c.pins

/-- `HOLD.HPIN`: the pin a hold watches. -/
def Config.hpin (c : Config) : BitVec 4 := slice 0 4 c.hold

/-- `HOLD.HLVL`: the level a hold waits for. -/
def Config.hlvl (c : Config) : Bool := bitAt 4 c.hold

/-- `HOLD.HTAP`: the phase tap a hold stalls before. -/
def Config.htap (c : Config) : BitVec 2 := slice 5 2 c.hold

/-- `HOLD.HEN`: hold enable. -/
def Config.hen (c : Config) : Bool := bitAt 7 c.hold

/-! ## Sampled inputs

Everything that is not line state is a per-cycle sampled input.  The move
bundle (`ctl_*`, `sym_*`), the host-write enables and data (`h_*`), the
synchronised pin levels and edges (`lvl`, `rise`, `fall`) and the freeze flag
`frz` come from the chip top; the move pick and the host-map enable decode are
outside this cut (`line_check.py` checks their wiring, not their equations). -/

structure Input where
  /-- Synchronous reset, low asserted (`rst_q`). -/
  resetN : Bool
  /-- Frozen cycle (SPEC §12.3). -/
  frz : Bool
  /-- This line's configuration window. -/
  cfg : Config
  /-- Synchronised pin levels `P0..P12`; selects 13..15 read 0. -/
  lvl : BitVec 16
  /-- Synchronised rising edges. -/
  rise : BitVec 16
  /-- Synchronised falling edges. -/
  fall : BitVec 16
  /-- The winning move targets `Lk.CTL`. -/
  ctlWe : Bool
  /-- `Lk.CTL` bus: `{1'b0, REN, ARM, RUN}`. -/
  ctlD : BitVec 3
  /-- The winning move targets this line's `L.SYM`/`L.DBIT`/`L.XOR` group. -/
  symWe : Bool
  /-- `0` SYM, `1` DBIT, `2` XOR; `3` follows the RTL default (XOR). -/
  symOp : BitVec 2
  /-- The symbol write data. -/
  symD : BitVec 4
  /-- Host write of `PHASE` byte 0 (bit 0) or byte 1 (bit 1). -/
  phWe : BitVec 2
  /-- Host write of `CTL`. -/
  hCtlWe : Bool
  /-- Host write of `STAT`. -/
  hStatWe : Bool
  /-- Host write data. -/
  hD : BitVec 8
  deriving DecidableEq, Repr

/-! ## §3.1 State

`PH` (16); `RUN`, `ARM`, `REN`; `HELD`; `FIRST`; `SC`, `SP`; `FIRED[2:0]`; the
working samples `W = {B1, A2, A1, A0}`; snapshot `SN` (4); remembered bit
`REM`; `STAGED`, `COMMITTED` (4 each); sticky `TAPMISS`. -/

structure State where
  /-- Phase accumulator. -/
  ph : BitVec 16
  /-- The line runs. -/
  run : Bool
  /-- Armed for a start edge. -/
  arm : Bool
  /-- Accepted edges are enabled. -/
  ren : Bool
  /-- `HELD`: the previous cycle stalled on a hold. -/
  held : Bool
  /-- `FIRST`: the starting beat is partial (§3.4, D28). -/
  first : Bool
  /-- `SC`: boundary seen since the last accepted edge. -/
  sc : Bool
  /-- `SP`: `SYNC`, the sampled boundary. -/
  sp : Bool
  /-- `FIRED[k]`: tap `k` already fired in this beat. -/
  fired : BitVec 3
  /-- Working samples `{B1, A2, A1, A0}`. -/
  w : BitVec 4
  /-- Snapshot `{B1, A2, A1, A0}`. -/
  sn : BitVec 4
  /-- Remembered bit: table output 1 of the previous snapshot. -/
  rem : Bool
  /-- Staged output symbol. -/
  staged : BitVec 4
  /-- Committed output symbol. -/
  committed : BitVec 4
  /-- Sticky tap-miss flag. -/
  tapmiss : Bool
  deriving DecidableEq, Repr

/-- The state a sampled reset edge leaves (the RTL's reset branch). -/
def resetState : State :=
  ⟨0, false, false, false, false, false, false, false, 0, 0, 0, false, 0, 0, false⟩

/-! ## §3.2 Beat generator -/

/-- Polarity-selected edge of one pin: `0` none, `1` rise, `2` fall, `3` both
(§3.1 `EDGE`/`T0EDGE`).  A select `>= 13` reads the zero high bits of
`rise`/`fall`, as `project.v` ties them.  The branches are written in the
elaborated `case` order (`3, 2, 1`, default), which is the same function as the
SPEC's polarity table. -/
def esel (pin : BitVec 4) (pol : BitVec 2) (rise fall : BitVec 16) : Bool :=
  if pol == (3 : BitVec 2) then (sel pin.toNat rise || sel pin.toNat fall)
  else if pol == (2 : BitVec 2) then sel pin.toNat fall
  else if pol == (1 : BitVec 2) then sel pin.toNat rise
  else false

/-- `edge`: the boundary edge of §3.2; a frozen cycle has no edge (§12.3). -/
def edge (_s : State) (i : Input) : Bool :=
  esel i.cfg.edgePin i.cfg.edgePol i.rise i.fall && !i.frz

/-- `e0`: the edge-sourced tap 0 of §3.3, also suppressed by a freeze. -/
def e0 (_s : State) (i : Input) : Bool :=
  esel i.cfg.t0Pin i.cfg.t0Pol i.rise i.fall && !i.frz

/-- A frozen line does not advance (§12.3): `runa = RUN && !frz`. -/
def runa (s : State) (i : Input) : Bool := s.run && !i.frz

/-- `inwin`: `WLO <= PH <= WHI`, or its wrap-around form when `WHI < WLO`. -/
def inwin (s : State) (i : Input) : Bool :=
  if decide (i.cfg.wlo <= i.cfg.whi) then (i.cfg.wlo <= s.ph && s.ph <= i.cfg.whi)
  else (s.ph >= i.cfg.wlo || s.ph <= i.cfg.whi)

/-- `start`: an armed line starts on its edge. -/
def start (s : State) (i : Input) : Bool := edge s i && s.arm && !s.run

/-- `accept`: a running line with `REN` accepts its edge (inside the window when
`WEN`). -/
def accept (s : State) (i : Input) : Bool :=
  edge s i && s.run && s.ren && (!i.cfg.wen || inwin s i)

/-- The 17-bit phase sum `n = PH + INC`. -/
def sum17 (s : State) (i : Input) : BitVec 17 :=
  ((0 : BitVec 1) ++ slice 0 16 s.ph) + ((0 : BitVec 1) ++ slice 0 16 i.cfg.inc)

/-- `n >= MOD`. -/
def over (s : State) (i : Input) : Bool :=
  sum17 s i >= ((0 : BitVec 1) ++ slice 0 16 i.cfg.mod)

/-- `n - MOD` (17-bit), the wrapped phase before truncation. -/
def nxw (s : State) (i : Input) : BitVec 17 :=
  sum17 s i - ((0 : BitVec 1) ++ slice 0 16 i.cfg.mod)

/-- `nx`: the phase after one advance, modulo `MOD`. -/
def nx (s : State) (i : Input) : BitVec 16 :=
  if over s i then slice 0 16 (nxw s i) else slice 0 16 (sum17 s i)

/-- `crossing`: the advance `p -> x` of this cycle crosses the phase tap `t`
(§3.4, without the `adv` term; §3.2a evaluates it with `adv = 1`). -/
def crossing (t p x : BitVec 16) (o : Bool) : Bool :=
  if o then (t > p || t <= x) else (p < t && t <= x)

/-- `T0 < MOD`: tap 0 is enabled as a phase tap. -/
def tlt0 (_s : State) (i : Input) : Bool := i.cfg.t0 < i.cfg.mod

/-- `T1 < MOD`: tap 1 is enabled. -/
def tlt1 (_s : State) (i : Input) : Bool := i.cfg.t1 < i.cfg.mod

/-- `T2 < MOD`: tap 2 is enabled. -/
def tlt2 (_s : State) (i : Input) : Bool := i.cfg.t2 < i.cfg.mod

/-- The phase tap a hold stalls before (`HTAP`). -/
def holdTap (i : Input) : BitVec 16 :=
  if i.cfg.htap == 0 then i.cfg.t0 else if i.cfg.htap == 1 then i.cfg.t1 else i.cfg.t2

/-- `HTAP` names an enabled phase tap: not `3`, and not `0` with `T0SRC`. -/
def holdTok (s : State) (i : Input) : Bool :=
  (i.cfg.htap != 3) && !((i.cfg.htap == 0) && i.cfg.t0src) &&
    (if i.cfg.htap == 0 then tlt0 s i else if i.cfg.htap == 1 then tlt1 s i
      else tlt2 s i)

/-- `hold`: the line stalls its phase until the pin reads `HLVL`. -/
def hold (s : State) (i : Input) : Bool :=
  i.cfg.hen && runa s i && !accept s i && holdTok s i &&
    crossing (holdTap i) s.ph (nx s i) (over s i) &&
    (sel (Config.hpin i.cfg).toNat i.lvl != i.cfg.hlvl)

/-- `adv`: the generator advances this cycle.  `hold` is §3.2a. -/
def adv (s : State) (i : Input) : Bool := runa s i && !accept s i && !hold s i

/-- `wrap`: an advancing cycle that reaches `MOD`, the `FOLLOW = 0` boundary. -/
def wrap (s : State) (i : Input) : Bool := adv s i && over s i

/-- `BEAT`: the line's boundary.  `FOLLOW = 1` takes the accepted edge, else the
phase wrap (§3.2, §3.3). -/
def beat (s : State) (i : Input) : Bool := if i.cfg.follow then accept s i else wrap s i

/-! ## §3.4 Taps, fired bits and `TAPMISS` -/

/-- `cross_0` for a phase-sourced tap 0: `adv && T0 < MOD && cross`. -/
def tapCross0 (s : State) (i : Input) : Bool :=
  adv s i && tlt0 s i && crossing i.cfg.t0 s.ph (nx s i) (over s i)

/-- `cross_1`. -/
def tapCross1 (s : State) (i : Input) : Bool :=
  adv s i && tlt1 s i && crossing i.cfg.t1 s.ph (nx s i) (over s i)

/-- `cross_2`. -/
def tapCross2 (s : State) (i : Input) : Bool :=
  adv s i && tlt2 s i && crossing i.cfg.t2 s.ph (nx s i) (over s i)

/-- `cross_0`: the edge `e0` when tap 0 is edge-sourced, else the phase cross. -/
def cross0 (s : State) (i : Input) : Bool :=
  if i.cfg.t0src then (s.run && e0 s i) else tapCross0 s i

/-- `next_0`: a tap-0 event that belongs to the beat starting at this boundary. -/
def next0 (s : State) (i : Input) : Bool :=
  if i.cfg.t0src then (s.run && e0 s i && beat s i)
  else (tapCross0 s i && beat s i && over s i && (i.cfg.t0 <= nx s i))

/-- `next_1`. -/
def next1 (s : State) (i : Input) : Bool :=
  tapCross1 s i && beat s i && over s i && (i.cfg.t1 <= nx s i)

/-- `next_2`. -/
def next2 (s : State) (i : Input) : Bool :=
  tapCross2 s i && beat s i && over s i && (i.cfg.t2 <= nx s i)

/-- `cur_0 = cross_0 && !next_0`. -/
def cur0 (s : State) (i : Input) : Bool := cross0 s i && !next0 s i

/-- `cur_1`. -/
def cur1 (s : State) (i : Input) : Bool := tapCross1 s i && !next1 s i

/-- `cur_2`. -/
def cur2 (s : State) (i : Input) : Bool := tapCross2 s i && !next2 s i

/-- The three `cross_k` bits, `k = 2,1,0` most significant first. -/
def crossBits (s : State) (i : Input) : BitVec 3 :=
  pack3 (tapCross2 s i) (tapCross1 s i) (cross0 s i)

/-- The three `next_k` bits. -/
def nextBits (s : State) (i : Input) : BitVec 3 := pack3 (next2 s i) (next1 s i) (next0 s i)

/-- `cur_k = cross_k && !next_k`, as the three-bit vector the RTL keeps. -/
def curBits (s : State) (i : Input) : BitVec 3 := pack3 (cur2 s i) (cur1 s i) (cur0 s i)

/-- `TAP0`: a current-beat event drops once `FIRED[0]` is set; a next-beat
event is not dropped. -/
def tap0 (s : State) (i : Input) : Bool := (cur0 s i && !bitAt 0 s.fired) || next0 s i

/-- `TAP1`. -/
def tap1 (s : State) (i : Input) : Bool := (cur1 s i && !bitAt 1 s.fired) || next1 s i

/-- `TAP2`. -/
def tap2 (s : State) (i : Input) : Bool := (cur2 s i && !bitAt 2 s.fired) || next2 s i

/-- `en_k`: tap 0 is enabled if `T0 < MOD`, or, edge-sourced, if
`T0EDGE.polarity != 0`; taps 1 and 2 are enabled if `Tk < MOD`. -/
def enBits (s : State) (i : Input) : BitVec 3 :=
  pack3 (tlt2 s i) (tlt1 s i)
    (if i.cfg.t0src then (i.cfg.t0Pol != (0 : BitVec 2)) else tlt0 s i)

/-- `{2'b11, ~(T0SRC && FIRST)}`: an edge-sourced tap 0 of the starting beat is
not a miss (D28). -/
def missOk (s : State) (i : Input) : BitVec 3 :=
  pack3 true true (!(i.cfg.t0src && s.first))

/-- `en_k && !FIRED[k] && !cur_k && miss_ok`. -/
def missBits (s : State) (i : Input) : BitVec 3 :=
  ((enBits s i &&& ~~~s.fired) &&& ~~~curBits s i) &&& missOk s i

/-- `TAPMISS`: a boundary with an enabled, unfired, not-current beat tap. -/
def missEv (s : State) (i : Input) : Bool := beat s i && (missBits s i != 0)

/-- `FIRED'`: a boundary loads the next-beat events, otherwise the current-beat
events are ORed in. -/
def firedNext (s : State) (i : Input) : BitVec 3 :=
  if beat s i then nextBits s i else s.fired ||| curBits s i

/-- `SEG = popcount(FIRED)` (§3.4). -/
def seg (s : State) : BitVec 2 :=
  (((0 : BitVec 1) ++ slice 0 1 s.fired) + ((0 : BitVec 1) ++ slice 1 1 s.fired)) +
    ((0 : BitVec 1) ++ slice 2 1 s.fired)

/-! ## §3.5 Capture, snapshot and input symbol -/

/-- The `LIVE` input pin of §12.1: `PINA` of this line. -/
def pina (i : Input) : Bool := sel (Config.pinaSel i.cfg).toNat i.lvl

/-- The second `LIVE` input pin of §12.1: `PINB` of this line. -/
def pinb (i : Input) : Bool := sel (Config.pinbSel i.cfg).toNat i.lvl

/-- The rising edge of the `PINA` pin (§8/§12.1 edge readback). -/
def pinaRise (i : Input) : Bool := sel (Config.pinaSel i.cfg).toNat i.rise

/-- The falling edge of the `PINA` pin. -/
def pinaFall (i : Input) : Bool := sel (Config.pinaSel i.cfg).toNat i.fall

/-- The working samples after this cycle's captures: `TAP0: A0 = pa`,
`TAP1: A1 = pa, B1 = pb`, `TAP2: A2 = pa`. -/
def wNext (s : State) (i : Input) : BitVec 4 :=
  pack4 (if tap1 s i then pinb i else bitAt 3 s.w)
    (if tap2 s i then pina i else bitAt 2 s.w)
    (if tap1 s i then pina i else bitAt 1 s.w)
    (if tap0 s i then pina i else bitAt 0 s.w)

/-- The three tap outputs, `k = 2,1,0` most significant first. -/
def tap (s : State) (i : Input) : BitVec 3 := pack3 (tap2 s i) (tap1 s i) (tap0 s i)

/-- `snap = (SNAP == 3) ? BEAT : TAP[SNAP]`. -/
def snap (s : State) (i : Input) : Bool :=
  if i.cfg.snap == 3 then beat s i else sel i.cfg.snap.toNat (tap s i)

/-- `{REM, SN}` (`L.CAP`). -/
def cap (s : State) : BitVec 5 := (if s.rem then (1 : BitVec 1) else 0) ++ slice 0 4 s.sn

/-- `IN = {LUT1[{REM,SN}], LUT0[{REM,SN}]}`. -/
def inSym (s : State) (i : Input) : BitVec 2 :=
  (if sel (cap s).toNat i.cfg.lut1 then (1 : BitVec 1) else 0) ++
    (if sel (cap s).toNat i.cfg.lut0 then (1 : BitVec 1) else 0)

/-! ## §3.6 Output symbol and commit -/

/-- `STAGED'`: the winning write of the line's symbol group.  `op = 3` is not
produced by `project.v`'s decode and follows the RTL `case` default (XOR). -/
def stagedNext (s : State) (i : Input) : BitVec 4 :=
  if i.symWe then
    (if i.symOp == (1 : BitVec 2) then (slice 1 3 s.staged ++ slice 0 1 i.symD)
     else if i.symOp == (0 : BitVec 2) then i.symD
     else s.staged ^^^ i.symD)
  else s.staged

/-! ## Precedence: generator, move, host write -/

/-- `PH'` before the host `PHASE` bytes: `PRE` on a start/accept, `nx` on an
advance, hold otherwise. -/
def phC (s : State) (i : Input) : BitVec 16 :=
  if start s i || accept s i then i.cfg.pre else if adv s i then nx s i else s.ph

/-- `PH'` after the host `PHASE` byte writes (both bytes win over moves and the
generator). -/
def phF (s : State) (i : Input) : BitVec 16 :=
  if bitAt 0 i.phWe then (slice 8 8 (phC s i) ++ i.hD)
  else if bitAt 1 i.phWe then (i.hD ++ slice 0 8 (phC s i))
  else phC s i

/-- `RUN'` before the host `CTL` write. -/
def runC (s : State) (i : Input) : Bool :=
  if i.ctlWe then bitAt 0 i.ctlD else (s.run || start s i)

/-- `ARM'` before the host `CTL` write. -/
def armC (s : State) (i : Input) : Bool :=
  if i.ctlWe then bitAt 1 i.ctlD else (s.arm && !start s i)

/-- `REN'` before the host `CTL` write. -/
def renC (s : State) (i : Input) : Bool := if i.ctlWe then bitAt 2 i.ctlD else s.ren

/-- `RUN'` after the host `CTL` write. -/
def runF (s : State) (i : Input) : Bool := if i.hCtlWe then bitAt 0 i.hD else runC s i

/-- `ARM'` after the host `CTL` write. -/
def armF (s : State) (i : Input) : Bool := if i.hCtlWe then bitAt 1 i.hD else armC s i

/-- `REN'` after the host `CTL` write. -/
def renF (s : State) (i : Input) : Bool := if i.hCtlWe then bitAt 2 i.hD else renC s i

/-- `RUN' && !RUN` after the host and move priority: the line starts, by an
edge, a move or a host write (§3.2, §3.6). -/
def starting (s : State) (i : Input) : Bool := runF s i && !s.run

/-- The starting phase's fired bits: enabled phase taps at or behind `PH'`.  Tap
0 is not a phase tap when edge-sourced (§3.4, D28). -/
def startBits (s : State) (i : Input) : BitVec 3 :=
  pack3 (tlt2 s i && (i.cfg.t2 <= phF s i)) (tlt1 s i && (i.cfg.t1 <= phF s i))
    (!i.cfg.t0src && tlt0 s i && (i.cfg.t0 <= phF s i))

/-- `COMMITTED' = STAGED'` on a boundary or a line start (§3.6; the start commit
lets a follower present its first bit before its first edge, D28). -/
def committedNext (s : State) (i : Input) : BitVec 4 :=
  if beat s i || starting s i then stagedNext s i else s.committed

/-- `SC'`. -/
def scNext (s : State) (i : Input) : Bool :=
  if i.cfg.follow then false
  else if accept s i then true else if beat s i then false else s.sc

/-- `SP'` (`SYNC`). -/
def spNext (s : State) (i : Input) : Bool :=
  if i.cfg.follow then (if beat s i then true else if wrap s i then false else s.sp)
  else if beat s i then s.sc else s.sp

/-- The line's transition: one sampled rising edge. -/
def step (s : State) (i : Input) : State :=
  { ph := if i.resetN then phF s i else 0
    run := if i.resetN then runF s i else false
    arm := if i.resetN then armF s i else false
    ren := if i.resetN then renF s i else false
    held := if i.resetN then (if i.frz then s.held else hold s i) else false
    first := if i.resetN then (starting s i || (s.first && !beat s i)) else false
    sc := if i.resetN then scNext s i else false
    sp := if i.resetN then spNext s i else false
    fired := if i.resetN then (if starting s i then startBits s i else firedNext s i) else 0
    w := if i.resetN then wNext s i else 0
    sn := if i.resetN then (if snap s i then wNext s i else s.sn) else 0
    rem := if i.resetN then (if snap s i then sel (cap s).toNat i.cfg.lut1 else s.rem) else false
    staged := if i.resetN then stagedNext s i else 0
    committed := if i.resetN then committedNext s i else 0
    tapmiss := if i.resetN then
      (missEv s i || (s.tapmiss && !(i.hStatWe && bitAt 0 i.hD))) else false }

/-! ## One-step consequences -/

/-- A sampled reset edge leaves `resetState`, whatever the prior values. -/
theorem reset_step (s : State) (i : Input) (h : i.resetN = false) : step s i = resetState := by
  simp [step, resetState, h]

/-- A frozen cycle with no move, no host write and `FOLLOW = 0` keeps the line
state: no edge, no advance, and `HELD` holds (§12.3).

In follower mode `SC' = 0` unconditionally (§3.3), so `SC` is the one register a
frozen cycle may change; that is the specification's own rule, not an RTL
difference (the RTL clears `SC` in a frozen follower cycle too). -/
theorem frz_step_holds (s : State) (i : Input) (hreset : i.resetN = true)
    (hfrz : i.frz = true) (hfollow : i.cfg.follow = false) (hctl : i.ctlWe = false)
    (hsym : i.symWe = false) (hph : i.phWe = 0) (hhctl : i.hCtlWe = false)
    (hhstat : i.hStatWe = false) : step s i = s := by
  have h0 : bitAt 0 i.phWe = false := by rw [hph]; decide
  have h1 : bitAt 1 i.phWe = false := by rw [hph]; decide
  have htap0 : tap0 s i = false := by
    simp [tap0, cur0, cur1, cur2, cross0, tapCross0,
      tapCross1, tapCross2, next0, next1, next2, tlt0, tlt1, tlt2, adv, runa,
      accept, e0, edge, esel, hfrz, pack3_false, bitAt_zero3]
  have htap1 : tap1 s i = false := by
    simp [tap1, cur0, cur1, cur2, cross0, tapCross0,
      tapCross1, tapCross2, next0, next1, next2, tlt0, tlt1, tlt2, adv, runa,
      accept, e0, edge, esel, hfrz, pack3_false, bitAt_zero3]
  have htap2 : tap2 s i = false := by
    simp [tap2, cur0, cur1, cur2, cross0, tapCross0,
      tapCross1, tapCross2, next0, next1, next2, tlt0, tlt1, tlt2, adv, runa,
      accept, e0, edge, esel, hfrz, pack3_false, bitAt_zero3]
  have hcross : crossBits s i = 0 := by
    simp [crossBits, cross0, tapCross0, tapCross1, tapCross2, adv, runa, e0, esel,
      hfrz, pack3_false]
  have hcur : curBits s i = 0 := by
    simp [curBits, cur0, cur1, cur2, cross0, tapCross0, tapCross1, tapCross2,
      next0, next1, next2, adv, runa, e0, esel, hfrz, pack3_false]
  have htap : tap s i = 0 := by rw [tap, htap0, htap1, htap2, pack3_false]
  have hsel : sel i.cfg.snap.toNat (0 : BitVec 3) = false := sel_zero _
  have hsnap : snap s i = false := by
    rw [snap]
    split
    · simp [beat, wrap, adv, runa, accept, edge, esel, hfrz, hfollow]
    · rw [htap]
      exact hsel
  have hw : wNext s i = s.w := by
    simp [wNext, htap0, htap1, htap2, pack4_bits]
  simp [step, hreset, hfrz, hfollow, hctl, hsym, h0, h1, hhctl, hhstat, hcur, hsnap, hw, beat, wrap, adv, runa, accept, start, edge, esel, missEv, firedNext,
    committedNext, stagedNext, scNext, spNext, phF, phC, runF, runC, armF, armC, renF,
    renC, starting]

/-- A frozen follower cycle clears `SC` and nothing else (§3.3). -/
theorem frz_follow_sc (s : State) (i : Input) (hreset : i.resetN = true)
    (hfollow : i.cfg.follow = true) : (step s i).sc = false := by
  simp [step, hreset, scNext, hfollow]

/-- The host `CTL` write wins over a move and over the generator. -/
theorem host_ctl_wins (s : State) (i : Input) (hreset : i.resetN = true)
    (h : i.hCtlWe = true) :
    (step s i).run = bitAt 0 i.hD ∧ (step s i).arm = bitAt 1 i.hD ∧
      (step s i).ren = bitAt 2 i.hD := by
  simp [step, runF, armF, renF, h, hreset]

/-- A move to `Lk.CTL` wins over the generator when no host write targets `CTL`. -/
theorem move_ctl_wins (s : State) (i : Input) (hreset : i.resetN = true)
    (hmove : i.ctlWe = true) (hhost : i.hCtlWe = false) :
    (step s i).run = bitAt 0 i.ctlD ∧ (step s i).arm = bitAt 1 i.ctlD ∧
      (step s i).ren = bitAt 2 i.ctlD := by
  simp [step, runF, runC, armF, armC, renF, renC, hmove, hhost, hreset]

/-- The generator's `RUN' = RUN || start` when neither a move nor a host write
sets `CTL`. -/
theorem run_generator (s : State) (i : Input) (hreset : i.resetN = true)
    (hmove : i.ctlWe = false) (hhost : i.hCtlWe = false) :
    (step s i).run = (s.run || start s i) := by
  simp [step, runF, runC, hmove, hhost, hreset]

/-- A host `PHASE` byte write wins over the generator and over a move. -/
theorem host_phase_wins (s : State) (i : Input) (hreset : i.resetN = true)
    (h : bitAt 0 i.phWe = true) :
    (step s i).ph = slice 8 8 (phC s i) ++ i.hD := by
  simp [step, phF, h, hreset]

/-- With `FOLLOW = 0` the boundary is exactly the phase wrap (§3.2). -/
theorem beat_eq_wrap (s : State) (i : Input) (h : i.cfg.follow = false) :
    beat s i = wrap s i := by
  simp [beat, h]

/-- An advancing `FOLLOW = 0` cycle beats exactly when `PH + INC >= MOD`. -/
theorem beat_of_advance (s : State) (i : Input) (h : i.cfg.follow = false)
    (hadv : adv s i = true) : beat s i = over s i := by
  simp [beat, wrap, hadv, h]

/-- The line start commits the staged symbol and marks the starting beat
(§3.4, §3.6, D28). -/
theorem start_commits (s : State) (i : Input) (hreset : i.resetN = true)
    (h : starting s i = true) :
    (step s i).committed = (step s i).staged ∧ (step s i).first = true ∧
      (step s i).fired = startBits s i := by
  simp [step, committedNext, h, hreset]

/-- A boundary commits the staged symbol in the same cycle (§3.6). -/
theorem beat_commits (s : State) (i : Input) (hreset : i.resetN = true)
    (h : beat s i = true) (hstart : starting s i = false) :
    (step s i).committed = (step s i).staged := by
  simp [step, committedNext, h, hstart, hreset]

/-! ## Traces -/

/-- The register state during cycle `n`: after `n` sampled edges. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- A sampled reset edge at cycle 0 leaves the reset state. -/
theorem stateAt_one_reset (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) : stateAt inputs initial 1 = resetState := by
  rw [stateAt_succ]
  exact reset_step initial (inputs 0) reset

/-- A frozen cycle with no move and no host write leaves the state unchanged on
the real trace, so deleting it gives the same state sequence (§12.3 for this
line). -/
theorem trace_frz_holds (inputs : Nat → Input) (initial : State) (n : Nat)
    (hreset : (inputs n).resetN = true) (hfrz : (inputs n).frz = true)
    (hfollow : (inputs n).cfg.follow = false) (hctl : (inputs n).ctlWe = false)
    (hsym : (inputs n).symWe = false) (hph : (inputs n).phWe = 0)
    (hhctl : (inputs n).hCtlWe = false) (hhstat : (inputs n).hStatWe = false) :
    stateAt inputs initial (n + 1) = stateAt inputs initial n := by
  rw [stateAt_succ]
  exact frz_step_holds _ _ hreset hfrz hfollow hctl hsym hph hhctl hhstat

end Metronome.Line
