import Metronome.Machine.Tables
import Metronome.Machine.Basic

/-!
§1 Configuration: the host-written, program-invisible state of `machine.CONFIG_BLOCKS`, held in latches.

It is modelled as the byte image of the configuration part of the host map (blocks LINE, THREAD, LFSR, STREAM, OUT,
addresses `LINE_BASE .. OUT_BASE + 14*0x10 - 1`). Each field is decoded from the bytes and bit positions that the
host map (ISA_TABLES_V2 "Host address map") gives it. Bits that no field uses are stored but never read.
-/

namespace Metronome.Machine

open Util Tables

/-- §1 Configuration latch bank, as the byte image of the configuration registers of the host map (§9 "Host map",
offset `a - LINE_BASE`). -/
structure Config where
  img : ByteArray

namespace Util
/-- Size of the configuration byte image (LINE_BASE .. end of the OUT block). -/
def cfgSize : Nat := OUT_BASE + N_OUT_PINS * STRIDE_OUT - LINE_BASE
/-- Configuration byte at host address `a`. -/
@[inline] def cfgByte (c : Config) (a : Nat) : Nat := bget c.img (a - LINE_BASE)
/-- Little-endian configuration field of `w` bytes at host address `a`. -/
@[inline] def cfgLE (c : Config) (a w : Nat) : Nat := bgetLE c.img (a - LINE_BASE) w
/-- Names of the host blocks that hold configuration latches (`machine.CONFIG_BLOCKS`). -- AMBIG(5) `CTRL.DOORBELL`
and `SRT.CTL` have access W but are runtime registers, not configuration. -/
def cfgBlockNames : List String := ["LINE", "THREAD", "LFSR", "STREAM", "OUT"]
end Util

/-- §1 Power-on/reset value: configuration clears to 0. -/
def Config.zero : Config := ⟨bzero Util.cfgSize⟩

/-- §9 / §13.1 A host address holds configuration: a byte of a mapped register (access W) of a configuration block
(LINE, THREAD, LFSR, STREAM, OUT). -- AMBIG(4) OUT.OE of pins 8..13 is mapped but has no latch. -/
def Config.isCfgAddr (a : Nat) : Bool :=
  hostBlocks.any fun (name, base, stride, inst, regs) =>
    Util.cfgBlockNames.contains name &&
    (List.range inst).any fun i =>
      regs.any fun (off, _, bytes, acc) =>
        acc == "W" && base + stride * i + off ≤ a && a < base + stride * i + off + bytes

/-- §1 / §13.1 A performed configuration write: the latch byte at `a` takes `b` (only configuration addresses). -/
def Config.write (c : Config) (a b : Nat) : Config :=
  if Config.isCfgAddr a then ⟨bset c.img (a - LINE_BASE) b⟩ else c

/-- §3.1 Line configuration (decoded from LINE block registers, ISA_TABLES_V2 layouts). -/
structure LineCfg where
  inc : Nat
  mod : Nat
  t0 : Nat
  t1 : Nat
  t2 : Nat
  pre : Nat
  wlo : Nat
  whi : Nat
  edgePin : Nat
  edgePol : Nat
  wen : Bool
  follow : Bool
  t0Pin : Nat
  t0Pol : Nat
  t0src : Bool
  snap : Nat
  pina : Nat
  pinb : Nat
  lut0 : Nat
  lut1 : Nat
  hpin : Nat
  hlvl : Bool
  htap : Nat
  hen : Bool
deriving Repr, Inhabited

/-- §3.1 Decode line `l`'s configuration: `INC..WHI` 16 bits each; `EDGE` byte = pin 3:0, polarity 5:4, `WEN` bit 6,
`FOLLOW` bit 7; `T0EDGE` byte = pin 3:0, polarity 5:4, `T0SRC` bit 6; `PINS` = `PINA` 3:0, `PINB` 7:4; `SNAP` 1:0;
`LUT0`, `LUT1` 32 bits; §3.2a `HOLD` = `HPIN` 3:0, `HLVL` bit 4, `HTAP` 6:5, `HEN` bit 7. -/
def Config.line (c : Config) (l : Nat) : LineCfg :=
  let b := LINE_BASE + STRIDE_LINE * l
  let f16 (o : Nat) := cfgLE c (b + o) 2
  let edge := cfgByte c (b + LINE_EDGE)
  let t0e := cfgByte c (b + LINE_T0EDGE)
  let pins := cfgByte c (b + LINE_PINS)
  let hold := cfgByte c (b + LINE_HOLD)
  { inc := f16 LINE_INC, mod := f16 LINE_MOD, t0 := f16 LINE_T0, t1 := f16 LINE_T1, t2 := f16 LINE_T2,
    pre := f16 LINE_PRE, wlo := f16 LINE_WLO, whi := f16 LINE_WHI,
    edgePin := nbits edge 0 4, edgePol := nbits edge 4 2, wen := nbit edge 6, follow := nbit edge 7,
    t0Pin := nbits t0e 0 4, t0Pol := nbits t0e 4 2, t0src := nbit t0e 6,
    snap := nbits (cfgByte c (b + LINE_SNAP)) 0 2,
    pina := nbits pins 0 4, pinb := nbits pins 4 4,
    lut0 := cfgLE c (b + LINE_LUT0) 4, lut1 := cfgLE c (b + LINE_LUT1) 4,
    hpin := nbits hold 0 4, hlvl := nbit hold 4, htap := nbits hold 5 2, hen := nbit hold 7 }

/-- §4 Thread configuration. -/
structure ThreadCfg where
  core : Nat
  line : Nat
  trig : Nat
  w0c : Nat
  w1c : Nat
  w0h : Nat
  w1h : Nat
deriving Repr, Inhabited

/-- §4 Decode thread `t`'s configuration: `CFG` = `CORE` bit 0, `LINE` 2:1, `TRIG` 7:3; `W0C`, `W1C` bits 5:0;
`W0H`, `W1H` 8 bits. -/
def Config.thread (c : Config) (t : Nat) : ThreadCfg :=
  let b := THREAD_BASE + STRIDE_THREAD * t
  let cfg := cfgByte c (b + THREAD_CFG)
  { core := nbits cfg 0 1, line := nbits cfg 1 2, trig := nbits cfg 3 5,
    w0c := nbits (cfgByte c (b + THREAD_W0C)) 0 6, w1c := nbits (cfgByte c (b + THREAD_W1C)) 0 6,
    w0h := cfgByte c (b + THREAD_W0H), w1h := cfgByte c (b + THREAD_W1H) }

/-- §8 / §12.1 Output pin configuration. -/
structure OutCfg where
  line : Nat
  bound : Bool
  live : Nat
  sel0 : Nat
  sel1 : Nat
  sel2 : Nat
  lut : Nat
  oe : Nat
deriving Repr, Inhabited

/-- §8 / §12.1 Decode output pin `o`: `BIND` = `LINE` 1:0, `BOUND` bit 2, `LIVE` 4:3; `SEL` = `SEL0` 1:0, `SEL1` 3:2,
`SEL2` 5:4; `LUT` 32 bits; `OE` 32 bits for o < 8 (0 otherwise). -/
def Config.out (c : Config) (o : Nat) : OutCfg :=
  let b := OUT_BASE + STRIDE_OUT * o
  let bind := cfgByte c (b + OUT_BIND)
  let sel := cfgByte c (b + OUT_SEL)
  { line := nbits bind 0 2, bound := nbit bind 2, live := nbits bind 3 2,
    sel0 := nbits sel 0 2, sel1 := nbits sel 2 2, sel2 := nbits sel 4 2,
    lut := cfgLE c (b + OUT_LUT) 4,
    oe := if o < N_OE_PINS then cfgLE c (b + OUT_OE) 4 else 0 }

/-- §6.3 Stream configuration. -/
structure StreamCfg where
  rx : Bool
  msb : Bool
  start : Nat
  len : Nat
  mark : Nat
deriving Repr, Inhabited

/-- §6.3 Decode stream `k`: `MODE` bit 0 (1 receive), bit 1 `MSB`; `START` bits 10:0; `LEN`, `MARK` bits 11:0. -/
def Config.stream (c : Config) (k : Nat) : StreamCfg :=
  let b := STREAM_BASE + STRIDE_STREAM * k
  let m := cfgByte c (b + STREAM_MODE)
  { rx := nbit m 0, msb := nbit m 1,
    start := nbits (cfgLE c (b + STREAM_START) 2) 0 STREAM_ADDR_BITS,
    len := nbits (cfgLE c (b + STREAM_LEN) 2) 0 STREAM_LEN_BITS,
    mark := nbits (cfgLE c (b + STREAM_MARK) 2) 0 STREAM_LEN_BITS }

/-- §6.1 LFSR `k` polynomial `POLY` (32 bits, configuration). -/
def Config.poly (c : Config) (k : Nat) : Nat := cfgLE c (LFSR_BASE + STRIDE_LFSR * k + LFSR_POLY) 4

/-- §1 The configuration seen by all logic in cycle t, decoded per block instance. -/
structure CfgView where
  lines : Vector LineCfg 4
  threads : Vector ThreadCfg 6
  outs : Vector OutCfg 14
  streams : Vector StreamCfg 2

/-- §1 Decode every block instance of the configuration. -/
def cfgView (c : Config) : CfgView :=
  { lines := Vector.ofFn fun i => c.line i.val, threads := Vector.ofFn fun i => c.thread i.val,
    outs := Vector.ofFn fun i => c.out i.val, streams := Vector.ofFn fun i => c.stream i.val }

end Metronome.Machine
