import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Chip-top glue: sources, guards, control registers, mailbox and output pins

This module is the independent specification of the combinational and registered
glue of the chip top that no earlier cut covers
([project.v](../../src/project.v)):

* **Sources and guards** (SPEC_V2 §6, §7): the 512-bit source vector `srcs`
  (64 slots of eight bits each) and the 64-bit guard vector `guards`, plus the
  per-line `g_line` bundle that carries the line-relative guards.  The slot
  order is the ISA table's (`machine.SRC`, `machine.GUARD_CONDS`, transcribed
  here); source indices beyond the table read 0 and so do guard indices beyond
  it (§9a.1).
* **Control, flags, mailbox and sticky errors** (SPEC_V2 §6.1, §9, §12.3):
  `RUN_global`, `IRQEN`, `IRQ`, the doorbell `DB`, the flag pair `F`/`FP`, the
  mailbox `INB`/`INV`/`INVP`/`OUTB`/`OUTV`, and the `ERR` term that `IRQ` reads.
* **Output pins** (SPEC_V2 §8, §12.1, §12.3): per output the `BIND`/`SEL`/`LUT`
  decode with the `LIVE` substitutions, the `OUT`/`OEN` registers, and the
  three top-level pin buses `uo_out = {OUT[13:8], IRQ, MISO}`,
  `uio_out = OUT[7:0]`, `uio_oe = OEN`.

Everything here is written from the SPEC text, not from the RTL.  The RTL side
is [GlueEquivalence.lean.in](GlueEquivalence.lean.in), filled from the
elaborated netlist by `glue_check.py`: one theorem per register, per output
field and **per vector slot**, so every goal stays small.

## Cycle boundary

`stateAt inputs n` is the register state during chip cycle `n`, after `n`
sampled edges, exactly as in `Metronome.CoreCtl`.  Combinational glue (the
source and guard vectors, `g_line`, `ERR`) is a function of cycle-`n` state and
of the upstream unit outputs, which this cut binds as per-cycle leaves.
-/

set_option autoImplicit false

namespace Metronome.Glue

/-! ## Bits and slices -/

/-- One net bit as a `Bool`, the shape of a scalar RTL operand. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-- Bits `off … off+w-1` of `x`, the shape the RTL adapter emits for a bus slice. -/
def slice {n : Nat} (x : BitVec n) (off w : Nat) : BitVec w :=
  BitVec.truncate w (BitVec.ushiftRight x off)

/-- The register read the output table performs: bit `i` of a 32-bit `LUT`/`OE`. -/
def readBit {n : Nat} (x : BitVec n) (i : Nat) : Bool :=
  ((BitVec.ushiftRight x i &&& (1 : BitVec n)) != 0)

/-- A one-bit source as its eight-bit slot: the bit in bit 0, zeros above (§6). -/
def bitByte (b : Bool) : BitVec 8 := if b then 1 else 0

theorem bitByte_bitAt_zero (b : Bool) : bitAt (bitByte b) 0 = b := by
  unfold bitByte bitAt
  cases b <;> rfl

/-! ## Sources (SPEC_V2 §6, §9a.1)

SPEC_V2 §6: "The move bus is 8 bits; single-bit sources occupy bit 0, and
unused high bits read 0."  The source ports are the ISA table's
(`machine.SRC`); the four core-local ports `ZERO`, `IMM`, `L.IN` and `L.CAP` are
substituted by each core (`Metronome.Core` proves the core's own overrides), so
the *global* vector leaves those four slots zero.  Index 39 and above read 0
(§9a.1).
-/

/-- The cycle-`t` values the global source vector reads.  Every one is an output
of another block (a unit, a line, a stream, the pointer, the host mailbox), so
this cut binds them as per-cycle leaves. -/
structure Sources where
  /-- `F[15:0]` (`FLAGS.LO`, `FLAGS.HI`). -/
  fl : BitVec 16
  /-- `PIN[12:0]`: the synchronised (or replayed) pin levels (`PINS.LO`, `PINS.HI`). -/
  pins : BitVec 13
  /-- `ACC`: the accumulator. -/
  accA : BitVec 8
  /-- `R0..R3`: the accumulator scratch bytes. -/
  accR : BitVec 32
  /-- `SH0.D`, `SH1.D`: the shifter data bytes. -/
  shD : BitVec 16
  /-- `SH0.O`, `SH1.O`: the shifter output bits. -/
  shO : BitVec 2
  /-- `CNT0..2.LO`, `CNT0..2.HI`: the six counter bytes. -/
  cnV : BitVec 48
  /-- `LF0.B0..B3`, `LF1.B0..B3`, and the two output bits in bits 0 and 32. -/
  lfS : BitVec 64
  /-- `P0.D`: the pointer's last landed byte. -/
  pDat : BitVec 8
  /-- `S0.BIT`, `S1.BIT`. -/
  sBit : BitVec 2
  /-- `S0.BYTE`, `S1.BYTE`. -/
  sByte : BitVec 16
  /-- `HOST.IN`: the mailbox input byte. -/
  inB : BitVec 8

/-- One source slot of the global vector: eight bits per `machine.SRC` index. -/
def srcAt (i : Nat) (s : Sources) : BitVec 8 :=
  match i with
  | 0 => 0                                        -- ZERO (core-local)
  | 1 => 0                                        -- IMM (core-local)
  | 2 => 0                                        -- L.IN (core-local)
  | 3 => 0                                        -- L.CAP (core-local)
  | 4 => slice s.fl 0 8                           -- FLAGS.LO
  | 5 => slice s.fl 8 8                           -- FLAGS.HI
  | 6 => slice s.pins 0 8                         -- PINS.LO
  | 7 => (slice s.pins 8 5).setWidth 8            -- PINS.HI
  | 8 => s.accA                                   -- ACC
  | 9 => slice s.accR 0 8                         -- R0
  | 10 => slice s.accR 8 8                        -- R1
  | 11 => slice s.accR 16 8                       -- R2
  | 12 => slice s.accR 24 8                       -- R3
  | 13 => slice s.shD 0 8                         -- SH0.D
  | 14 => slice s.shD 8 8                         -- SH1.D
  | 15 => bitByte (bitAt s.shO 0)                 -- SH0.O
  | 16 => bitByte (bitAt s.shO 1)                 -- SH1.O
  | 17 => slice s.cnV 0 8                         -- CNT0.LO
  | 18 => slice s.cnV 16 8                        -- CNT1.LO
  | 19 => slice s.cnV 32 8                        -- CNT2.LO
  | 20 => slice s.cnV 8 8                         -- CNT0.HI
  | 21 => slice s.cnV 24 8                        -- CNT1.HI
  | 22 => slice s.cnV 40 8                        -- CNT2.HI
  | 23 => slice s.lfS 0 8                         -- LF0.B0
  | 24 => slice s.lfS 8 8                         -- LF0.B1
  | 25 => slice s.lfS 16 8                        -- LF0.B2
  | 26 => slice s.lfS 24 8                        -- LF0.B3
  | 27 => slice s.lfS 32 8                        -- LF1.B0
  | 28 => slice s.lfS 40 8                        -- LF1.B1
  | 29 => slice s.lfS 48 8                        -- LF1.B2
  | 30 => slice s.lfS 56 8                        -- LF1.B3
  | 31 => bitByte (bitAt s.lfS 0)                 -- LF0.O
  | 32 => bitByte (bitAt s.lfS 32)                -- LF1.O
  | 33 => s.pDat                                  -- P0.D
  | 34 => bitByte (bitAt s.sBit 0)                -- S0.BIT
  | 35 => bitByte (bitAt s.sBit 1)                -- S1.BIT
  | 36 => slice s.sByte 0 8                       -- S0.BYTE
  | 37 => slice s.sByte 8 8                       -- S1.BYTE
  | 38 => s.inB                                   -- HOST.IN
  | _ => 0                                        -- beyond the table (§9a.1)

/-- The source indices whose slot is one bit in bit 0 (`machine.SRC`). -/
def singleBitSources : List Nat := [15, 16, 31, 32, 34, 35]

/-- The high seven bits of a single-bit source are zero, as §6 requires. -/
theorem srcAt_singleBit (i : Nat) (h : i ∈ singleBitSources) (s : Sources) :
    srcAt i s &&& 0xFE = 0 := by
  simp only [singleBitSources, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [srcAt, bitByte] <;> bv_decide

/-- Source indices beyond `machine.SRC` read 0 (§9a.1). -/
theorem srcAt_beyond (i : Nat) (s : Sources) (h : 39 ≤ i) : srcAt i s = 0 := by
  unfold srcAt
  split <;> (first | omega | rfl)

/-! ## Guards (SPEC_V2 §7, §9a.1)

SPEC_V2 §7: "Indices are in ISA_TABLES_V2.md.  Guard 0 is constant true.
Line-relative guards use the executing thread's line, or for watchers the line
of the thread being dispatched: `L.IN0, L.IN1` are the bits of `IN`, `L.SYNC`
is `SP`, `L.PINA, L.PINB` are `PIN[PINA]`, `PIN[PINB]`.  `Lk.RUN` is line k's
`RUN`.  `PINk` is `PIN[k]`."

The five line-relative indices (27..31) are not part of the global vector: the
chip top builds a five-bit bundle per line (`g_line`, see `lineGuard`) and each
core substitutes it for its executing line, so the global slot reads 0.  Index
62 and above evaluate false (§9a.1).
-/

/-- The cycle-`t` values the global guard vector reads. -/
structure Guards where
  /-- `F[15:0]` (`F0..F15`). -/
  fl : BitVec 16
  /-- `SH0.DONE`, `SH1.DONE`. -/
  shDone : BitVec 2
  /-- `SH0.OUT`, `SH1.OUT`. -/
  shOut : BitVec 2
  /-- `CNT0.Z`, `CNT1.Z`, `CNT2.Z`. -/
  cntZ : BitVec 3
  /-- `ACC.Z`. -/
  accZ : Bool
  /-- `ACC.C`. -/
  accC : Bool
  /-- `ACC.N`. -/
  accN : Bool
  /-- The two LFSR states; `LFk.OUT` is bit 0 of each. -/
  lfS : BitVec 64
  /-- `HOST.INV`. -/
  inv : Bool
  /-- `OUTV`; `HOST.OUTE` is its complement (§6.1). -/
  outv : Bool
  /-- `P0.RDY`. -/
  pRdy : Bool
  /-- `S0.END`, `S1.END`. -/
  sEnd : BitVec 2
  /-- `S0.MARK`, `S1.MARK`. -/
  sMark : BitVec 2
  /-- `S0.BYTE`, `S1.BYTE`. -/
  sByte : BitVec 2
  /-- `S0.BIT`, `S1.BIT`. -/
  sBit : BitVec 2
  /-- `PIN[12:0]`. -/
  pins : BitVec 13
  /-- `L0.RUN .. L3.RUN`. -/
  lRun : BitVec 4

/-- One guard slot of the global vector, indexed by the ISA table
(`machine.GUARD_CONDS`). -/
def guardAt (i : Nat) (g : Guards) : Bool :=
  match i with
  | 0 => true                                     -- TRUE
  | 1 => bitAt g.fl 0                             -- F0
  | 2 => bitAt g.fl 1                             -- F1
  | 3 => bitAt g.fl 2                             -- F2
  | 4 => bitAt g.fl 3                             -- F3
  | 5 => bitAt g.fl 4                             -- F4
  | 6 => bitAt g.fl 5                             -- F5
  | 7 => bitAt g.fl 6                             -- F6
  | 8 => bitAt g.fl 7                             -- F7
  | 9 => bitAt g.fl 8                             -- F8
  | 10 => bitAt g.fl 9                            -- F9
  | 11 => bitAt g.fl 10                           -- F10
  | 12 => bitAt g.fl 11                           -- F11
  | 13 => bitAt g.fl 12                           -- F12
  | 14 => bitAt g.fl 13                           -- F13
  | 15 => bitAt g.fl 14                           -- F14
  | 16 => bitAt g.fl 15                           -- F15
  | 17 => bitAt g.shDone 0                        -- SH0.DONE
  | 18 => bitAt g.shDone 1                        -- SH1.DONE
  | 19 => bitAt g.shOut 0                         -- SH0.OUT
  | 20 => bitAt g.shOut 1                         -- SH1.OUT
  | 21 => bitAt g.cntZ 0                          -- CNT0.Z
  | 22 => bitAt g.cntZ 1                          -- CNT1.Z
  | 23 => bitAt g.cntZ 2                          -- CNT2.Z
  | 24 => g.accZ                                  -- ACC.Z
  | 25 => g.accC                                  -- ACC.C
  | 26 => g.accN                                  -- ACC.N
  | 27 => false                                   -- L.IN0 (line-relative)
  | 28 => false                                   -- L.IN1 (line-relative)
  | 29 => false                                   -- L.SYNC (line-relative)
  | 30 => false                                   -- L.PINA (line-relative)
  | 31 => false                                   -- L.PINB (line-relative)
  | 32 => bitAt g.lfS 0                           -- LF0.OUT
  | 33 => bitAt g.lfS 32                          -- LF1.OUT
  | 34 => g.inv                                   -- HOST.INV
  | 35 => !g.outv                                 -- HOST.OUTE
  | 36 => g.pRdy                                  -- P0.RDY
  | 37 => bitAt g.sEnd 0                          -- S0.END
  | 38 => bitAt g.sEnd 1                          -- S1.END
  | 39 => bitAt g.sMark 0                         -- S0.MARK
  | 40 => bitAt g.sMark 1                         -- S1.MARK
  | 41 => bitAt g.sByte 0                         -- S0.BYTE
  | 42 => bitAt g.sByte 1                         -- S1.BYTE
  | 43 => bitAt g.sBit 0                          -- S0.BIT
  | 44 => bitAt g.sBit 1                          -- S1.BIT
  | 45 => bitAt g.pins 0                          -- PIN0
  | 46 => bitAt g.pins 1                          -- PIN1
  | 47 => bitAt g.pins 2                          -- PIN2
  | 48 => bitAt g.pins 3                          -- PIN3
  | 49 => bitAt g.pins 4                          -- PIN4
  | 50 => bitAt g.pins 5                          -- PIN5
  | 51 => bitAt g.pins 6                          -- PIN6
  | 52 => bitAt g.pins 7                          -- PIN7
  | 53 => bitAt g.pins 8                          -- PIN8
  | 54 => bitAt g.pins 9                          -- PIN9
  | 55 => bitAt g.pins 10                         -- PIN10
  | 56 => bitAt g.pins 11                         -- PIN11
  | 57 => bitAt g.pins 12                         -- PIN12
  | 58 => bitAt g.lRun 0                          -- L0.RUN
  | 59 => bitAt g.lRun 1                          -- L1.RUN
  | 60 => bitAt g.lRun 2                          -- L2.RUN
  | 61 => bitAt g.lRun 3                          -- L3.RUN
  | _ => false                                    -- beyond the table (§9a.1)

/-- The guard indices that are false in the global vector because they are
line-relative (§7); each core supplies `g_line`'s own bundle for them. -/
def lineRelativeGuards : List Nat := [27, 28, 29, 30, 31]

/-- The line-relative guard slots of the global vector read 0. -/
theorem guardAt_lineRelative (i : Nat) (h : i ∈ lineRelativeGuards) (g : Guards) :
    guardAt i g = false := by
  simp only [lineRelativeGuards, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Guard indices beyond `machine.GUARD_CONDS` evaluate false (§9a.1). -/
theorem guardAt_beyond (i : Nat) (g : Guards) (h : 62 ≤ i) : guardAt i g = false := by
  unfold guardAt
  split <;> (first | omega | rfl)

/-- The per-line guard bundle the chip top hands to a core as `g_line`: bits
0..4 are guard indices 27..31 for that line, so `L.IN0`, `L.IN1`, `L.SYNC`,
`L.PINA`, `L.PINB` read `l_in`, `l_sp`, `l_pina`, `l_pinb` of the line. -/
structure LineGuards where
  /-- `l_in`: two input-symbol bits per line. -/
  inn : BitVec 8
  /-- `l_sp`: the synchronised `SP` bit per line. -/
  sp : BitVec 4
  /-- `l_pina`: the `PINA` pin level per line. -/
  pinA : BitVec 4
  /-- `l_pinb`: the `PINB` pin level per line. -/
  pinB : BitVec 4

/-- The five-bit `g_line` bundle of line `l`, in guard-index order. -/
def lineGuard (l : Nat) (g : LineGuards) : BitVec 5 :=
  (if bitAt g.inn (2 * l) then 1 else 0) |||
  (if bitAt g.inn (2 * l + 1) then 2 else 0) |||
  (if bitAt g.sp l then 4 else 0) |||
  (if bitAt g.pinA l then 8 else 0) |||
  (if bitAt g.pinB l then 16 else 0)

/-- Reading guard `27 + j` of line `l` from the bundle, for the five indices. -/
theorem lineGuard_at (l : Nat) (g : LineGuards) :
    bitAt (lineGuard l g) 0 = bitAt g.inn (2 * l) ∧
    bitAt (lineGuard l g) 1 = bitAt g.inn (2 * l + 1) ∧
    bitAt (lineGuard l g) 2 = bitAt g.sp l ∧
    bitAt (lineGuard l g) 3 = bitAt g.pinA l ∧
    bitAt (lineGuard l g) 4 = bitAt g.pinB l := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [lineGuard, bitAt] <;> bv_decide

/-! ## Flags, mailbox and control (SPEC_V2 §6.1, §9, §12.3)

SPEC_V2 §6.1: "Flags `F[15:0]`. `SET n: F[n]' = 1`. `CLR n: F[n]' = 0`.
`FP' = F` every cycle."  §12.3 adds that `FP` holds in a frozen cycle, so a
flag rise during the freeze is seen by a trigger in the first unfrozen cycle.

SPEC_V2 §9: `CTRL.RUN` bit 0 is `RUN_global`; `IRQEN` bits 0 and 1;
`HOSTIN` writes `INB` and sets `INV`; `HOSTOUT` writes `OUTB` and raises
`OUTV`; `HOSTSTAT` bit 1 clears `OUTV`; `DOORBELL` "reads 0; writing bit t in
cycle W makes `DB[t] = 1` in cycle W+1 only", and §12.3 holds a doorbell pulse
written in a frozen cycle.  `IRQ' = (IRQEN[0] && OUTV) || (IRQEN[1] && ERR)`
with `ERR` the list of §9: `CONFLICT`, `MEMHAZ`, `CWOVR` (13.1), every
thread's `LATE` and `OVR`, every line's `TAPMISS` and every stream's
`STARVED`.

`INV` is also cleared by an enabled move that reads `HOST.IN` (§6), and §12.3
holds `INVP`.  `fp`/`INVP` are the "previous" copies used for edge triggers.
-/

/-- `D_FLAGS_SET` of `machine.DST`: the `FLAGS` destination that sets a bit. -/
def flagsSetDst : BitVec 6 := 5

/-- `F[idx] := v`, every other bit unchanged. -/
def setFlag (f : BitVec 16) (idx : BitVec 4) (v : Bool) : BitVec 16 :=
  if v then f ||| BitVec.shiftLeft (1 : BitVec 16) idx.toNat
  else f &&& ~~~(BitVec.shiftLeft (1 : BitVec 16) idx.toNat)

/-- The flag update writes bit `n` and holds the rest. -/
theorem setFlag_at (f : BitVec 16) (idx : BitVec 4) (v : Bool) :
    bitAt (setFlag f idx v) idx.toNat = v := by
  unfold setFlag bitAt
  split <;> bv_decide

/-- A flag write leaves every other bit alone. -/
theorem setFlag_other (f : BitVec 16) (idx j : BitVec 4) (v : Bool) (ne : j ≠ idx) :
    bitAt (setFlag f idx v) j.toNat = bitAt f j.toNat := by
  unfold setFlag bitAt
  split <;> bv_decide

/-- The glue registers' state. -/
structure GlueState where
  /-- `RUN_global` (`CTRL.RUN` bit 0). -/
  runG : Bool
  /-- `IRQEN[1:0]`. -/
  irqEn : BitVec 2
  /-- `IRQ`. -/
  irq : Bool
  /-- `DB[NT-1:0]`, the doorbell. -/
  db : BitVec 6
  /-- `F[15:0]`. -/
  fl : BitVec 16
  /-- `FP[15:0]`, the previous flags. -/
  flp : BitVec 16
  /-- `INB`, the mailbox input byte. -/
  inB : BitVec 8
  /-- `INV`, the mailbox input-valid flag. -/
  inv : Bool
  /-- `INVP`, the previous `INV`. -/
  invp : Bool
  /-- `OUTB`, the mailbox output byte. -/
  outB : BitVec 8
  /-- `OUTV`, the mailbox output-valid flag. -/
  outv : Bool

/-- The sampled inputs of the glue registers.  The `wr*` strobes are the
chip-top host-write decodes (`c_wr_run`, `c_wr_irqen`, `c_wr_db`, `c_wr_hin`,
`c_wr_hst`); the host-map cut proves each is "host write to that `CTRL` byte".
`wFlags` and `wHout` are the picked `FLAGS` and `HOST.OUT` write words, which
the move-resolution cut proves.  The sticky/event terms are `ERR`'s parts. -/
structure GlueInput where
  /-- `rst_q`: the synchronised reset. -/
  resetN : Bool
  /-- `frz`: this cycle is frozen (§12.3). -/
  frz : Bool
  /-- `c_wr_run`: a host write to `CTRL.RUN`. -/
  wrRun : Bool
  /-- `c_wr_irqen`: a host write to `CTRL.IRQEN`. -/
  wrIrqEn : Bool
  /-- `c_wr_db`: a host write to `CTRL.DOORBELL`. -/
  wrDb : Bool
  /-- `c_wr_hin`: a host write to `CTRL.HOSTIN`. -/
  wrHin : Bool
  /-- `c_wr_hst`: a host write to `CTRL.HOSTSTAT`. -/
  wrHst : Bool
  /-- `w_flags`: the picked `FLAGS` word `{we, dst, data}`. -/
  wFlags : BitVec 15
  /-- `w_hout`: the picked `HOST.OUT` word `{we, dst, data}`. -/
  wHout : BitVec 15
  /-- `h_wd`: the host data byte. -/
  hWd : BitVec 8
  /-- `rd_hin`: the enabled moves that read `HOST.IN` (`Metronome.Moves.readsOf`). -/
  rdHin : BitVec 6
  /-- `CONFLICT`. -/
  conflict : Bool
  /-- `MEMHAZ`. -/
  memhaz : Bool
  /-- `CWOVR`. -/
  cwOverrun : Bool
  /-- Every thread's `LATE`. -/
  tLate : BitVec 6
  /-- Every thread's `OVR`. -/
  tOvr : BitVec 6
  /-- Every line's `TAPMISS`. -/
  lTapmiss : BitVec 4
  /-- Every stream's `STARVED`. -/
  sStarved : BitVec 2

/-- The `FLAGS` write's enable bit `w_flags[14]`. -/
def flagsWrite (i : GlueInput) : Bool := bitAt i.wFlags 14

/-- The flag index: the move byte's low nibble (`w_flags[3:0]`). -/
def flagsIndex (i : GlueInput) : BitVec 4 := slice i.wFlags 0 4

/-- The flag value: `SET` writes 1, every other `FLAGS` destination writes 0. -/
def flagsValue (i : GlueInput) : Bool := slice i.wFlags 8 6 == flagsSetDst

/-- The `HOST.OUT` write's enable bit `w_hout[14]`. -/
def hostOutWrite (i : GlueInput) : Bool := bitAt i.wHout 14

/-- `HOST.OUT`'s data byte. -/
def hostOutData (i : GlueInput) : BitVec 8 := slice i.wHout 0 8

/-- A `HOSTSTAT` write of bit 1 clears `OUTV`. -/
def hostStatClear (i : GlueInput) : Bool := i.wrHst && bitAt i.hWd 1

/-- `CTRL.DOORBELL`'s six data bits. -/
def doorbellBits (i : GlueInput) : BitVec 6 := slice i.hWd 0 6

/-- "Some bit of this bus is set", the RTL's `$reduce_or` of a status vector. -/
def any2 (x : BitVec 2) : Bool := bitAt x 0 || bitAt x 1

/-- "Some bit of this bus is set". -/
def any4 (x : BitVec 4) : Bool :=
  bitAt x 0 || bitAt x 1 || bitAt x 2 || bitAt x 3

/-- "Some bit of this bus is set". -/
def any6 (x : BitVec 6) : Bool :=
  bitAt x 0 || bitAt x 1 || bitAt x 2 || bitAt x 3 || bitAt x 4 || bitAt x 5

/-- Some enabled move reads `HOST.IN` (`Metronome.Moves.readsOf`'s reduce). -/
def anyRead (r : BitVec 6) : Bool := any6 r

/-- SPEC_V2 §9's `ERR`: any sticky error or any thread's `LATE`/`OVR`, line's
`TAPMISS` or stream's `STARVED`. -/
def err (i : GlueInput) : Bool :=
  i.conflict || i.memhaz || i.cwOverrun || any6 i.tLate || any6 i.tOvr ||
  any4 i.lTapmiss || any2 i.sStarved

/-- One glue cycle: SPEC_V2 §6.1, §9 and §12.3. -/
def step (s : GlueState) (i : GlueInput) : GlueState where
  runG := if i.resetN then (if i.wrRun then bitAt i.hWd 0 else s.runG) else false
  irqEn := if i.resetN then (if i.wrIrqEn then slice i.hWd 0 2 else s.irqEn) else 0
  irq := if i.resetN then
      ((bitAt s.irqEn 0 && s.outv) || (bitAt s.irqEn 1 && err i)) else false
  db := if i.resetN then
      ((if i.wrDb then doorbellBits i else 0) ||| (if i.frz then s.db else 0)) else 0
  fl := if i.resetN then
      (if flagsWrite i then setFlag s.fl (flagsIndex i) (flagsValue i) else s.fl) else 0
  flp := if i.resetN then (if i.frz then s.flp else s.fl) else 0
  inB := if i.resetN then (if i.wrHin then i.hWd else s.inB) else 0
  inv := if i.resetN then
      (if i.wrHin then true else (if anyRead i.rdHin then false else s.inv)) else false
  invp := if i.resetN then (if i.frz then s.invp else s.inv) else false
  outB := if i.resetN then (if hostOutWrite i then hostOutData i else s.outB) else 0
  outv := if i.resetN then
      (if hostOutWrite i then true
       else if hostStatClear i then false else s.outv) else false

/-- Reset clears every glue register. -/
def resetState : GlueState :=
  ⟨false, 0, false, 0, 0, 0, 0, false, false, 0, false⟩

/-- Two glue states with equal fields are equal. -/
@[ext] theorem GlueState.ext {a b : GlueState} (runG : a.runG = b.runG)
    (irqEn : a.irqEn = b.irqEn) (irq : a.irq = b.irq) (db : a.db = b.db)
    (fl : a.fl = b.fl) (flp : a.flp = b.flp) (inB : a.inB = b.inB)
    (inv : a.inv = b.inv) (invp : a.invp = b.invp) (outB : a.outB = b.outB)
    (outv : a.outv = b.outv) : a = b := by
  obtain ⟨⟩ := a
  obtain ⟨⟩ := b
  simp_all

theorem runG_next (s : GlueState) (i : GlueInput) :
    (step s i).runG =
      (if i.resetN then (if i.wrRun then bitAt i.hWd 0 else s.runG) else false) := rfl

theorem irqEn_next (s : GlueState) (i : GlueInput) :
    (step s i).irqEn =
      (if i.resetN then (if i.wrIrqEn then slice i.hWd 0 2 else s.irqEn) else 0) := rfl

theorem irq_next (s : GlueState) (i : GlueInput) :
    (step s i).irq = (if i.resetN then
      ((bitAt s.irqEn 0 && s.outv) || (bitAt s.irqEn 1 && err i)) else false) := rfl

theorem db_next (s : GlueState) (i : GlueInput) :
    (step s i).db = (if i.resetN then
      ((if i.wrDb then doorbellBits i else 0) ||| (if i.frz then s.db else 0))
      else 0) := rfl

theorem fl_next (s : GlueState) (i : GlueInput) :
    (step s i).fl = (if i.resetN then
      (if flagsWrite i then setFlag s.fl (flagsIndex i) (flagsValue i) else s.fl)
      else 0) := rfl

theorem flp_next (s : GlueState) (i : GlueInput) :
    (step s i).flp = (if i.resetN then (if i.frz then s.flp else s.fl) else 0) := rfl

theorem inB_next (s : GlueState) (i : GlueInput) :
    (step s i).inB = (if i.resetN then (if i.wrHin then i.hWd else s.inB) else 0) := rfl

theorem inv_next (s : GlueState) (i : GlueInput) :
    (step s i).inv = (if i.resetN then
      (if i.wrHin then true else (if anyRead i.rdHin then false else s.inv))
      else false) := rfl

theorem invp_next (s : GlueState) (i : GlueInput) :
    (step s i).invp = (if i.resetN then (if i.frz then s.invp else s.inv) else false) := rfl

theorem outB_next (s : GlueState) (i : GlueInput) :
    (step s i).outB = (if i.resetN then
      (if hostOutWrite i then hostOutData i else s.outB) else 0) := rfl

theorem outv_next (s : GlueState) (i : GlueInput) :
    (step s i).outv = (if i.resetN then
      (if hostOutWrite i then true
       else if hostStatClear i then false else s.outv) else false) := rfl

/-- A reset edge leaves the reset state. -/
theorem step_reset (s : GlueState) (i : GlueInput) (h : i.resetN = false) :
    step s i = resetState := by
  cases s
  simp [step, resetState, h]

/-- Without `IRQEN[0]` or `IRQEN[1]` the interrupt output is low. -/
theorem irq_of_disabled (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (h : s.irqEn = 0) : (step s i).irq = false := by
  rw [irq_next]
  simp [reset, h, bitAt]

/-- With `IRQEN[0]` and `OUTV` the interrupt is raised. -/
theorem irq_of_outv (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (en : bitAt s.irqEn 0 = true) (outv : s.outv = true) : (step s i).irq = true := by
  rw [irq_next]
  simp [reset, en, outv]

/-- With `IRQEN[1]` and any `ERR` term the interrupt is raised. -/
theorem irq_of_err (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (en : bitAt s.irqEn 1 = true) (e : err i = true) : (step s i).irq = true := by
  rw [irq_next]
  simp [reset, en, e]

/-- `ERR` is the disjunction of §9's terms. -/
theorem err_iff (i : GlueInput) :
    err i = true ↔ (i.conflict = true ∨ i.memhaz = true ∨ i.cwOverrun = true ∨
      any6 i.tLate = true ∨ any6 i.tOvr = true ∨ any4 i.lTapmiss = true ∨
      any2 i.sStarved = true) := by
  unfold err
  simp only [Bool.or_eq_true, or_assoc]

/-- A frozen cycle holds a doorbell pulse written in that cycle (`DB' = written | DB`). -/
theorem db_frozen_hold (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (frz : i.frz = true) :
    (step s i).db = ((if i.wrDb then doorbellBits i else 0) ||| s.db) := by
  rw [db_next]
  simp [reset, frz]

/-- A frozen cycle without a doorbell write leaves `DB` unchanged. -/
theorem db_frozen_keeps (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (frz : i.frz = true) (noWrite : i.wrDb = false) : (step s i).db = s.db := by
  rw [db_frozen_hold s i reset frz]
  simp [noWrite]

/-- A frozen cycle holds `FP` (§12.3). -/
theorem flp_frozen_holds (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (frz : i.frz = true) : (step s i).flp = s.flp := by
  rw [flp_next]
  simp [reset, frz]

/-- A frozen cycle holds `INVP` (§12.3). -/
theorem invp_frozen_holds (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (frz : i.frz = true) : (step s i).invp = s.invp := by
  rw [invp_next]
  simp [reset, frz]

/-- A `SET` flag write sets the addressed flag. -/
theorem fl_set (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (write : flagsWrite i = true) (v : flagsValue i = true) :
    bitAt (step s i).fl (flagsIndex i).toNat = true := by
  rw [fl_next]
  simp only [reset, write, ite_true, setFlag, v]
  unfold bitAt
  bv_decide

/-- A `CLR` flag write clears the addressed flag. -/
theorem fl_clear (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (write : flagsWrite i = true) (v : flagsValue i = false) :
    bitAt (step s i).fl (flagsIndex i).toNat = false := by
  rw [fl_next]
  simp only [reset, write, ite_true, setFlag, v]
  unfold bitAt
  bv_decide

/-- A flag write leaves every other flag alone. -/
theorem fl_other (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (write : flagsWrite i = true) (j : BitVec 4) (ne : j ≠ flagsIndex i) :
    bitAt (step s i).fl j.toNat = bitAt s.fl j.toNat := by
  rw [fl_next]
  simp only [reset, write, ite_true]
  exact setFlag_other s.fl (flagsIndex i) j (flagsValue i) ne

/-- `HOSTIN` sets `INV` and loads `INB`. -/
theorem inv_host_write (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (wr : i.wrHin = true) :
    (step s i).inv = true ∧ (step s i).inB = i.hWd := by
  rw [inv_next, inB_next]
  simp [reset, wr]

/-- A `HOST.IN` read clears `INV` when no host write lands in the same cycle. -/
theorem inv_read_clears (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (noWrite : i.wrHin = false) (read : anyRead i.rdHin = true) :
    (step s i).inv = false := by
  rw [inv_next]
  simp [reset, noWrite, read]

/-- Without a write or a read, `INV` holds. -/
theorem inv_hold (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (noWrite : i.wrHin = false) (noRead : anyRead i.rdHin = false) :
    (step s i).inv = s.inv := by
  rw [inv_next]
  simp [reset, noWrite, noRead]

/-- `HOSTOUT` raises `OUTV` and loads `OUTB`. -/
theorem outv_host_write (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (wr : hostOutWrite i = true) :
    (step s i).outv = true ∧ (step s i).outB = hostOutData i := by
  rw [outv_next, outB_next]
  simp [reset, wr]

/-- A `HOSTSTAT` write of bit 1 clears `OUTV`. -/
theorem outv_host_clear (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (noWrite : hostOutWrite i = false) (clear : hostStatClear i = true) :
    (step s i).outv = false := by
  rw [outv_next]
  simp [reset, noWrite, clear]

/-- A `CTRL.RUN` write loads `RUN_global` from bit 0. -/
theorem runG_host_write (s : GlueState) (i : GlueInput) (reset : i.resetN = true)
    (wr : i.wrRun = true) : (step s i).runG = bitAt i.hWd 0 := by
  rw [runG_next]
  simp [reset, wr]

/-! ### Trace lift -/

/-- The register state during cycle `n`. -/
def stateAt (inputs : Nat → GlueInput) (n : Nat) : GlueState :=
  run (fun s i => step s i) inputs resetState n

theorem stateAt_succ (inputs : Nat → GlueInput) (n : Nat) :
    stateAt inputs (n + 1) = step (stateAt inputs n) (inputs n) := rfl

theorem stateAt_zero (inputs : Nat → GlueInput) : stateAt inputs 0 = resetState := rfl

/-- Starting from reset, `IRQ` is low until an `IRQEN` write enables it. -/
theorem trace_irq_quiet (inputs : Nat → GlueInput) :
    ∀ n, (∀ k, k < n → (inputs k).resetN = true) →
      (∀ k, k < n → (stateAt inputs k).irqEn = 0) →
      (stateAt inputs n).irq = false := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro noReset quiet
    have low := ih (fun k lt => noReset k (by omega)) (fun k lt => quiet k (by omega))
    rw [stateAt_succ]
    exact irq_of_disabled _ _ (noReset n (by omega)) (quiet n (by omega))

/-! ## Output pins (SPEC_V2 §8, §12.1, §12.3)

SPEC_V2 §8: `idx = BOUND ? {SEG(LINE), COMMITTED(LINE)[SEL2],
COMMITTED(LINE)[SEL1], COMMITTED(LINE)[SEL0]} : 0`, `OUT[o]' = LUT[idx]` and
`OEN[o]' = OE[idx]` for `o < 8`; "After reset every pin drives 0 with its
output enable off."  §12.1 adds the `LIVE` substitutions: `BIND` bit 3 replaces
`b2` by `PIN[PINA(ln)]` and bit 4 replaces `b1` by `PIN[PINB(ln)]`; a select at
or above 13 reads 0 (the RTL's `l_pina`/`l_pinb` are four-bit per-line buses
of the thirteen input pins).  §12.3 holds both registers in a frozen cycle.

The configuration bytes (`BIND`, `SEL`, `LUT`, `OE`) are free per-cycle leaves
here: the latch-bank cut covers their content.
-/

/-- One output pin's configuration and the line buses its table reads. -/
structure OutCfg where
  /-- `BIND` byte: bit 2 `BOUND`, bit 3 `LIVE[0]`, bit 4 `LIVE[1]`, bits 1:0 `LINE`. -/
  bind : BitVec 8
  /-- `SEL` byte: `SEL0` in bits 1:0, `SEL1` in 3:2, `SEL2` in 5:4. -/
  sel : BitVec 8
  /-- `LUT`: the 32-entry output table. -/
  lut : BitVec 32
  /-- `OE`: the 32-entry output-enable table (`o < 8`). -/
  oe : BitVec 32
  /-- `l_comm`: the four `COMMITTED` nibbles, one per line. -/
  comm : BitVec 16
  /-- `l_pina`: the `PINA` pin level of each line. -/
  pinA : BitVec 4
  /-- `l_pinb`: the `PINB` pin level of each line. -/
  pinB : BitVec 4
  /-- `l_seg`: the two `SEG` bits of each line. -/
  seg : BitVec 8

/-- `LINE` of the output's `BIND` byte. -/
def outLine (c : OutCfg) : BitVec 2 := slice c.bind 0 2

/-- `COMMITTED(LINE)` of the bound line. -/
def outComm (c : OutCfg) : BitVec 4 := slice c.comm (4 * (outLine c).toNat) 4

/-- `BOUND` (bit 2 of `BIND`). -/
def outBound (c : OutCfg) : Bool := bitAt c.bind 2

/-- `LIVE[0]` (bit 3 of `BIND`): replace `b2` by `PIN[PINA(LINE)]`. -/
def outLiveB2 (c : OutCfg) : Bool := bitAt c.bind 3

/-- `LIVE[1]` (bit 4 of `BIND`): replace `b1` by `PIN[PINB(LINE)]`. -/
def outLiveB1 (c : OutCfg) : Bool := bitAt c.bind 4

/-- `b0 = COMMITTED(LINE)[SEL0]`. -/
def outB0 (c : OutCfg) : Bool := bitAt (outComm c) (slice c.sel 0 2).toNat

/-- `b1`, with §12.1's `LIVE` substitution. -/
def outB1 (c : OutCfg) : Bool :=
  if outLiveB1 c then bitAt c.pinB (outLine c).toNat
  else bitAt (outComm c) (slice c.sel 2 2).toNat

/-- `b2`, with §12.1's `LIVE` substitution. -/
def outB2 (c : OutCfg) : Bool :=
  if outLiveB2 c then bitAt c.pinA (outLine c).toNat
  else bitAt (outComm c) (slice c.sel 4 2).toNat

/-- `SEG(LINE)`. -/
def outSeg (c : OutCfg) : BitVec 2 := slice c.seg (2 * (outLine c).toNat) 2

/-- §8/§12.1's five-bit table index `{SEG(LINE), b2, b1, b0}`, or 0 when unbound. -/
def outIdx (c : OutCfg) : BitVec 5 :=
  if outBound c then
    ((if outB0 c then (1 : BitVec 5) else 0) |||
     (if outB1 c then (2 : BitVec 5) else 0) |||
     (if outB2 c then (4 : BitVec 5) else 0) |||
     BitVec.shiftLeft (BitVec.setWidth 5 (outSeg c)) 3)
  else 0

/-- `OUT[o]'`: the table entry at `idx`, held in a frozen cycle, 0 out of reset. -/
def outNext (c : OutCfg) (cur resetN frz : Bool) : Bool :=
  if resetN then (if frz then cur else readBit c.lut (outIdx c).toNat) else false

/-- `OEN[o]'` (`o < 8`). -/
def oeNext (c : OutCfg) (cur resetN frz : Bool) : Bool :=
  if resetN then (if frz then cur else readBit c.oe (outIdx c).toNat) else false

/-- A frozen cycle holds the output register (§12.3). -/
theorem outNext_frozen (c : OutCfg) (cur : Bool) : outNext c cur true true = cur := by
  unfold outNext
  simp

/-- A frozen cycle holds the output-enable register (§12.3). -/
theorem oeNext_frozen (c : OutCfg) (cur : Bool) :
    oeNext c cur true true = cur := by
  unfold oeNext
  simp

/-- Reset clears both registers. -/
theorem outNext_reset (c : OutCfg) (cur frz : Bool) : outNext c cur false frz = false := rfl

theorem oeNext_reset (c : OutCfg) (cur frz : Bool) : oeNext c cur false frz = false := rfl

/-- The top-level pin buses: `uo_out = {OUT[13:8], IRQ, MISO}`, `uio_out =
OUT[7:0]`, `uio_oe = OEN`. -/
def pins (out : BitVec 14) (oe : BitVec 8) (irq miso : Bool) :
    BitVec 8 × BitVec 8 × BitVec 8 :=
  ((bitByte miso) ||| (if irq then (2 : BitVec 8) else 0) |||
     BitVec.shiftLeft (BitVec.setWidth 8 (slice out 8 6)) 2,
   slice out 0 8, oe)

/-- The three pin buses are the registers' bits (§8). -/
theorem pins_eq (out : BitVec 14) (oe : BitVec 8) (irq miso : Bool) :
    (pins out oe irq miso).1 = (bitByte miso ||| (if irq then 2 else 0) |||
      BitVec.shiftLeft (BitVec.setWidth 8 (slice out 8 6)) 2) ∧
    (pins out oe irq miso).2.1 = slice out 0 8 ∧
    (pins out oe irq miso).2.2 = oe := ⟨rfl, rfl, rfl⟩

end Metronome.Glue
