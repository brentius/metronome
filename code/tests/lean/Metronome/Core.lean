import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# The two cores (SPEC_V2 §5, §6, §7 and §12.3)

An independent specification of `src/md2_core.v`, written from the pseudocode
block of SPEC_V2 §5 (state, per-cycle equations, dispatch), the move bus of §6
(8-bit data, single-bit sources in bit 0), the guard and jump-condition rules of
§7 (`JUMP_GUARDS`, line-relative guards from the executing line `XL`) and the
freeze of §12.3 (no execute/fetch/dispatch; every register holds; `XV`/`RV`/`FPC`
readback).

Instruction field positions are the ones in `wiki/ISA_TABLES_V2.md` (generated
from `code/md2/machine.py`); `src/md2_defs.vh` names the same positions.  The
cut in `core_check.py` checks the elaborated bit slices against both and reports
any difference instead of silently redefining the encoding.

## Encoding of quantities the SPEC leaves as tables

* `JG_TABLE` is the `JUMP_GUARDS` column of `wiki/ISA_TABLES_V2.md` (32 entries,
  all defined, §7).  The RTL packs the same table into the parameter `JG_MAP`
  (six bits per entry, `src/md2_defs.vh`); the adapter checks the elaborated `jg`
  assembly bit by bit against this list.
* The guard slots `TRUE`, `L.IN0`, `L.IN1`, `L.SYNC`, `L.PINA`, `L.PINB` are the
  §7 indices 0, 27, 28, 29, 30, 31; `MD_N_GUARD = 62` guards are defined, so the
  codes past the table read 0 (§7, `src/md2_map.vh`).
* The source slots `ZERO`, `IMM`, `L.IN`, `L.CAP` are 0..3 and `MD_N_SRC = 39`
  (§6.1, `wiki/ISA_TABLES_V2.md` "Source ports"); the core replaces those four
  slots of the input `srcs` vector and zeroes the codes past the table (§6:
  "unused high bits read 0").

## `IR` capture

SPEC §5 writes `XV' = load; if load: IR' = word at the memory output`.  The RTL
captures the memory output in every unfrozen cycle (`if (!frz) ir <= rdata;`).
The model below follows the RTL.  This is not an observable difference: `XV' =
load`, so a word captured without `load` is never decoded, and on `load` the two
rules agree (`irNext_of_load`, `xv_fpc_invariant`).

## Cycle convention

`stateAt inputs initial n` is the register state during cycle `n`; `inputs n`
is the sampled input bundle of that cycle and produces the state of `n + 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Metronome.Core

/-! ## Bit helpers -/

/-- Bits `[lo, lo+n)` of a vector, as an `n`-bit vector. -/
def slice {w : Nat} (v : BitVec w) (lo n : Nat) : BitVec n :=
  BitVec.truncate n (BitVec.ushiftRight v lo)

/-- Bit `k` of a vector as a `Bool`. -/
def bitOf {w : Nat} (v : BitVec w) (k : Nat) : Bool :=
  (BitVec.truncate 1 (BitVec.ushiftRight v k)) != 0

/-- The low `n` bits of a `w`-bit vector. -/
def lowMask (w n : Nat) : BitVec w :=
  ~~~(BitVec.shiftLeft (BitVec.allOnes w) n)

/-- `v` with bit `k` replaced by `b`. -/
def setBit {w : Nat} (v : BitVec w) (k : Nat) (b : Bool) : BitVec w :=
  if b then v ||| BitVec.shiftLeft (1 : BitVec w) k
  else v &&& ~~~(BitVec.shiftLeft (1 : BitVec w) k)

/-- A `w`-bit vector with bit `k` set when `b`. -/
def boolMask {w : Nat} (k : Nat) (b : Bool) : BitVec w :=
  if b then BitVec.shiftLeft (1 : BitVec w) k else 0

/-- The `w`-bit field of the thread-indexed table `v` selected by a one-hot
`win` vector: `OR_g (win[g] ? slot g : 0)`. -/
def selSlot {w : Nat} (v : BitVec (6 * w)) (win : BitVec 6) : BitVec w :=
  (if bitOf win 0 then slice v (0 * w) w else 0) |||
  (if bitOf win 1 then slice v (1 * w) w else 0) |||
  (if bitOf win 2 then slice v (2 * w) w else 0) |||
  (if bitOf win 3 then slice v (3 * w) w else 0) |||
  (if bitOf win 4 then slice v (4 * w) w else 0) |||
  (if bitOf win 5 then slice v (5 * w) w else 0)

/-- The thread index selected by a one-hot `win` vector. -/
def selIdx (win : BitVec 6) : BitVec 3 :=
  (if bitOf win 0 then BitVec.ofNat 3 0 else 0) |||
  (if bitOf win 1 then BitVec.ofNat 3 1 else 0) |||
  (if bitOf win 2 then BitVec.ofNat 3 2 else 0) |||
  (if bitOf win 3 then BitVec.ofNat 3 3 else 0) |||
  (if bitOf win 4 then BitVec.ofNat 3 4 else 0) |||
  (if bitOf win 5 then BitVec.ofNat 3 5 else 0)

/-- A selected thread index is one of the six thread indices. -/
theorem selIdx_toNat_lt_six (win : BitVec 6) (h : win &&& (win - 1) = 0) :
    (selIdx win).toNat < 6 := by
  revert h
  revert win
  decide

/-! ## Tables and constants (`wiki/ISA_TABLES_V2.md`, `src/md2_map.vh`) -/

/-- `JUMP_GUARDS[j]` (§7, `wiki/ISA_TABLES_V2.md` "Jump conditions"). -/
def JG_TABLE : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
   34, 35, 36, 37, 39, 41, 43, 38, 40, 42, 44]

/-- `JUMP_GUARDS` applied to a guard vector (§7): entry `jcond` selects
the guard named in the table.  Written as a `jcond` case split with literal
guard indices, so the extracted `jc` (a shift of the RTL's packed table)
is proved equal to it. -/
def jumpGuardBit (g : BitVec 64) (j : BitVec 5) : Bool :=
  if j == BitVec.ofNat 5 0 then bitOf g 0
  else if j == BitVec.ofNat 5 1 then bitOf g 1
  else if j == BitVec.ofNat 5 2 then bitOf g 2
  else if j == BitVec.ofNat 5 3 then bitOf g 3
  else if j == BitVec.ofNat 5 4 then bitOf g 4
  else if j == BitVec.ofNat 5 5 then bitOf g 5
  else if j == BitVec.ofNat 5 6 then bitOf g 6
  else if j == BitVec.ofNat 5 7 then bitOf g 7
  else if j == BitVec.ofNat 5 8 then bitOf g 8
  else if j == BitVec.ofNat 5 9 then bitOf g 17
  else if j == BitVec.ofNat 5 10 then bitOf g 18
  else if j == BitVec.ofNat 5 11 then bitOf g 21
  else if j == BitVec.ofNat 5 12 then bitOf g 22
  else if j == BitVec.ofNat 5 13 then bitOf g 23
  else if j == BitVec.ofNat 5 14 then bitOf g 24
  else if j == BitVec.ofNat 5 15 then bitOf g 25
  else if j == BitVec.ofNat 5 16 then bitOf g 26
  else if j == BitVec.ofNat 5 17 then bitOf g 27
  else if j == BitVec.ofNat 5 18 then bitOf g 28
  else if j == BitVec.ofNat 5 19 then bitOf g 29
  else if j == BitVec.ofNat 5 20 then bitOf g 30
  else if j == BitVec.ofNat 5 21 then bitOf g 34
  else if j == BitVec.ofNat 5 22 then bitOf g 35
  else if j == BitVec.ofNat 5 23 then bitOf g 36
  else if j == BitVec.ofNat 5 24 then bitOf g 37
  else if j == BitVec.ofNat 5 25 then bitOf g 39
  else if j == BitVec.ofNat 5 26 then bitOf g 41
  else if j == BitVec.ofNat 5 27 then bitOf g 43
  else if j == BitVec.ofNat 5 28 then bitOf g 38
  else if j == BitVec.ofNat 5 29 then bitOf g 40
  else if j == BitVec.ofNat 5 30 then bitOf g 42
  else if j == BitVec.ofNat 5 31 then bitOf g 44
  else false

abbrev N_THREADS : Nat := 6
abbrev LAST_T : BitVec 3 := 5
abbrev MD_N_GUARD : Nat := 62
abbrev MD_N_SRC : Nat := 39

abbrev G_TRUE : Nat := 0
abbrev G_L_IN0 : Nat := 27
abbrev G_L_IN1 : Nat := 28
abbrev G_L_SYNC : Nat := 29
abbrev G_L_PINA : Nat := 30
abbrev G_L_PINB : Nat := 31

abbrev S_ZERO : Nat := 0
abbrev S_IMM : Nat := 1
abbrev S_L_IN : Nat := 2
abbrev S_L_CAP : Nat := 3

abbrev JM_ALWAYS : BitVec 2 := 1
abbrev JM_IF : BitVec 2 := 2
abbrev JM_IFNOT : BitVec 2 := 3

abbrev GD_ALWAYS : BitVec 2 := 0
abbrev GD_IF : BitVec 2 := 1
abbrev GD_IFNOT : BitVec 2 := 2

/-! ## State and inputs -/

/-- Core state (§5): the instruction register, the R-valid flag, the fetched
address, the executing thread and its line, and the round-robin cursor. -/
structure State where
  /-- `XV`: `IR` holds an instruction to execute. -/
  xv : Bool
  /-- `RV`: the memory output holds a word of the current burst. -/
  rv : Bool
  /-- `FPC`: the address of the word at the memory output. -/
  fpc : BitVec 8
  /-- `XT`: the executing thread. -/
  xt : BitVec 3
  /-- `XL`: its line. -/
  xl : BitVec 2
  /-- `RR`: the round-robin cursor. -/
  rr : BitVec 3
  /-- `IR`: the instruction register. -/
  ir : BitVec 64
  deriving DecidableEq, Repr

/-- The sampled per-cycle inputs of one core. -/
structure Input where
  /-- `rst_n` at the clock edge. -/
  resetN : Bool
  /-- `frz` (§12.3): this cycle is frozen. -/
  frz : Bool
  /-- `RUN_global`. -/
  runG : Bool
  /-- `rdata`: the program word at address `FPC`. -/
  rdata : BitVec 64
  /-- Thread `READY` flags. -/
  tReady : BitVec 6
  /-- Thread `CORE` bindings. -/
  tCore : BitVec 6
  /-- Thread `LINE` bindings, two bits each. -/
  tLine : BitVec 12
  /-- Thread `PC` values, eight bits each. -/
  tPc : BitVec 48
  /-- Thread watcher codes `W0C`, six bits each. -/
  tW0c : BitVec 36
  /-- Thread watcher codes `W1C`, six bits each. -/
  tW1c : BitVec 36
  /-- Thread watcher handlers `W0H`, eight bits each. -/
  tW0h : BitVec 48
  /-- Thread watcher handlers `W1H`, eight bits each. -/
  tW1h : BitVec 48
  /-- The global guard vector, with the line-relative slots replaced here. -/
  guards : BitVec 64
  /-- Per-line `{PINB, PINA, SYNC, IN1, IN0}` slots. -/
  gLine : BitVec 20
  /-- The global source vector, with `ZERO`/`IMM`/`L.IN`/`L.CAP` replaced here. -/
  srcs : BitVec 512
  /-- Per-line 2-bit input symbol. -/
  lIn : BitVec 8
  /-- Per-line 5-bit capture snapshot. -/
  lCap : BitVec 20
  deriving DecidableEq, Repr

/-! ## Decode (§5, field positions from `wiki/ISA_TABLES_V2.md`) -/

def i_pause (s : State) : Bool := bitOf s.ir 0
def i_jmode (s : State) : BitVec 2 := slice s.ir 1 2
def i_imm (s : State) : BitVec 8 := slice s.ir 3 8
def i_cond (s : State) : BitVec 6 := slice s.ir 11 6
def i_jcond (s : State) : BitVec 5 := slice s.ir 59 5
def i_g (s : State) (m : Nat) : BitVec 2 := slice s.ir (17 + 14 * m) 2
def i_s (s : State) (m : Nat) : BitVec 6 := slice s.ir (19 + 14 * m) 6
def i_d (s : State) (m : Nat) : BitVec 6 := slice s.ir (25 + 14 * m) 6

/-! ## Guards (§7) -/

/-- The five per-line guard slots of line `ln`. -/
def lineSlot (gl : BitVec 20) (ln : BitVec 2) : BitVec 5 :=
  slice gl (BitVec.toNat (5 * (BitVec.setWidth 32 ln))) 5

/-- §7: guard 0 is constant true, `L.IN0/L.IN1/L.SYNC/L.PINA/L.PINB` are the
slots of the executing line, and codes past the guard table are false. -/
def guardVec (g : BitVec 64) (gl : BitVec 20) (ln : BitVec 2) : BitVec 64 :=
  let s := lineSlot gl ln
  let v := setBit g G_TRUE true
  let v := setBit v G_L_IN0 (bitOf s 0)
  let v := setBit v G_L_IN1 (bitOf s 1)
  let v := setBit v G_L_SYNC (bitOf s 2)
  let v := setBit v G_L_PINA (bitOf s 3)
  let v := setBit v G_L_PINB (bitOf s 4)
  v &&& lowMask 64 MD_N_GUARD

/-- The move guard `C` of §5: `G[IR.cond]` on the executing line. -/
def cc (s : State) (i : Input) : Bool :=
  bitOf (guardVec i.guards i.gLine s.xl) (i_cond s).toNat

/-- The jump guard `JC` of §5: `G[JUMP_GUARDS[IR.jcond]]`. -/
def jc (s : State) (i : Input) : Bool :=
  jumpGuardBit (guardVec i.guards i.gLine s.xl) (i_jcond s)

/-! ## Sources (§6.1, "the move bus is 8 bits") -/

/-- Replace one 8-bit slot of the source vector. -/
def withSlot (v : BitVec 512) (slot : Nat) (x : BitVec 8) : BitVec 512 :=
  (v &&& ~~~(BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.allOnes 8)) (8 * slot))) |||
    BitVec.shiftLeft (BitVec.setWidth 512 x) (8 * slot)

/-- The source vector as the core sees it: `srcs` with the four core-local slots
replaced and every code past the source table reading 0. -/
def srcVec (s : State) (i : Input) : BitVec 512 :=
  let v := i.srcs
  let v := withSlot v S_ZERO 0
  let v := withSlot v S_IMM (i_imm s)
  let v := withSlot v S_L_IN
    (BitVec.setWidth 8 (slice i.lIn (BitVec.toNat (2 * (BitVec.setWidth 32 s.xl))) 2))
  let v := withSlot v S_L_CAP
    (BitVec.setWidth 8 (slice i.lCap (BitVec.toNat (5 * (BitVec.setWidth 32 s.xl))) 5))
  v &&& lowMask 512 (8 * MD_N_SRC)

/-- `SRC[IR.src_m]` of §5/§6. -/
def srcByte (s : State) (i : Input) (m : Nat) : BitVec 8 :=
  slice (srcVec s i) (BitVec.toNat (8 * (BitVec.setWidth 32 (i_s s m)))) 8

/-! ## Control (§5) -/

def xa (s : State) (i : Input) : Bool := s.xv && !i.frz
def ra (s : State) (i : Input) : Bool := s.rv && !i.frz

/-- `taken` of §5.  `JM_NEXT = 0` is not taken; the `if`/`ifnot` forms read the
jump guard `JC`. -/
def taken (s : State) (i : Input) : Bool :=
  (i_jmode s == JM_ALWAYS) || ((i_jmode s == JM_IF) && jc s i) ||
    ((i_jmode s == JM_IFNOT) && !jc s i)

def jmp (s : State) (i : Input) : Bool := xa s i && !(i_pause s) && taken s i
def pse (s : State) (i : Input) : Bool := xa s i && i_pause s
def load (s : State) (i : Input) : Bool := ra s i && !(jmp s i) && !(pse s i)
def free (s : State) (i : Input) : Bool := pse s i || (!s.xv && !s.rv && !i.frz)

def npc (s : State) (i : Input) : BitVec 8 := if taken s i then i_imm s else s.fpc

/-! ## Dispatch (§5: "first ready thread bound to `c` in circular order RR, ...") -/

/-- Per-thread "bound to core `c`" mask. -/
def mine (c : Bool) (i : Input) : BitVec 6 := if c then i.tCore else ~~~i.tCore

/-- Threads that may be dispatched this cycle. -/
def cand (c : Bool) (i : Input) : BitVec 6 :=
  i.tReady &&& mine c i &&& (if i.runG then BitVec.allOnes 6 else 0)

/-- The first candidate in the circular order `RR, RR+1, ... (mod 6)`, or `none`
when no ready thread is bound to `c`. -/
def firstCandOf (candv : BitVec 6) (rr : BitVec 3) : Nat → Option Nat
  | 0 =>
    if bitOf candv ((rr.toNat + 0) % 6) then some ((rr.toNat + 0) % 6) else none
  | k + 1 =>
    match firstCandOf candv rr k with
    | some j => some j
    | none =>
      if bitOf candv ((rr.toNat + (k + 1)) % 6) then some ((rr.toNat + (k + 1)) % 6)
      else none

/-- `disp_e` as the SPEC describes it: the first ready thread bound to `c` in
circular order from `RR`. -/
def dispThread (c : Bool) (s : State) (i : Input) : Option Nat :=
  firstCandOf (cand c i) s.rr 5

/-- `disp` of §5. -/
def disp (c : Bool) (s : State) (i : Input) : Bool :=
  free s i && (cand c i) != 0

/-- The one-hot form of `dispThread`: a circular priority chain.  This is the
closed form the elaboration uses; `firstCandOf_eq_win` proves it equal to the
circular scan above. -/
def winOf (candv : BitVec 6) (rr : BitVec 3) : BitVec 6 :=
  let afterRr := candv &&& BitVec.shiftLeft (BitVec.allOnes 6) rr.toNat
  let eligible := if afterRr != 0 then afterRr else candv
  let lower := BitVec.shiftLeft eligible 1 ||| BitVec.shiftLeft eligible 2 |||
    BitVec.shiftLeft eligible 3 ||| BitVec.shiftLeft eligible 4 |||
    BitVec.shiftLeft eligible 5
  eligible &&& ~~~lower

/-- `RR` invariant: the cursor is a thread index. -/
def rrOk (s : State) : Prop := s.rr.toNat < 6

theorem winOf_eq (c : Bool) (s : State) (i : Input) :
    winOf (cand c i) s.rr =
      (let afterRr := (cand c i) &&& BitVec.shiftLeft (BitVec.allOnes 6) s.rr.toNat
       let eligible := if afterRr != 0 then afterRr else cand c i
       let lower := BitVec.shiftLeft eligible 1 ||| BitVec.shiftLeft eligible 2 |||
         BitVec.shiftLeft eligible 3 ||| BitVec.shiftLeft eligible 4 |||
         BitVec.shiftLeft eligible 5
       eligible &&& ~~~lower) := rfl

/-- The circular scan equals the priority chain, for a cursor in `0..5`. -/
theorem firstCandOf_eq_win (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6) :
    firstCandOf candv rr 5 =
      (if winOf candv rr = 0 then none else some (selIdx (winOf candv rr)).toNat) := by
  revert hrr
  revert rr candv
  decide

theorem dispThread_eq (c : Bool) (s : State) (i : Input) (h : rrOk s) :
    dispThread c s i =
      (if winOf (cand c i) s.rr = 0 then none
       else some (selIdx (winOf (cand c i) s.rr)).toNat) :=
  firstCandOf_eq_win (cand c i) s.rr h

/-- `disp_e`: the dispatched thread index, 0 when nothing dispatches. -/
def dispE (c : Bool) (s : State) (i : Input) : BitVec 3 := selIdx (winOf (cand c i) s.rr)

/-- The priority chain keeps at most one bit, so its index is a thread index. -/
theorem winOf_atmost (candv : BitVec 6) (rr : BitVec 3) :
    winOf candv rr &&& (winOf candv rr - 1) = 0 := by
  revert candv rr
  decide

/-- `RR' = (e + 1) mod 6`. -/
def rrNext (e : BitVec 3) : BitVec 3 := if e == LAST_T then 0 else e + 1

def dLine (c : Bool) (s : State) (i : Input) : BitVec 2 := selSlot i.tLine (winOf (cand c i) s.rr)
def dPc (c : Bool) (s : State) (i : Input) : BitVec 8 := selSlot i.tPc (winOf (cand c i) s.rr)
def dW0c (c : Bool) (s : State) (i : Input) : BitVec 6 := selSlot i.tW0c (winOf (cand c i) s.rr)
def dW1c (c : Bool) (s : State) (i : Input) : BitVec 6 := selSlot i.tW1c (winOf (cand c i) s.rr)
def dW0h (c : Bool) (s : State) (i : Input) : BitVec 8 := selSlot i.tW0h (winOf (cand c i) s.rr)
def dW1h (c : Bool) (s : State) (i : Input) : BitVec 8 := selSlot i.tW1h (winOf (cand c i) s.rr)

/-- Watcher 0 fires for the dispatched thread (§5: `G_e` is relative to thread
`e`'s line, and `W0C = 0` disables the watcher). -/
def watcher0 (c : Bool) (s : State) (i : Input) : Bool :=
  (dW0c c s i) != 0 && bitOf (guardVec i.guards i.gLine (dLine c s i)) (dW0c c s i).toNat

/-- Watcher 1 fires for the dispatched thread. -/
def watcher1 (c : Bool) (s : State) (i : Input) : Bool :=
  (dW1c c s i) != 0 && bitOf (guardVec i.guards i.gLine (dLine c s i)) (dW1c c s i).toNat

/-- `d`: the watcher handler, else the thread's `PC` (§5). -/
def dpc (c : Bool) (s : State) (i : Input) : BitVec 8 :=
  if watcher0 c s i then dW0h c s i
  else if watcher1 c s i then dW1h c s i
  else dPc c s i

/-- `fetch address = jmp ? IR.imm : load ? FPC + 1 : disp ? d : none` (§5). -/
def fetchAddr (c : Bool) (s : State) (i : Input) : BitVec 8 :=
  if jmp s i then i_imm s else if load s i then s.fpc + 1 else dpc c s i

def fetchEn (c : Bool) (s : State) (i : Input) : Bool :=
  jmp s i || load s i || disp c s i

/-! ## Moves (§5, §6) -/

/-- The per-move guard of §5. -/
def moveGuardOk (g : BitVec 2) (cnd : Bool) : Bool :=
  (g == GD_ALWAYS) || ((g == GD_IF) && cnd) || ((g == GD_IFNOT) && !cnd)

def mvEnAt (c : Bool) (s : State) (i : Input) (m : Nat) : Bool :=
  xa s i && moveGuardOk (i_g s m) (cc s i)

/-! ## Outputs -/

/-- The combinational outputs of one core. -/
structure Out where
  fetchEn : Bool
  fetchAddr : BitVec 8
  pauseO : Bool
  npcO : BitVec 8
  dispO : Bool
  dispE : BitVec 3
  xtO : BitVec 3
  xlO : BitVec 2
  mvEn : BitVec 3
  mvSrc : BitVec 18
  mvDst : BitVec 18
  mvData : BitVec 24
  dbgXv : Bool
  dbgRv : Bool
  dbgFpc : BitVec 8
  deriving DecidableEq, Repr

def out (c : Bool) (s : State) (i : Input) : Out where
  fetchEn := fetchEn c s i
  fetchAddr := fetchAddr c s i
  pauseO := pse s i
  npcO := npc s i
  dispO := disp c s i
  dispE := dispE c s i
  xtO := s.xt
  xlO := s.xl
  mvEn := boolMask 0 (mvEnAt c s i 0) ||| boolMask 1 (mvEnAt c s i 1) |||
    boolMask 2 (mvEnAt c s i 2)
  mvSrc := BitVec.setWidth 18 (i_s s 0) |||
    BitVec.shiftLeft (BitVec.setWidth 18 (i_s s 1)) 6 |||
    BitVec.shiftLeft (BitVec.setWidth 18 (i_s s 2)) 12
  mvDst := BitVec.setWidth 18 (i_d s 0) |||
    BitVec.shiftLeft (BitVec.setWidth 18 (i_d s 1)) 6 |||
    BitVec.shiftLeft (BitVec.setWidth 18 (i_d s 2)) 12
  mvData := BitVec.setWidth 24 (srcByte s i 0) |||
    BitVec.shiftLeft (BitVec.setWidth 24 (srcByte s i 1)) 8 |||
    BitVec.shiftLeft (BitVec.setWidth 24 (srcByte s i 2)) 16
  dbgXv := s.xv
  dbgRv := s.rv
  dbgFpc := s.fpc

/-! ## Next state (§5, §12.3) -/

def next (c : Bool) (s : State) (i : Input) : State where
  xv := i.resetN && (if i.frz then s.xv else load s i)
  rv := i.resetN && (if i.frz then s.rv else fetchEn c s i)
  fpc := if !i.resetN then 0
    else if i.frz then s.fpc else if fetchEn c s i then fetchAddr c s i else s.fpc
  xt := if !i.resetN then 0 else if i.frz then s.xt else if disp c s i then dispE c s i else s.xt
  xl := if !i.resetN then 0 else if i.frz then s.xl else if disp c s i then dLine c s i else s.xl
  rr := if !i.resetN then 0
    else if i.frz then s.rr else if disp c s i then rrNext (dispE c s i) else s.rr
  ir := if i.frz then s.ir else i.rdata

/-- The §5/§6/§7/§12.3 transition: the name the emitted equivalence theorems
use. -/
abbrev step (c : Bool) (s : State) (i : Input) : State := next c s i

/-! ## Readings of the §5 pseudocode -/

theorem xv_next (c : Bool) (s : State) (i : Input) :
    (next c s i).xv = (i.resetN && (if i.frz then s.xv else load s i)) := rfl

theorem rv_next (c : Bool) (s : State) (i : Input) :
    (next c s i).rv = (i.resetN && (if i.frz then s.rv else fetchEn c s i)) := rfl

theorem ir_next (c : Bool) (s : State) (i : Input) :
    (next c s i).ir = (if i.frz then s.ir else i.rdata) := rfl

theorem fpc_next (c : Bool) (s : State) (i : Input) :
    (next c s i).fpc = (if !i.resetN then 0
      else if i.frz then s.fpc else if fetchEn c s i then fetchAddr c s i else s.fpc) := rfl

theorem xt_next (c : Bool) (s : State) (i : Input) :
    (next c s i).xt = (if !i.resetN then 0
      else if i.frz then s.xt else if disp c s i then dispE c s i else s.xt) := rfl

theorem xl_next (c : Bool) (s : State) (i : Input) :
    (next c s i).xl = (if !i.resetN then 0
      else if i.frz then s.xl else if disp c s i then dLine c s i else s.xl) := rfl

theorem rr_next (c : Bool) (s : State) (i : Input) :
    (next c s i).rr = (if !i.resetN then 0
      else if i.frz then s.rr else if disp c s i then rrNext (dispE c s i) else s.rr) := rfl

/-- SPEC §5: on `load` the instruction register takes the word at the memory
output.  (The RTL also captures without `load`; see the module comment.) -/
theorem irNext_of_load (c : Bool) (s : State) (i : Input) (h : load s i = true) :
    (next c s i).ir = i.rdata := by
  have hf : i.frz = false := by
    by_cases h' : i.frz = true
    · simp [load, ra, h'] at h
    · simpa using h'
  simp [next, hf]

/-! ## §12.3: a frozen cycle holds every register -/

theorem frz_holds (c : Bool) (s : State) (i : Input) (hf : i.frz = true)
    (hr : i.resetN = true) : next c s i = s := by
  have h : next c s i = ⟨s.xv, s.rv, s.fpc, s.xt, s.xl, s.rr, s.ir⟩ := by
    simp [next, hf, hr]
  rw [h]

/-- §12.3: no move is enabled outside an unfrozen execute cycle. -/
theorem mvEnAt_zero (c : Bool) (s : State) (i : Input)
    (h : s.xv = false ∨ i.frz = true) :
    mvEnAt c s i 0 = false ∧ mvEnAt c s i 1 = false ∧ mvEnAt c s i 2 = false := by
  obtain (h | h) := h <;> simp [mvEnAt, xa, h]

theorem mvEn_zero (c : Bool) (s : State) (i : Input)
    (h : s.xv = false ∨ i.frz = true) : (out c s i).mvEn = 0 := by
  obtain ⟨h0, h1, h2⟩ := mvEnAt_zero c s i h
  simp [out, h0, h1, h2, boolMask]

/-! ## §5 consequences -/

/-- `free` is exactly "the core frees up this cycle". -/
theorem free_iff (c : Bool) (s : State) (i : Input) :
    free s i = (pse s i || (!s.xv && !s.rv && !i.frz)) := rfl

/-- SPEC §5 "Consequences": when the core is free and an instruction is in the
X stage, that instruction is a pause, and it retires this cycle. -/
theorem free_no_execute (c : Bool) (s : State) (i : Input) (hfree : free s i = true)
    (hxv : s.xv = true) :
    i_pause s = true ∧ pse s i = true ∧ (next c s i).xv = false := by
  have hpf : i_pause s = true ∧ i.frz = false := by
    by_cases h : i_pause s = true
    · by_cases hf : i.frz = true
      · simp [free, pse, xa, hxv, h, hf] at hfree
      · exact ⟨h, by simpa using hf⟩
    · simp [free, pse, xa, hxv, h] at hfree
  obtain ⟨hp, hfz⟩ := hpf
  have hpse : pse s i = true := by simp [pse, xa, hxv, hp, hfz]
  refine ⟨hp, hpse, ?_⟩
  have hl : load s i = false := by simp [load, jmp, pse, xa, hxv, hp, hfz]
  rw [xv_next, hl, hfz]
  simp

/-- SPEC §12.3: a frozen cycle executes no move, jumps nothing, pauses nothing,
fetches nothing and dispatches nothing. -/
theorem frz_no_fetch (c : Bool) (s : State) (i : Input) (hf : i.frz = true) :
    fetchEn c s i = false ∧ jmp s i = false ∧ pse s i = false ∧
      disp c s i = false ∧ (out c s i).mvEn = 0 := by
  have hxa : xa s i = false := by simp [xa, hf]
  have hfree : free s i = false := by simp [free, pse, xa, hf]
  refine ⟨?_, ?_, ?_, ?_, mvEn_zero c s i (Or.inr hf)⟩
  · simp [fetchEn, jmp, load, ra, disp, hxa, hfree, hf]
  · simp [jmp, hxa]
  · simp [pse, hxa]
  · simp [disp, hfree]

/-- SPEC §5: `disp` needs a free core, `RUN_global`, and a ready thread bound to
`c`. -/
theorem disp_iff (c : Bool) (s : State) (i : Input) :
    disp c s i = true ↔ free s i = true ∧ cand c i ≠ 0 := by
  simp [disp, Bool.and_eq_true]

/-- SPEC §5: the dispatch sets `RR' = (e + 1) mod 6`. -/
theorem disp_rr_next (c : Bool) (s : State) (i : Input) (hr : i.resetN = true)
    (hf : i.frz = false) (hd : disp c s i = true) :
    (next c s i).rr = rrNext (dispE c s i) := by
  simp [next, hr, hf, hd]

/-- SPEC §5: `RR` changes only on dispatch. -/
theorem rr_only_on_disp (c : Bool) (s : State) (i : Input) (hr : i.resetN = true)
    (hf : i.frz = false) (hd : disp c s i = false) :
    (next c s i).rr = s.rr := by
  simp [next, hr, hf, hd]

theorem dispE_toNat_le_five (c : Bool) (s : State) (i : Input) :
    (dispE c s i).toNat < 6 :=
  selIdx_toNat_lt_six _ (winOf_atmost _ _)

theorem rrNext_toNat_lt_six (e : BitVec 3) (he : e.toNat < 6) :
    (rrNext e).toNat < 6 := by
  revert he
  revert e
  decide

/-- The round-robin cursor stays a thread index. -/
theorem rr_next_lt_six (c : Bool) (s : State) (i : Input) (h : rrOk s) :
    rrOk (next c s i) := by
  show (next c s i).rr.toNat < 6
  by_cases hr : i.resetN = true
  · by_cases hf : i.frz = true
    · rw [frz_holds c s i hf hr]; exact h
    · have hf' : i.frz = false := by simpa using hf
      by_cases hd : disp c s i = true
      · rw [disp_rr_next c s i hr hf' hd]
        exact rrNext_toNat_lt_six _ (dispE_toNat_le_five c s i)
      · rw [rr_only_on_disp c s i hr hf' (by simpa using hd)]
        exact h
  · have hr' : i.resetN = false := by simpa using hr
    simp [next, hr']

/-! ## The `XV ⇒ FPC = PC(IR) + 1` invariant of §5

The state does not record the address `IR` came from; `FPC` *is* the R stage's
address.  So the SPEC invariant reads: whenever the core will execute from `IR`,
`FPC` has advanced one past the word it captured.  A frozen cycle holds both. -/

theorem xv_fpc_invariant (c : Bool) (s : State) (i : Input) (h : (next c s i).xv = true) :
    (i.frz = true ∧ (next c s i).fpc = s.fpc ∧ (next c s i).ir = s.ir) ∨
      (i.frz = false ∧ (next c s i).fpc = s.fpc + 1 ∧ (next c s i).ir = i.rdata) := by
  have hr : i.resetN = true := by
    by_cases h' : i.resetN = true
    · exact h'
    · have h2 : i.resetN = false := by simpa using h'
      simp [next, h2] at h
  by_cases hf : i.frz = true
  · left
    refine ⟨hf, ?_, ?_⟩ <;> simp [next, hf, hr]
  · right
    have hf' : i.frz = false := by simpa using hf
    have hload : load s i = true := by simpa [next, hr, hf'] using h
    have hl := hload
    simp only [load, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨⟨hra, hj⟩, hp⟩ := hl
    have hfetch : fetchEn c s i = true := by simp [fetchEn, hj, hload]
    have hfa : fetchAddr c s i = s.fpc + 1 := by simp [fetchAddr, hj, hload]
    refine ⟨hf', ?_, ?_⟩
    · simp [next, hr, hf', hfetch, hfa]
    · simp [next, hf']

/-! ## Traces -/

def stateAt (c : Bool) (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => next c s i) inputs initial n

theorem stateAt_succ (c : Bool) (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt c inputs initial (n + 1) = next c (stateAt c inputs initial n) (inputs n) := rfl

theorem stateAt_zero (c : Bool) (inputs : Nat → Input) (initial : State) :
    stateAt c inputs initial 0 = initial := rfl

/-- SPEC §5 "Consequences": a trigger in cycle `t` with an idle core reaches the
first instruction in `t + 3`.  Stated from the dispatch cycle, which is `t + 1`
(the trigger sets `READY` in `t + 1`): an idle core that may dispatch this cycle
has `RV` next cycle and the first instruction in `IR` the cycle after, so
dispatch in `n` executes in `n + 2`. -/
theorem trace_dispatch_idle (c : Bool) (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (stateAt c inputs initial n).xv = false)
    (hrv : (stateAt c inputs initial n).rv = false)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hcand : cand c (inputs n) ≠ 0)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (stateAt c inputs initial (n + 1)).rv = true ∧
      (stateAt c inputs initial (n + 1)).xv = false ∧
      (stateAt c inputs initial (n + 1)).fpc =
        dpc c (stateAt c inputs initial n) (inputs n) ∧
      (stateAt c inputs initial (n + 2)).xv = true ∧
      (stateAt c inputs initial (n + 2)).fpc =
        dpc c (stateAt c inputs initial n) (inputs n) + 1 ∧
      (stateAt c inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  let s := stateAt c inputs initial n
  let s1 := next c s (inputs n)
  have hxv' : s.xv = false := hxv
  have hrv' : s.rv = false := hrv
  have hfree : free s (inputs n) = true := by simp [free, hxv', hrv', hfrz]
  have hdisp : disp c s (inputs n) = true := by
    rw [disp, hfree]
    simpa using hcand
  have hsj : jmp s (inputs n) = false := by simp [jmp, xa, hxv']
  have hsl : load s (inputs n) = false := by simp [load, ra, hrv']
  have hsfen : fetchEn c s (inputs n) = true := by simp [fetchEn, hdisp]
  have hsfa : fetchAddr c s (inputs n) = dpc c s (inputs n) := by
    simp [fetchAddr, hsj, hsl]
  have h1 : stateAt c inputs initial (n + 1) = s1 := by
    simpa [s1, s] using stateAt_succ c inputs initial n
  have hs1xv : s1.xv = false := by simp [s1, xv_next, hreset, hfrz, hsl]
  have hs1rv : s1.rv = true := by simp [s1, rv_next, hreset, hfrz, hsfen]
  have hs1fpc : s1.fpc = dpc c s (inputs n) := by
    simp [s1, fpc_next, hreset, hfrz, hsfen, hsfa]
  have hl1 : load s1 (inputs (n + 1)) = true := by
    simp [load, ra, jmp, pse, xa, hs1xv, hs1rv, hfrz1]
  have hfen1 : fetchEn c s1 (inputs (n + 1)) = true := by simp [fetchEn, hl1]
  have hfa1 : fetchAddr c s1 (inputs (n + 1)) = s1.fpc + 1 := by
    simp [fetchAddr, jmp, xa, hs1xv, hfrz1, hl1]
  have h2 : stateAt c inputs initial (n + 2) = next c s1 (inputs (n + 1)) := by
    have h := stateAt_succ c inputs initial (n + 1)
    rw [h1] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact hs1rv
  · rw [h1]; exact hs1xv
  · rw [h1]; exact hs1fpc
  · rw [h2]; simp [xv_next, hreset1, hfrz1, hl1]
  · rw [h2, fpc_next, hreset1, hfrz1, hfen1, hfa1, hs1fpc]
    simp [s]
  · rw [h2]; simp [ir_next, hfrz1]

/-- SPEC §5 "Consequences": a taken jump on a non-pausing instruction costs one
idle cycle; the target executes two cycles after the jump. -/
theorem trace_jump_idle (c : Bool) (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (stateAt c inputs initial n).xv = true)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hjmp : jmp (stateAt c inputs initial n) (inputs n) = true)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (stateAt c inputs initial (n + 1)).xv = false ∧
      (stateAt c inputs initial (n + 1)).rv = true ∧
      (stateAt c inputs initial (n + 1)).fpc =
        i_imm (stateAt c inputs initial n) ∧
      (stateAt c inputs initial (n + 2)).xv = true ∧
      (stateAt c inputs initial (n + 2)).fpc =
        i_imm (stateAt c inputs initial n) + 1 ∧
      (stateAt c inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  let s := stateAt c inputs initial n
  let s1 := next c s (inputs n)
  have hxv' : s.xv = true := hxv
  have hj : jmp s (inputs n) = true := hjmp
  have hxa : xa s (inputs n) = true := by
    by_cases h : xa s (inputs n) = true
    · exact h
    · simp [jmp, s, h] at hjmp
  have hpause : i_pause s = false := by
    by_cases h : i_pause s = true
    · simp [jmp, s, h] at hjmp
    · simpa using h
  have hp : pse s (inputs n) = false := by simp [pse, hxa, hpause]
  have hfen : fetchEn c s (inputs n) = true := by simp [fetchEn, hj]
  have hfa : fetchAddr c s (inputs n) = i_imm s := by simp [fetchAddr, hj]
  have hsl : load s (inputs n) = false := by simp [load, hj]
  have h1 : stateAt c inputs initial (n + 1) = s1 := by
    simpa [s1, s] using stateAt_succ c inputs initial n
  have hs1xv : s1.xv = false := by simp [s1, xv_next, hreset, hfrz, hsl]
  have hs1rv : s1.rv = true := by simp [s1, rv_next, hreset, hfrz, hfen]
  have hs1fpc : s1.fpc = i_imm s := by
    simp [s1, fpc_next, hreset, hfrz, hfen, hfa]
  have hl1 : load s1 (inputs (n + 1)) = true := by
    simp [load, ra, jmp, pse, xa, hs1xv, hs1rv, hfrz1]
  have hfen1 : fetchEn c s1 (inputs (n + 1)) = true := by simp [fetchEn, hl1]
  have hfa1 : fetchAddr c s1 (inputs (n + 1)) = s1.fpc + 1 := by
    simp [fetchAddr, jmp, xa, hs1xv, hfrz1, hl1]
  have h2 : stateAt c inputs initial (n + 2) = next c s1 (inputs (n + 1)) := by
    have h := stateAt_succ c inputs initial (n + 1)
    rw [h1] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact hs1xv
  · rw [h1]; exact hs1rv
  · rw [h1]; exact hs1fpc
  · rw [h2]; simp [xv_next, hreset1, hfrz1, hl1]
  · rw [h2, fpc_next, hreset1, hfrz1, hfen1, hfa1, hs1fpc]
    simp [s]
  · rw [h2]; simp [ir_next, hfrz1]

end Metronome.Core
