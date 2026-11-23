import Metronome.Machine.Stream

/-! §5 Cores (pipeline, dispatch, watchers); §6 source ports and enabled moves; §7 guard and jump conditions;
§12.3 freeze of the cores. -/

namespace Metronome.Machine

open Util Tables

/-- §5 / ISA_TABLES_V2 instruction word field (`machine.FIELDS`: lsb, width). -/
def insnField (ir : BitVec 64) (f : Nat × Nat) : Nat := nbits ir.toNat f.1 f.2

/-- §7 Guard condition `g` evaluated on cycle-t state, with line-relative guards taken from line `l`:
`L.IN0, L.IN1` are the bits of `IN`, `L.SYNC` is `SP`, `L.PINA, L.PINB` are `PIN[PINA]`, `PIN[PINB]`, `Lk.RUN` is
line k's `RUN`, `PINk` is `PIN[k]`; §6.1 `HOST.OUTE` is `!OUTV`, `LFk.OUT` is `S[0]`; §6.3 stream guards; guard 0
is constant true and indices beyond the table are false (9a.1). -/
def guardVal (s : State) (cv : CfgView) (p : PinView) (l : Nat) (g : GuardOp) : Bool :=
  let lc := vget cv.lines l
  let ls := vget s.lines l
  let u := s.units
  let sc (k : Nat) := vget cv.streams k
  let ss (k : Nat) := vget s.streams k
  match g with
  | .true_ => true
  | .invalid => false
  | .flag k => bit u.f k
  | .shDone k => (vget u.sh k).cnt.toNat == 0
  | .shOut k => shOut (vget u.sh k)
  | .cntZ k => (vget u.cnt k).toNat == 0
  | .accZ => u.z
  | .accC => u.c
  | .accN => u.n
  | .lIn0 => nbit (inSym lc ls) 0
  | .lIn1 => nbit (inSym lc ls) 1
  | .lSync => ls.sp
  | .lPinA => p.pin lc.pina
  | .lPinB => p.pin lc.pinb
  | .lfOut k => bit (vget u.lf k) 0
  | .hostInv => s.ctrl.inv
  | .hostOutE => !s.ctrl.outv
  | .pRdy => s.p0.rdy
  | .sEnd k => streamEnd (sc k) (ss k)
  | .sMark k => streamMark (sc k) (ss k)
  | .sByte k => streamAtByte (ss k)
  | .sBit k => streamBit (sc k) k s.dbg (ss k)
  | .pin k => p.pin k
  | .lRun k => (vget s.lines k).run

/-- §6 Source port value on the 8-bit move bus (single-bit sources in bit 0, unused high bits 0), read from cycle-t
state with line-relative ports on line `l`. `L.IN` is the 2-bit `IN`; `L.CAP` is `{REM, SN}`; `PINS.LO/HI` are
`PIN[7:0]` and `PIN[12:8]`; `P0.D` is `D`; `HOST.IN` is `INB`; indices beyond the table read 0 (9a.1). -/
def srcVal (s : State) (cv : CfgView) (p : PinView) (l : Nat) (imm : Nat) (op : SrcOp) : Nat :=
  let lc := vget cv.lines l
  let ls := vget s.lines l
  let u := s.units
  match op with
  | .zero => 0
  | .imm => imm % 256
  | .lIn => inSym lc ls
  | .lCap => b2n ls.rem * 16 + ls.sn.toNat
  | .flagsLo => getByte u.f 0
  | .flagsHi => getByte u.f 1
  | .pinsLo => p.lvl % 256
  | .pinsHi => (p.lvl >>> 8) % 32
  | .acc => u.a.toNat
  | .reg k => (vget u.r k).toNat
  | .shD k => (vget u.sh k).d.toNat
  | .shO k => b2n (shOut (vget u.sh k))
  | .cntLo k => getByte (vget u.cnt k) 0
  | .cntHi k => getByte (vget u.cnt k) 1
  | .lfB k b => getByte (vget u.lf k) b
  | .lfO k => b2n (bit (vget u.lf k) 0)
  | .pD => s.p0.d.toNat
  | .sBit k => b2n (streamBit (vget cv.streams k) k s.dbg (vget s.streams k))
  | .sByte k => streamByte (vget cv.streams k) (vget s.streams k)
  | .hostIn => s.ctrl.inb.toNat

/-- §5 Combinational control of one core in cycle t. -/
structure CoreComb where
  moves : List Move
  taken : Bool
  npc : Nat
  jmp : Bool
  pse : Bool
  load : Bool
  free : Bool
  disp : Bool
  dispThread : Nat
  dispAddr : Nat
  fetch : Option Nat
deriving Repr, Inhabited

/-- §5 Dispatch choice: the first ready thread bound to core c in circular order `RR, RR+1, ... (mod 6)`. -/
def pickThread (s : State) (cv : CfgView) (c : Nat) : Option Nat :=
  let rr := (vget s.cores c).rr.toNat
  ((List.range N_THREADS).map fun i => (rr + i) % N_THREADS).find? fun e =>
    (vget cv.threads e).core == c && (vget s.threads e).ready

/-- §5 Watchers: `d = (W0C[e] != 0 && G_e[W0C[e]]) ? W0H[e] : (W1C[e] != 0 && G_e[W1C[e]]) ? W1H[e] : PC[e]`, with `G_e`
relative to thread e's line, on the state before the cycle's moves. -/
def watcherAddr (s : State) (cv : CfgView) (p : PinView) (e : Nat) : Nat :=
  let tc := vget cv.threads e
  let G (i : Nat) := guardVal s cv p tc.line (guardOp i)
  if tc.w0c != 0 && G tc.w0c then tc.w0h
  else if tc.w1c != 0 && G tc.w1c then tc.w1h
  else (vget s.threads e).pc.toNat

/-- §5 / §6 / §7 / §12.3 Core c in cycle t:

```
if XV: C = G[IR.cond]; JC = G[JUMP_GUARDS[IR.jcond]]; en_m per guard_m; taken per jmode; npc = taken ? imm : FPC
jmp = XV && !pause && taken;  pse = XV && pause;  load = RV && !jmp && !pse;  free = pse || (!XV && !RV)
disp = free && RUN_global && some ready thread bound to c
fetch address = jmp ? IR.imm : load ? FPC + 1 : disp ? d : none
```
In a frozen cycle nothing executes, jumps, pauses, fetches or dispatches, and there are no moves. -/
def coreComb (s : State) (cv : CfgView) (p : PinView) (c : Nat) (frozen : Bool) : CoreComb :=
  let cs := vget s.cores c
  let ir := cs.ir
  let xl := cs.xl.toNat
  let xt := cs.xt.toNat
  let xv := cs.xv && !frozen
  let G (g : GuardOp) := guardVal s cv p xl g
  let cnd := G (guardOp (insnField ir FIELD_cond))
  let jc := G (jumpGuard (insnField ir FIELD_jcond))
  let imm := insnField ir FIELD_imm
  let moveFields := [(FIELD_m0_guard, FIELD_m0_src, FIELD_m0_dst), (FIELD_m1_guard, FIELD_m1_src, FIELD_m1_dst),
                     (FIELD_m2_guard, FIELD_m2_src, FIELD_m2_dst)]
  let moves : List Move := if !xv then [] else
    (moveFields.zip (List.range N_MOVES)).filterMap fun ((fg, fs, fd), m) =>
      let gm := insnField ir fg
      let en := gm == MGUARD_always || (gm == MGUARD_if && cnd) || (gm == MGUARD_ifnot && !cnd)
      if en then
        let si := insnField ir fs
        some { core := c, idx := m, src := si, dst := insnField ir fd,
               v := srcVal s cv p xl imm (srcOp si), thread := xt, line := xl,
               armed := (vget s.threads xt).armed }
      else none
  let jm := insnField ir FIELD_jmode
  let taken := jm == JMODE_always || (jm == JMODE_if && jc) || (jm == JMODE_ifnot && !jc)
  let npc := if taken then imm else cs.fpc.toNat
  let pause := insnField ir FIELD_pause == 1
  let jmp := xv && !pause && taken
  let pse := xv && pause
  let load := !frozen && cs.rv && !jmp && !pse
  let free := !frozen && (pse || (!cs.xv && !cs.rv))
  let pick := if free && s.ctrl.run then pickThread s cv c else none
  let disp := pick.isSome
  let e := pick.getD 0
  let d := if disp then watcherAddr s cv p e else 0
  let fetch := if jmp then some imm else if load then some ((cs.fpc.toNat + 1) % 256) else if disp then some d
    else none
  { moves, taken, npc, jmp, pse, load, free, disp, dispThread := e, dispAddr := d, fetch }

/-- §5 / §12.3 Core next state: `FPC' = address` if a fetch address; `RV' = jmp || load || disp`; `XV' = load`; if
load `IR' =` the word at the memory output; on dispatch `XT' = e, XL' = LINE[e], RR' = (e + 1) mod 6`. The program
memory output takes the word at the fetch address (`mout`) and holds when no address is presented
(-- AMBIG(20)). In a frozen cycle the core holds. -/
def coreNext (cs : CoreSt) (cv : CfgView) (cb : CoreComb) (word : Option Nat) (frozen : Bool) : CoreSt :=
  if frozen then cs else
  let tc := vget cv.threads cb.dispThread
  { xv := cb.load, ir := if cb.load then cs.mout else cs.ir, rv := cb.jmp || cb.load || cb.disp,
    fpc := match cb.fetch with
      | some a => bv 8 a
      | none => cs.fpc
    xt := if cb.disp then bv 3 cb.dispThread else cs.xt,
    xl := if cb.disp then bv 2 tc.line else cs.xl,
    rr := if cb.disp then bv 3 ((cb.dispThread + 1) % N_THREADS) else cs.rr,
    mout := match word with
      | some w => bv 64 w
      | none => cs.mout }

/-- §5 Program memory word `w` of a core (byte k of word w holds word bits 8k+7..8k). -/
def progWord (m : ByteArray) (w : Nat) : Nat := bgetLE m (8 * (w % 256)) 8

end Metronome.Machine
