import Metronome.Machine.Line

/-!
§6 Moves, write groups and conflicts; §7 and 9a.1 encodings. The port, guard and trigger meanings are decoded once
from the generated name tables (`Tables.srcNames`, `dstNames`, `guardNames`, `triggerNames`, `writeGroups`), so the
index of every port is the table's.
-/

namespace Metronome.Machine

open Util Tables

/-- §6 / ISA_TABLES_V2 destination ports. `lsym op`: 1 `L.SYM`, 2 `L.DBIT`, 3 `L.XOR` (§3.6); `acc op`: 0 LD, 1 ADD,
2 SUB, 3 AND, 4 OR, 5 XOR, 6 CMP (§6.1). -/
inductive DstOp where
  | null
  | lsym (op : Nat)
  | stop
  | fset
  | fclr
  | acc (op : Nat)
  | reg (k : Nat)
  | shLd (k : Nat)
  | shSh (k : Nat)
  | shCfg (k : Nat)
  | cntLo (k : Nat)
  | cntHi (k : Nat)
  | cntDec (k : Nat)
  | lfSt (k : Nat)
  | lfB (k b : Nat)
  | pAl
  | pAh
  | pW
  | pR
  | sAdv (k : Nat)
  | sRx (k : Nat)
  | sCtl (k : Nat)
  | lCtl (k : Nat)
  | hostOut
  | cwAl
  | cwAh
  | cwD
deriving Repr, Inhabited

/-- §6 / ISA_TABLES_V2 source ports. -/
inductive SrcOp where
  | zero
  | imm
  | lIn
  | lCap
  | flagsLo
  | flagsHi
  | pinsLo
  | pinsHi
  | acc
  | reg (k : Nat)
  | shD (k : Nat)
  | shO (k : Nat)
  | cntLo (k : Nat)
  | cntHi (k : Nat)
  | lfB (k b : Nat)
  | lfO (k : Nat)
  | pD
  | sBit (k : Nat)
  | sByte (k : Nat)
  | hostIn
deriving Repr, Inhabited

/-- §7 / ISA_TABLES_V2 guard conditions; `invalid` for indices beyond the table (9a.1: false). -/
inductive GuardOp where
  | true_
  | invalid
  | flag (k : Nat)
  | shDone (k : Nat)
  | shOut (k : Nat)
  | cntZ (k : Nat)
  | accZ
  | accC
  | accN
  | lIn0
  | lIn1
  | lSync
  | lPinA
  | lPinB
  | lfOut (k : Nat)
  | hostInv
  | hostOutE
  | pRdy
  | sEnd (k : Nat)
  | sMark (k : Nat)
  | sByte (k : Nat)
  | sBit (k : Nat)
  | pin (k : Nat)
  | lRun (k : Nat)
deriving Repr, Inhabited

/-- §4 / ISA_TABLES_V2 trigger sources (`TRIG` codes); `none` also for codes beyond the table (9a.1). -/
inductive TrigOp where
  | none
  | beat (g : Nat)
  | tap (g k : Nat)
  | flagRise (k : Nat)
  | pinaRise
  | pinaFall
  | pinaEdge
  | hostInv
  | always
deriving Repr, Inhabited

namespace Util
/-- Split a unit name into its letters and trailing instance number: `"SH1"` -> `("SH", some 1)`. -/
def splitIdx (s : String) : String × Option Nat :=
  let cs := s.toList
  let ds := (cs.reverse.takeWhile Char.isDigit).reverse
  let pre := cs.take (cs.length - ds.length)
  (String.ofList pre, if ds.isEmpty then none else (String.ofList ds).toNat?)

/-- Unit and port of a dotted port name. -/
def parsePort (name : String) : (String × Option Nat) × String :=
  match name.splitOn "." with
  | [u, p] => (splitIdx u, p)
  | [u] => (splitIdx u, "")
  | _ => (("", none), "")

/-- Look up a key in an association list. -/
def look {α : Type} (xs : List (String × α)) (k : String) : Option α := (xs.find? (·.1 == k)).map (·.2)

/-- Decode a destination name of `Tables.dstNames`. -/
def dstOfName (name : String) : DstOp :=
  let ((u, ko), p) := parsePort name
  let k := ko.getD 0
  let fixed : List (String × DstOp) :=
    [("L.SYM", .lsym 1), ("L.DBIT", .lsym 2), ("L.XOR", .lsym 3), ("T.STOP", .stop), ("FLAGS.SET", .fset),
     ("FLAGS.CLR", .fclr), ("ACC.LD", .acc 0), ("ACC.ADD", .acc 1), ("ACC.SUB", .acc 2), ("ACC.AND", .acc 3),
     ("ACC.OR", .acc 4), ("ACC.XOR", .acc 5), ("ACC.CMP", .acc 6), ("P0.AL", .pAl), ("P0.AH", .pAh),
     ("P0.W", .pW), ("P0.R", .pR), ("HOST.OUT", .hostOut), ("CW.AL", .cwAl), ("CW.AH", .cwAh), ("CW.D", .cwD)]
  let fam : List (String × DstOp) :=
    [("R.", .reg k), ("SH.LD", .shLd k), ("SH.SH", .shSh k), ("SH.CFG", .shCfg k), ("CNT.LO", .cntLo k),
     ("CNT.HI", .cntHi k), ("CNT.DEC", .cntDec k), ("LF.ST", .lfSt k), ("S.ADV", .sAdv k), ("S.RX", .sRx k),
     ("S.CTL", .sCtl k), ("L.CTL", .lCtl k)]
  match look fixed name with
  | some d => d
  | none =>
    if ko.isNone then .null
    else match look fam (u ++ "." ++ p) with
      | some d => d
      | none => match u, splitIdx p with
        | "LF", ("B", some b) => .lfB k b
        | _, _ => .null

/-- Decode a source name of `Tables.srcNames`. -/
def srcOfName (name : String) : SrcOp :=
  let ((u, ko), p) := parsePort name
  let k := ko.getD 0
  let fixed : List (String × SrcOp) :=
    [("ZERO", .zero), ("IMM", .imm), ("L.IN", .lIn), ("L.CAP", .lCap), ("FLAGS.LO", .flagsLo),
     ("FLAGS.HI", .flagsHi), ("PINS.LO", .pinsLo), ("PINS.HI", .pinsHi), ("ACC", .acc), ("P0.D", .pD),
     ("HOST.IN", .hostIn)]
  let fam : List (String × SrcOp) :=
    [("R.", .reg k), ("SH.D", .shD k), ("SH.O", .shO k), ("CNT.LO", .cntLo k), ("CNT.HI", .cntHi k),
     ("LF.O", .lfO k), ("S.BIT", .sBit k), ("S.BYTE", .sByte k)]
  match look fixed name with
  | some d => d
  | none =>
    if ko.isNone then .zero
    else match look fam (u ++ "." ++ p) with
      | some d => d
      | none => match u, splitIdx p with
        | "LF", ("B", some b) => .lfB k b
        | _, _ => .zero

/-- Decode a guard name of `Tables.guardNames`. -/
def guardOfName (name : String) : GuardOp :=
  let ((u, ko), p) := parsePort name
  let k := ko.getD 0
  let fixed : List (String × GuardOp) :=
    [("TRUE", .true_), ("ACC.Z", .accZ), ("ACC.C", .accC), ("ACC.N", .accN), ("L.IN0", .lIn0), ("L.IN1", .lIn1),
     ("L.SYNC", .lSync), ("L.PINA", .lPinA), ("L.PINB", .lPinB), ("HOST.INV", .hostInv),
     ("HOST.OUTE", .hostOutE), ("P0.RDY", .pRdy)]
  let fam : List (String × GuardOp) :=
    [("F.", .flag k), ("SH.DONE", .shDone k), ("SH.OUT", .shOut k), ("CNT.Z", .cntZ k), ("LF.OUT", .lfOut k),
     ("S.END", .sEnd k), ("S.MARK", .sMark k), ("S.BYTE", .sByte k), ("S.BIT", .sBit k), ("PIN.", .pin k),
     ("L.RUN", .lRun k)]
  match look fixed name with
  | some d => d
  | none =>
    if ko.isNone then .invalid
    else (look fam (u ++ "." ++ p)).getD .invalid

/-- Decode a trigger name of `Tables.triggerNames`. -/
def trigOfName (name : String) : TrigOp :=
  let ((u, ko), p) := parsePort name
  let k := ko.getD 0
  let fixed : List (String × TrigOp) :=
    [("PINA.RISE", .pinaRise), ("PINA.FALL", .pinaFall), ("PINA.EDGE", .pinaEdge), ("HOST.INV", .hostInv),
     ("ALWAYS", .always)]
  match look fixed name with
  | some d => d
  | none =>
    if ko.isNone then .none
    else if u == "L" && p == "BEAT" then .beat k
    else if u == "FLAG" && p == "RISE" then .flagRise k
    else match u, splitIdx p with
      | "L", ("TAP", some t) => .tap k t
      | _, _ => .none

/-- Decoded destination table. -/
def dstOps : Array DstOp := dstNames.map dstOfName
/-- Decoded source table. -/
def srcOps : Array SrcOp := srcNames.map srcOfName
/-- Decoded guard table. -/
def guardOps : Array GuardOp := guardNames.map guardOfName
/-- Decoded trigger table. -/
def trigOps : Array TrigOp := triggerNames.map trigOfName
/-- Jump-condition table as guard indices. -/
def jumpGuardIdx : Array Nat := jumpGuardNames.map fun n => (guardNames.idxOf? n).getD guardNames.size
/-- Write group index of each destination. -/
def dstGroup : Array (Option Nat) :=
  dstNames.map fun n => writeGroups.findIdx? fun (_, ms) => ms.contains n
end Util

/-- §6 / 9a.1 Destination port of an index; indices beyond the table are `NULL`. -/
def dstOp (i : Nat) : DstOp := dstOps.getD i .null

/-- §6 / 9a.1 Source port of an index; indices beyond the table read 0. -/
def srcOp (i : Nat) : SrcOp := srcOps.getD i .zero

/-- §7 / 9a.1 Guard of an index; indices beyond the table evaluate false. -/
def guardOp (i : Nat) : GuardOp := guardOps.getD i .invalid

/-- §7 Jump condition `jcond` selects guard `JUMP_GUARDS[jcond]`; all 32 entries are defined. -/
def jumpGuard (j : Nat) : GuardOp := guardOp (jumpGuardIdx.getD j guardNames.size)

/-- §4 / 9a.1 Trigger source of a `TRIG` code; codes beyond the table never fire. -/
def trigOp (i : Nat) : TrigOp := trigOps.getD i .none

/-- §6 One enabled move of cycle t: its core and move index, destination index, bus value (8 bits, read from cycle-t
state) and its source index, the executing thread `XT` and line `XL`, and that thread's `ARMED`. -/
structure Move where
  core : Nat
  idx : Nat
  src : Nat
  dst : Nat
  v : Nat
  thread : Nat
  line : Nat
  armed : Bool
deriving Repr, Inhabited

/-- §6 Write group of a move: `machine.WRITE_GROUPS` index, with `L.SYM` resolved to the executing thread's line and
`T.STOP` to the thread. `NULL` has no group. -/
def moveGroup (m : Move) : Option (Nat × Nat) :=
  match dstOp m.dst with
  | .null => none
  | .lsym _ => (dstGroup.getD m.dst none).map (·, m.line)
  | .stop => (dstGroup.getD m.dst none).map (·, m.thread)
  | _ => (dstGroup.getD m.dst none).map (·, 0)

/-- §6 Conflict resolution. `ms` lists the enabled moves of both cores in (core, move index) order. If two or more
enabled moves target one group, `CONFLICT' = 1` and only the write with the lowest (core, move index) takes effect.
Returns the winning moves and the conflict flag. -/
def resolveMoves (ms : List Move) : List Move × Bool :=
  let step := fun (acc : List Move × List (Nat × Nat) × Bool) (m : Move) =>
    let (ws, seen, cf) := acc
    match moveGroup m with
    | none => acc
    | some g => if seen.contains g then (ws, seen, true) else (ws ++ [m], seen ++ [g], cf)
  let (ws, _, cf) := ms.foldl step ([], [], false)
  (ws, cf)

end Metronome.Machine
