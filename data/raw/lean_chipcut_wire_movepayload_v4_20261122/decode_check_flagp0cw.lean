/-
# Compiled check of `DstFlagP0CwTable`

The table `MovePayloadWire.DstFlagP0CwTable` (the `FLAGS`/`P0`/`CW` destination
codes) cannot be checked in the kernel: `Machine.dstOp` decodes the generated
string table through `String.splitOnAux`, which is irreducible.  This program
evaluates `Machine.dstOp` on all 64 destination codes (compiled, not kernel) and
checks every row of the table.

Run:  lake env lean --run .../decode_check_flagp0cw.lean
Exit code 0 iff every row holds for all 64 codes.
-/
import Metronome.ChipCut.Discharge.MovePayloadWire

open Metronome

/-- The 64 destination codes. -/
def codes : List Nat := List.range 64

/-- Codes whose decode is `fset` but is not 5. -/
def badFset : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .fset => d != 5 | _ => false

def badFclr : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .fclr => d != 6 | _ => false

def badPAl : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .pAl => d != 43 | _ => false

def badPAh : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .pAh => d != 44 | _ => false

def badPW : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .pW => d != 45 | _ => false

def badPR : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .pR => d != 46 | _ => false

def badCwAl : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .cwAl => d != 58 | _ => false

def badCwAh : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .cwAh => d != 59 | _ => false

def badCwD : List Nat :=
  codes.filter fun d => match Machine.dstOp d with | .cwD => d != 60 | _ => false

/-- Codes in the `CW` write group (code 58's group) that do not decode as one of
the three `CW` ports. -/
def badCwGroup : List Nat :=
  codes.filter fun d =>
    (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 58) &&
      (match Machine.dstOp d with | .cwAl => false | .cwAh => false | .cwD => false | _ => true)

/-- The nine table rows, as names and violation lists. -/
def rows : List (String × List Nat) :=
  [("fset  (d = 5)", badFset), ("fclr  (d = 6)", badFclr),
   ("pAl   (d = 43)", badPAl), ("pAh   (d = 44)", badPAh),
   ("pW    (d = 45)", badPW), ("pR    (d = 46)", badPR),
   ("cwAl  (d = 58)", badCwAl), ("cwAh  (d = 59)", badCwAh),
   ("cwD   (d = 60)", badCwD), ("cwGroup (CW codes)", badCwGroup)]

/-- The three `CW` codes are one write group, and the group is not `NULL`/`L.SYM`/
`T.STOP` (the `pickScan` side conditions). -/
def cwGroupId : Bool :=
  (Moves.dgTable (BitVec.ofNat 6 58) == Moves.dgTable (BitVec.ofNat 6 59)) &&
    (Moves.dgTable (BitVec.ofNat 6 58) == Moves.dgTable (BitVec.ofNat 6 60)) &&
      (!(Moves.dgTable (BitVec.ofNat 6 58) == Moves.dgNone)) &&
        (!(Moves.dgTable (BitVec.ofNat 6 58) == Moves.dgLSym)) &&
          (!(Moves.dgTable (BitVec.ofNat 6 58) == Moves.dgTStop))

def main : IO Unit := do
  let mut failures := 0
  for (name, bad) in rows do
    if bad.isEmpty then
      IO.println s!"ok   {name}"
    else
      failures := failures + 1
      IO.println s!"FAIL {name}: codes {bad}"
  if cwGroupId then
    IO.println "ok   cwGroupId (58/59/60 one non-keyed group)"
  else
    failures := failures + 1
    IO.println "FAIL cwGroupId"
  IO.println s!"checked {codes.length} codes, {rows.length + 1} rows, failures = {failures}"
  if failures != 0 then
    IO.Process.exit 1
