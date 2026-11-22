import Metronome.ChipCut.Discharge.MoveFabricKeyed

/-!
# Compiled check of `DstStreamLineTable` (evidence, not part of the submission)

`Machine.dstOp` is opaque in the kernel on the parsed destination names
(`String.splitOn` is `@[irreducible]`), so the `DstStreamLineTable` rows are
checked by **compiled evaluation** (the same method as `decode_check_payload`).
The kernel statement is `DstStreamLineTable` in `MoveFabricKeyed.lean`; this file
prints the failing codes (expected: none).
-/

open Metronome

/-- One row: the decoded stream/line-control port must have its own code. -/
def rowOk (o : Machine.DstOp) (d : Nat) : Bool :=
  match o with
  | .sAdv n => d == 47 + n
  | .sRx n => d == 49 + n
  | .sCtl n => d == 51 + n
  | .lCtl n => d == 53 + n
  | .lsym n => n == d
  | _ => true

/-- All 64 codes violate no row. -/
def badCodes : List Nat :=
  (List.range 64).filter (fun d => !(rowOk (Machine.dstOp d) d))

/-- The number of failing codes (must be 0). -/
def failures : Nat := badCodes.length

def report : IO Unit := do
  IO.println s!"decode_check_streamline: codes = 64, failures = {failures}"
  IO.println s!"bad codes = {badCodes}"

def main : IO Unit := report
