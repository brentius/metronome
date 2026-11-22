import Metronome.ChipCut.Assembly

open Metronome

/-- Check all indexed entries and one representative of the constant out-of-range defaults. -/
def failures (size : Nat) (ok : Nat -> Bool) : List Nat :=
  (List.range (size + 1)).filter fun i => !ok i

def main : IO UInt32 := do
  let src := failures 64 fun i => Machine.srcOp i == Bridge.Glue.srcOpOf i
  let guard := failures 64 fun i => Machine.guardOp i == Bridge.Glue.guardOpOf i
  let jg := failures 32 fun i =>
    Machine.Util.jumpGuardIdx.getD i Machine.Tables.guardNames.size == Core.JG_TABLE.getD i 62
  IO.println s!"SrcTable failures (codes 0..64): {src}"
  IO.println s!"GuardTable failures (codes 0..64): {guard}"
  IO.println s!"JGTable failures (codes 0..32): {jg}"
  return if src.isEmpty && guard.isEmpty && jg.isEmpty then 0 else 1