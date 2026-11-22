import Metronome.Bridge.Moves

/-!
# Compiled check of the machine's destination/source decoder tables

The kernel cannot reduce `String.splitOnAux` (it is `@[irreducible]` in Lean
4.35.0 core), so `Metronome.Machine.Util.dstOfName` of a *parsed* destination
name (any name that is not one of the 21 fixed names) has no kernel value.  The
bridge therefore takes the decoder kind table as the single global hypothesis
`Metronome.Bridge.Moves.DstKindTable`.  This script checks that hypothesis, and
the (kernel-proved) group table, by *compiled* evaluation of the machine's own
`dstOp`, `dstGroup` and `srcOp` against the cut's `dgTable`.

Run from `code/tests/lean`:

    lake env lean --run ../../data/raw/lean_bridge_moves_v4_20261121b/decode_check.lean

Exit code 0 means every one of the 64 destination kinds, all 64 group entries and
the two source codes agree.
-/

open Metronome.Machine

def dstClassOf : DstOp → Nat
  | .null => 0
  | .lsym _ => 1
  | .stop => 2
  | _ => 3

def srcClassOf : SrcOp → Nat
  | .pD => 1
  | .hostIn => 2
  | _ => 0

def main : IO UInt32 := do
  let mut bad : Nat := 0
  let mut kinds : Array Nat := #[]
  let mut groups : Array Nat := #[]
  for d in List.range 64 do
    let g := (Metronome.Moves.dgTable (BitVec.ofNat 6 d)).toNat
    let k := dstClassOf (Metronome.Machine.dstOp d)
    let ek := if g == 0 then 1 else if g == 1 then 2 else if g == 31 then 0 else 3
    kinds := kinds.push k
    groups := groups.push g
    if k != ek then
      IO.println s!"FAIL kind d={d}: machine={k} cut={ek}"
      bad := bad + 1
    let mg := Metronome.Machine.Util.dstGroup.getD d none
    let eg := if g == 31 then none else some g
    if mg != eg then
      IO.println s!"FAIL group d={d}: machine={mg} cut={eg}"
      bad := bad + 1
  IO.println s!"machine dst kinds  (0 NULL, 1 L.SYM, 2 T.STOP, 3 other): {kinds.toList}"
  IO.println s!"cut dgTable codes (31 = none): {groups.toList}"
  let s33 := srcClassOf (Metronome.Machine.srcOp 33)
  let s38 := srcClassOf (Metronome.Machine.srcOp 38)
  if s33 != 1 then
    IO.println s!"FAIL source 33: class {s33} (expected P0.D)"
    bad := bad + 1
  if s38 != 2 then
    IO.println s!"FAIL source 38: class {s38} (expected HOST.IN)"
    bad := bad + 1
  IO.println s!"source classes: 33 -> {s33} (1 = P0.D), 38 -> {s38} (2 = HOST.IN)"
  if bad == 0 then
    IO.println "DECODE CHECK OK: 64 destination kinds, 64 destination groups, 2 source codes"
    return 0
  else
    IO.println s!"DECODE CHECK FAILED: {bad} mismatches"
    return 1
