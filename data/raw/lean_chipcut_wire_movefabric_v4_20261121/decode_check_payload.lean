import Metronome.ChipCut.Discharge.MoveFabric

/-!
# Compiled check of `DstPayloadTable`

`DstPayloadTable` (`Metronome/ChipCut/Discharge/MoveFabric.lean` §12) says, for
every write-group family `f` and every code `d < 64`,

    (Moves.dgTable d == famG f) = famIn f (Machine.dstOp d)

i.e. the cut's group code set is exactly the set of codes whose machine decode
carries that group's payload.  The kernel cannot reduce `Machine.Util.dstOfName` on
the generated table's parsed names (`String.splitOnAux` is `@[irreducible]` in Lean
4.35.0 core), which is why this is a hypothesis at all.  This script checks it by
*compiled* evaluation of the machine's own `dstOp` against the cut's `dgTable`,
exactly as `data/raw/lean_bridge_moves_v4_20261121b/decode_check.lean` checks
`DstKindTable`.

Run from `code/tests/lean`:

    lake env lean --run ../../data/raw/lean_chipcut_wire_movefabric_v4_20261121/decode_check_payload.lean

Exit code 0 means every (family, code) pair agrees.
-/

open Metronome

namespace Check

open Metronome.ChipCut.Discharge.MoveFabric

/-- All write-group families (with their index ranges). -/
def families : List Fam :=
  [ .acc, .flags,
    .reg 0, .reg 1, .reg 2, .reg 3,
    .sh 0, .sh 1, .shCfg 0, .shCfg 1,
    .cnt 0, .cnt 1, .cnt 2,
    .lf 0, .lf 1,
    .p0,
    .stream 0, .stream 1,
    .lCtl 0, .lCtl 1, .lCtl 2, .lCtl 3,
    .hostOut ]

def main : IO UInt32 := do
  let mut bad : Nat := 0
  for f in families do
    let g := (famG f).toNat
    let mut codes : Array Nat := #[]
    for d in List.range 64 do
      let cutoff := (Moves.dgTable (BitVec.ofNat 6 d) == famG f)
      let mach := famIn f (Machine.dstOp d)
      if cutoff != mach then
        IO.println s!"FAIL fam={repr f} code={d}: cut group test={cutoff} machine pattern={mach}"
        bad := bad + 1
      if cutoff then codes := codes.push d
    if (famG f == Moves.dgNone) || (famG f == Moves.dgLSym) || (famG f == Moves.dgTStop) then
      IO.println s!"FAIL nonkeyed fam={repr f}: group {g} is NULL/L.SYM/T.STOP"
      bad := bad + 1
    IO.println s!"fam {repr f}: group {g}, codes {codes.toList}"
  -- codeOf component: the payload index fixes the code
  for d in List.range 64 do
    match Machine.dstOp d with
    | .reg n => if d != 14 + n then IO.println s!"FAIL codeOf reg d={d} n={n}"; bad := bad + 1
    | .shCfg n => if d != 22 + n then IO.println s!"FAIL codeOf shCfg d={d} n={n}"; bad := bad + 1
    | .acc n => if d != 7 + n then IO.println s!"FAIL codeOf acc d={d} n={n}"; bad := bad + 1
    | _ => pure ()
  -- accRange component: every ACC op code is one of the seven ISA codes
  for d in List.range 64 do
    match Machine.dstOp d with
    | .acc n => if n >= 7 then
        IO.println s!"FAIL accRange d={d} n={n}"
        bad := bad + 1
    | _ => pure ()
  IO.println s!"checked {families.length} families x 64 codes (+ nonkeyed + codeOf + accRange); failures = {bad}"
  if bad == 0 then
    IO.println "DstPayloadTable: OK (compiled evaluation)"
    return 0
  else
    return 1

end Check

def main : IO UInt32 := Check.main
