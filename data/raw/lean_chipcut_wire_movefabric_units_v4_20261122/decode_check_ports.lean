import Metronome.ChipCut.Discharge.MoveFabricUnits

/-!
# Compiled check of `DstPortTable`

`DstPortTable` (`Metronome/ChipCut/Discharge/MoveFabricUnits.lean` §3) says, at
the ten destination codes the `CNTk`/`LFk`/`SHk` fields read, that the machine's
decoder carries the port the cut's code names:

    18+k → SHk.LD      20+k → SHk.SH
    24+k → CNTk.LO     27+k → CNTk.HI     30+k → CNTk.DEC
    33+k → LFk.ST      35+4k → LFk.B0     36+4k → LFk.B1
    37+4k → LFk.B2     38+4k → LFk.B3

`DstPayloadTable` fixes only the *group* of a code (group `8+k` holds both
`SHk.LD` and `SHk.SH`), so the port map is a separate hypothesis.  As with
`DstKindTable`/`DstPayloadTable`, the kernel cannot reduce
`Machine.Util.dstOfName` on the generated table's parsed names
(`String.splitOnAux` is `@[irreducible]` in Lean 4.35.0 core); this script checks
the table by *compiled* evaluation of the machine's own `dstOp` against the cut's
`dgTable`, and also prints each family's code list (the input of `cnt_codes` /
`lf_codes` / `sh_codes`).

Run from `code/tests/lean`:

    lake env lean --run ../../../data/raw/lean_chipcut_wire_movefabric_units_v4_20261122/decode_check_ports.lean

Exit code 0 means every code decodes to the stated port.
-/

open Metronome

namespace Check

open Metronome.ChipCut.Discharge.MoveFabric

/-- `DstOp` has no `BEq`, so compare the `Repr` strings. -/
def same (o : Machine.DstOp) (p : Machine.DstOp) : Bool := reprStr o == reprStr p

def expect (name : String) (code : Nat) (p : Machine.DstOp) : IO Nat := do
  if same (Machine.dstOp code) p then
    pure 0
  else
    IO.println s!"FAIL {name}: dstOp {code} = {repr (Machine.dstOp code)}, expected {repr p}"
    pure 1

/-- The codes of each of the three families, from the cut's `dgTable`. -/
def groupCodes (f : Fam) : List Nat :=
  (List.range 64).filter (fun d => Moves.dgTable (BitVec.ofNat 6 d) == famG f)

def main : IO UInt32 := do
  let mut bad : Nat := 0
  for k in [0, 1] do
    bad := bad + (← expect "shLd" (18 + k) (.shLd k))
    bad := bad + (← expect "shSh" (20 + k) (.shSh k))
    bad := bad + (← expect "lfSt" (33 + k) (.lfSt k))
    bad := bad + (← expect "lfB0" (35 + 4 * k) (.lfB k 0))
    bad := bad + (← expect "lfB1" (36 + 4 * k) (.lfB k 1))
    bad := bad + (← expect "lfB2" (37 + 4 * k) (.lfB k 2))
    bad := bad + (← expect "lfB3" (38 + 4 * k) (.lfB k 3))
  for k in [0, 1, 2] do
    bad := bad + (← expect "cntLo" (24 + k) (.cntLo k))
    bad := bad + (← expect "cntHi" (27 + k) (.cntHi k))
    bad := bad + (← expect "cntDec" (30 + k) (.cntDec k))
  for f in [Fam.sh 0, Fam.sh 1, Fam.cnt 0, Fam.cnt 1, Fam.cnt 2, Fam.lf 0, Fam.lf 1] do
    IO.println s!"fam {repr f}: group {(famG f).toNat}, codes {groupCodes f}"
  IO.println s!"checked 20 (family, code) ports; failures = {bad}"
  if bad == 0 then
    IO.println "DstPortTable: OK (compiled evaluation)"
    return 0
  else
    return 1

end Check

def main : IO UInt32 := Check.main
