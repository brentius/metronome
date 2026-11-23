# W-P (payload rows and control stickies): `Metronome/ChipCut/Discharge/MovePayloadWire.lean`

Task: the last five `OpenWiring` fields that reduce to the move fabric, the pointer
move and the configuration-write queue — `unitFlagPQ`, `p0Move`, `cwMove`,
`ctrlMemhaz`, `ctrlCwovr` — plus the one new global table they need
(`DstFlagP0CwTable`).

Toolchain: Lean 4.35.0, core libraries only.  Acceptance:

```
lake build Metronome.ChipCut.Discharge.MovePayloadWire      # exit 0, 66 jobs, 39 s
```

with the lakefile's `-DwarningAsError=true` (no warnings).  No `sorry`, no
`admit`, no `native_decide`.  `lake build Metronome.ChipCut` and
`lake build Metronome.ChipCut.Assembly` exit 0; `git diff HEAD -- src` is empty.

Revisions: `MovePayloadWire.lean` SHA-256
`8627C2137F096263D41E74B42E3276065F089B0074BCB263B95E922544008A62` (30420 B).

Evidence: `data/raw/lean_chipcut_wire_movepayload_v4_20261122/` —
`commands.log` (commands, exit codes, wall times), `axioms.lean`/`axioms.txt`,
`statements.lean`/`statements.txt` (the exact statements),
`decode_check_flagp0cw.lean` (compiled check of the new table),
`check_assembly_fields.lean` (the five statements are definitionally the
`Assembly.OpenWiring` fields), `probe*.lean` (scratch probes, not part of the
delivery).

Nothing outside this module, this note and that evidence directory was written.
`src/` and `BOTS/` were not touched.

---

## 1. Delivered (all kernel-checked)

| `OpenWiring` field | theorem | status |
|---|---|---|
| `unitFlagPQ` | **`unitFlagPQ`** | discharged |
| `p0Move` | **`p0Move`** | discharged |
| `cwMove` | **`cwMove`** | discharged |
| `ctrlMemhaz` | **`ctrlMemhaz`** | discharged (one *proved-instance* argument, §5) |
| `ctrlCwovr` | **`ctrlCwovr`** | discharged |

Supporting results in the module:

| item | theorem |
|---|---|
| the new global table | `structure DstFlagP0CwTable` (§2) |
| `FLAGS` payload row | `unitFlagPQ` |
| `P0` payload row | `hPQ_p0`; the `isSome` form `mhcP0Move_isSome` |
| `CW` payload row | `hPQ_cw` (with `cwMoveOf`, `cwSel`) |
| cut `CW` word | `cwWord_code`, `cwWord_data`, `cwWord_we` |
| control stickies | `p0Next_haz`, `pending_req`, `isPD_class`, `srcOpOf_pD_all`, `srcPD_iff`, `pdSlot`, `pdScan`, `readsOf_any`, `ctrlInTrue_memhaz_unfold`, `p0Haz_eq`, `step_coreIssue`, `arbIn_coreIssue`, `accept_not`, `mhcDrains`, `cwNext_coreDrain_val`, `mhcDrains_eq`, `mhcCwo_ovr_eq` |

## 2. The new table: `DstFlagP0CwTable`

`Machine.dstOp` cannot be evaluated in the kernel on the generated table's parsed
names (`String.splitOnAux` is irreducible), and the `P0`/`CW` payload statements
need the *code* of each port.  One global hypothesis, in the
`DstKindTable`/`DstPayloadTable` style:

```lean
structure DstFlagP0CwTable : Prop where
  fset : ∀ d, d < 64 → Machine.dstOp d = .fset → d = 5
  fclr : ∀ d, d < 64 → Machine.dstOp d = .fclr → d = 6
  pAl  : ∀ d, d < 64 → Machine.dstOp d = .pAl  → d = 43
  pAh  : ∀ d, d < 64 → Machine.dstOp d = .pAh  → d = 44
  pW   : ∀ d, d < 64 → Machine.dstOp d = .pW   → d = 45
  pR   : ∀ d, d < 64 → Machine.dstOp d = .pR   → d = 46
  cwAl : ∀ d, d < 64 → Machine.dstOp d = .cwAl → d = 58
  cwAh : ∀ d, d < 64 → Machine.dstOp d = .cwAh → d = 59
  cwD  : ∀ d, d < 64 → Machine.dstOp d = .cwD  → d = 60
  cwGroup : ∀ d, d < 64 → (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 58) = true →
    Machine.dstOp d = .cwAl ∨ Machine.dstOp d = .cwAh ∨ Machine.dstOp d = .cwD
```

`FLAGS`/`P0` also have `DstPayloadTable` group membership (`Fam.flags`/`Fam.p0`),
which supplies the *converse* direction ("in the group ⇒ is a member"); `CW` has
no `Fam` row (that table is not this module's to edit), so its group's code set is
the `cwGroup` row here.

**Compiled check** (`decode_check_flagp0cw.lean`, `lake env lean --run`): all 64
codes against every row, plus "58/59/60 are one group and it is not
`NULL`/`L.SYM`/`T.STOP`": **11 rows, 0 failures, exit 0** (2.5 s).  So the table
is a checkable global hypothesis of the same class as `DstKindTable`.

## 3. `unitFlagPQ` (the `FLAGS` row)

Exactly the `hPQ` that `MoveFabric.unitInputs_flag_low4` carries:

```lean
theorem unitFlagPQ (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    ∀ d, d < 64 →
      (match Machine.dstOp d with | .fset => some true | .fclr => some false | _ => none) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 5) then
        some (BitVec.ofNat 6 d == Metronome.Glue.flagsSetDst) else none)
```

Proof (the `hPQ_stream_adv` pattern): `hT.payload Fam.flags` gives the group test
= `famIn .flags`; in the group the `cases dstOp d` are `.fset`/`.fclr`, the code
rows give `d = 5`/`6`, and `flagsSetDst = 5` evaluates (`decide`) to `true`/`false`.
Outside the group a `.fset`/`.fclr` decode would force `d = 5`/`6` — inside it —
so those cases are contradictory; all others are `rfl`.

## 4. `p0Move` and its `isSome` half

`hPQ_p0` is the same construction for `Fam.p0`, with `Q = Strobes.p0Sel`:

```lean
theorem p0Move … (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    mhcP0Move m pin = Bridge.Mem.mvOf (memIn s pin)
```

is `MoveFabricKeyed.p0_open_move` with the instance supplied, i.e. one
`pickScan_mWs` for group 17 with `Q dst = some (p0Sel dst).toNat`.

`mhcP0Move_isSome` is the same scan with `.isSome` on both sides
(`findSome?_isSome_congr'`): the machine's pointer winner exists iff the cut's
`P0` strobe `(memIn s pin).pWe = (gw s pin 43).we` is up.  It is what `p0haz`
needs, without the full record identity.

## 5. `cwMove`: the `CW` group's single word

Codes 58/59/60 are **one** write group (checked: `dgTable 58 = dgTable 59 =
dgTable 60`), so the cut reads it through one word, `Wire.cwWord = GroupWord.pack
(gw s pin 58)`, and the queue's three strobes are that word:

```lean
CoreQueue.writeData i = bitAt i.cw 14 && (cwCode i.cw == 60)   -- CW.D
CoreQueue.writeLow  i = bitAt i.cw 14 && (cwCode i.cw == 58)   -- CW.AL
CoreQueue.writeHigh i = bitAt i.cw 14 && (cwCode i.cw == 59)   -- CW.AH
```

The three word projections are `cwWord_we`/`cwWord_code`/`cwWord_data`
(`CoreCtl.makeWord_we/_dst/_data`; the `CoreQueue` `bitAt`/`cwCode`/`cwData` and
`Glue`/`CoreCtl` versions have identical bodies, so the `exact` is definitional).

`hPQ_cw` uses the machine's payload `cwMoveOf` (`.cwAl ↦ 0`, `.cwAh ↦ 1`,
`.cwD ↦ 2`) and the cut's `cwSel`, which mirrors `mvOf`'s priority order
`CW.D > CW.AL > CW.AH`:

```lean
def cwSel (dst : BitVec 6) : Option Nat :=
  if dst == 60 then some 2 else if dst == 58 then some 0 else if dst == 59 then some 1 else none
```

Then one `pickScan_mWs` for `Moves.dgTable 58` with `Q = cwSel` and
`findSome?_map_pair` for the record adapter:

```lean
theorem cwMove … (hF : DstFlagP0CwTable) :
    mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin)
```

Two facts make the `hPQ_cw` proof work where the payload table cannot help: the
`cwGroup` row gives "in the group ⇒ one of the three ports" (so the `_` cases of
`cases dstOp d` are contradictory in the group), and the code rows identify each
port with its code, at which point `cwSel` is a closed `decide`.

## 6. `ctrlMemhaz`

The machine's `ctrlInTrue.memhaz` is `pdHaz || p0haz`:

* `pdHaz = !m.p0.rdy && (allMoves).any (srcOp = .pD)` — over **all** moves (the
  pre-resolution list), not the winners;
* `p0haz` is `Machine.p0Next`'s hazard output, `mv.isSome && pending && !served`.

The cut's `Moves.memhazEvent en src haz rdy` is
`haz || (!(readsOf en src srcP0D == 0) && !rdy)`.  Three bridges:

1. **The `P0.D` read scan** (`pdScan`): `MoveBus.en`/`.src` + the source table
   (`srcPD_iff`, from the total `srcOpOf`: code 33 is the only `P0.D`) identify
   each live slot's `isPD (srcOp mv.src)` with the cut's enabled-mask bit
   (`pdSlot`); disabled slots are `false` on both sides
   (`any_filterMap_split`).  `readsOf_any` turns `!(readsOf … == 0)` into the same
   six-slot disjunction.
2. **The pointer hazard** (`p0Haz_eq`): `p0Next_haz` (`rfl`), `pending_req`
   (`Mem.pending` is `reqOf ≠ .none`, via `Inv.reqNeThree`), `mhcP0Move_isSome`
   (the `P0` strobe) and the arbiter fact `(served == 3) = grantP0`.
3. **The `||` shape** is `Bool.or_comm` after commuting the first `&&`.

```lean
theorem ctrlMemhaz … (hsrc : Bridge.Glue.SrcTable) (hT : DstPayloadTable) (hF : DstFlagP0CwTable)
    (hserved : (machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin)) :
    (ctrlInTrue m pin).memhaz =
      Moves.memhazEvent (mvEn s pin) (mvSrc s pin) (Mem.haz s.p0 (memIn s pin)) s.p0.rdy
```

`hserved` is **not a new hypothesis**: `CoreCombWire.p0_open_served` proves it
from `ChipRel`, `Inv` and the stream-mode adapter; the `Glue`-local
`machineServed` is that theorem's `machServed` definitionally.
`check_assembly_fields.lean` contains the check
`(machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin) := p0_open_served …`,
so the assembler can pass the existing theorem.

## 7. `ctrlCwovr`

The cut's event is `writeData && !accept`; `accept = writeData && (!pending ||
drain)`, so (`accept_not`)

```lean
writeData && !accept = writeData && pending && !drain
```

On the machine side `Machine.cwNext`'s `ovr` is `true` only in the `CW.D` branch
of its move match, and there only when the queue holds:

```
ovr = (the move is CW.D) && cw.cwv && !drains
drains = !frozen && cw.cwv && (if qIsCfg then coreDrain else true)
coreDrain = !hh && hostCfg.isNone && !frozen && cw.cwv && qIsCfg && !bwp
```

The bridge is `mhcDrains_eq` (`drains` = `CoreQueue.drain`, with `cw_open_hostCfg`
for the host write, `CwRel` for the queue fields and `arbIn_coreIssue` for the
arbiter's `coreIssue`: `!held && !previousWrite && !hostCfg && (pending && isCfg &&
!frz)`), i.e. the same condition on both sides; the frozen cycle is included and
is vacuous (both are `false`, D50).  `mhcCwo_ovr_eq` then identifies the machine's
overrun with `writeData && pending && !drain`: after `cwMove` (so the machine's
move is `mvOf (cqIn s pin)`), a case analysis on the three queue strobes, the five
configuration atoms (`frz`, `pending`, `isCfg`, `heldValid`, `previousWrite`) and
the offered host write closes every combination (`simp_all` with the `CwRel`
fields, `cw_open_hostCfg`, `arbIn_coreIssue` and `cqIn` unfolded).

```lean
theorem ctrlCwovr … (hF : DstFlagP0CwTable) :
    (ctrlInTrue m pin).cwovr =
      (CoreQueue.writeData (cqIn s pin) && !CoreQueue.accept s.cq (cqIn s pin))
```

## 8. Hypotheses of each theorem

All five take the `pickScan`-class bundle `ChipRel`, `Inv`, the jump-guard table,
`CoreInputBus`, `GrpPacked`, `DstKindTable`; plus

| theorem | extra |
|---|---|
| `unitFlagPQ`, `hPQ_p0`, `hPQ_cw` | `DstPayloadTable` (the first two), `DstFlagP0CwTable` |
| `p0Move`, `mhcP0Move_isSome` | `DstPayloadTable`, `DstFlagP0CwTable` |
| `cwMove` | `DstFlagP0CwTable` |
| `ctrlMemhaz` | `Bridge.Glue.SrcTable`, `DstPayloadTable`, `DstFlagP0CwTable`, `hserved` (= `p0_open_served`) |
| `ctrlCwovr` | `DstFlagP0CwTable` |

`Bridge.Glue.SrcTable` is the pre-existing `ExplicitPremises.srcTable`; it is what
identifies source code 33 as `P0.D` (`srcOp_cut` in `Bridge.Moves` makes the 64-code
kernel check `srcOpOf_pD_all` a `decide`).

## 9. Statement match against `Assembly.OpenWiring`

`check_assembly_fields.lean` imports `Assembly` and this module and proves, by
`rfl`, that each field's proposition and the theorem's proposition are the same
term:

```lean
example … (ho : OpenWiring s m pin) :
    OpenWiring.unitFlagPQ ho = MovePayloadWire.unitFlagPQ hT hF := rfl   -- etc.
```

So the assembler can fill the five fields with these theorems directly (the
`ctrlMemhaz` field also needs the `p0_open_served` instance and the `srcTable`
premise, both already in scope in `premises_of`).  `Assembly.lean` itself was not
edited (not this task's file).

## 10. Findings

1. **The `CW` group is a single write group** (58/59/60), so the cut's one
   `gw s pin 58` word carries the winning port; the machine's `findSome?` scan and
   the cut's word agree because at most one `CW` move can win.  This is why
   `cwMove` needs the `cwGroup` row (the payload table has no `CW` family) but no
   priority reasoning.
2. **`pdHaz` scans the pre-resolution move list**, exactly like the cut's
   `readsOf` mask (which is over `mvEn`), not the winner list.  Reusing the
   `hostInRead` argument (`any_filterMap_split` + `MoveBus.src`) was therefore
   direct.
3. **The pointer hazard is the `p0` bridge's**, not a move-fabric fact: its
   `served` bit is the arbiter grant (`p0_open_served`) and its `pending` bit is
   `Mem.pending` — no pick, no payload.
4. **The overrun machinery is exact on both sides, frozen cycle included.**  The
   machine's `drains` and the cut's `CoreQueue.drain` agree (`mhcDrains_eq`), the
   arbiter's `coreIssue` is the machine's core-drain condition (`arbIn_coreIssue`),
   and the `CW.D`-presence test is `writeData` (`cwMove` + `mvOf`); the overrun
   identity then closes in every combination of its atoms.

## 11. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MovePayloadWire        # exit 0, 39 s
lake env lean -DwarningAsError=true Metronome/ChipCut/Discharge/MovePayloadWire.lean   # exit 0
lake env lean --run ..\..\..\data\raw\lean_chipcut_wire_movepayload_v4_20261122\decode_check_flagp0cw.lean
                                                              # 11 rows, 0 failures, exit 0
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movepayload_v4_20261122\axioms.lean
                                                              # exit 0, no sorryAx
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movepayload_v4_20261122\statements.lean
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movepayload_v4_20261122\check_assembly_fields.lean
lake build Metronome.ChipCut.Assembly                         # exit 0, 73 jobs (regression)
cd ..; git diff HEAD -- src                             # empty
```

`commands.log` records every command with its exit code and wall time.

## 12. Build hygiene

Other agents were editing `LineThread.lean`, `MemHostCfg.lean` and `StreamDbg.lean`
concurrently; their `.olean`s were deleted/rebuilt several times during this
session, so a few `lake env lean` runs failed with "object file … does not exist"
and were retried unchanged until the dependency settled.  No `lake clean` was run,
no `.olean` was deleted, and no file outside this module, this note and the
evidence directory was written.  The module compiles in 39 s from a cold
elaboration (66 jobs).
