# Bridge: `Metronome.Line`/`Metronome.Moves` against `Machine.Line`/`Machine.Moves`

Item 4C of the Lean verification plan.  The two independent Lean transcriptions
of `wiki/SPEC_V2.md` are (1) the per-cut specifications that the RTL is proved
equal to (`code/tests/lean/Metronome/Line.lean`, `Moves.lean`), and (2) the
whole-chip executable machine (`code/tests/lean/Metronome/Machine/**`).  This
note records what is bridged, under which abstraction map and side conditions,
and what is still open.

Files:

| Path | Role |
|---|---|
| `code/tests/lean/Metronome/Bridge/Line.lean` | line bridge (new) |
| `code/tests/lean/Metronome/Bridge/Moves.lean` | move/sticky/mailbox/fold/pick bridge (new) |
| `data/raw/lean_bridge_line_moves_v4_20261121/` | `commands.log`, `axioms.txt`, `line.log`, `moves.log` |
| `data/raw/lean_bridge_line_v4_20261121b/` | `commands.log`, `axioms.txt` (item 4G, line bridge extension) |
| `data/raw/lean_bridge_moves_v4_20261121b/` | 4H: `commands.log`, `axioms.txt`, `Axioms.lean`, `decode_check.log`, `decode_check.lean` |
| `data/raw/lean_bridge_line_v4_20261121c/` | `commands.log`, `axioms.txt`, `line.log`, `build_cached.log`, `build_final.log` (item 4I: `FIRST`/`FIRED`/`SNAP` field equations, `step_bridge'`) |

Commands (from `code/tests/lean`, Lean 4.35.0, core libs):

```text
lake build Metronome.Machine Metronome.Line Metronome.Moves      # exit 0
lake env lean Metronome/Bridge/Line.lean                         # exit 0
lake env lean Metronome/Bridge/Moves.lean                        # exit 0
lake build Metronome.Bridge.Moves                                # exit 0 (4H)
lake env lean --run ../../data/raw/lean_bridge_moves_v4_20261121b/decode_check.lean  # exit 0
lake build Metronome.Bridge.Line                                 # exit 0, warnings as errors (4I)
```

No `sorry`, no `sorryAx`, no `native_decide`.  `#print axioms` for every
theorem is in `axioms.txt`; the only native certificates are the three
`bv_decide` axioms of `and_one_bne_zero_{16,3,32}` (documented trust of the
existing suite, used to prove `x &&& 1 != 0 = x[0]`).

---

## 1. Line component

### Abstraction map (all explicit, in `Bridge/Line.lean`)

| cut | machine | definition |
|---|---|---|
| `Line.Config` (32-byte window view) | `Machine.LineCfg` | `absCfg`: every field as `BitVec.toNat` (16-bit phases, bytes, 2-bit tap/`SNAP`, selectors), Bools unchanged |
| `Line.State` (15 fields) | `Machine.LineSt` | `absSt`: field for field |
| `Line.Input` | `Machine.LineIn` + `frozen` | `absIn`: `sym := some ⟨absSymOp symOp, symD.toNat⟩` when `symWe`, `ctlMove := some ctlD.toNat`, `hPhase := some (0,hD)` / `some (1,hD)`, `hCtl := some hD`, `hTapmissClr := hStatWe && hD[0]`; `frozen := i.frz` |
| `lvl`, `rise`, `fall` (free vectors) | `Machine.PinView` | `PinAbs lvl prev` + `PinAbs.view`; `PinAgree` is the side condition |
| `symOp : BitVec 2` (0 SYM, 1 DBIT, 2 XOR) | machine `L.SYM=1, L.DBIT=2, L.XOR=3` | `absSymOp`: `0↦1, 1↦2, 2↦3, 3↦3` (the cut's `3` is the RTL `case` default, XOR) |

Bit plumbing lemmas: `bitAt_eq_nbit`, `sel16_eq_nbit`, `sel3_eq_nbit`,
`sel32_eq_nbit`, `slice_toNat`, `pack3_toNat`, `pack4_toNat`, `pack3_bit`,
`packBits3_as_pack3`, `or3_as_pack3`, `nbit_two_mul_add`, `bv_le_decide`,
`bv_ge_decide`, `slice16_self`, `concat17_toNat`, `esel_eq`.

### Bridged combinational fields (proved, symbolic state/input)

| field | theorem | what it says |
|---|---|---|
| `edge` | `edge_bridge` | `§3.2` polarity-selected boundary edge = machine `edgeSel`, freeze-gated in both |
| `e0` | `e0_bridge` | `§3.3` edge-sourced tap 0 |
| `inwin` | `inwin_bridge` | `WLO..WHI` window, including the `WHI < WLO` wrap form |
| `start` | `start_bridge` | `edge && ARM && !RUN` |
| `accept` | `accept_bridge` | `edge && RUN && REN && (!WEN \|\| inwin)` |
| `sum17` / `nxw` / `nx` | `sum17_toNat`, `nxw_toNat`, `nx_toNat`, `nx_machine` | 17-bit `PH + INC`, wrapped difference and truncated `nx`, as `Nat` |
| `over` | `over_eq_decide`, `over_bridge` | `N >= MOD`, as the machine's `Nat` comparison |
| `crossing` | `crossing_eq`, `decide_bv16_lt/le` | the tap-crossing conditional, with `BitVec` comparisons transferred to `Nat` |
| `holdOk` (`HTAP`/`T0SRC`) | `holdOk_bridge`, `holdTap_bridge`, `tapEnabled_{zero,one,two}`, `isPhaseTap_*`, `tapT_*` | `HEN`/`HTAP != 3`/`tapEnabled`/`isPhaseTap` = the cut's `holdTok`, all four `HTAP` values |
| `hold` | `hold_bridge` (side condition `frz = false`) | machine `hold` = cut `hold` off a frozen cycle |
| `adv` / `wrap` / `beat` | `adv_bridge`, `wrap_bridge`, `beat_bridge` | unconditional: `adv` is freeze-gated in both; `beat` cases on `FOLLOW` |
| `cross[0..2]` | `cross0_bridge`, `cross1_bridge`, `cross2_bridge` | `T0SRC` edge-sourced tap 0, and the two phase crossings |
| `next[0..2]` | `next0_bridge`, `next1_bridge`, `next2_bridge` | next-beat tap events (`over` and `Tk <= nx`) |
| `cur[0..2]`, `tap[0..2]` | `cur0..2_bridge`, `tap0..2_bridge`, `bitAt_eq_bit` | current-beat events and the `FIRED`-gated tap outputs |
| `en[0..2]` | `lineComb_en0..2`, `tapEnabled_*` | enabled taps |
| `miss` (`TAPMISS` event) | `missBits_expand`, `missBits_disj`, `miss_test` (used by `tapmiss_test`) | `en &&& ~FIRED &&& ~cur &&& missOk != 0` = the machine's `any` over `k = 0..2`; `D28` start exception |
| `TAPMISS` register | `tapmiss_test` | sticky miss and `STAT[0]` clear |
| `wNext` (capture) | `capture_test`, `setBit_pack4_0..3`, `pack4_bit0..3`, `w_test`, `w_inline_st` | `setBit` chain = `pack4` of the four capture bits |
| `sn` / `rem` | `sn_bridge`, `rem_bridge`, `rem_test`, `nbit_two_mul_add` | snapshot register and `REM = in_sym[1]` |
| `snap` dot product | `snap_bridge`, `sel_pack3` | `SNAP == 3 ? BEAT : TAP[SNAP]` |
| `stagedNext` | `stagedNext_test`, `stagedNext_inline`, `dbit_test`, `absSymOp{0,1,2}` | `SYM`/`DBIT`/`XOR`, including the `sym_op = 3` default |
| `committedNext` | `committed_test`, `beat_st`, `start_st`, `stagedNext_st2`, `starting` | beat/start commit |
| `run`/`arm`/`ren` | `run_test`, `arm_test`, `ren_test` | move and host `CTL` priority |
| `sc`/`sp` | `sc_bridge`, `sp_bridge` | `FOLLOW` and `accept`/`beat`/`wrap` |
| `held` | `held_bridge` | `frozen ? HELD : hold` |
| `ph` / `phF` | `phC_bridge`, `phF_bridge`, `ph_bridge`, `setByte0_16`, `setByte1_16` | generator phase, then host `PHASE` byte via `setByte` |
| `first` | `first_bridge`, `prod_snd_ite`, `starting_st` | `starting \|\| (FIRST && !BEAT)` |
| `fired` | `fired_bridge`, `prod_fst_ite`, `startBits`/`nextBits`/`curBits` bridges, `or3_bits` | `startBits` / `nextBits` / `FIRED \|\| curBits` |
| `seg` | `seg_test`, `seg_out` | `popcount(FIRED)` (eight `FIRED` values by `decide`) |
| `in_sym` | `inSym_toNat`, `in_sym_out`, `cap_toNat`, `cap_out` | `IN = {LUT1[{REM,SN}], LUT0[{REM,SN}]}` |
| `PINA`/`PINB` | `pina_test`/`pinb_test`, `pina_out`/`pinb_out` | `§12.1` live pins |

`step_bridge` assembles all register equations into
`absSt (Line.step s i) = Machine.lineNext ...` with three field equations as
explicit hypotheses (`hfirst`, `hfired`, `hsnap`).  `step_bridge'` is the same
statement with those three hypotheses discharged by `first_bridge`,
`fired_bridge` and `snap_bridge`, so only `hcfg`, `PinAgree` and `hreset`
remain.

### Side conditions (line)

1. `hcfg : lc = absCfg i.cfg` — the machine's decoded line configuration is the
   cut's window view.  (`Machine.Config.line` decodes the byte image; the cut's
   byte-slice wiring is `line_check.py`'s, so the decode itself is not re-proved
   here.)
2. `PinAgree a i` — the cut's free `lvl`/`rise`/`fall` vectors are the machine's
   §2 `PIN`, `RISE`, `FALL` vectors.
3. `iM = absIn i` — the machine's line inputs are `absIn` of the cut's (used as
   the definition of `absIn`, not as a separate hypothesis).
4. `hreset : i.resetN = true` — `step_bridge` models the register transition,
   not the synchronous reset branch (reset is chip-level in `Machine`); the cut's
   `reset_step` covers the other branch.
5. `frz = false` for `hold_bridge` only.  The state bridge does **not** need it:
   `held_bridge` and `adv_bridge` are unconditional.
6. `hfirst`, `hfired`, `hsnap` — the three field equations are now theorems
   (`first_bridge`, `fired_bridge`, `snap_bridge`).  They remain explicit
   hypotheses of `step_bridge` for compatibility; `step_bridge'` discharges them.

### Disagreements / readings (witnessed)

* **Frozen `hold` signal.**  The cut's `hold` includes `RUN && !frz`
  (`runa`), the machine's `LineComb.hold` does not.  Witnesses:
  `hold_frozen_cut` (the cut's hold is `false` whenever `frz = true`) and
  `hold_frozen_machine` (a concrete `lineComb` with `frz = true` whose `hold`
  is `true`).  This is a difference in the combinational signal, not in
  behaviour: `HELD'` and `adv` are freeze-gated in both models (`lineNext`
  selects `st.held` when frozen; `adv` starts with `!frozen`), so
  `held_bridge`/`adv_bridge` hold unconditionally.  SPEC clause: §12.3.
  AMBIGUITIES.md does not list it (the machine's comment says "in a frozen
  cycle `edge = e0 = 0` and `adv = 0`", not that `hold` is low).
* **`sym_op = 3`.**  The cut reads the unused code as XOR (RTL `case` default);
  the machine has no `op = 0` and reads `op = 3` as XOR.  Witnesses:
  `absSymOp_three` (`absSymOp 3 = 3`) and `staged_op3_is_xor` (the cut's
  `stagedNext` with `symOp = 3` is `STAGED ^^^ symD`).  SPEC clause: §3.6.
  AMBIGUITIES.md does not list it; the cut's own README records it as item 1 of
  "SPEC ambiguities and RTL/SPEC differences".
* **`DBIT` staging.**  SPEC §3.6 writes `{STAGED[3:1], bus[0]}`; the machine
  implements it as `(STAGED/2)*2 + bus[0]` (replace bit 0), the cut as
  `slice 1 3 STAGED ++ slice 0 1 bus`.  These are the same value
  (`dbit_test`), so no disagreement.
* **Frozen follower `SC`.**  Both models clear `SC` in a frozen `FOLLOW = 1`
  cycle (cut `scNext`, machine `lineNext`'s `(false, …)` branch); no
  disagreement.  SPEC §3.3 / §12.3.

### Gaps (line)

None.  The last three register equations, previously the hypotheses of
`step_bridge`, are proved theorems (item 4I); `step_bridge'` has no field
hypotheses.

* **`snap` dot product** (`snap_bridge`).  After `absCfg_snap` the goal has the
  `Nat` index `i.cfg.snap.toNat` on both sides; `bv2_cases` splits the 2-bit
  `SNAP` into its four literals, so the machine's `tap[k]!` becomes a literal
  index (matched by `tap0/1/2_bridge`) and the cut's `sel k (pack3 …)` is read
  by `sel_pack3`.  `SNAP = 3` gives `BEAT` (`beat_bridge`) on both sides.  The
  earlier blocker (a `BitVec` index kept inside the `Nat` accessor) disappears
  once the split is on the value, not on the `toNat` equation.
* **`FIRST` register** (`first_bridge`).  `prod_snd_ite` distributes the tuple
  projection over the `starting`/`beat` `ite`s; `starting_st` (the `.run` field
  equation of `run_test` read through `absSt`) names the machine's start
  condition, and the four `ctlWe`/`hCtlWe` cases with `FOLLOW` reduce both sides
  to the same Boolean.
* **`FIRED` register** (`fired_bridge`).  Same projection lemma (`prod_fst_ite`)
  and `starting_st`; the `startBits` list is `range_three_map` followed by
  `packBits3_as_pack3`, with `tapEnabled_*`, `isPhaseTap_*`, `tapT_*`,
  `phF_bridge` and `bv_le_decide` per bit; the no-boundary branch is
  `or3_bits`/`next0..2_bridge`/`cur0..2_bridge`.  The last case split is on
  `T0SRC` (the D28 exception) and on the two host `PHASE` write-enable bits, so
  the `setByte` form of `ph'` matches `phF` by `setByte0_16`/`setByte1_16`.

Everything else is proved: `step_bridge'` holds with only `hreset`, `hcfg` and
`PinAgree`, and all outputs (`BEAT`, `TAPk`, `in_sym`, `cap`, `seg`, `PINA`,
`PINB`) are bridged by `beat_bridge`, `tap*_bridge`, `in_sym_out`, `cap_out`,
`seg_out`, `pina_out`, `pinb_out`.


---

## 2. Moves component

### Abstraction map

* Destination code → write group: the cut's `dgTable : BitVec 6 → BitVec 5`
  against `Machine.Tables.writeGroups`/`dstNames`; `groupOfName` /
  `groupCodeOf` are the list (kernel-reducible) form of the machine's
  `Util.dstGroup` array lookup.
* Move key: the cut's `sameKey` (group; plus `line` for `L.SYM`, `thread` for
  `T.STOP`) against the machine's `moveGroup` (`(group, line)` for `.lsym`,
  `(group, thread)` for `.stop`, `(group, 0)` otherwise).
* Sticky inputs: `(state, event, clear)` with `event` the cycle's
  `conflict`/`memhaz` event and `clear` the host `CTRL.STICKY` bit 0/1.

### Theorems

| theorem | statement |
|---|---|
| `wgList_eq` | the bridge's `wgList` is exactly `Machine.Tables.writeGroups.toList` (with each member array as a list), by `decide` |
| `dgTable_matches_all` | for all 64 destination codes: `(dgTable d).toNat` is the group index of the `d`-th `dstNames` entry in the machine's table (`31` = `DG_NONE`); `decide` |
| `dgTable_matches` | per-code form of the above (`d < 64`) |
| `dgTable_null_31` | `NULL` (code 0) has code 31 (`DG_NONE`) |
| `dstGroup_getElem?` | the machine's `Util.dstGroup[d]?` is the list search over `dstNames.toList[d]?` |
| `dstGroup_getElem?_wg` | that search is the bridge's `groupOfName` |
| `ctrl_conflict_bridge` | `Machine.ctrlNext`'s `conflict` bit is `Moves.stickyNext state ⟨true, event, clear⟩` |
| `ctrl_memhaz_bridge` | the same for `memhaz` with `STICKY` bit 1 |
| `ctrl_conflict_frozen` | `frozen` does not change the `conflict` equation (both values give the same next bit) |
| `ctrl_conflict_clear_only`, `ctrl_conflict_event` | a clear-only cycle clears; an event sets regardless of a simultaneous clear |
| `ctrl_inv_bridge` | `INV'` is the cut's `invNext state true hostWrite readHin` |
| `ctrl_inv_host_write_wins`, `ctrl_inv_read_clears` | host `HOSTIN` write beats a same-cycle `HOST.IN` read; a read alone clears |
| `memhaz_event_bridge` | the machine's `!RDY && <some P0.D read>` event is the cut's `memhazEventOf` |
| `memhaz_event_of_read` | a `P0.D` read while `!RDY` raises the event |

### Side conditions (moves)

1. `hsticky`/`hclear`: the host `STICKY` byte and its bit are the cut's
   `clear` input (the host-map cut owns the address decode).
2. `MoveAgree` (per cycle, field level): the machine move's `dst` is the slot's
   destination code, its `line`/`thread` are the slot's (`Nat` values), disabled
   slots are padded with `NULL` (`dst = 0`), and the cut's slot `group` is
   `dgTable` of the slot's `dst` (the RTL equality of `moves_check.py`).  From
   this, `moveTable_of_agree` *proves* the per-cycle `MoveTable` key equality;
   the old per-cycle hypothesis about the machine's decoder output is gone.
3. `DstKindTable` (one global hypothesis, not per cycle): the `L.SYM`/`T.STOP`/
   `NULL` kind of the 64 destination codes.  The group table is kernel-proved
   (`dstGroup_all`); the kind table cannot be kernel-decoded because
   `String.splitOnAux` is `@[irreducible]` in Lean 4.35.0 core, so it is checked
   by compiled evaluation (`decode_check.lean`, exit 0).
4. `SrcTable` is discharged: `srcOp_cut` proves in the kernel that the machine's
   `srcOp 33`/`srcOp 38` are `P0.D`/`HOST.IN` (the names are in the fixed list, so
   `dstOfName`/`srcOfName` reduce).

### Disagreements (moves)

None found.  `T.STOP` is keyed per thread in both models; `L.SYM` is keyed per
executing line in both; `NULL` has no group in both (`dgTable 0 = 31`,
`moveGroup .null = none`).  `CONFLICT`/`MEMHAZ` update while frozen in both
(`ctrl_conflict_frozen`), which matches the cut's sticky step and the SPEC §12.3
list (it does not stop the sticky bits).

### Gaps (moves)

* `MoveAgree` is the abstraction map, taken as a hypothesis: the machine move's
  `dst`, `line` and `thread` fields are the slot's, disabled slots are padded
  with `NULL`, and the cut's `group` field is `dgTable` of its `dst` (the RTL
  equality is `moves_check.py`'s).
* `DstKindTable` is checked by compiled evaluation, not by the kernel (see the
  4H section below).
* The group word is proved for non-keyed real groups.  The keyed groups
  (`L.SYM`, `T.STOP`) are covered at the winner level by
  `resolveMoves_winners`, but not as a single packed word (the RTL itself writes
  those per line/thread through `symMask`/the thread ports).

---

## 3. 4H: `resolveMoves` against `winAt`, `conflictEv` and `pick`

Evidence: `data/raw/lean_bridge_moves_v4_20261121b/` (`commands.log`,
`axioms.txt`, `decode_check.log`, `Axioms.lean`, `decode_check.lean`).

### The fold invariant

`Machine.resolveMoves` folds the six moves in `(core, move index)` order with
state `(winners, seen keys, conflict)`; the bridge writes the same step as
`Bridge.Moves.stepOn` and the fold as `resolveAux`
(`resolveMoves_eq` is definitional).  The invariant `fold_prefix` is stated over
the prefix of the first `n ≤ 6` slots: for every start state
`(ws0, seen0, cf0)` and every `n ≤ 6`, after folding `(six m).take n`

1. the winner list is `ws0 ++ winsFrom seen0 m n`;
2. `seen` contains exactly the keys `keySeen seen0 (keyAt m) n`;
3. the conflict flag is `cf0 || dupFrom seen0 (keyAt m) n`,

with `keyAt m j = moveGroup (m j)`,
`keySeen seen0 g n k = seen0.contains k || (List.range n).any (fun j => g j == some k)`,
`winFrom` the negation of `keySeen` at a `some` key, `dupFrom` the "an earlier
slot has this key" scan, and `winsFrom` the `filterMap` of the prefix's winning
slots.  The proof is an induction on `n` (`fold_prefix`), using the three step
lemmas `stepOn_none`/`stepOn_contains`/`stepOn_new` and the list lemmas
`keySeen_succ`/`winsFrom_succ`.

Instantiated at six (`six_take_six`) with the key translation
`keyAt_eq : keyAt m k = slotKeyOf (b.get k)` from `MoveTable`:

* `resolveMoves_winners`: the machine's winner list equals
  `(List.range 6).filterMap (fun k => if winAt b k then some (m k) else none)` —
  the same winner set, in slot order (the cut's `winners_unique` gives at most
  one winner per key).
* `resolveMoves_conflict`: the machine's conflict flag equals `conflictEv b`,
  via `dupFrom_six` and the cut's `conflictEv_eq_pairSameKey`.

### The group word

* `winnerGroup_eq_singleton`: for a real non-keyed group `G`
  (`G ≠ dgNone`, `G ≠ dgLSym`, `G ≠ dgTStop`), if slot `k` is the lowest valid
  slot of `G`, the machine's winners of `G` are exactly `[m k]`.
* `pickWord_eq_word`: the cut's `pickWord (hitsMask en grp G) dst dat` is
  `{1, dst_k, data_k}` for that slot (from the cut's `pick_first_0..5`).
* `resolveMoves_pick`: both together for `b = bundleOf en grp dst dat xl xt`;
  with `(m k).dst = dst_k.toNat` and `(m k).v = data_k.toNat` from the
  abstraction map, the machine's only group-`G` write and the cut's pick are the
  same `{dst, data}` word.

### `MoveTable` and `SrcTable` discharged (or reduced to one global check)

* `dstGroup_all` (kernel `decide`): the machine's `dstGroup` entry is the cut's
  `dgTable` for all 64 codes; `dstGroup_of_code` is the per-code form.
* `dstClass_fixed` (kernel `decide`): the 21 fixed destination names decode to
  the kinds the cut's table implies.  The other 40 names need
  `Metronome.Machine.Util.parsePort`, hence `String.splitOn`, whose worker
  `String.splitOnAux` is `@[irreducible]` in Lean 4.35.0 core; the kernel has no
  value for them.  Their kind is the single global hypothesis `DstKindTable`
  (one statement for all 64 codes, not per cycle), checked by compiled
  evaluation in `decode_check.lean`
  (`lake env lean --run .../decode_check.lean`, exit 0, output in
  `decode_check.log`).
* `moveTable_of_agree`: the per-cycle `MoveTable` follows from the field-level
  `MoveAgree` and the code table; the old per-cycle decoder hypothesis is gone.
* `resolveAux_pad`: padding the six-move list with a `NULL` (`dst = 0`) move does
  not change the fold, so "the machine's list of enabled moves" and "all six with
  disabled slots padded `NULL`" agree.
* `srcOp_cut`: the machine's `srcOp 33`/`srcOp 38` are `P0.D`/`HOST.IN`
  (kernel, fixed names); `SrcTable` is discharged.

### Disagreements

None.  The only reading choice is SPEC_V2 §6's "two or more enabled moves target
one group": read per key (group plus the line for `L.SYM` and the thread for
`T.STOP`, as the parentheticals say) rather than per group code.
`lsym_two_lines_witness` (kernel `decide`) fixes it: two enabled `L.SYM` moves on
lines 0 and 1 both win and raise no conflict, although both have group code 0.
`Metronome/Machine/AMBIGUITIES.md` has no move-resolution entry.  The agreeing
fragment under the explicit side condition `G ∉ {L.SYM, T.STOP}` is
`resolveMoves_pick`.

