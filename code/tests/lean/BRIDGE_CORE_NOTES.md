# Bridge notes: the core cut vs the machine's core (item 4E)

Files: `Metronome/Bridge/Core.lean` (owned by this task).  Evidence:
`data/raw/lean_bridge_core_v4_20261121/` (`axioms.txt`, `commands.log`) for the
transition/output pass and `data/raw/lean_bridge_core_v4_20261121b/` for the move-bus
pass (33 new theorems, gap 1 closed).

Status: `lake build Metronome.Bridge.Core` (with `-DwarningAsError=true`) and
`lake env lean Metronome/Bridge/Core.lean` both exit 0 (Lean 4.35.0, core libs only);
127 theorems (94 + 33 for the packed move bus), no `sorry`, no `native_decide`;
`#print axioms` for every theorem reports only `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`, no native certificate axioms — in particular no `bv_decide`
is used in this file).  `git diff --quiet HEAD -- src` is true (the RTL was not touched).

The cut is `Metronome.Core` (SPEC_V2 §5/§6/§7/§12.3 of `md2_core.v`, proved equal to
the extracted RTL by `core_check.py`); the machine is `Metronome.Machine.Core`
(`coreComb`, `coreNext`).  This file proves the cut's one-cycle transition and its
outputs are the machine's per-core functions, so "RTL = cut = machine" composes.

---

## 1. Abstraction map

The cut is parameterised by a core flag `c : Bool` and takes the thread file, the guard
and source vectors, the line inputs, the program word and the freeze flag as *free
ports*; the machine reads them from its chip state.  The map is therefore **relational
on the inputs**:

| machine | cut |
|---|---|
| `absCore mout s` (a `CoreSt`) | the cut state `s`: `xv, ir, rv, fpc, xt, xl, rr` copied; `mout := mout` |
| `coreNat c` | the cut's `c` (`false ↦ 0`, `true ↦ 1`) |
| `vget ms.cores (coreNat c)` | `absCore i.rdata s` — the program-memory output register **is** the cut's `Input.rdata` |
| `guardVal ms cv p ln (guardOp k)` | bit `k` of `guardVec i.guards i.gLine ln` (all `ln < 4`, all codes `k`) |
| `srcVal ms cv p s.xl.toNat imm (srcOp k)` | `.toNat` of the cut's source byte `slice (srcVec s i) (8k) 8` (all codes `k`) |
| `(vget ms.threads e).ready` | `bitOf i.tReady e` |
| `((vget cv.threads e).core == coreNat c)` | `bitOf (mine c i) e` |
| `(vget cv.threads e).line`, `.w0c`, `.w1c`, `.w0h`, `.w1h` | the cut's 2/6/6/8/8-bit slices of `tLine`, `tW0c`, `tW1c`, `tW0h`, `tW1h` |
| `(vget ms.threads e).pc.toNat` | `.toNat` of the cut's 8-bit `tPc` slice |
| `ms.ctrl.run` | `i.runG` |
| — | `rrOk : s.rr.toNat < 6` (the cut's cursor invariant, `Core.rr_next_lt_six`) |

These are the fields of `structure Rel c ms cv p s i` (one hypothesis bundle).  Values
cross the map as `BitVec.toNat` on the cut side and the machine's `Nat`; the machine's
`bv n x.toNat` is the identity on the cut's fields (`bv_toNat`).  The guard/source
relations are stated for *every* code (past the 62/39-entry tables both sides read
false/0, §7/§6.1/9a.1), so no table-length side condition leaks into the theorems.

## 2. Bridge theorems (grouped, one line each)

**Bit plumbing.** `slice_toNat` (cut `slice` = machine `nbits`), `bitOf_eq_nbit`
(`bitOf` = `nbit`), `bitOf_eq_getLsbD`, `bitOf_and`/`bitOf_or`/`bitOf_allOnes`/
`bitOf_zero`, `bv_toNat`, `ofNat_toNat_self`, `bv2_eq_of_toNat`, `bv3_eq_of_toNat`,
`beq_toNat`, `beq_one_eq_decide`, `bne_zero_toNat`, `toNat_ite`, `match_some_getD`,
`insnField_lt`.

**§5 decode.** `i_jmode_eq`, `i_imm_eq`, `i_cond_eq`, `i_jcond_eq`, `i_g_eq_0/1/2`,
`i_s_eq_0/1/2`, `i_d_eq_0/1/2` (each cut field `.toNat` = `insnField ir FIELD_*`),
`pause_bridge` (cut `i_pause` = the machine's `pause == 1`).

**§7 guards.** `jumpGuardBit_eq_pick` (the cut's flat if-chain is a list walker),
`pick_eq` (bit walker = index walker read through `bitOf`, using that bit 62 of the
masked guard vector is clear: `guardVec_bit62`, `guardVec_bit63`), `pickIdx_eq` (the
chain index is the §7 table entry), `jumpGuardBit_eq`, `cc_bridge` (move guard `C`),
`jc_bridge` (jump guard `JC`).

**§5 dispatch.** `find?_congr`, `pickThread_spec` (the machine's `List.find?` over
`(RR + i) mod 6` **is** the cut's circular scan, 512 kernel-decided cases),
`winOf_ne_zero`, `pickThread_bridge` (`pickThread` = the cut's `dispThread` as an
`Option Nat`), `pick_isSome`, `pick_getD`, `disp_bridge`, `dispE_bridge`,
`dispThread_bridge`, `dispThread_lt`, `pickThread_lt`, `winOf_zero`, `selIdx_zero`,
`winOf_onehot_fin`/`winOf_onehot`, `selSlot_of_onehot`, `selSlot_bridge` (the one-hot
priority chain selects the dispatched thread's slot), `cand_ne_zero_of_disp`.

**§5 thread slots and watchers.** `dLine_bridge` (`XL'` = `LINE[e]`), `dPc_bridge`,
`dW0c_bridge`, `dW1c_bridge`, `dW0h_bridge`, `dW1h_bridge`, `watcher0_bridge`,
`watcher1_bridge` (watcher fires as `W0C/W1C != 0 && G_e[code]`), `dpc_bridge` (`d` =
`Machine.watcherAddr`), `comb_dispAddr`.

**§5 control and fetch.** `taken_bridge` (jmode ± jump guard), `jmp_bridge`,
`pse_bridge`, `load_bridge`, `free_bridge` (§12.3 freeze qualification),
`npc_bridge` (`taken ? imm : FPC`), `fetch_bridge` (`fetch = some fetch_addr` exactly
when `fetch_en`, and the address matches), `fetchEn_bridge` (`jmp || load || disp`).

**§6 move bus.** `moveGuardOk_bridge` (the cut's per-move guard test **is** the
machine's move-enable test); the machine's bus words are encoded by `moveAt` (the
enabled move of index `m`), `mvEnOf` (3-bit enable word), `mvSrcOf`, `mvDstOf`,
`mvDataOf`.  The packed equalities are proved in §2a below.

### 2a. §6 packed move bus (gap 1 closed)

The machine's `moves` is a `List.filterMap` whose `Option.match` compiles to the
generated auxiliary `List.foldl_filterMap.match_1`; `rw`/`simp` will not rewrite under
it.  The route taken avoids that auxiliary instead of fighting it:

* `slotGuard`/`slotSrc`/`slotDst` name the three `(guard, src, dst)` field triples of
  the §5 instruction word; `moveEn` is the machine's per-slot enable test, `moveVal` the
  machine's per-slot `Move` (core/index/src/dst/value/thread/line/armed) written on the
  cut's `IR`, `XL`, `XT`, and `moveCand m = if moveEn m then some (moveVal m) else none`.
* `coreComb_moves`: the machine's list **is** `(List.range 3).filterMap (moveCand …)` on
  an active cycle and `[]` otherwise.  Because `moveCand` *is* the machine's lambda body,
  unfolding `coreComb`, reducing `N_MOVES = 3` and `List.range 3 = [0, 1, 2]` (`range3`),
  rewriting the machine's `CoreSt` to the cut's (`Rel.core`, `absCore`) and flipping the
  `if !xv then` condition (`ite_eq_left`/`ite_eq_right` on `Core.xa`) makes it `rfl` —
  no `filterMap` equation lemma is needed.  (The `Core.xa`/`!xv` flip is done with
  `ite_eq_*` on the condition `(!(Core.xa s i)) = true`, because the elaborated
  `Decidable` instance mentions `absCore` and defeats `rw` on the whole `if`.)
* `moveAt_eq_cand`: on an active cycle the machine's `find?` for slot `m` is that slot's
  candidate (eight cases on `moveEn 0/1/2`).  (`coreComb_moves_of_xa` /
  `coreComb_moves_of_idle` are the two halves of `coreComb_moves`, for consumers.)
* `i_g_slot`/`i_s_slot`/`i_d_slot` identify the cut's `i_g`/`i_s`/`i_d` of slot `m < 3`
  with the machine's `insnField` of the slot's field; `mvEnAt_bridge` then turns
  `moveGuardOk_bridge` into `mvEnAt m = xa && moveEn m`.
* `pack3` packs three `w`-bit fields; `pack3_slice0/1/2` extract field `0/1/2`
  bitwise (`BitVec.eq_of_getLsbD_eq` + the `getLsbD` lemmas, with the `decide` guards
  converted to `if`s by `decide_and_if`/`decide_and_not_decide_and_if`/
  `not_decide_and_if` so `omega` settles the index arithmetic).  `mvSrc_field`,
  `mvDst_field` and `mvData_field` instantiate them at `w = 6` (source, destination) and
  `w = 8` (data); `srcByte_index` rewrites the cut's data byte index
  `BitVec.toNat (8 * BitVec.setWidth 32 (i_s s m))` to `8 * (i_s s m).toNat`.
* `moves_bridge` (the goal): for every slot `m < 3`, (1) the cut's `mv_en` bit `m` is
  `(moveAt cb m).isSome`, (2) the machine's `mvEnOf` bit `m` is the same, (3) any present
  machine entry has `idx = m` and `src`/`dst`/`v` equal the cut's `mv_src`/`mv_dst`
  6-bit slice `m` and `mv_data` byte `m`, (4) under `mv_en m` the machine's
  `mvSrcOf`/`mvDstOf`/`mvDataOf` equal those slices, (5) under `¬mv_en m` they are `0`.
  The value equality uses `srcByte_index` and `Rel.srcs` at the slot's source code, so
  the machine's `srcVal` (global source builder) is the cut's source byte.

**§5/§12.3 next state.** `rrNext_eq`, `xv_bridge`, `rv_bridge`, `fpc_bridge`,
`xt_bridge`, `xl_bridge`, `rr_bridge`, `ir_bridge`, assembled by `step_bridge` (the
seven registers of `coreNext` = the cut's `next`); `frz_hold_bridge` (a frozen cycle
holds the machine's `CoreSt`), `reset_bridge` (the cut's reset branch).

**Outputs.** `out_bridge`: `fetch_en`, `pause_o`, `npc_o`, `disp_o`, `xt_o`, `xl_o`,
`CST.XV`, `CST.RV`, `FPC` equal the machine's `CoreComb`/`CoreSt` readings, plus the
conditional `fetch_addr = fetch` (when fetching) and `disp_e = dispThread` (on
dispatch).  `ir_no_load_diverges` and `dispE_no_disp_witness` are the difference
witnesses (§4).

## 3. Side conditions

| condition | where | why |
|---|---|---|
| `h : Rel c ms cv p s i` | every bridge | the input relation of §1 |
| `hJGTab : ∀ n, jumpGuardIdx.getD n 62 = JG_TABLE.getD n 62` | `jc_bridge`, `taken/jmp/load/fetch/npc/out/step` | the machine's `jumpGuard` table is decoded at definition time from *string names* (`Array.idxOf?`), which the kernel does not reduce; the cut's table is the literal §7 list.  The numeric agreement is exactly the SPEC's §7 table; it is checked outside Lean (`gen_tables.py --check`, `wiki/ISA_TABLES_V2.md`). |
| `hreset : i.resetN = true` | next-state bridges | `coreNext` has no reset input (the chip's `Chip.resetStep` clears the register file); `reset_bridge` covers the cut's reset branch. |
| `hld : load ∨ frz` | `ir_bridge`, `step_bridge` | the `IR` capture difference (§4.1). |
| `hd : disp = true` | `dispE_bridge`, `dLine/dPc/dW0c/W1c/W0h/W1h`, `watcher0/1`, `dpc_bridge`, `dispThread_bridge` | these are the §5 values read *only* on dispatch; outside it the cut shows the first candidate and the machine shows 0 (§4.2). |
| `hrun : i.runG = true` | `pickThread_bridge` | the candidate vector's `RUN_global` mask; `disp_bridge`/`dispE_bridge` case-split it themselves. |
| `hxa : (xv && !frz) = true` | (internal, in the dispatch proofs) | the §5 execute gate `xa`. |
| `hm : m < 3` | `i_g_slot`, `i_s_slot`, `i_d_slot`, `mvEnAt_bridge`, `moveAt_eq_cand`, `mvEn_bit`, `mvEnOf_bit`, `mvSrc_field`, `mvDst_field`, `mvData_field`, `moves_bridge` | the slot index is one of the three §6 move slots; `i_g`/`i_s`/`i_d` past slot 2 decode other instruction bits, and the bus words only carry three slots.  The theorems also case-split `m ∈ {0,1,2}` (`rcases … with rfl \| rfl \| rfl`), so no `interval_cases` (Mathlib) is needed. |

## 4. Disagreements found (with witnesses)

**4.1 `IR` capture without `load` — SPEC §5 vs the RTL/cut.**  §5 writes
`XV' = load; if load: IR' = the word at the memory output`; the machine follows this
literally (`coreNext`: `ir' = if load then mout else ir`).  The cut, like
`src/md2_core.v`, captures `rdata` in *every* unfrozen cycle.  Witness
`ir_no_load_diverges`: with `load = false`, `i.frz = false`, `cs.ir = s.ir` and
`i.rdata ≠ s.ir`, the cut's next `IR` is `i.rdata` and the machine's is `s.ir`.
*Unobservable*: `XV' = load`, so a word captured without `load` is never decoded;
`step_bridge` is stated with `load ∨ frozen` and `irNext_of_load` (cut) is the §5 rule.

**4.2 `disp_e` when nothing dispatches — SPEC §5 vs the cut.**  §5 says `disp_e` is
"the dispatched thread index, 0 when nothing dispatches"; the machine's `dispThread`
is `pick.getD 0` (`= 0` when `pick = none`: `dispThread_zero_of_not_disp`).  The cut's
`dispE` is `selIdx (winOf cand RR)` — with a *busy* core that has a ready thread it is
that (non-zero) candidate.  Witness `dispE_no_disp_witness`: a concrete busy cycle
(`xv = rv = true`, `frz = false`, thread 1 ready and bound to core 0, `run = 1`) gives
`disp_o = false` but `disp_e = 1`.  *Unobservable*: §5 reads `disp_e` only under
`disp_o` (`XT'`, `XL'`, `RR'`), and `dispE_bridge` is stated with `disp = true`.  The
cut's own README ("both sides default to 0") holds only when no thread is ready for
the core.

**4.3 No other disagreement.**  Every other register, flag and output is proved equal
unconditionally (or conditional only on the enable under which §5 reads it), including
the §12.3 freeze qualification of `free`, the `jmp`/`pause` mutual exclusion in
`load`, the circular dispatch scan, the watcher priority, and the fetch-address
priority (`jmp` > `load` > `disp`).

## 5. Gaps

1. **Move-bus packed words — closed (see §2a).**  `mv_en`/`mv_src`/`mv_dst`/`mv_data`
   as *packed* vectors are now proved equal slot by slot (`moves_bridge`), including
   that the machine's list contains exactly the enabled moves (`coreComb_moves`) and
   that each entry's `src`/`dst`/`v` are the cut's packed slices.  The earlier attempts
   did fail on the generated `List.foldl_filterMap.match_1` auxiliary; the fix is to
   *define* the per-slot candidate (`moveCand`) instead of rewriting the machine's
   lambda.  Still out of scope (deliberately): the bus *consumer* (`corectl`, lowest
   `(core, move)` wins), which belongs to the core-queue/`corectl` cut, and the §6
   move *effects* (gap 5).
2. **Program-memory contract.**  `rdata` = the word at the previous fetch address is
   not modelled (the cut takes `rdata` as a free port); `step_bridge` states the fetch
   address the machine presents and leaves the next cycle's `mout` to the caller.
   `mout` is therefore excluded from `step_bridge`'s conclusion (the seven registers
   only; `absCore mout s` records the interface).
3. **Reset.**  `coreNext` has no reset input; `reset_bridge` states the cut's reset
   branch and the machine's chip-level `Chip.resetStep` is the freeze cut's business.
4. **Guard/source builders.**  The `Rel.guards`/`Rel.srcs` relations are hypotheses:
   the chip's global guard/source builders (`project.v`, the line/flag/stream/pointer
   units) are outside the core cut (as `core_check.py` and its README record).  The
   relations are satisfiable because both sides agree past the tables (cut: `lowMask`;
   machine: `guardOp`/`srcOp` defaults read false/0), but the builder-level proof
   itself belongs to the line/units/stream bridges.
5. **Move effects.**  Arming, `LATE`, line/stream/unit writes (§6 execution) are the
   moves/units/line cuts' business; this file bridges the core's *bus*, not the effects.

## 6. Reproduce

```text
cd code/tests/lean
lake build Metronome.Machine Metronome.Core
lake build Metronome.Bridge.Core          # -DwarningAsError=true from lakefile.toml, ~16 s
lake env lean Metronome/Bridge/Core.lean  # ~21 s cold, exit 0
```

`#print axioms` output and the exact commands with exit codes and wall times: the
transition/output pass (`94 theorems`) in
`data/raw/lean_bridge_core_v4_20261121/` (`axioms.txt`, `commands.log`), and the move-bus
pass (`33 theorems`, `axioms_check.lean` is the `#print axioms` driver) in
`data/raw/lean_bridge_core_v4_20261121b/`.
