# Discharge: the `lines` and `threads` premises (item 4Q, premise discharge 2/5)

File: `lean/Metronome/ChipCut/Discharge/LineThread.lean`
(namespace `Metronome.ChipCut.Discharge`).
Toolchain: Lean 4.35.0, core libraries only, `lake build` with
`-DwarningAsError=true` (Lean's own linters on; `linter.unusedVariables` and
`linter.deprecated` disabled as allowed).
Acceptance: `lake build Metronome.ChipCut.Discharge.LineThread` exits 0.

Evidence: `data/raw/lean_chipcut_discharge_linethread_v4_20261121/`
(`axioms.lean`, `axioms.txt`, `commands.log`).  No `sorry`/`admit`, no
`native_decide` introduced here; the only non-core axioms reached by the two
main theorems are the pre-existing `bv_decide` certificates of
`Bridge/Line.lean`.

---

## 1. What the two theorems say

```lean
theorem premise_lines (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hcfg : forall l : Fin 4,
      (Machine.cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l.val))
    (hwire : WireAgree s m pin) :
    forall l : Fin 4,
      (Machine.step m pin).lines[l] = Bridge.Line.absSt (lineAt (activeStep s pin) l.val)

theorem premise_threads (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwire : WireAgree s m pin) :
    forall t : Fin 6,
      (Machine.step m pin).threads[t] =
        Bridge.Thread.absState (threadAt (activeStep s pin) t.val)
```

The conclusions are verbatim the `lines` and `threads` fields of
`Metronome.ChipCut.Premises`.  `premise_lines` carries two extra hypotheses
(`hcfg`, the `hcfg` argument of `Bridge.Line.step_bridge'`; `hwire`, the input
record wiring), `premise_threads` one.  They are not forced: the shapes of the
two conclusions are exactly the `Premises` fields, and everything the two
bridge theorems need *besides* those hypotheses is proved here.

Nothing outside this file was edited.  The file was re-checked after the
orchestrator's packer reversal (`pack8s`/`packBools`/`packNs`, item 0 now in the
low bits): this file never reasons about those packers, only about
`ltThreadIn`'s use of `mvEn`/`mvGrp`/`mvDst`/`mvDat`/`mvXl`/`mvXt` as opaque
vectors, so no lemma here depended on the old order.  The `ChipRel` core-clause
weakening (`xv → ir = ir'`) does not touch these fields either.

## 2. The projection functions (the missing piece of §3.4.1)

`CHIPCUT_NOTES.md` §3.4.1 says the premise bodies stayed post-step comparisons
because "the machine's per-cycle input records ... `Machine.runStep` builds
inline — no projection functions exist to state 'the cut input is the machine's
input'".  This file adds exactly those:

| definition | content |
|---|---|
| `ltCbs` | the two `Machine.coreComb` bundles of the cycle |
| `ltLcs` | the four `Machine.lineComb` bundles |
| `ltAllMoves` | the machine's enabled moves, `cbs[0].moves ++ cbs[1].moves` |
| `ltWs` | `(Machine.resolveMoves (ltAllMoves m)).1`, the winners |
| `ltHw` | the host write of the cycle (`hostNext`'s written word; it reads only `m.host`, so `served` is irrelevant — `hostNext_hw` is `rfl`) |
| `ltLineIn` | the four `Machine.LineIn` records (`sym`, `ctlMove`, `hPhase`, `hCtl`, `hTapmissClr`) |
| `ltThreadIn` | the six `Machine.ThreadIn` records (`trig`, `beat`, `late`, `stop`, `dispatch`, `pause`, `hPC`, `hStat`) |

with the definitional projections

* `runStep_lines_vec`, `runStep_threads_vec`: `(Machine.runStep m pin).1.lines`
  and `.threads` are `Vector.ofFn` of those records (both `rfl`);
* `runStep_lines`, `runStep_threads`: the pointwise forms;
* `machine_step_runStep`: on an active cycle `Machine.step m pin` *is*
  `(runStep m pin).1`, from `ChipRel.rstQ` and `runRst`.

## 3. Proved here (no extra hypothesis)

* `sync_eq`: `(absChip s).sync = m.sync` from `ChipRel.sync` (byte split of the
  16-bit synchroniser words);
* `dbg_eq`: `(absChip s).dbg = m.dbg` from `ChipRel.dbg` (11 fields);
* `lcs_eq` / `lcs_get`: `lcsOf s = ltLcs m`.  The cut's `lcsOf` reads
  `(cfgView s.cont.cfg).lines[l]!` while the machine reads `(cfgView m.cfg).lines[l]`;
  the `!`-to-entry conversion is `getElem!_eq_get` (`getElem!_pos` does not apply
  to `Vector`'s `Nat` get element instance), and `ChipRel.cfg` and
  `ChipRel.lines` close it;
* `trigEvent_eq`: `trigEvent` of `m` and of `absChip s` agree (it reads only
  `units.f`, `units.fp`, `ctrl.inv`, `ctrl.invp`, the thread's `ready`/`running`,
  the configuration view, the pin view and the line combinations — all fixed by
  `ChipRel`);
* `trig_eq`: `(ltThreadIn m t).trig` is `Metronome.Thread.trig` of the cut's
  `threadIn`.  This is the `Bridge.Thread.trig_refines` wiring (`ev`/`db` at
  `!FRZ` with `trigEvent`), done directly: the cut's `threadIn.ev` is *defined*
  as `Machine.trigEvent (absChip s) ...`, so `trigEvent_eq` plus
  `ChipRel.dbg.frz`/`ctrl.db`/`threads.en` close it in four `Bool` cases;
* `lineIn_ext`, `threadIn_ext`: extensionality for the two machine records
  (they carry no generated `ext` theorem, like `Machine.ThreadSt`);
* `lineIn_eq`, `threadIn_eq`: the record equalities, from the bundle below and
  `trig_eq`;
* `lineComb_pin_congr`, `lineNext_pin_congr`: `Machine.lineComb`/`lineNext` read
  the pin view only through `lvl`/`prev`, so a pin view from the cut's
  synchronisers can replace the machine's;
* `activeStep_line`, `activeStep_thread`: the cut's next line/thread is its own
  `Line.step`/`Thread.step` on `lineIn`/`threadIn`;
* `pinAbs`: the canonical `Bridge.Line.PinAbs` from the cut's synchroniser and
  replay registers;
* `no_accept_of_disp`: the **first** `Bridge.Thread.step_eq` side condition
  `¬(accept ∧ disp)`, from the machine's dispatch rule.  The machine side is
  `corePick`/`coreComb_disp`/`coreComb_dispThread` (the `pick` local of
  `Machine.coreComb`), `corePick_ready` (`pick = some e` forces the
  `if free && run` branch and then `pickThread = some e`, whose candidate
  predicate includes `READY`) and `ltThreadIn_dispatch_ready`; the cut side is
  `Metronome.Thread.accept = trig && !(READY || RUNNING)` together with
  `ChipRel.threads`.  So this side condition is **not** a hypothesis.

## 4. The residual hypotheses, and why each is one

### 4.1 `hcfg` (configuration decode round trip)

`Bridge.Line.step_bridge'` takes `hcfg : lc = Bridge.Line.absCfg i.cfg`.  With
`lc = (cfgView m.cfg).lines[l]` and `i.cfg = lineCfgOf lc` (Wire.lean) this is
the decode-encode round trip of the line configuration.

`CHIPCUT_NOTES.md` §3.2 and §4 list the configuration decode inverse
(`lineCfgOf`, `outCfgOf`) among the **trusted chip-top decode interfaces** and
call it a premise, not a wiring bug; this file therefore carries it, and the
notes here record how it would be proved: every `Machine.LineCfg` field comes
from `Config.line` as either `cfgLE c a 2` (`< 65536`, hence
`(BitVec.ofNat 16 x).toNat = x`), `cfgLE c a 4` (`< 2^32`), or
`nbits byte lsb w` (`< 2^w`), and `lineCfgOf` repacks exactly those fields into
the byte layout (`edge = pin 3:0, pol 5:4, WEN 6, FOLLOW 7`, etc.).  The 24 field
goals are then `Nat` `%`/`/` facts (`(x + 16 * k) % 16 = x` for `x < 16`, the
analogous `>>> 4`, `>>> 6`, `>>> 7` forms, `(x + 16 * (p + 4 * k)) / 16 % 4 = p`,
...), which the core `Nat.add_mul_mod_self_right`/`Nat.add_mul_div_right` and
`Nat.mod_eq_of_lt` lemmas close directly.

### 4.2 `WireAgree` (the input records)

`WireAgree` is a structure of per-field equalities of the two records (each
field type is literally the corresponding field of
`Bridge.Line.absIn (lineIn s pin l)` / `Bridge.Thread.absInput ...`).  The
split is exactly §3.4.1's "remaining wiring/side condition" column for items 2
and 3:

| field | bridge that produces it |
|---|---|
| `pinAgree`, `pinLvl`, `pinPrev` | §2 `PinAgree` of `Bridge.Line.step_bridge'`; from `Bridge.Debug.level_toNat`/`previous_toNat`/`rise_bit`/`fall_bit`, the byte split `pinVec (ui ++ uio) = (ui >>> 3) ++ uio` (`bv_decide`), and the `Nat` arithmetic of `Machine.Util.protoPins` (`b.toNat + (a.toNat >>> 3) * 256`) |
| `sym`, `ctl` | `Bridge.Moves.resolveMoves_pick`/`winnerGroup_eq_singleton` (`L.CTL` is non-keyed; `L.SYM` is keyed by line) on top of `Bridge.Core.moves_bridge` and the `DstKindTable`-class destination-name hypotheses |
| `hPhase`, `hCtl`, `hTapmissClr`, `hPC`, `hStat` | `Bridge.Host.hw_bridge` (the write the machine issues this cycle) plus the host-map byte decode |
| `beat` | `Bridge.Line.beat_bridge` under `pinAgree` and `hcfg` |
| `late`, `stop`, `dispatch`, `pause` | the `T.STOP`/late move picks and the cores' combinational `disp`/`dispE`/`pse`/`npc` against `Core.out` (`Bridge.Core`, item 4) |
| `pauseDisp` | the second `Bridge.Thread.step_eq` side condition (below) |

(side condition 1, `¬(accept ∧ disp)`, is *proved* here: `no_accept_of_disp`.)

### 4.3 The remaining `Bridge.Thread.step_eq` side condition

`accDisp : ¬(accept ∧ disp)` is proved (`no_accept_of_disp`): `Machine.pickThread`
only returns a thread bound to the core **and `READY`** (`List.find?_some` on its
candidate predicate, `pickThread_some`), a dispatch of `t` forces the
`if free && run` branch and `pickThread = some t` (`corePick`, `corePick_ready`,
`ltThreadIn_dispatch_ready`), and `Metronome.Thread.accept = trig && !(READY ||
RUNNING)`, so an accepted trigger and a dispatch are mutually exclusive for the
same thread.  `ChipRel.threads` carries the readiness to the cut.

`pauseDisp : ¬(pause ∧ disp)` is the one remaining side condition.  A pause
targets the executing thread `XT` of a core; a dispatch targets a `READY` thread.
The two coincide only if the executing thread is `READY`, which never happens on
a reachable cycle (dispatch sets `RUNNING` and clears `READY`; a trigger on a
busy thread is an overrun and does not set `READY`).  This is the reviewer's
argument, and it needs the machine invariant

```
forall c < 2, (vget m.threads (vget m.cores c).xt.toNat).ready = false
```

which is **not** part of `ChipCut.Inv` (four fields: `req ≠ 3`, `rr < 6`,
`HostPins.Agrees`, the stale-landing condition).  That missing invariant is the
only reason `pauseDisp` is a hypothesis here.

## 5. The reviewer's `slotWin` / `allMoves` point (reconciled)

The reviewer noted that the cut's late detection tested `slotWin` while
`Machine/Chip.lean:78` scans `allMoves`.  Checked against the current sources:

* `Step.lean`'s `threadIn.lateSet` now reads `slotValid s pin q` — `mv_en` and
  `mv_valid`, **not** `slotWin` — i.e. the 4R fix is in place.  `Wire.lean`'s
  `slotValid` is `Moves.validBits` (enabled and group =/= `DG_NONE`).
* The machine's `late` (`Machine/Chip.lean:78`) scans `allMoves` with
  `!mv.armed` and `dstOp mv.dst = .lsym _`.  `allMoves` is *pre-resolution*, so
  the two sides scan the same set: a slot with destination `NULL` is not valid
  on the cut side (`group = dgNone`) and does not decode as `.lsym` on the
  machine side (`dstOp 0 = .null`), and every other enabled slot is in
  `allMoves`.  Both read the thread's `ARMED` through `mv.thread = xt` and
  `slotThread = mvXt` restricted to 3 bits, which `ChipCut.Wire.mvXt` builds
  from the same core registers.
* The machine's `stop` scans the **winner** list `ws`, while the cut's `stop`
  reads `slotValid`.  The two agree because `T.STOP` is keyed per thread: if a
  valid `T.STOP` slot for thread `t` exists, the winner of key
  `(dgTStop, t)` is the *lowest* such slot, so it is also a valid `T.STOP` for
  `t`; hence `any (valid stop for t)` iff `any (winning stop for t)`.  This is
  the `Bridge.Moves.winnerGroup_eq_singleton`/`sameKey` argument.

No cut/machine disagreement exists in these fields.

## 6. Naming and coexistence with the other discharge files

All helpers of this file carry the `lt` prefix (`ltCbs`, `ltLcs`, `ltAllMoves`,
`ltWs`, `ltHw`, `ltLineIn`, `ltThreadIn`, `ltThreadIn_dispatch_ready`) because
the four sibling files of `Metronome.ChipCut.Discharge` are in the same Lean
namespace and three of them independently defined machine-side helpers with the
obvious names (`machCbs`, `machWs`, `machHw`, ...).  With the `lt` prefix there
is no declaration-name overlap with `CoreUnits.lean`, `Glue.lean`,
`MemHostCfg.lean` or `StreamDbg.lean` (checked by declaration-name scan).  Since
the helper definitions are the same idea, the orchestrator may want to
consolidate them into one shared module later; nothing in this file depends on
the other four.

## 7. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut                      # exit 0
lake build Metronome.ChipCut.Discharge.LineThread # exit 0, ~10-15 s from a removed olean
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_linethread_v4_20261121\axioms.lean  # exit 0
```

`axioms.txt` shows `propext`, `Classical.choice`, `Quot.sound` (and, for
`premise_lines`, four pre-existing `Bridge.Line` `bv_decide` certificates); no
`sorryAx`.
