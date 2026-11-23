# W-K (keyed move picks): `Metronome/ChipCut/Discharge/MoveFabricKeyed.lean`

Task: the **keyed** group picks and the consumer fields that reduce to them.
`MoveFabric.lean` (`pickScan`/`pickScan_mWs`) deliberately excludes `L.SYM`
(keyed by line) and `T.STOP` (keyed by thread), and the three fields that read the
*winners* rather than the valid bits.

Toolchain: Lean 4.35.0, core libraries only.  Acceptance: `lake build
Metronome.ChipCut.Discharge.MoveFabricKeyed` exits 0 with the lakefile's
`-DwarningAsError=true`; no `sorry`, no `admit`, no `native_decide`.

Evidence: `data/raw/lean_chipcut_wire_movefabric_keyed_v4_20261122/` —
`axioms.lean`, `axioms.txt`, `commands.log`.  `axioms.txt` has no `sorryAx` and no
`Lean.trustCompiler`; the only non-core axioms are the `bv_decide` certificates of
`bits6_bit` (6) and of the pre-existing `Moves.hitsMask_bit_*`/`beq_comm_5` (7),
the same kind MoveFabric and Bridge already use.  `lake build Metronome.ChipCut`
exits 0 and `git diff HEAD -- src` is empty.

Nothing outside this file, this note and the evidence directory was written.

---

## 1. What is delivered (all kernel-checked)

| file | field | theorem |
|---|---|---|
| `LineThread` | `WireAgree.late` | **`wireAgree_late`** (verbatim) |
| `LineThread` | `WireAgree.stop` | **`wireAgree_stop`** (verbatim) |
| `MemHostCfg` | `p0_open_move` (the `Premises.p0` hypothesis) | **`p0_open_move`** (verbatim modulo the `Fam.p0` payload instance `hPQ`) |
| `Glue` | `CtrlMoveFabric.hostInRead` | **`ctrlMoveFabric_hostInRead`** (verbatim, with `Bridge.Glue.SrcTable`) |

Statements, verbatim as proved (all over `(s m pin)` with `hrel : ChipRel s m`,
`hinv : Inv s`, `hJGTab : JGTable`, `hbus : ∀ c, CoreInputBus s m pin c (sIr s m c)`,
`hgrp : GrpPacked s pin`, `hkind : Bridge.Moves.DstKindTable`, and the extra
hypothesis named on the line):

```lean
theorem wireAgree_late ... (t : Fin 6) :
    (ltThreadIn m t).late =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).late

theorem wireAgree_stop ... (t : Fin 6) :
    (ltThreadIn m t).stop =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).stop

theorem p0_open_move ... (hPQ : ∀ d, d < 64 → p0MoveOf (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 43) then
        some ((Strobes.p0Sel (BitVec.ofNat 6 d)).toNat) else none)) :
    mhcP0Move m pin = Bridge.Mem.mvOf (memIn s pin)

theorem ctrlMoveFabric_hostInRead ... (hsrc : Bridge.Glue.SrcTable) :
    (ctrlInTrue m pin).hostInRead = (Bridge.Glue.ctrlInOf (glueIn s pin)).hostInRead
```

`hact : runRst s pin = true` is *not* needed by any of the four: none of them
mentions `Machine.step`/`activeStep`, only the combinational input records.

## 2. The keyed-hit machinery

The cut keys the two special groups itself:

* `Wire.slotValid` = `Moves.validBits` bit (enabled ∧ group ≠ `DG_NONE`) — the
  *valid* mask, not the winners;
* `Wire.symWord l` = `Moves.hitOr (Moves.symMask win grp xl l) dst dat` — the
  one-hot per-line `L.SYM` winner mask OR-reduced to a word;
* `Step.threadIn.stop`/`.lateSet` = `anySix` of `slotValid && dst == …`.

The machine's side is `dstOp`-based:

* `ltLineIn.sym`/`.ctlMove` scan the **winners** (`ltWs`) for `.lsym op` with
  `mv.line == l` (resp. `.lCtl k` with `k == l`);
* `ltThreadIn.stop` scans the **winners** for `.stop` with `mv.thread == t`;
* `ltThreadIn.late` scans **`ltAllMoves`** (pre-resolution!) for `.lsym _` with
  `mv.thread == t` and `!mv.armed`.

This file's core definition is the keyed hit

```lean
def keyedHit (b : Moves.Bundle) (G : BitVec 5) (key : Moves.Slot → Bool) (q : Nat) : Bool :=
  Moves.validAt (b.get q) && ((b.get q).group == G) && (key (b.get q))
```

(with `threadKey t sl := sl.thread == t`, `lineKey l sl := sl.line == l`), and the
keyed analogue of `pickScan`'s "first hit wins" step:

> **`winAt_of_keyed_first_stop`**: if slot `k` is the first keyed hit of
> `(DG_T_STOP, t)`, then `Moves.winAt (movBundle s pin) k`.

Proof: `Moves.winAt_true_of_unblocked` with `blocked = false`.  A blocking slot
`j < k` is valid with the same key; `Bridge.Moves.sameKey_iff_slotKey` turns that
into `slotKey (get j) = slotKey (get k)`, and `slotKey_stop` identifies that key as
`some (DG_T_STOP.toNat, t)` (the group is `dgTStop` and `disc` is the thread
`Bridge.Moves.disc_tstop`), so `get j` has group `DG_T_STOP` and thread `t` — i.e.
it is itself a keyed hit, contradicting firstness (`hfirst`).  Nothing in the
argument uses the kind table (the group comes from the *cut's* `dgTable`).

**`any_win_stop_eq`** then says the two scans select the same set:

```lean
(List.range 6).any (fun q => if Moves.winAt (movBundle s pin) q then stopCut … q else false)
  = (List.range 6).any (stopCut …)
```

(`⇐`: take the first valid hit, `range_find?_before` + `winAt_of_keyed_first_stop`;
`⇒`: a winning hit is a valid hit.)

### 2.1 A proof-engineering note: rewriting `match` under `List.any`

`(l.filterMap g).any f` rewrites to `l.any (fun a => match g a with | some b => f b
| none => false)`.  The `match`'s binder is not stable across `rw`/`▸` (Lean does
not match two `match`es up to α-equivalence there), so per-slot lemmas stated in
the `match` form cannot be plugged into this scan directly.  The two scan lemmas
used here avoid the match entirely:

```lean
theorem any_filterMap_split (l) (g) (f) (F)
    (h  : ∀ a ∈ l, ∀ b, g a = some b → f b = F a)
    (h0 : ∀ a ∈ l, g a = none → F a = false) :
    (l.filterMap g).any f = l.any F

theorem any_ite_congr (l) (c F G)
    (h : ∀ a ∈ l, c a = true → F a = G a) :
    l.any (fun a => if c a then F a else false) = l.any (fun a => if c a then G a else false)
```

`any_filterMap_split` is what `late`/`hostInRead` need (the `none` case is a
disabled slot, where the cut predicate is `false`); `any_ite_congr` is what `stop`
needs (the identity is only needed under `winAt`, which forces the slot enabled).

## 3. The destination-decoder classification

`DstKindTable` gives the *class* (`dstClassNat` ∈ {0 NULL, 1 L.SYM, 2 T.STOP,
3 other}) of every code, expressed with the cut's group (`dgNat`).  Two arithmetic
lemmas turn it into the group test itself (`class1_eq`, `class2_eq`), and the two
64-code kernel checks fix the cut's table:

```lean
theorem dgTable_lsym_iff  (v : BitVec 6) : (Moves.dgTable v == Moves.dgLSym)  = (v <= 3 && v != 0)
theorem dgTable_tstop_iff (v : BitVec 6) : (Moves.dgTable v == Moves.dgTStop) = (v == 4)
```

(`v ∈ {1,2,3}` is `L.SYM`/`L.DBIT`/`L.XOR`, `v = 4` is `T.STOP`.)  Composed with
`DstKindTable`:

```lean
theorem isLsym_eq_group (hkind) {d} (hd : d < 64) :
    isLsym (Machine.dstOp d) = (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym)
theorem isLsym_iff_range (hkind) (v : BitVec 6) :
    isLsym (Machine.dstOp v.toNat) = (v <= 3 && v != 0)   -- both directions
theorem isStop_iff_code (hkind) (v : BitVec 6) :
    isStop (Machine.dstOp v.toNat) = (v == 4)
```

`isLsym`/`isStop` are the `dstOp`-constructor tests of the machine side; the two
`_iff` lemmas give the machine's `.lsym`/`.stop` test *and its converse* (needed
for the `stop` direction "a winning `T.STOP` slot is `slotDst == 4`").

## 4. Slot plumbing (new here, or re-derived where MoveFabric keeps it private)

| lemma | content |
|---|---|
| `slotValid_eq` | `slotValid s pin q = enabled && !(group == dgNone)` for `q < 6` (via `bits6_bit`, and `validAt` reading only those two fields) |
| `movBundle_dst_slot` / `movBundle_thread_slot` | the bundle's `dst`/`thread` are `slotDst`/`slotThread` |
| `machMove_thread` / `machMove_dstSlot` | an enabled slot's move carries the cut's thread/destination slices (`MoveBus.thread`/`.dst`) |
| `moveVal_armed`, `slotArmed` | the machine move's `armed` is `(vget m.threads mv.thread).armed`: `machSlot`'s `some mv` is the core's `moveVal`, whose `armed` reads the executing thread's `ARMED` |
| `threads_armed` | `(vget m.threads u).armed = (threadAt s u).armed` (`ChipRel.threads`) |
| `thread_beq_slot` | `(mv.thread == t) = (slotThread … == ofNat 3 t)` (needs `BitVec.ofNat_toNat`/`setWidth_eq`) |
| `mAllMoves_ltAllMoves`, `mhcWs_eq_mWs` | `ltAllMoves m = mAllMoves m pin`, `mhcWs m pin = mWs m pin` (both are defeq `rfl`s modulo `Vector.ofFn` indexing) |
| `findSome?_map_pair` | `(findSome? (… (a, g x))).map (fun p => c p.1 p.2) = findSome? (… (c a (g x)))` — the record-vs-pair adapter |
| `glue_bitAt_eq` | `Glue.bitAt = Machine.Util.bit` (`rfl`-equal definitions through `CoreCtl.bitAt`) |

## 5. Per field: method and residual hypotheses

### 5.1 `WireAgree.late` — **discharged**, no keyed pick needed

The machine scans `ltAllMoves` (the *pre-resolution* list), so no winners and no
payload are involved.  Slot by slot (`lateSlot`):

* enabled slot: `mv.thread`/`mv.dst` are the cut's slices; `dstOp (slotDst).toNat`
  is `.lsym` iff `slotDst ∈ {1,2,3}` (`isLsym_iff_range`); `slotValid` is true
  there (`slotValid_of_range`); and `mv.armed` is the executing thread's `ARMED`,
  which is `t`'s when `mv.thread == t` (`threads_armed`);
* disabled slot: the cut predicate is `false` (`lateCut_false`) and the machine
  contributes `false` (the placeholder's `dst = 0` has no group), so the
  `any_filterMap_split` split closes it.

The residual hypotheses are exactly the `pickScan_mWs` bundle; nothing about
`L.SYM`'s *key* is needed (the earlier pessimism in `WIRE_MOVEFABRIC_NOTES` §11
was unnecessary: `late` never reads a winner).

### 5.2 `WireAgree.stop` — **discharged** (the keyed pick)

Machine: winners ∧ `.stop` ∧ `thread == t`.  Cut: `slotValid && dst == 4 &&
thread == t`.  Per live slot the two are the same word (`stopSlot`: thread slice,
`isStop_iff_code`, and `slotValid_of_stop`), and for the *scan* the winner/valid
difference is exactly `any_win_stop_eq` (§2).  Note `stopCut … q =
keyedHit … dgTStop (threadKey …) q` (`stopCut_eq_keyedHit`), which is how the
keyed-hit lemma is applied.

### 5.3 `MemHostCfg.p0_open_move` — **discharged** modulo the `Fam.p0` payload instance

One `pickScan_mWs` instance: `P := p0MoveOf`, `Q dst := some (Strobes.p0Sel
dst).toNat`, `T := id`, `G := dgTable 43` (the `P0` group, codes 43..46), then
`findSome?_map_pair` re-associates the `(Nat × Nat)` pairs into `Machine.P0Move`
records, and the cut side unfolds to `Bridge.Mem.mvOf (memIn s pin)` (`pWe`/`pSel`/
`pData` are literally `(gw s pin 43).we`/`p0Sel …dst`/`….data`).

The one carried hypothesis `hPQ` is the **`Fam.p0` instance of `DstPayloadTable`**,
in the same shape as `ctrlMoveFabric_hostOut`/`unitInputs_flag_low4` carry theirs:
it is `p0MoveOf (dstOp d)` against the group test, i.e. "codes 43..46 decode to
`P0.AL/AH/W/R` in that order and nothing else decodes to them".  It is *not* a
RTL/machine disagreement: it is the parsed-name opacity of `Machine.dstOp`
(`WIRE_MOVEFABRIC_NOTES` §6), which `DstPayloadTable` is designed to absorb.  To
remove it one needs the per-family instance

```lean
hPQ_of_payload (famIn .p0) p0MoveOf (fun dst => some (p0Sel dst).toNat) (famG .p0)
  (hT .p0) (…cases on dstOp d for the four codes…) (…none case…)
```

whose two `ht`/`hf` sub-goals need `dstOp d = .pAl → d = 43` (etc.); that is a
64-code statement about `dstOp` which the kernel cannot decide for the parsed
names, so it belongs with the rest of the string-table work (compiled check), not
here.

### 5.4 `Glue.CtrlMoveFabric.hostInRead` — **discharged** (with `SrcTable`)

Machine: `(allMoves).any (fun mv => isHostIn (srcOp mv.src))`.  Cut:
`Glue.anyRead (rdHin s pin)` = `any6 (Moves.readsOf (mvEn) (mvSrc) srcHostIn)`.

* per live slot (`hostInSlot`): `mv.src` is the cut's `mvSrc` slice (`MoveBus.src`,
  added by W1), and `srcOp d = .hostIn` iff `d = 38`; the latter is the **source
  table**: `Bridge.Glue.SrcTable` states `Machine.srcOp i = srcOpOf i` for the
  total computable `srcOpOf`, so "38 is the only `HOST.IN` code" is a 64-code
  kernel `decide` (`srcOpOf_hostIn_all`, `srcHostIn_iff`);
* the cut's mask bit `q` is `bitAt (mvEn) q && (mvSrc slice == 38)`
  (`bits6_bit` + `Moves.readAt`), and on a live slot `bitAt (mvEn) q = true`
  (`MoveBus.en`);
* disabled slots: `bitAt (mvEn) q = false`, so both sides are `false`
  (`any_filterMap_split`'s `none` case).

`hsrc : Bridge.Glue.SrcTable` is a pre-existing global table hypothesis
(`Bridge/Glue.lean:425`), of the same class as `DstKindTable`.

## 6. Findings

1. **`late` is not a keyed pick.**  The machine scans the *pre-resolution* list, so
   the cut's `slotValid` mask is exactly the machine's enabled-plus-grouped slots;
   the `L.SYM` key is irrelevant (only the *destination class* is).  No winner,
   no payload, no `slotWin` subtlety.
2. **`stop` is a keyed pick, and the two readings scan different sets** (winners
   vs valid bits).  They agree because the first keyed hit wins: `any_win_stop_eq`
   is the complete proof of the reviewer's §5.5 argument in
   `DISCHARGE_LINETHREAD_NOTES.md`.
3. **The machine's `armed` is per executing thread.**  `machSlot`'s enabled move
   is the core's `moveVal`, whose `armed` field is `(vget m.threads mv.thread)`,
   so the cut's `!ARMED_t` and the machine's `!mv.armed` agree only under
   `mv.thread == t` — which is the other conjunct of the same test.
4. **`hostInRead` needs the source table, not a pick.**  There is no group pick
   here: the cut's `rdHin` is the enabled-source mask (`Moves.readsOf`), and the
   only table fact is "code 38 is `HOST.IN`", which `SrcTable`'s total `srcOpOf`
   makes kernel-decidable.

## 7. Open: `WireAgree.sym`/`ctl` (projected) and the stream move picks

These are **not** in this file yet.  The statements, the pieces that now exist and
the exact remaining work:

### 7.1 `sym`/`ctl` — projected forms (data-width, `WIRE_MOVEFABRIC_NOTES` §5)

```lean
(ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
  (Bridge.Line.absIn (lineIn s pin l)).sym.map (fun w => (w.op, w.v))
(ltLineIn m l).ctlMove.map (fun v => v % 8) =
  (Bridge.Line.absIn (lineIn s pin l)).ctlMove.map (fun v => v)
```

(the cut truncates: `Wire.lineIn.symD = truncate 4` of the picked word,
`ctlD = ofNat 3`; the machine keeps the whole data byte, and `absSymOp` recodes
the 2-bit `lineSop`).

The steps, with what is available:

1. *One-hotness of the per-line winner mask*: `atMostOne (Moves.symMask
   (Moves.winBits …) (mvGrp …) (mvXl …) l)` — **not** a `bv_decide` fact (unlike
   `Strobes.hitsMask_atMostOne`, the mask is a filter of the *winners*): it is
   `Moves.winners_unique` over the 15 slot pairs, i.e. a 15-case `bv_decide`-free
   argument on `winAt`.  This is the missing `symMask` one-hot lemma.
2. *HitOr under a one-hot mask*: if bit `k` is set, `Moves.hitOr mask dst dat =
   makeWord true (slice dst (6k) 6) (slice dat (8k) 8)`; the cut's `symWord` then
   gives `bit 14 = we`, `symOp` from the destination code (`Strobes.lineSop`) and
   `symD` from the data nibble.
3. *The line-keyed first hit wins*: as `winAt_of_keyed_first_stop`, but with
   `key := lineKey (ofNat 2 l)` and using `Bridge.Moves.disc_lsym` in place of
   `disc_tstop`.  `sameKey` then also keys by the line (`!(group == dgLSym) ||
   line == line`).
4. *The machine's winner scan*: `(ltWs).findSome?` with the `.lsym`/`.lCtl`
   pattern is the word of the *unique* winner of the key, so it is the same slot
   as the mask's single bit (step 1 + step 3).
5. *The recode*: `absSymOp (lineSop d) = op` for the three codes
   `d ∈ {1,2,3}` (`Strobes.lineSop` = 0/1/2 for `L.SYM`/`L.DBIT`/`L.XOR`,
   `Bridge.Line.absSymOp` maps back), and `truncate 4`'s value is `% 16`
   (`truncate_four_toNat` in MoveFabric).

So the recipe is complete and all inputs (`symMask`, `hitOr`, `lineSop`,
`absSymOp`, `MoveFabric.truncate_four_toNat`, `Moves.winners_unique`,
`Bridge.Moves.disc_lsym`) exist; what is missing is the one-hot lemma of step 1
and its two consumers.

### 7.2 `StreamWire.input`, the move-pick part

The machine's fields (`StreamDbg.machStreamIn m k`) against
`Bridge.StreamB.absIn` at `streamIn s pin k`:

* **`adv`** (verbatim, both `Bool`): `Strobes.opg` of the `Sk` group at code
  `47+k` (`Strobes.opg_eq_pick` turns the cut's strobe into the picked word's
  `we && dst == 47+k`), so this is one `pickScan_mWs` instance for `Fam.stream k`
  with `Q dst := some (dst == 47+k)`.
* **`ctlMove`** needs a **projection**: the cut's is `some (ctlVal i)` with
  `ctlVal ∈ {0,1,2,3}` (`Bridge.Stream.ctlVal`), the machine's `some mv.v` is the
  whole byte; `ctlVal i = if rewind then 1 else 0 + if flush then 2 else 0`
  (`Bridge.Stream.absIn`), so the provable form is `… ctlMove.map (· % 4) = …`.
  The move term is the same `Fam.stream k` word (`Strobes.streamCtlOf_opg`).
* **`rx`** needs a **projection and is a source-level check**: the machine's `rx`
  is `some mv.v` of the `Sk.RX k` winner, the cut's is `some (if rxBit then 1 else
  0)` where `rxBit = bit 0 of the picked group word` — and the picked word *is*
  that winner's word (the RTL reads `w[0]` of the whole-group `PICKG(DG_SK)`,
  `src/project.v:471`), so the two agree on bit 0 only:
  `… rx.map (· % 2) = …`.  (`% 2` of a byte is its bit 0.)

The remaining `input` fields (`served`, `landNow`, `ramOut`, `cev`/`record`,
`apply`/`late`) are other bridges (arbiter, landing, capture), not the move
fabric, exactly as `DISCHARGE_STREAMDBG_NOTES` §4 lists them.

## 8. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MoveFabricKeyed     # exit 0, 5 s
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movefabric_keyed_v4_20261122\axioms.lean
                                                          # exit 0, 2.6 s, no sorryAx
lake build Metronome.ChipCut                              # exit 0 (regression)
cd ..
git diff HEAD -- src                                      # empty
```

`commands.log` records commands, exit codes and wall times.

## 10. Round 2: the per-line `L.SYM` mask and the stream/CTL pick findings

Round 2 added to the module (verified, in build order after §12):

| item | theorem | statement |
|---|---|---|
| one-hot | **`symMask_atMostOne (en grp xl xt) (line)`** | `Moves.atMostOne (Moves.symMask (Moves.winBits en grp xl xt) grp xl line) = true` |
| one-hot | `symMask_pair`, `sameKey_lsym`, `winBits_bit` | the pairwise form: two set bits are two winners of the key `(DG_L_SYM, line)` |
| `hitOr` | **`hitOr_onehot (k) (hk) (dst) (dat)`** | `Moves.hitOr (1 <<< k) dst dat = CoreCtl.makeWord true (CoreCtl.slice dst (6k) 6) (CoreCtl.slice dat (8k) 8)` |
| width | `byte_mod_two`, `byte_mod_four`, `ctlMoveBits` | `d.toNat % 2 = bit 0`, `d.toNat % 4 = ctlMoveBits d` |
| witness | `stream_rx_data_witness`, `stream_ctl_absent_witness` | the exact `rx`/`ctlMove` field forms are false |

`symMask_atMostOne` is **not** a `bv_decide` fact (unlike `Strobes.hitsMask_atMostOne`):
the mask is a *filter of the winners*, so it is `Moves.winners_unique` over the 15
slot pairs, with `sameKey_lsym` (group `DG_L_SYM` + the same line ⇒ `sameKey`) as
the key step.  `hitOr_onehot` is the 6-case extraction (the `if`s are discharged by
`decide` on the concrete shifted mask).  Both are generic in `(en, grp, xl, xt)`.

### 10.1 Findings that block the exact field forms

**`Sk.CTL` (`ctlMove`) is not a width projection.**  The cut's
`absIn.ctlMove = some (ctlVal i)` with
`ctlVal i = (if i.rewind then 1 else 0) + (if i.flush then 2 else 0)`, and the cut's
`streamIn` builds `rewind/flush = (mctl && dataBit) || (hctl && hostBit)`
(`Strobes.streamCtlOf`): the value **folds the host `SRT.CTL` bits in**, and is
`some (hostBits)` even when there is no `Sk.CTL` move.  The machine's field is the
*winning move's* bus byte, `none` when there is no move.  So

```lean
(machStreamIn m k).ctlMove.map (· % 4) = (absInOf k …).ctlMove       -- FALSE
```

with two independent witnesses (`stream_ctl_absent_witness` is the "no move" gap:
`none ≠ some 0`; the host bits are the second gap).  The provable statement is the
move part only:

```lean
(machStreamIn m k).ctlMove.map (fun v => v % 4) =
  (if (gw s pin (ofNat 6 (51 + k.val))).we && ((gw …).dst == ofNat 6 (51 + k.val))
   then some (ctlMoveBits (gw s pin (ofNat 6 (51 + k.val))).data) else none)
```

and the field form follows **under two extra hypotheses** (`no host SRT.CTL byte
write for `k`, and the `Sk.CTL` strobe high), where `ctlVal` collapses to
`ctlMoveBits` (`byte_mod_four`).

**`Sk.RX` (`rx`) is the low bit of the *group* winner.**  `Wire.lineIn`'s sibling
`Wire.streamIn` sets `rxBit := bit (gw (47+k)).data 0` — the low bit of the whole
`DG_SK` group pick (RTL `w[0]`, `src/project.v:471`) — while the machine's field is
the RX winner's full byte.  Since the group has one winner, that byte *is* the RX
move's data when the RX strobe fires, so the field is a genuine **2-way truncation**
(`% 2`), witnessed by `stream_rx_data_witness` (`2 ≠ bit 0`).

**`Sk.ADV` (`adv`) is exact *modulo a code table*.**  Both sides are `Bool`, but the
machine tests the *decoded* port (`dstOp = .sAdv k`) while the cut tests the picked
word's *destination code* (`dst == 47+k`).  Unlike `L.SYM`/`T.STOP` (`DstKindTable`)
and the payload families (`DstPayloadTable`), no table fact relates the stream
codes 47+k/49+k/51+k to their decoded ops — and `Machine.dstOp` is opaque on those
parsed names (`dstOp 47` does not reduce).  So `adv` reduces to one `pickScan_mWs`
instance for `Fam.stream k` **plus** a `codeOf`-style row

```lean
sAdv : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sAdv n → d = 47 + n   -- and sRx/sCtl/lCtl
```

(the missing rows of `DstPayloadTable.codeOf`, which covers only `reg`/`shCfg`/`acc`;
checked by compiled evaluation like the rest of the table).  With it the group's
code test and the machine's decode agree, and `pickScan_mWs` with
`Q dst := some (dst == ofNat 6 (47+k))` gives `adv = we && (dst == 47+k)`, i.e. the
cut's `strobe`.  The `lCtl` row is not needed for `WireAgree.ctl`: group 20+k holds
exactly one code, so group membership alone pins `dst == 53+k` (a 64-code `decide`
on `dgTable`).

### 10.2 The projected `sym` (open, recipe complete)

```lean
(ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
  (Bridge.Line.absIn (lineIn s pin l)).sym.map (fun w => (w.op, w.v))
```

Remaining steps, all with the pieces now in place: (i) `symMask_atMostOne` gives
the mask is `0` or `1 <<< k` — to *find* `k` use `pickWord_we_exists` **on the
winners' mask? no**: use `hitsMask_onehot_first`-style on the *keyed* mask via
`hitsMask` of the line's `symMask`… more simply: if `symWe` (= bit 14 of `symWord`)
is true then the mask is non-zero, so `(range 6).find? (bitAt mask)` gives `k`, and
`atMostOne` upgrades the mask to `1 <<< k`; (ii) `hitOr_onehot` then gives the
cut's `{we, dst, data}` word; (iii) the machine's winner scan
(`scan_rewrite` + the per-slot equivalence `.lsym op ↔ (group == dgLSym) ∧ line`)
picks the same slot — this needs the **`lsym` row of the code table**
(`dstOp d = .lsym n → n = d`) to identify the op with the code
`absSymOp (lineSop code)`; (iv) `truncate_four_toNat` (`MoveFabric`) gives `% 16`.

`WireAgree.ctl` (`% 8`, `Lk.CTL` is non-keyed) is the same shape as
`unitInputs_shCfg_low5`: one `pickScan_mWs` instance for `Fam.lCtl l` with
`Q := fun _ => some ()`, the computable `we → dst == 53+l`, and
`truncate`-to-`% 8` on the data byte.

## 11. Reproduce (round 2)

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MoveFabricKeyed      # exit 0, 4.6 s
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movefabric_keyed_v4_20261122\axioms.lean
                                                            # exit 0, 1.8 s, 13 theorems, no sorryAx
```

Round-2 `commands.log` records a 118 s full re-elaboration after another agent
cleared the build directory (`lake clean` by someone else, not this task; the
module and all its dependencies were rebuilt and the module still builds).

## 12. Build hygiene note

`MoveFabric.lean` is owned by another agent and was edited concurrently (the
`MoveBus.src` field this file's `hostInRead` uses landed in the same session).
The first builds re-elaborated it (20 s, 41 s); after it settled the module builds
in 3–10 s and no file outside this module was touched.  No `lake clean` was run
and no `.olean` was deleted.

One incident worth recording for reproducibility: two intermediate PowerShell
`Get-Content`/`Set-Content` round trips re-encoded this file and broke several
Unicode tokens (the `∀`/`→`/`∨` glyphs); the file was rewritten from scratch with
UTF-8 and then built clean.  The delivered file is plain UTF-8 (no BOM) and the
build is warning-free.

## 13. Round 3: the stream/line-control code table

Added to the module (verified): the global table hypothesis

`lean
structure DstStreamLineTable : Prop where
  sAdv : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sAdv n → d = 47 + n
  sRx  : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sRx n → d = 49 + n
  sCtl : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sCtl n → d = 51 + n
  lCtl : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .lCtl n → d = 53 + n
  lsym : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .lsym n → n = d
`

(the codeOf rows DstPayloadTable does not cover), the injectivity helpers
ofNat6_beq_of_ne/ofNat6_beq_self, and the two **forward** rows

`lean
theorem dstOp_sAdv (hT : DstPayloadTable) (hC : DstStreamLineTable) (hd : 47 + n < 64) :
    Machine.dstOp (47 + n) = .sAdv n
theorem dstOp_sRx (hT) (hC) (hn : n < 2) (hd : 49 + n < 64) :
    Machine.dstOp (49 + n) = .sRx n
`

which are the *converse* direction needed by pickScan_mWs's hPQ (they combine
hT.payload with the table rows; the sRx/sCtl rows also need 
 < 2, since
dgTable (49+n) = famG (.stream n) only for 
 ∈ {0,1}).

**Compiled check.** decode_check_streamline.lean (evidence dir) evaluates
Machine.dstOp on all 64 codes and tests every row: 64 codes, failures = 0,
ad codes = [], exit 0, 2.3 s (lake env lean --run).  So DstStreamLineTable
is a checkable global hypothesis, same class as DstKindTable/DstPayloadTable.

**Remaining for the round-3 fields** (all machinery now in place, no unknown
ingredients): hPQ for Fam.stream k / Fam.lCtl k (the four cases on
dstOp d: the two/three stream rows give d = code, dstOp_sAdv/dstOp_sRx
give the converse; lCtl's group has a single code so dgTable alone pins it),
then one pickScan_mWs each with Q dst := some (dst == ofNat 6 (47+k))
(resp. 49+k, 53+k) gives dv/x/ctl as we && (dst == code); % 2/% 8
on the value components via yte_mod_two/yte_mod_four-style lemmas; the
stream-control combined form uses Bridge.StreamB.ctlVal/Strobes.streamCtlOf
and the frozen host-flush rule of Machine.streamNext; sym additionally uses
symMask_atMostOne + hitOr_onehot + the lsym row.  The 118 s rebuild earlier
in the session shows the iteration cost is dominated by dependency re-elaboration,
not these proofs.
