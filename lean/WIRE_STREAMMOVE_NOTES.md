# W-S: `Metronome/ChipCut/Discharge/StreamMoveWire.lean`

Task: the two stream move-pick fields of `StreamWire.input` — the `Sk.RX` low
bit (`rx`) and the combined stream control (`ctlMove` + `hCtl` vs
`rewind`/`flush`/`clrStarved`).

Toolchain: Lean 4.35.0, core libraries only.  Acceptance: `lake build
Metronome.ChipCut.Discharge.StreamMoveWire` exits 0 with the lakefile's
`-DwarningAsError=true`; no `sorry`, no `admit`, no `native_decide`.

Evidence: `data/raw/lean_chipcut_wire_streammove_v4_20261122/` —
`axioms.lean`, `axioms.txt` (22 `#print axioms` lines: 13 from round 1, 9 from
round 2), `commands.log`.
`axioms.txt` has no `sorryAx` and no `Lean.trustCompiler`; the only non-core
axioms are the pre-existing `bv_decide` certificates of `Moves.hitsMask_bit_*`,
`Moves.beq_comm_5` and `Strobes.dsteqMask_pick`/`hitsMask_atMostOne` (reached
through `pickScan_mWs` and `byte_mod_two`), the same class MoveFabric and
MoveFabricKeyed already use.

Nothing outside this file, this note and the evidence directory was written.

---

## 1. What is delivered (all kernel-checked)

| target | theorem | status |
|---|---|---|
| `rx` | **`streams_rx_low1`** | **discharged** (in the `% 2` form; the exact form is false, `MoveFabricKeyed.stream_rx_data_witness`) |
| combined control | **`streams_ctl_combined`** | **discharged** for `rewind`/`clrStarved` and for the *consumed* `flush`; the plain `flushReq = flush` form holds on unfrozen cycles (`streams_flush_live`) and is false on frozen ones (see §4.2) |
| combined control, unconditional | **`streams_ctl_combined'`** | **discharged** with only the standard hypotheses (round 2, §7); its three side hypotheses are `streams_ctlMove_pick`, `streams_hCtl`, `streams_frz` |

Statements, verbatim as proved (all over `(s m pin)` with `ChipRel`, `Inv`,
`hJGTab`, `CoreInputBus`, `hgrp`, `DstKindTable`):

```lean
theorem streams_rx_low1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 → …)                      -- verbatim pickScan_mWs hypothesis
    (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) :
    ∀ k : Fin 2, (machStreamIn m k).rx.map (fun v => v % 2) =
      (absInOf k (streamAt s k.val) (streamIn s pin k.val)).rx
```

(`absInOf k (streamAt s k.val) (streamIn s pin k.val)` is exactly
`Bridge.StreamB.absIn (k.val == 0) … (gatedIn k …)`, i.e. the right-hand side of
`StreamWire.input`.)

```lean
theorem streams_ctl_combined (s : State) (m : Machine.State) (pin : Machine.PinIn) (k : Fin 2)
    (hmove : (machStreamIn m k).ctlMove =
      (if strobe s pin (BitVec.ofNat 6 (51 + k.val))
        then some (gw s pin (BitVec.ofNat 6 (51 + k.val))).data.toNat else none))
    (hhost : (machStreamIn m k).hCtl =
      (if hwIsSome s "SRT" k.val "CTL" then some (hwData s).toNat else none))
    (hfrz : m.dbg.frz = (streamIn s pin k.val).frz) :
    ((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 0 ||
        Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 0) =
      (streamIn s pin k.val).rewind)
    ∧ (((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
        (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) && !m.dbg.frz) =
      ((streamIn s pin k.val).flush && !(streamIn s pin k.val).frz))
    ∧ (Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 7 =
      (streamIn s pin k.val).clrStarved)
```

Supporting lemmas (all kernel-checked, no extra axioms):

| lemma | content |
|---|---|
| `core_bitAt_eq_nbit` | `CoreCtl.bitAt x i = nbit x.toNat i` (the `CoreCtl` twin of `Bridge.Glue.bitAt_eq_nbit`; `Strobes` uses `CoreCtl.bitAt`) |
| `getD_ite_some` | `(if c then some x else none).getD 0 = if c then x else 0` |
| `machStreamIn_rx`, `machStreamIn_ctlMove` | the machine's `sel` scans in the plain `findSome?` shape `pickScan_mWs` consumes |
| `dgTable_stream_adv/rx/ctl` | `dgTable (47+k) = dgTable (49+k) = dgTable (51+k) = famG (.stream k)` (the third and second by a 2-case `decide`) |
| `gw_stream_adv/rx/ctl` | `gw s pin (47+k) = gw s pin (49+k) = gw s pin (51+k) = streamPick s pin k` |
| `streamCtl_combine` | the pure boolean identity behind `streams_ctl_combined` |
| `streams_flush_live` | `flushReq = flush` on an unfrozen cycle |

## 2. Target 1: `rx` is the low bit of the stream group's winner

Machine side: one `pickScan_mWs` instance for `Fam.stream k` with

```lean
sRxUnit k : Machine.DstOp → Option Unit   -- `.sRx j => if j == k then some () else none`, else none
codeUnit (49+k) : BitVec 6 → Option Unit  -- `d => if d == ofNat 6 (49+k) then some () else none`
T := id (then the pair's second component over `% 2`)
```

`hPQ` is the payload table's stream row plus the two code-table rows
(`DstStreamLineTable.sRx` for `dstOp d = .sRx n ⇒ d = 49+n`, and `.sAdv`/`.sCtl`
for the two *other* codes of the same group, which must map to `none` in both
`P` and `Q`).  Cut side: `rxWe` is the `Sk.RX k` strobe and `rxBit` is bit 0 of
`gw (47+k)`.  `Strobes.opg_eq_pick` at `(49+k)` gives
`rxWe = (gw (49+k)).we && ((gw (49+k)).dst == 49+k)`, `gw_stream_rx`+`gw_stream_adv`
identify both `gw` reads with the same `streamPick`, and `byte_mod_two` turns
`(pickWord).data.toNat % 2` into `if bit data 0 then 1 else 0`.

**Finding (a deviation from the brief's recipe).**  The brief suggests
`Q dst := some (dst == ofNat 6 (49+k))` with `T := · % 2`.  That cannot satisfy
`hPQ`: on the `Sk.ADV k` code (same group, `dgTable d == G`) the machine-side
payload is `none`, while `some (d == 49+k)` is `some false`, not `none`.  The
payload must carry the code test *inside* the `Option`, i.e.
`Q dst := if dst == ofNat 6 (49+k) then some () else none`; the `&&` is then
recovered by a two-case `by_cases` when the pair's second component is taken.
This is the same `Q`-shape `unitInputs_shCfg_low5` uses for `SHk.CFG`.

## 3. The stream write group has one word

`Sk.ADV k`, `Sk.RX k`, `Sk.CTL k` are codes `47+k`, `49+k`, `51+k` of *one*
group (`Fam.stream k`), which is why the cut may read a single `gw` word and
decide the port from the word's destination code (`Wire.streamIn.cfgMode`,
`rxBit`, `streamCtlOf`).  `dgTable_stream_rx`/`_ctl` are 2-case kernel `decide`s
(`k.val ∈ {0,1}`), and `gw_stream_*` follow by unfolding `gw` (the `famG`
argument is `dgTable (ofNat 6 (47+k))` by `rfl`).

## 4. Target 2: the combined control bits

### 4.1 What the two sides compute

Cut (`Wire.streamIn`, `Strobes.streamCtlOf`):

```
rewind     = (mctl && data[0]) || (hctl && host[0])
flush      = (mctl && data[1]) || (hctl && host[1])
clrStarved =                   hctl && host[7]
```

Machine (`Machine.streamNext`, `Metronome/Machine/Stream.lean:148-152`):

```
rewind   := nbit mctl 0 || nbit hctl 0
flushReq := nbit mctl 1 || (!frozen && nbit hctl 1)
clr      := nbit hctl 7
```

`streams_ctl_combined` proves the three conjuncts under the two wiring
hypotheses `hmove` (the `Sk.CTL` pick: the machine's `ctlMove` is `gw (51+k)`'s
byte when its strobe fires, `none` otherwise — so `getD 0` is `if strobe then
data.toNat else 0`) and `hhost` (the machine's `hCtl` is the host `SRT.CTL` byte
when its write strobe fires, `none` otherwise), plus the freeze sample
`m.dbg.frz = (streamIn …).frz`.  The proof is `streamCtl_combine` after `simp
only` on the two hypotheses: nothing about `machWs` is needed here, so the
control statement is independent of the move-fabric hypotheses.

Note `hmove` is *not* the false field equality: the cut's `ctlMove` is
`some (ctlVal i)` with `ctlVal = (if rewind then 1 else 0) + (if flush then 2 else 0)`,
i.e. it folds the host bits in, and is `some 0` even without a move
(`MoveFabricKeyed.stream_ctl_absent_witness`); `hmove` compares the machine's
field with the picked *word*, which is what the `pickScan`/`gw` machinery gives.

### 4.2 The frozen-cycle subtlety (and why the flush conjunct is gated)

The machine applies its host-flush gate inside `flushReq`
(`!frozen && nbit hctl 1`), but a **move** flush bit is *not* gated there: with
`frozen = true` and the `Sk.CTL` winner's data bit 1 set, `flushReq = true` while
the cut's `flush` input is not gated either.  The gate on the machine side is
*where it is consumed*: `streamNext` passes `flushReq` to `streamAuto` only in
its `else` (unfrozen) branch, so a frozen cycle never acts on it.  The cut gates
the whole flush in `Stream.fl` (`rxMode && i.flush && !endC && !i.frz`,
`Metronome/Stream.lean:286`), so a frozen cycle never acts on it either.

Hence the delivered flush conjunct carries `&& !frozen` on both sides (the
*effective* flush), and

* `flushReq = cut.flush` is **false** in general — witness:
  `frozen = true`, move byte bit 1 set, host byte bit 1 clear: `flushReq = true`,
  cut `flush = true` as a field but the cut's `fl` is `false`, and the machine's
  frozen branch ignores `flushReq`.  No machine/cut disagreement: both act on
  nothing.
* `streams_flush_live` recovers the plain form on unfrozen cycles (where
  `!frozen` is inert on both sides).

`rewind` and `clrStarved` have no such gate: §12.3 keeps the host stream rewind
and the `STARVED` clear running while frozen, on both sides
(`StreamDbg.frozen_rel_rewind`).

### 4.3 How an assembler restates `StreamWire.input`'s control part

`StreamWire.input` (`∀ k, machStreamIn m k = absInOf k …`) is **false** for
`ctlMove` (`none` vs `some 0`, `stream_ctl_absent_witness`) and for `hCtl`'s
representation (`Option Nat` of `hwByte` vs the cut's `hwIsSome`/`hwData`), so it
cannot be discharged as stated.  The replacement is:

1. keep the field equalities for `adv`/`rx`/`served`/`landNow`/`ramOut`/`cev`/
   `record`/`apply`/`late` (W1b's `adv`, the arbiter/landing/capture bridges);
2. replace the `ctlMove`/`hCtl` part by `streams_ctl_combined`: the three
   booleans `Machine.streamNext` reads from `(ctlMove, hCtl, frozen)` are the
   cut's `rewind`, `flush` (effective) and `clrStarved`.  The bridge's own values
   are `Bridge.StreamB.ctlVal`/`clrVal`, whose bit readings are the `@[simp]`
   lemmas `Bridge.StreamB.nbit_ctl0`/`nbit_ctl1`/`nbit_clr0`/`nbit_clr7`, so the
   replacement composes with `absIn` without further arithmetic;
3. `hmove` is the `Sk.CTL` pick (`gw (51+k)`'s `we && dst == 51+k` and data,
   `gw_stream_ctl` identifies the word), `hhost` is the host-byte wiring
   (`machHw m = hwOf s` plus "the write value is the cut's `hwData`", which is
   `DbgWire.hdbg`-class work, not move fabric).

## 5. Findings

1. **`rx` is a genuine 2-way truncation, not a payload mismatch.**  Both readings
   are the *same* group winner (`gw (47+k) = gw (49+k)`); the machine keeps the
   byte, the cut reads `w[0]`.  `% 2` is the exact relation.
2. **The payload `Q` must be `Option`-valued in the group's *own* code test.**
   The brief's `Q dst := some (dst == code)` fails `hPQ` on the other two codes of
   the same stream group (§2).
3. **The control part never needs the move fabric.**  `streamNext` reads
   `ctlMove`/`hCtl` only through `getD 0`'s bits 0/1/7, so the control statement
   holds with just the `Sk.CTL` pick and the host byte; the whole `pickScan`
   machinery is irrelevant to it.  `streams_ctl_combined` therefore carries no
   move-fabric hypotheses at all.
4. **The frozen flush is consumed, not computed.**  The machine's `flushReq` is
   *true* in a frozen cycle with a move flush bit, but unused; the cut's `fl` is
   false there.  The equality of *effective* flush (`&& !frozen`) is the right
   statement, and `streams_flush_live` is the unfrozen strength (§4.2).
5. **No RTL/machine disagreement found** on either field: both differences are
   data-width/representation facts (like `WireAgree.sym`/`UnitInputs.flag`), and
   the frozen flush is a "both ignore it" coincidence of *where* the gate sits.

## 6. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.StreamMoveWire     # exit 0, 3.1 s (66 jobs)
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_streammove_v4_20261122\axioms.lean
                                                          # exit 0, 3.6 s, 13 lines, no sorryAx
lake build Metronome.ChipCut                             # exit 0 (regression, up to date)
lake build Metronome                                     # exit 0 (whole library, up to date)
cd ..
git diff HEAD -- src                                      # empty
```

Development was done in a scratch file next to `lakefile.toml` (compiled with
`lake env lean -DwarningAsError=true`, 2.3–3.6 s per iteration, ~9 iterations)
and spliced only once it compiled; the scratch file and its logs were deleted.
`commands.log` records commands, exit codes and wall times.

## 7. Round 2: the three side hypotheses of the control statement

`streams_ctl_combined` carried `hmove`, `hhost` and `hfrz`; all three are now
theorems, and **`streams_ctl_combined'`** states the same three conjuncts with
only `ChipRel`, `Inv`, `hJGTab`, `CoreInputBus`, `hgrp`, `DstKindTable`,
`DstPayloadTable`, `DstStreamLineTable`:

```lean
theorem streams_ctl_combined' (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) :
    ∀ k : Fin 2,
    ((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 0 ||
        Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 0) =
      (streamIn s pin k.val).rewind)
      ∧ (((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
          (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) && !m.dbg.frz) =
        ((streamIn s pin k.val).flush && !(streamIn s pin k.val).frz))
      ∧ (Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 7 =
        (streamIn s pin k.val).clrStarved)
```

plus `streams_flush_live'` (the unfrozen `flushReq = flush` form, same
hypotheses plus `m.dbg.frz = false`).

### 7.1 `hmove` → **`streams_ctlMove_pick`** (statement verbatim)

```lean
theorem streams_ctlMove_pick … (k : Fin 2) :
    (machStreamIn m k).ctlMove =
      (if strobe s pin (BitVec.ofNat 6 (51 + k.val))
        then some (gw s pin (BitVec.ofNat 6 (51 + k.val))).data.toNat else none)
```

The `streams_adv` pattern with `.sCtl`: `sCtlUnit k` (`Option Unit` payload),
**`hPQ_stream_ctl`** (the `hPQ_stream_adv` twin: `S*.CTL`'s code test
`dst == 51+k`, with `DstStreamLineTable.sCtl` for the `dstOp d = .sCtl n ⇒
d = 51+n` row and `.sAdv`/`.sRx` for the two other codes of the group), one
`pickScan_mWs` with `Q dst := if dst == 51+k then some () else none` (the
`Q`-shape finding of §2 again), then `findSome?_snd_map` + `Strobes.opg_eq_pick`
at `(51+k)` + `dgTable_stream_ctl`/`gw_stream_ctl`.

One proof-engineering detail: after `machStreamIn_ctlMove`/`machWs_eq_mWs'` the
goal can be syntactically-reflexive-but-not-closed by `rw`; the final step of the
strobe computation needs an explicit `rfl` (defeq, not syntactic).  In the
spliced file the two `machStreamIn_*` rewrites close by themselves (same-file
elaboration), in the scratch they did not — a reminder that `rw`'s closing check
is syntactic while `rfl` is up to definitional equality.

### 7.2 `hhost` → **`streams_hCtl`** (statement verbatim)

```lean
theorem streams_hCtl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (k : Fin 2) :
    (machStreamIn m k).hCtl =
      (if hwIsSome s "SRT" k.val "CTL" then some (hwData s).toNat else none)
```

Chain: `machHw m = ltHw m` (`LineThread.hostNext_hw`, `rfl`) → `ltHw m = hwOf s`
(host link) → `hwByte (hwOf s) … = if (hwAt (hwOf s) …).isSome then
some s.hostCmd.wdata.toNat else none` (`hwByte_eq`), and `hwIsSome`/`hwData` are
definitionally those two pieces.

**Finding (import clash).**  `HostPinWire.ltHw_eq`/`hwByte_eq` are exactly this
bridge, but `HostPinWire` **cannot be imported** in this part of the tree: it
redeclares `Metronome.ChipCut.Discharge.bgetLE_lt`, which `CoreUnits` (imported
by `MoveFabric`) already defines, so the import fails with "environment already
contains 'Metronome.ChipCut.Discharge.bgetLE_lt'".  The three steps are therefore
re-derived locally as `ltHw_eq'`, `hwAt_val'`, `hwByte_eq'` (in the
`…StreamMoveWire` namespace, so they do not clash with `HostPinWire`'s copies),
using `MemHostCfg.linkRel_cut` (`LinkRel s.hostCmd m`).  Anyone wishing to reuse
`HostPinWire` wholesale should first de-duplicate `bgetLE_lt`.

### 7.3 `hfrz` → **`streams_frz`** (statement verbatim, one line)

```lean
theorem streams_frz … (hrel : ChipRel s m) (k : Fin 2) :
    m.dbg.frz = (streamIn s pin k.val).frz
-- proof: rw [dbgRel_frz hrel.dbg]; rfl
```

No new finding: `ChipRel.dbg` is a `DbgRel`, whose `frz` projection is
`s.freeze.frz` (`MemHostCfg.dbgRel_frz`), and the cut's `streamIn.frz` is that
same register.

## 8. Reproduce (round 2)

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MoveFabricKeyed     # exit 0, 0.4 s (dep pre-check)
lake build Metronome.ChipCut.Discharge.StreamMoveWire      # exit 0, 7.1 s (66 jobs; module 2.8 s)
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_streammove_v4_20261122\axioms.lean
                                                           # exit 0, 2.7 s, 22 lines, no sorryAx
cd ..
git diff HEAD -- src                                       # empty
```

Round 2 was developed in `scratch_streammove2.lean` (importing the round-1
module, so only the new section was re-elaborated: 2.4–5.4 s per iteration, 4
iterations) and spliced; the scratch file and logs were deleted.
