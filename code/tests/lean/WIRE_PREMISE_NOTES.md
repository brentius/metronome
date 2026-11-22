# W6 discharge: two `ExplicitPremises` fields are theorems (`PremiseWire.lean`)

File: `code/tests/lean/Metronome/ChipCut/Discharge/PremiseWire.lean`
(namespace `Metronome.ChipCut.Discharge.PremiseWire`), 2026-11-22.
Toolchain: Lean 4.35.0, core libraries only; `lake build` with
`-DwarningAsError=true` (the project's `lakefile.toml` sets
`moreLeanArgs = ["-DwarningAsError=true"]`; `linter.unusedVariables`,
`linter.deprecated`, `linter.unusedSimpArgs` off as the sibling files do).

Acceptance: `lake build Metronome.ChipCut.Discharge.PremiseWire` exits 0
(0.3 s incremental; 2.9 s / exit 0 for a from-source type-check of the file
alone with `-DwarningAsError=true` and no cached olean — see `commands.log`).

Note on the acceptance command: Lake itself rejects the flag
(`lake build … -DwarningAsError=true` → `lake: error: unknown short option '-D'`;
`-D` is a *Lean* option, not a Lake one).  The project's `lakefile.toml` already
sets `moreLeanArgs = ["-DwarningAsError=true"]`, so every `lake build` target is
compiled warnings-as-errors; the literal per-invocation form is
`lake env lean -DwarningAsError=true Metronome/ChipCut/Discharge/PremiseWire.lean`,
which is the from-source check above.

Evidence: `data/raw/lean_chipcut_premise_v4_20261122/` — `commands.log`,
`statements.lean`/`statements.txt` (`#check` dump of every delivered theorem),
`axioms.lean`/`axioms.txt`, `check_fields.lean` (the acceptance checks of §3 and
the negative control of §2.4), and the drafts `scratch_*.lean` from the first
attempt.

No `sorry`, no `native_decide`.  Nothing outside this file, this note and that
directory was edited: `Metronome/ChipCut/Assembly.lean` is untouched and
`git diff --quiet HEAD -- src` is true.

---

## 0. Exact statements (as proved; `statements.txt` is the `#check` dump)

```lean
theorem grpPacked_holds (s : State) (pin : Machine.PinIn) :
    MoveFabricKeyed.GrpPacked s pin

theorem cwH19_step (s : State) (pin : Machine.PinIn) (hpinv : HostPinInv s) :
    ¬ ((step s pin).arb.heldValid = true ∧
      (hostCfgOf (step s pin)).isSome = true)

theorem cwH19_reset (cont : Contents) :
    ¬ ((resetState cont).arb.heldValid = true ∧
      (hostCfgOf (resetState cont)).isSome = true)

theorem cwH19_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, ¬ ((cutStateAt pins (resetState cont) n).arb.heldValid = true ∧
      (hostCfgOf (cutStateAt pins (resetState cont) n)).isSome = true)
```

Supporting lemmas (all proved here):

```lean
theorem pack6_slice (x0 x1 x2 x3 x4 x5 : BitVec 5) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (pack6 x0 x1 x2 x3 x4 x5) (5 * q) 5 = grpAt q x0 x1 x2 x3 x4 x5

theorem mapOfWith_slice (tab : BitVec 320) (dst : BitVec 36) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (Moves.mapOfWith tab dst) (5 * q) 5 =
      Moves.dgLookupAt tab (CoreCtl.slice dst (6 * q) 6)

theorem hostCfgOf_isSome_wr (s : State) (h : (hostCfgOf s).isSome = true) :
    s.hostCmd.wr = true

theorem completing_bitc (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = true) : s.bitc = 7

theorem hostPinInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, HostPinInv (cutStateAt pins (resetState cont) n)
```

`grpPacked_holds` is exactly the type of `ExplicitPremises.grpPacked`
(`Assembly.lean` 98) and `cwH19_trace _ _ n` is exactly the type of
`ExplicitPremises.cwH19` (Assembly.lean 104) at the trace states
`trace_refines'` quantifies over (Assembly.lean 998).  `check_fields.lean`
checks both facts by `example`, and rebuilds a full `ExplicitPremises` record
with `{ hexp with grpPacked := …, cwH19 := … }` — it type-checks, so no other
field is affected.

## 1. `grpPacked` (the cut-side group-packing identity)

The cut defines the packed group bus as a table map of the destination bus:

* `mvGrp s pin = Moves.mapOf (mvDst s pin)` (`Wire.lean` 347),
* `Moves.mapOf dst = Moves.mapOfWith Moves.dgMapLiteral dst` (`Moves.lean` 100),
* `Moves.mapOfWith tab dst` is the shift-and-OR of the six lookups
  `tab[5 * dst_q +: 5]`, `dst_q = slice dst (6 * q) 6` (`Moves.lean` 90–96),
* `Moves.dgTable d = Moves.dgLookupAt dgMapLiteral d` (`Moves.lean` 72–76).

So the whole obligation is the six-slot slicing identity
`slice (⋁_q (tab[dst_q] << 5q)) (5q) 5 = tab[dst_q]`.  `pack6_slice` proves it
by `rcases` on `q ∈ {0..5}` and `bv_decide` per slot (30-bit symbolic OR; the
six certificate axioms are listed in `axioms.txt`).  `mapOfWith_slice` is that
lemma instantiated at the six lookups, and `grpPacked_holds` composes it with
`MoveFabricKeyed.bundle_grp` (slot `q`'s group is the group-bus slice) and
`MoveFabric.bundle_dst` (slot `q`'s destination is the destination-bus slice).

The theorem is **unconditional**: no `ChipRel`, no reachability, no state
invariant.  It is a wiring identity of the cut, so the review's reading is
right — `grpPacked` was never a premise, only a missing lemma.

## 2. `cwH19` (AMBIG 19: no host configuration write while `HH` waits)

### 2.1 The argument

Write `s` for the current cycle and `s' = step s pin` for the next.

1. `(arbIn s).resetN = true` (`Bridge.CfgWrite.cfgIn`), so
   `Config.heldValid_next` gives
   `s'.arb.heldValid = (s.arb.previousWrite && (arbIn s).hostValid)`.
   Hence `s'.arb.heldValid = true` **implies a host configuration write is
   offered in the current cycle**, i.e. `(arbIn s).hostValid = true`, and
   `arbIn`'s `hostValid` is `(hostCfgOf s).isSome` (`Wire.lean` 62–65,
   `Bridge/CfgWrite.lean` 352–359).
2. `(hostCfgOf s).isSome = true` means the *registered* host write strobe is
   up: `hostCfgOf` is `hwOf` filtered by `isCfgAddr`, and `hwOf` is `some` only
   when `s.hostCmd.wr` (`Wire.lean` 47–57).  So `s.hostCmd.wr = true`.
3. `HostPinInv.wrBitc` (a proved reachable invariant, `HostPinWire.lean` 693)
   then gives `s.hostCmd.bitc = 0`.  Semantically: `wr` is a one-cycle pulse
   raised by `HostCmd.wrNext` on the *completing* edge of a data byte, and
   `HostCmd.bitcNext` clears the bit counter on that same edge
   (`HostCmd.lean` 153–157, 176–177), so the strobe is only ever up with a
   fresh byte, never with a nearly-finished one.
4. `(hostCfgOf s').isSome = true` means `s'.hostCmd.wr = true`, i.e.
   `HostCmd.wrNext s.hostCmd (hostCmdIn s pin) = true`, which forces
   `HostCmd.completing s.hostCmd (hostCmdIn s pin) = true`
   (`wrNext_completing`, `HostPinWire.lean` 713) and hence `s.hostCmd.bitc = 7`.

`0 = 7` is impossible, so the overlap is empty.

The reset branch is immediate: `resetChip` is `resetState` up to `rst`/`rqh`,
and the arbiter clears (`heldValid = false`).

`cwH19_step` is the preservation step and `cwH19_trace` iterates it from
`hostPinInv_reset`, so the statement holds at every state of every trace from
`resetState cont`, which is the shape `trace_refines'` consumes.

### 2.2 No SCK-spacing premise is needed

The brief expected a temporal argument from `Discharge.host_sck_spacing`
(`HostPinWire.lean` 827) plus "consecutive host configuration writes are ≥ 8 SCK
edges apart".  That is stronger than necessary: the *one-cycle* nature of `wr`
already excludes the overlap, in the same cycle, with no assumption about SCK
pacing at all.  `host_sck_spacing` is therefore **not** used here and remains a
premise only where it was: AMBIG 17/21 (`premise_host`'s `host_open_quiet`,
Assembly.lean 891).

Equivalently: two host bytes cannot complete in consecutive cycles, because a
completion needs `bitc = 7` and the completion that raised `wr` cleared it to
`0`.  The 8-SCK-edge spacing is a consequence of the byte counter, not an extra
timing fact — so the "≥ 8 edges" phrasing can be dropped from the premise list.

### 2.3 What is *not* claimed

* Nothing about `s.arb.heldValid` and `hostCfgOf` on unreachable states: the
  statement is proved along the trace only (see 2.4).
* No change to `Discharge.host_sck_spacing`, `premise_host`, `premise_cw` or
  `cw_open_h19` (`MemHostCfg.lean` 1400), which still takes the overlap
  exclusion as an argument — it is now a supplied theorem rather than an
  assumption.

### 2.4 The trace framing is essential (negative control)

`cwH19` is *false* for arbitrary states: nothing in `HostPinInv` forbids
`heldValid = true` together with `wr = true` and `bitc = 0`.  `check_fields.lean`
§4 proves

```lean
example (a : BitVec 16) (ha : Machine.Config.isCfgAddr a.toNat = true) :
    ∃ s : State, s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true
```

by exhibiting the record-updated reset state.  (Such an `a` exists: compiled
evaluation of `isCfgAddr` at `BitVec.ofNat 16 Tables.LINE_BASE` is `true`, i.e.
`0x2000`; `decide` cannot kernel-reduce `isCfgAddr` because it walks the
`Array.anyM` of the host block table, so the witness is stated conditionally —
`native_decide` is not used anywhere in this project.)  Hence the theorem is
stated for the trace `cutStateAt pins (resetState cont) n`, exactly where the
capstone needs it, and not as `∀ s`.

## 3. Acceptance checks (`check_fields.lean`, exit 0)

1. `grpPacked_holds` has the field type `MoveFabricKeyed.GrpPacked s pin`.
2. `cwH19_trace _ _ n` has the field type at the trace state.
3. `{ hexp with grpPacked := …, cwH19 := … }` type-checks as
   `ExplicitPremises` — the two fields are replaceable without touching the
   other fourteen.
4. The negative control of §2.4.

Axioms (`axioms.txt`): `cwH19_step` and `cwH19_trace` depend only on
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no `bv_decide`
certificate, so the `0 = 7` contradiction is decided in the kernel.
`pack6_slice`, `mapOfWith_slice` and `grpPacked_holds` add only the six
`bv_decide` certificates of `pack6_slice` (the project's accepted pattern for
bit-vector slices, cf. `WIRE_HOSTPIN_NOTES.md`).

## 4. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.PremiseWire          # exit 0, 0.3 s
# NB: `lake build … -DwarningAsError=true` is rejected by Lake itself
# ("unknown short option '-D'"); the flag is a Lean option.  lakefile.toml's
# moreLeanArgs already applies it to every target.  For a literal flag check:
lake env lean -DwarningAsError=true `
  -o "$env:TEMP/PremiseWire.olean" `
  Metronome/ChipCut/Discharge/PremiseWire.lean              # exit 0, 2.9 s, no diagnostics
lake env lean ..\..\..\data\raw\lean_chipcut_premise_v4_20261122\check_fields.lean   # exit 0, 3.3 s
lake env lean ..\..\..\data\raw\lean_chipcut_premise_v4_20261122\statements.lean > statements.txt
lake env lean ..\..\..\data\raw\lean_chipcut_premise_v4_20261122\axioms.lean > axioms.txt
cd ../../..
git diff --quiet HEAD -- src                              # exit 0
git diff --quiet HEAD -- code/tests/lean/Metronome/ChipCut/Assembly.lean   # exit 0
```

`commands.log` holds the command / exit-code / wall-time log of the runs above
(2026-11-22, this machine).  The evidence directory is local only:
`.gitignore:45:/data/` ignores it, so `git status` shows just the two tracked-area
additions (the new module and this note).

## 5. Follow-up for the capstone owner (not done here)

`Assembly.lean` is outside this task's ownership, so the two fields are still
*declared* in `ExplicitPremises`.  Two mechanical options, both one-file edits
in `Assembly.lean`:

* keep the fields and have the consumer pass
  `grpPacked := Discharge.PremiseWire.grpPacked_holds _ (pins n)` and
  `cwH19 := Discharge.PremiseWire.cwH19_trace pins cont n` when it builds
  `hexp n` (no proof inside `Assembly.lean` changes); or
* delete the two fields from `ExplicitPremises` and supply
  `grpPacked_holds` / `cwH19_trace` at the six `hexp.grpPacked` /
  `hexp.cwH19` use sites (Assembly.lean 735, 739, 822–824, 829–834, 861–878,
  880–906, 918) — then `premise_cw`'s `cw_open_h19` argument becomes
  `cwH19_trace` at the current state.

Either way the premise count in the write-up drops by two, and the surviving
`ExplicitPremises` fields are the string/table hypotheses, the two cycle
contracts (`hostSckSpacing`, `streamModeQuiet`), the release window
(`cwWindow`) and the latch-bank contract.

The new module is standalone: it is built by name
(`lake build Metronome.ChipCut.Discharge.PremiseWire`) like its `Discharge`
siblings and was deliberately **not** added to the root `Metronome.lean` import
list, which is outside this task's file ownership.  Importing it from the
capstone entry point (or from `Assembly.lean`) is the one-line step that makes
it part of the default library build.
