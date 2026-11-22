# Bridge notes: `Metronome.Units` / `Metronome.Stream` ↔ `Metronome.Machine`

Written 2026-11-21; extended 2026-11-21b (accumulator flags, stream outputs and
requests, the frozen stream cycle, divergence witnesses), 2026-11-21c (the
unfrozen stream cycle, the buffer relation and its preservation gap) and
2026-11-21d (the frozen cycle with a host rewind).  Files:

* `code/tests/lean/Metronome/Bridge/Units.lean` — the per-unit bridge.
* `code/tests/lean/Metronome/Bridge/Stream.lean` — the stream bridge.
* Evidence: `data/raw/lean_bridge_units_stream_v4_20261121b/`
  (`axioms.txt`, `commands.log`); the 2026-11-21a round is in
  `data/raw/lean_bridge_units_stream_v4_20261121/`; the 2026-11-21c round is in
  `data/raw/lean_bridge_stream_v4_20261121c/` (`axioms.txt`, `commands.log`,
  `build.log`); the 2026-11-21d round (frozen rewind) is in
  `data/raw/lean_bridge_stream_frozen_v4_20261121/` (`axioms.lean`,
  `axioms.txt`, `commands.log`, `build.log`, `run_evidence.ps1`).

Purpose: `Metronome/Units.lean` and `Metronome/Stream.lean` are the specifications
that `units_check.py` and `stream_check.py` prove the **extracted RTL** equal to
(one `rtlStep` per register, lifted to traces).  `Metronome.Machine` is the
independent whole-chip spec.  Each bridge theorem below is a one-step equality
between the cut spec and the corresponding machine component under an explicit
abstraction map, so (RTL = cut) ∘ (cut = machine) gives (RTL = machine) for the
bridged fragment.

Acceptance: `lake build Metronome.Bridge.Units Metronome.Bridge.Stream` exits 0
with `-DwarningAsError=true` (11.2 s and 6.8 s on a full rebuild in round b;
round c rebuilds the stream module in 323.1 s, round d in 862 s, see
`data/raw/lean_bridge_stream_v4_20261121c/commands.log` and
`data/raw/lean_bridge_stream_frozen_v4_20261121/commands.log`).  No
`sorry`/`sorryAx`; `axioms.txt` records `#print axioms` for every new theorem.

## Conventions

* The cut takes one sampled input record per unit; the machine takes one `Option`
  per write group (§6).  `absIn` maps `none` = "the cut says no write" and
  `some (code, value)` otherwise.
* `unitsNext`/`streamNext` are only reached with `rst_q` high in the machine, so
  `resetN = true` is a *hypothesis*, not part of the abstraction.
* Freeze does not appear in the unit bridges: `unitsNext` uses `frozen` only for
  `FP` (§12.3), and no move can occur in a frozen cycle (§12.3).

## Counter (§6.1 / SPEC v1 §6.1)

| item | value |
|---|---|
| abstraction | `CounterB.abs s = s.v` (BitVec 16); `CounterB.absIn`: `we` → `none`; `sel = 0` → `some (0, d)`; `sel = 1` → `some (1, d)`; else (codes 2 and 3) → `some (2, d)` |
| theorem | `CounterB.abs_step : abs (Counter.step s i) = Machine.cntNext (abs s) (absIn i)` (`i.resetN = true`) |
| output | `CounterB.zOut_eq : Counter.zOut s = (s.v.toNat == 0)` |
| side conditions | `resetN = true` only |
| disagreement | none.  Counter port code 3 is `DEC` in both readings. |

## Shifter (§6.1 / SPEC v1 §6.1)

| item | value |
|---|---|
| abstraction | `ShifterB.abs s = ⟨s.dr, s.cnt, s.len, s.msb⟩`; `absOp`: `!we` → `none`, else `some (!sel, d)`; `absCfg`: `some cfgD` if `cfgWe` |
| theorem | `ShifterB.abs_step : abs (Shifter.step s i) = Machine.shNext (abs s) (absOp i) (absCfg i)` (`resetN = true`) |
| outputs | `ShifterB.out_eq`, `ShifterB.done_eq` |
| disagreement | none. |

## LFSR / CRC (§6.1 / SPEC v1 §6.1)

| item | value |
|---|---|
| abstraction | `LfsrB.abs s = s.s`; `absIn`: `ST` = `some (none, d)`, `B0..B3` = `some (some 0..3, d)`, codes 5..7 hold |
| theorem | `LfsrB.abs_step : abs (Lfsr.step s i) = Machine.lfNext (abs s) i.poly.toNat (absIn i)` (`resetN = true`) |
| output | `LfsrB.out_eq` |
| disagreement | none. |

## Accumulator (§6.1 / SPEC v1 §6.1): `A`, `Z`, `C`, `N` and the scratch bank

**Now complete for all seven op codes**, under the §6 `OneHotOrZero` write-group
contract and the code-7 side condition.

| item | value |
|---|---|
| abstraction | `rbyte x k = truncate 8 (x >>> 8k)` (byte `k` of the packed `r`); `absUnits s = { a := s.a, z := s.z, c := s.c, n := s.n, r := fun k => rbyte s.r k }`; `absReg i` = the four `Rk` write groups as the machine `reg`; `absIn i : Machine.UnitsIn` = `acc := if hit = 0 then none else some (winnerSel i, winnerData i)`, `reg := absReg i` |
| key lemma | `accNext_eq`: for `sel ≠ 7`, `Machine.accNext a z c n sel v = (A-write result, Z, C-write result, N)` where each component is the cut's `Acc.alu a c sel v` field (`LD`, `ADD`, `SUB`, `AND`, `OR`, `XOR`, `CMP` are the seven cases) |
| `Nat`/`BitVec` bridge | `BitVec.toNat_and/or/xor` (`and_val`/`or_val`/`xor_val`), `BitVec.toNat_sub` (`sub_val`, `sub_form`), `toNat_sum9` + `add_val` for the 9-bit sum, `beq_zero_nat` and `bitAt_eq_nbit` for `Z`/`N`, `ule_eq` for `C` |
| supporting | `winnerSel_eq_slot`, `winnerData_eq_slot` (the winner `if` chain picks the one-hot slot), `onehot_ne_zero`, `absIn_none`, `absIn_slot`, `winnerWa/Wc/Cy/Z/N/Res_eq_slot` (from `Acc.winnerResult_eq_slot` by `congrArg`), `r_eq_units` (the bank: `rNext_bytes` against the machine `reg` group) |
| theorems | `Agrees_hit0` (`hit = 0`), `Agrees_slot` (one-hot at slot `m`), `abs_step_slot`, and **`AccB.abs_step`**: `Agrees (mstep cfg s (absIn i)) s i` under `resetN = true`, `OneHotOrZero i.hit`, `i.hit = 0 ∨ winnerSel i ≠ 7`.  `Agrees` is the five-field statement: `A`, `Z`, `C`, `N` (machine `a/z/c/n`) and `Vector.ofFn (fun k => rbyte (Acc.rNext s i) k) = u.r`. |
| code-7 side condition | kept from the 2026-11-21a round: `AccB.code7_z_disagrees` (kernel `decide`) shows the cut's `alu` code 7 (`Z = (v == 0)`) against the machine's hold.  `Acc.opCodeOf` maps destination codes 7..13 to op codes 0..6 and everything else to 6, so the RTL never presents 7; the chip therefore guarantees the side condition. |
| disagreement | none for codes 0..6 in both readings.  SPEC v1 §6.1 names no code-7 operation; the two readings differ there (witness above, `AMBIGUITIES.md` has no entry for it). |

## Streams (§6.3 / §12.3 / §12.4 / §13.2)

### The abstraction

`StreamB.abs s` is the cut's fourteen registers as `Machine.StreamSt` (the map is
the identity on every field); `cfgOf i` is `{rx := cfgMode, msb := cfgMsb, start
:= cfgStart.toNat, len := cfgLen.toNat, mark := cfgMark.toNat}`; `modeOf cap i`
is the machine's mode number (`3` replay, `2` capture, `1` receive, `0`
transmit); `dbgOfCap cap i` sets the machine's `cen`/`rpl` from the cut's
**gated** `cen`/`rpl` (a `CAP = 0` stream has no capture/replay at all);
`absIn cap s i` is the machine's `StreamIn`:

| machine input | from the cut |
|---|---|
| `adv` | `i.adv` |
| `rx` | `some (if rxBit then 1 else 0)` when `rxWe`, else `none` |
| `ctlMove` | `ctlVal i = rewind + 2·flush` (bit 0 rewind, bit 1 flush) |
| `hCtl` | `clrVal i = 128·clrStarved` (host bit 7 clears `STARVED`) |
| `served` | `i.gnt` |
| `landNow` | `s.ld && !i.frzd` — see below |
| `ramOut` | `i.rdata.toNat` |
| `cev`, `record` | `i.capPush`, `i.capRec.toNat` |
| `apply`, `late` | `i.replayApply`, `i.replayLate` (the chip computes these from `DC` and the record, §13.2; both specs take them as inputs) |

`landNow := LD && !FRZD` is the chip's §6.2/§12.3 timing: a word read in cycle
`s` is at the RAM output in `s+1`, a freeze in `s+1` captures it at the end of
`s+1` (so `LD` and `WV` update only in the first unfrozen cycle), and a leftover
`LD` in a second frozen cycle does **not** correspond to a valid RAM output.

### Outputs, guards and the RAM request (proved for every state and input)

| theorem | value |
|---|---|
| `end_eq` / `mark_eq` / `byteAt_eq` / `byte_eq` (kept) | `Sk.END`, `Sk.MARK`, `Sk.BYTE`, source `Sk.BYTE` |
| `bsel_toNat` | `b = MSB ? ~BIDX : BIDX` as a `Nat` is `streamB` |
| `and_one`, `stream_bitAt_eq` | the cut's `Stream.bitAt` is `Machine.Util.bit` at the same index |
| `streamMode_zero` | `Machine.streamMode (cfgOf i) 0 (dbgOfCap cap i) = modeOf cap i` |
| `bit_eq` | `Stream.bitOut cap s i = Machine.streamBit (cfgOf i) 0 (dbgOfCap cap i) (abs s)` |
| `cutReq_eq` | **`cutReq cap s i = Machine.streamReq (modeOf cap i) (abs s)`**, all three forms: word read (transmit, replay), byte write of `PEND` at `BA` (receive), whole-word write of `WB` at `BA[10:2]` (capture) |
| `mode_cases` | the four modes with every mode predicate decided (used by the step bridge and `bit_eq`/`cutReq_eq`) |

Because `abs` keeps `WB`, `PEND`, `BA`, `RQ`, `PV` unchanged, `cutReq_eq` is
unconditional: at a *given* state the request agrees without any side condition
on the replay buffer.

### The frozen cycle (proved)

`StreamB.abs_step_frozen`: in a frozen cycle with **no rewind**, no landing
exception and no move input, the cut's step and the machine's step are the *same
state* (`abs (Stream.step cap s i) = Machine.streamNext ... true`).  Premises:
`resetN = true`, `frz = true`, `rewind = false`, `LD = true → FRZD = true`
(the landing has already happened, so `landNow = false`), and the side condition

> `ADV = RX = flush = capture-push = replay-late = false`

which is **what the chip guarantees**: §12.3 "streams and the pointer make no
autonomous update and are not served", so no move reaches a stream in a frozen
cycle, and a host stream flush is ignored while frozen (§12.3; the cut's `fl`
and the machine's `flushReq` both gate on `FRZ`).  In this fragment freeze,
`STARVED` clearing and holding, `RQ`/`LD`/`PV` holding and the rewind override
all agree.

#### The frozen cycle with a host rewind (`abs_step_frozen_rewind`, round d)

§12.3 keeps the host stream `CTL` — and hence a rewind and the `STARVED` clear —
running while frozen, so a frozen cycle is not necessarily a holding cycle.
`StreamB.abs_step_frozen_rewind` replaces `rewind = false` by `rewind = true`
(the `STARVED` clear is unconstrained in both theorems: `clrStarved` is not a
premise) and keeps every other premise of `abs_step_frozen`, concluding the
same state equality.  Field by field (§6.3's rewind list, §12.3):

| field | value in both readings | why |
|---|---|---|
| `POS`, `BIDX` | `0` | §6.3 rewind override (`posNext`, `bidxNext`) |
| `BA` | `START` (`cfgStart`), via `cfgOf` | §6.3 |
| `CUR` | `0` | §6.3 |
| `CV`, `WV`, `RQ`, `LD`, `PV` | `0` | §6.3 |
| `WB`, `NB` | held | §6.3's list omits them, and no landing occurs (`LD → FRZD`) |
| `PEND` | held | no receive move |
| `STARVED` | `STARVED && !CTL[7]`, **no starve event** | no `ADV`, no `RX` (side condition) |

The only field the two readings then differ on is the **inert** `NV` of a
`CAP = 0` stream (divergence (b') below: §6.3's rewind list omits `NV`, AMBIG(14)
clears it), so the theorem carries the named hypothesis
`hnv : cap = true ∨ s.nv = false`.  It does *not* drop the rewind case: a host
may rewind while frozen, and §12.3 says such a rewind acts, so the discharge has
to cover it — the relational form is `ChipCut.Discharge.frozen_rel_rewind`,
which needs no `hnv` because its buffer relation constrains only the valid
slots.

### Divergences (witnesses, kernel `decide`; no spec was edited)

1. **Frozen `STARVED` event (a).**  §12.3 "in a frozen cycle there is no
   autonomous update" (the machine's frozen branch returns `ev = false`), while
   the cut's `starveEvent` is **not** gated by `FRZ`.  Witness
   `freeze_starved_disagrees`: a frozen cycle with a free `ADV` gives
   `STARVED' = true` in the cut and `false` in the machine.  The chip never
   presents `ADV` while frozen, which is exactly the side condition of
   `abs_step_frozen`.
2. **Frozen replay landing (b).**  §13.2's two-deep buffer (`WB`, then `NB`)
   with `apply: WB' = NB, WV' = NV, NV' = 0` is read as AMBIG(11) on the machine
   side.  A word landing in a frozen cycle with `WV = 0`: the cut parks it in
   `NB` (`nbNext`) and holds `WB`; the machine stores it in `WB`
   (`streamNext`'s frozen branch: `MODE = 3 && WV` goes to `NB`, otherwise
   `WB`).  Witness `frozen_replay_buffer_disagrees`: cut `NB = 0x1234`, `WB = 7`;
   machine `WB = 0x1234`, `NB = 9`.  The *valid* contents agree — in this case
   both `WV` and `NV` are clear — and the next unfrozen cycle re-converges (the
   cut promotes `NB` through `landing`, the machine promotes `WB` through
   `landNow = false`); but the raw `NB`/`WB` slots differ at the frozen cycle, so
   the state bridge cannot be stated field-by-field at that point.
3. **Inert `NV` of a `CAP = 0` stream at a rewind (b').**  SPEC §6.3's rewind
   list is `POS, BIDX, BA, CUR, CV, WV, RQ, LD, PV`; §13.2 adds `NV` (AMBIG(14)).
   The cut's `nvNext` clears `NV` on a rewind only when `CAP = 1` (with `CAP = 0`
   the field is inert: the RTL has no second slot), the machine clears it
   always.  Witness `frozen_rewind_inert_nv_disagrees`: cut `NV = true`, machine
   `NV = false`.  `NV` is not a stream register when `CAP = 0`.  This is the
   named hypothesis `hnv` of `abs_step_frozen_rewind` (round d) and the reason
   `ReplayRel`'s `CAP = 0` part does not mention `NV`.

### The unfrozen cycle: the scalar registers (proved in round c)

`AbsRelB cap s m` is the relation of the unfrozen bridge: the ten scalar
registers agree (`POS`, `BIDX`, `BA`, `CUR`, `CV`, `RQ`, `LD`, `PEND`, `PV`,
`STARVED`) and the four buffer slots satisfy `BufRel` (below).

**`abs_step_unfrozen`** (frz = false, `resetN = true`): each scalar register of
`Stream.step` equals the machine's, one lemma per register, each proved by
splitting on the four modes (`mode_cases`) and then on the branch conditions:

| register | modes | branch conditions needed |
|---|---|---|
| `pos_step_unfrozen` | all four | `rewind`; replay `RQ && g`; capture `push && !(PV && !g)`; receive `done`; transmit `ADV && CV && BIDX == 7` |
| `bidx_step_unfrozen` | all four | `rewind`; replay/capture hold; receive `done`, `bitin`; transmit `ADV && CV`, `BIDX == 7`, `WV` |
| `ba_step_unfrozen` | all four | `rewind`; `RQ && g` (replay), `PV && g` (capture/receive), `!CV && WV` / `ADV && CV && BIDX == 7 && WV` (transmit) |
| `cur_step_unfrozen` | all four | as `BA`, with `LB` in transmit and `NSH` in receive |
| `cv_step_unfrozen` | transmit only changes | `!CV && WV`, `ADV && CV && BIDX == 7 && WV` |
| `rq_step_unfrozen` | replay, transmit | `RQ && g`, `!RQ && !LD && !END && !(WV && NV)` |
| `ld_step_unfrozen` | replay, transmit | `RQ && g`, `LD` |
| `pend_step_unfrozen` | receive only changes | `done`, `PV && !g`, `NSH` |
| `pv_step_unfrozen` | receive, capture | `done`, `PV`, `g`; `push`, `PV`, `g` |
| `starved_step_unfrozen` | all four | the starve event of the mode (`STARVED` clear bit 7, `late` in replay) |

Supporting lemmas (each proved for every state, mode and input):

* **branch-condition bridges**: `advT_eq`, `last_eq`, `lane_three`, `endC_eq`,
  `bitin_eq`, `bsel_eq_m`, `nsh_eq`, `cfgStart_bv`, plus `beq_nat` / `bne_nat`
  (`BitVec` equality is `Nat` equality of the values) and `lb_eq` / `lb_eq_m`
  (`LB` is the machine's lane extraction), `streamLB_congr`, `lane_val`,
  `shift_one_nat` (`1 <<< b` as a `Nat`), `nbit_clr1` (host `CTL` bit 1 is
  clear), `absIn_rx_isSome`, `absIn_bus0`.
* **state plumbing**: `AbsRelB` (the relation), `BufRel` (the provable buffer
  core), `ReplayRel` (the intended buffer relation, below), the projection
  lemmas `ReplayRel.wv_eq` / `wb_of_wv` / `nb_of_nv` / `nv_eq` / `shape`,
  `BufRel.wv_eq` / `wb_of_wv` / `nv_eq` / `nb_of_nv`, `ReplayRel.toBufRel`,
  and the `simp` lemmas `pair_fst` / `pair_snd` / `fst_ite` / `snd_ite` and
  `<field>_ite` for the fourteen `StreamSt` fields (they push projections
  through the machine's `if` tree, which is what makes the field proofs
  tractable).
* **side conditions**: `resetN = true` (the machine's `streamNext` is only
  reached with `rst_q` high) and `frz = false`; nothing else.

### The replay buffer relation

`ReplayRel cap s m` is the intended relation (a relation, not a function, on
`WB`/`WV`/`NB`/`NV`):

* `WV` and `NV` agree;
* `WV = 1` ⇒ `WB` agrees; `NV = 1` ⇒ `NB` agrees;
* `WV = 0` ⇒ `NV = 0` (no valid second slot while the first is empty);
* the pending landing word agrees: `LD = 1` ⇒ the cut's `NB` equals the
  machine's `NB` when `WV = 1` and its `WB` when `WV = 0`;
* `RQ` and `LD` are never set together (the read handshake);
* for `CAP = 0` the relation only asks `WB`, `WV`, `NB` to agree (`NB`/`NV` are
  inert in the cut and the machine clears `NV` on a rewind, AMBIG(14)).

`BufRel` is `ReplayRel` without the last two clauses of the `CAP = 1` part (the
occupancy shape and the pending landing word); `ReplayRel.toBufRel` derives
`BufRel` from `ReplayRel`.  The scalar bridge above only needs `WV` agreement
and "a valid `WB` agrees" (for `LB`), both in `BufRel`.

**`BufRel` preservation is *not* proved.**  The blockers are exact and are in
the replay landing/`apply` corners, all in the frozen-landing exception of
§12.3 and AMBIG(11):

1. **frozen landing, `WV = 0`** (witness (b) above): the cut parks the word in
   `NB`, the machine in `WB`, so the raw slots differ while both `WV` and `NV`
   are clear.  That is what the pending-landing clause is for: in the *next*
   unfrozen cycle the cut lands from `NB` (`landing = if FRZD then NB else
   rdata`) and the machine from `WB` (`word = if landNow then ramOut else if WV
   then NB else WB`), and they agree.  Proving this needs `FRZD`, which is an
   *input* of the cycle: the clause is re-established at the frozen step, not
   at the unfrozen one.
2. **`apply` together with a landing** (`apply ∧ LD`): the machine's next
   landing word is its `NB` (because `apply` publishes `NV` into `WV`), the
   cut's `NB` is its stale second slot; the cut and the machine then legitimately
   disagree on the *invalid* slot.  The relation's pending-landing clause
   therefore needs a further clause relating the stale `NB` to the machine's
   `NB` in exactly the states where `NV = 0`.
3. **landing into the second slot when the previous cycle was frozen**
   (`LD ∧ occupied ∧ FRZD`): the cut holds `NB` (its `nbNext` frozen branch needs
   `!FRZD`) while the machine stores the landing word there, and both set
   `NV = 1`; the cut's slot is then a different (stale) word.

So `WB`/`WV`/`NB`/`NV` are bridged for every state only by `BufRel` *given*
that the pending landing has been accounted for; the composition
frozen-then-unfrozen needs one more clause on the cut's stale `NB` (item 2) and
the `FRZD` index (items 1 and 3).  No spec was edited and no proof was forced:
the frozen-state equality, `abs_step_unfrozen` and the three witnesses are the
proved fragment.

### Remaining gaps (not delivered)

* **The replay-buffer relation across the unfrozen step** (item 1–3 above):
  `BufRel`/`ReplayRel` preservation is not proved, so
  `abs_step_unfrozen` bridges the ten scalar registers and *not* `WB`/`WV`/
  `NB`/`NV` as a state theorem.  The request, guard and `BIT`/`BYTE` bridges
  are unconditional (`cutReq_eq`, `end_eq`, …), because they read the *current*
  state and `abs` keeps the buffers unchanged.
* **The frozen step in relational form.**  `abs_step_frozen` (and
  `abs_step_frozen_rewind` for the host-rewind case) prove exact state equality,
  hence preserve *any* relation, but only against the abstraction `abs s`; the
  relational statements are `ChipCut.Discharge.frozen_rel` /
  `frozen_rel_rewind` (that module's notes, §3.1), not bridge theorems.
* The camera-ready form of the freeze side condition (2) as a chip-derived
  invariant is stated in prose here; it is not yet proved from
  `Metronome.Machine.Chip`'s move decode.

## Evidence and commands

`data/raw/lean_bridge_stream_frozen_v4_20261121/commands.log` records the
round-d commands, exit codes and wall times: `lake build Metronome.Bridge.Stream
Metronome.ChipCut.Discharge.StreamDbg` exit 0 (the stream bridge re-elaborated
in 862 s with `-DwarningAsError=true` and no warnings, the discharge in 14 s);
`axioms.txt` has 13 `#print axioms` lines including `abs_step_frozen_rewind` and
`frozen_rel_rewind`, none `sorryAx`; `src/` untouched (`git diff --quiet HEAD --
src`: exit 0).  `data/raw/lean_bridge_stream_v4_20261121c/commands.log` records
the round-c commands (`lake build Metronome.Bridge.Stream`: exit 0, 323.1 s
clean rebuild, no warnings; `axioms.txt`: 35 `#print axioms` lines, no
`sorryAx`).  The round-b numbers are in
`data/raw/lean_bridge_units_stream_v4_20261121b/commands.log`.
Two distinctions to keep: the ACC results are **RTL-equal-cut** composed with
**cut-equal-machine** (i.e. RTL = machine for the accumulator fragment); the
stream step results are Lean-checked implications only (no co-simulation), and
the buffer relation is a proved *statement* whose preservation is the open item
above.
