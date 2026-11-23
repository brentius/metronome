# Discharge: `p0`, `hostReq`, `host`, `cw`, `bank`, `contents` (MemHostCfg)

File: `Metronome/ChipCut/Discharge/MemHostCfg.lean`, namespace
`Metronome.ChipCut.Discharge`.  Acceptance: `lake build Metronome.ChipCut
Metronome.ChipCut.Discharge.MemHostCfg` exits 0 with `-DwarningAsError=true`
(Lean 4.35.0, core libraries only).  Evidence:
`data/raw/lean_chipcut_discharge_memhostcfg_v4_20261121c/` (`commands.log`,
`build.log`, `axioms.txt`, `axioms.lean`).  No `sorry`, no `native_decide`, no
edits outside this file and these notes (`git diff --quiet HEAD -- src` is true).

Revision **c** closes the two `cw` facts that are not about the move fabric or
the release window: `cw_open_hostCfg` (the host configuration write) and
`cw_open_frozen` (the D50 frozen cycle) are theorems.  `premise_cw` now takes
only `cw_open_h19`, `cw_open_move` and `cw_open_window` as named facts.
Revision **b** had fixed the latch-bank wiring on the ChipCut side (`Step.lean`
steps the bank from the arbiter's *stage* state), removed the
`bank_lag_witness` counterexample, proved `premise_bank` and `premise_contents`,
and made `cw_open_abs` a theorem.

## 1. What the file adds

`Machine.runStep` builds every per-cycle quantity inline in one `let` chain, so a
premise field could not be stated as *"the cut's input is the machine's input"*
(`CHIPCUT_NOTES.md` §3.4/§3.4.1).  The `mhc*` definitions are the missing
projections of that chain (`mhcCbs`, `mhcWs`, `mhcP0Move`, `mhcCwMove`,
`mhcModes`/`mhcModesReq`/`mhcReqs`, `mhcServed`, `mhcReq`, `mhcRam`,
`mhcOwner`, `mhcLaneN`, `mhcHw`, `mhcWindow`, `mhcHostCfg`, `mhcCwo`,
`mhcFetch`, `mhcPw`), each with a `rfl`-level projection lemma (`step_p0`,
`step_host_req`, `step_host`, `step_cw`, `step_cfg`, `step_pmem`, `step_ram`,
`step_mout`).  The `mhc` prefix keeps them clear of the sibling
`Discharge/*.lean` files (they use `mach*`).

## 2. Per-field result

| field | status | proved / named |
|---|---|---|
| `p0` | **proved** (4 named wiring facts) | `Bridge.Mem.p0_step_eq` + the new `p0Next_rel` (the `stale_bridge` that `Bridge/Mem.lean` names but does not export) and `p0Next_stale_landRdy`; named: `p0_open_move`, `p0_open_served`, `p0_open_land`, `p0_open_lane` |
| `hostReq` | **proved** (2 named facts) | `slot_step` + `hostNext_slot`; the data-window decode (`inData_toNat`, `inData_ramWindow`, `dataWindow_decide`, `and_window`, `dataAddr_eq`) and the new-request agreement (`hostNew_eq`, `hostRead_inr`, `hostRead_not_inr`) are proved; named: `hostReq_open_served`, `hostReq_open_strobe` |
| `host` | **proved** (2 named side conditions) | `linkRelR_step`; the pin view (`pin_sck_eq`/`pin_csn_eq`/`pin_mosi_eq`, `sck_bridge`…`sckRise_bridge`, `pinOf_hostReadIn`, `hostNext_pin_congr`), the landing byte (`ramByte_bridge`) and the `regRead` decode (`regRead_eq`, `regRead_bridge`) are proved; named: `host_open_regVal`, `host_open_quiet` |
| `cw` | **proved** (3 named facts) | unfrozen: `cfg_compose_bridge` + `staged_bpa` + `held_bridge` on the machine's own `cwNext` (`cwNext_st_congr`, `cwNext_abs_bridge`); frozen (D50): `cw_open_frozen` (§4); host write: `cw_open_hostCfg`. Named: `cw_open_h19` (AMBIG 19), `cw_open_move`, `cw_open_window` (AMBIG 1/2) |
| `bank` | **proved** (3 facts about the trusted latch bank) | `Bank.step` with the arbiter's stage state is `Machine.cfgNext` (`§1` W+2): `premise_bank` proves both `BankRel` clauses with `bget_bset_self`/`bget_bset_ne`, `cfgByte_write_self`/`cfgByte_write_ne`/`cfgByte_cfgNext_ne`, `bank_addrOf_toNat`, `bpa_toNat`; named: `bank_open_mask`, `bank_open_cfg`, `bank_open_size` |
| `contents` | **proved** (3 named facts) | `cfg`, `pmem`, the host-write agreement (`mhcHw_bridge`) and the `coreNext` memory-output congruence (`coreNext_mout_congr`) are proved; the `mout`/`dmem`/`ramOut`/`ramOwner`/`ramLane` congruence needs `contents_open_cbs`, `contents_open_req`, `contents_open_served` |

`axioms.txt`: no `sorryAx`.  `premise_p0`, `premise_bank`, `premise_contents`,
`cw_open_hostCfg` and the frozen chain up to `mhcCwMove_frozen` depend only on
`propext`/`Classical.choice`/`Quot.sound`; `premise_hostReq` and `premise_host`
add only `bv_decide` certificates (`inData_bv`, `pin_*_eq`, plus pre-existing
`Bridge.Host` ones); `premise_cw` the pre-existing `Bridge.CfgWrite`/
`CoreQueue` ones (`pack_take`, `pack_eq_append`, `wh_wd`, `wl_wd`, `wl_wh`).

## 3. The three resolved findings

1. **Latch bank one cycle early** (reported in revision a): `Step.lean` fed the
   bank from *this* cycle's arbiter grant while `Machine.cfgNext` applies the
   *previous* cycle's write (`§1` W+2).  Fixed on the ChipCut side
   (`bank := Bank.step s.bank s.arb.previousWrite s.arb.staged.addr
   s.arb.staged.data`); with that wiring `premise_bank` is a theorem, and
   `CwRel` supplies exactly the stage-to-`cw` identifications it needs.
2. **`stale_bridge` missing from `Bridge/Mem.lean`**: supplied here
   (`p0Next_rel`, `p0Next_stale_landRdy`).
3. **`cwNext` congruence missing from `Bridge/CfgWrite.lean`**: supplied here
   (`cwNext_st_congr` over the registers `cwNext` reads, `cwNext_abs_bridge` for
   the machine's own arguments).

## 4. The frozen cycle (D50): `cw_open_frozen`

The route of `DISCHARGE_MEMHOSTCFG_NOTES.md` revision b is now a chain of small
lemmas in the file, one per step:

1. `hitsMask_zero6`: a zero move-enable word gives a zero hit mask
   (`Moves.hitsMask`, `Moves.bits6`/`hitAt` all conjoin `en`).
2. `gw_frozen`: a frozen cycle presents no move (`Inv.frozenNoMove`,
   `Core.mvEn_zero`), so the `CW` write group is `⟨false, 0, 0⟩`
   (`Moves.pickWord_none`, `pickWord`'s `we := !(hit == 0)`).
3. `cwWord_frozen`: `cwWord s pin = 0` (`CoreCtl.GroupWord.pack` of the empty
   group word).
4. `cqIn_writes_frozen`: `CoreQueue.writeData`/`writeLow`/`writeHigh` are all
   false, i.e. `CW` word bit 14 (`writeData`) and the byte/flag decodes are
   clear.
5. `cq_step_frozen`: with `accept = false` and `drain = false`
   (`CoreQueue.drain` has the `!frz` gate), the queue holds: `addr`,
   `pending`, `pendingAddr`, `pendingData` unchanged.  The address half is
   `CoreQueue.pack` of the unchanged low/high bytes
   (`Bridge.CfgWrite.pack_round`).
6. `coreComb_moves_frozen` / `mhcCwMove_frozen`: the machine's core bundle
   emits no moves when `frozen = true`, so its `CW` move is `none`
   (`Machine.resolveMoves` of an empty list).
7. `cwNext_frozen_queue`: `Machine.cwNext cw hostCfg none window true` holds
   `cwa`/`cwv`/`cwqa`/`cwqd`.
8. `frozen_bank_port`: the frozen analogue of
   `Bridge.CfgWrite.arbiter_bridge` + `queue_fields_arb`.  `arbIn`'s `coreValid`
   is `… && !s.freeze.frz`, which is exactly `cwNext`'s `frozen` gate, so
   `arbStep s = Config.step s.arb {cfgIn s.cq hostCfg with coreValid := false}`.
   With no move, a closed window and `frozen = true`, `Machine.cwNext` and that
   `Config.step` agree on `bwp`/`hh` and on the guarded `bpa`/`bpd`/`hha`/`hhd`
   (case split on `heldValid`, `previousWrite` and `hostCfg`; `h19` excludes the
   AMBIG 19 overlap; `addrOf_offOf_hostCfg` inverts the nine-bit offset).
9. `cw_open_frozen`: assembles the ten `CwRel` fields from 5–8 plus
   `ChipRel.cw` for the registers the machine's `cwNext` leaves alone.  Its
   hypotheses are the frozen premise, `cw_open_h19`-style overlap exclusion,
   and the closed window (`mhcWindow m = false`, AMBIG 1/2, still a separate
   named fact).

`cw_open_hostCfg` is the host configuration write: `mhcHw_bridge` identifies
the machine's host write with the cut's `hwOf s`, and `mhcHostCfg`/`hostCfgOf`
apply the same `isCfgAddr` filter.  It needs no new hypothesis.

Implementation note (revision c): inside `cw_open_frozen` the `frozen_bank_port`
and `cwNext_frozen_queue` instances are stated with `hostCfgOf s`/`false`, not
with `mhcHostCfg m pin`/`mhcWindow m`, because the goal has already been
rewritten to `cwNext … (hostCfgOf s) none false true` by
`cw_open_hostCfg`/`mhcCwMove_frozen`/`cw_open_window`/the frozen bit.  The
earlier revision's version was rejected by Lean at the `cwqd` field for exactly
that reason (first entry of `commands.log`).

## 5. Remaining named facts, and why

* `p0_open_move`, `p0_open_served`, `hostReq_open_served`, `cw_open_move`: the
  move fabric and the arbiter's served index agree with the cut's `gw`/`grant*`.
  The move side needs the per-core input agreement (`Bridge.Core.Rel`: guard and
  source tables, thread file), i.e. the same obligation the `cores` premise
  carries; the arbiter then follows (`Bridge.Mem.arbiter_eq`).
* `p0_open_land`, `p0_open_lane`: the landing interface between the `Contents`
  RAM-output plumbing (`ramOwner`, `ramLane`) and the pointer cut
  (`land`, `landLane`).
* `hostReq_open_strobe`: `wr` and `rd` are mutually exclusive (one-cycle pulses
  from a single completion — a reachable-state invariant).
* `host_open_regVal`: the machine's register-read value equals the trusted
  chip-top decode `regVal (absChip s) (cfgView s.cont.cfg)`; the *shape* test
  (`regRead`) is proved, the ~30-case value decode is not.
* `host_open_quiet`: a completing byte cycle has no `wr` and no `ackBit`; this is
  a one-cycle-pulse/timing property (a data-RAM landing is two core cycles after
  a byte completion, so its coincidence with `bitc = 7` depends on SCK pacing —
  the AMBIG 17/21 style coincidence).
* `cw_open_h19`: AMBIG 19 (a host configuration write arriving while `HH`
  waits); carried as `Bridge.CfgWrite` does.
* `cw_open_window`: the release window is closed (`mhcWindow m = false`,
  AMBIG 1/2) — a property of the reset-synchroniser phase, not of this file.
* `contents_open_cbs`: the per-core combinational bundle (guard and source
  vectors, thread file, fetch word) agrees between `m` and `absChip s` — the
  `cores`/`lines`/`threads` input obligations.
* `contents_open_req`, `contents_open_served`: the arbiter's served request and
  index agree with the abstraction (the stream-request presence/openness and the
  P0/host request presence, i.e. `p0_open_served`/`hostReq_open_served` plus
  `Bridge.Stream.cutReq_eq`).
* `bank_open_mask` (a byte is unlatched or fully latched), `bank_open_cfg` (a
  latched offset is a decoded configuration address, the AMBIG 4 boundary) and
  `bank_open_size` (the byte image covers `cfgSize` bytes) are the latch-bank
  contents contract.

## 6. Carried deviations

Frozen `RLVP`, AMBIG 19 (adjacent host configuration writes), stream `BufRel`
corners, core `IR` without load and the string-table hypotheses are unchanged.

## 7. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut                              # exit 0
lake build Metronome.ChipCut.Discharge.MemHostCfg          # exit 0, 13.5 s incremental
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_memhostcfg_v4_20261121c\axioms.lean
cd ..
git diff --quiet HEAD -- src                              # exit 0
```

Full command/exit-code/wall-time log:
`data/raw/lean_chipcut_discharge_memhostcfg_v4_20261121c/commands.log`.
