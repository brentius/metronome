# ChipCut: whole-chip product and refinement (item 4Q)

Status after the independent review (revision **b**): `lake build Metronome.ChipCut`
exits 0 with `-DwarningAsError=true` (Lean 4.35.0, core libraries only), no
`sorry`/`sorryAx`, no `native_decide`/`admit` in the ChipCut files, and
`git diff --quiet HEAD -- src` is true.

Evidence: `data/raw/lean_chipcut_v4_20261121b/` — `build.log`, `axioms.txt`,
`axioms.lean`, `commands.log`, `sorry_scan.txt`, `run_evidence.ps1`
(clean build 24.4 s, axioms 2.5 s, both exit 0).

This revision fixes the two blockers and the two findings that could be closed
in the ChipCut files.  It does **not** discharge the component bridges: the
active-cycle premises remain named hypotheses, restated where possible over the
current related states and the RTL wiring, and §3.2 records for each field what
is still missing and why it cannot yet be stated as a current-state fact.

---

## 1. Files

| file | contents |
|---|---|
| `Metronome/ChipCut/State.lean` | `Contents`, `State` (the product), `resetState`, `absChip` |
| `Metronome/ChipCut/Wire.lean` | every cut input built from the product state and pins; host-window gates; `cwDrain`; `pinsOf` |
| `Metronome/ChipCut/Step.lean` | `activeStep`, `resetChip`, `step : State → PinIn → State` |
| `Metronome/ChipCut/Rel.lean` (**new**) | `SyncRel`/`CoreRegsRel`/`UnitsRel`/`CtrlRel`/`DbgRel`, the validity-guarded `P0Rel`/`CwRel`/`BankRel`, `ChipRel`, `pins_of_rel` |
| `Metronome/ChipCut/Proof.lean` | `Inv`, `SideConds` (both theorems, not hypotheses), `inv_reset`/`inv_step`/`inv_trace`, the reset edge (`chip_reset_refines`, `chip_reset_refines_rel`), `Premises`, `chip_step_refines`, `rel_reset`, `trace_refines` |
| `Metronome/ChipCut.lean` | entry point importing `Proof` (unchanged) |

No existing Lean file outside `Metronome/ChipCut*`, `Metronome.lean`,
`lakefile.toml`, `verify.py`, `README.md`, `*_check.py` or `src/` was edited.

## 2. The product and the relation

The product, its step and the canonical abstraction `absChip` are unchanged in
shape (see `State.lean`/`Step.lean`, and the previous notes revision for the
component table).  One definition changed: `contentsReset.mout` is now
`Vector.replicate 2 0` (the same value, in a form the proofs can unfold).

### 2.1 `ChipRel` (rel.lean)

`ChipRel s m` is a structure of 25 fields.  Three are **validity-guarded**
because the RTL and the machine differ only where a value is not read:

* `p0 : P0Rel m.p0 s.p0` — `ptr`, `d`, `RDY`, `req`, `land` exact; the machine's
  `stale` is compared with the cut's `!landRdy` **only while `land`**
  (`P0Rel.stale : a.land = true → a.stale = !b.landRdy`);
* `cw : CwRel m.cw s.cq s.arb` — queue fields (`cwa`, `cwv`, `cwqa`, `cwqd`) and
  the bank-port flags (`bwp`, `hh`) exact; `bpa`/`bpd` compared only when `bwp`,
  `hha`/`hhd` only when `hh`;
* `bank : BankRel s.bank m.cfg` — bytes without a latch (mask 0) read zero,
  latched bytes equal the machine's configuration byte.  The second clause is
  the stated latch-image contract; it is vacuous in the product's reset state.

New exact relations requested by the review:

* `hostReq : m.host.req = Bridge.Mem.absSlot s.p0` — the host data-RAM slot,
  which drives the machine's arbiter and the cut's `Mem` slot;
* `bank` (above) is now part of `ChipRel` (it was an unused `Inv` placeholder).

`pins_of_rel : ChipRel s m → pinsOf s = Machine.pinsOut m` projects the driven
pins (`uio_out = OUT[7:0]`, `uio_oe = OEN`, `uo_out = {OUT[13:8], IRQ, MISO}`,
MISO = `TX[7]`; `project.v` 818-820).

### 2.2 Headline statements (verbatim)

```lean
theorem chip_reset_refines (s : State) (pin : Machine.PinIn) (hrun : runRst s pin = false) :
    ChipRel (step s pin) (Machine.step (absChip s) pin)

theorem chip_step_refines (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hprem : runRst s pin = true → Premises s m pin) :
    ChipRel (step s pin) (Machine.step m pin)

theorem trace_refines (pins : Nat → Machine.PinIn) (cont : Contents)
    (hprem : ∀ n, runRst (cutStateAt pins (resetState cont) n) (pins n) = true →
      Premises (cutStateAt pins (resetState cont) n)
        (machineStateAt pins (absChip (resetState cont)) n) (pins n)) :
    ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n)
```

`axioms.txt`: each depends only on `propext`, `Classical.choice`, `Quot.sound`
plus the pre-existing `Strobes`/`Mem` `bv_decide` certificates (no `sorryAx`).

## 3. The review findings

### 3.1 BLOCKER 1 — reset branches

**Was:** `Premises` was false on every reset cycle: `bpa`/`hha` compared the
machine's reset 0 with `cwOf`'s `addrOf 0 = 0x2000`, and `absP0` set
`stale = !landRdy = true` where the machine resets `stale = false`.

**Now:** the three guards in §2.1 make the relation compatible with both reset
values, and the whole reset edge is proved **with no premises**:

* `chip_reset_refines_rel : ChipRel s m → runRst s pin = false →
  ChipRel (step s pin) (Machine.step m pin)` — the form the trace uses;
* `chip_reset_refines` — the required statement against `absChip s`.

The reset proof is field-by-field against `Machine.resetStep`:
`rstM`/`rstQ` from `Debug.Reset.step` (`project.v` 50-56), `rqh` from the
machine's two-cycle formula, `sync` from `SpiPins.resetState`, the cut reset
states via `line_abs_reset`/`Bridge.Thread.abs_reset`/`stream_abs_reset`, the
`cfg` field via `cfgNext_cwRel` (only reads `bwp`/`bpa`/`bpd`), `pmem`/`dmem`/
`ramOut` via the relation, `mout` = 0, host via `Bridge.Host.linkRelR_reset`
plus a `host`-field congruence lemma (`linkRelR_host_congr`, proved here because
`LinkRelR` reads only `m.host`), and `bank` via `bankRel_reset` (mask 0).

Small reset lemmas proved in `Proof.lean`: `lineAt_resetChip`,
`threadAt_resetChip`, `streamAt_resetChip`, `shAt_resetChip`, `cntAt_resetChip`,
`lfAt_resetChip`, `p0Rel_reset`, `cwRel_reset`, `bankRel_reset`, plus
`resetChip_cont`, `contentsReset_{cfg,pmem,dmem,ramOut}`, `resetStep_cfg`.

### 3.2 BLOCKER 2 — wiring against `project.v`

The four reported mismatches are fixed, and the requested audit found six more
(none of them a new *spec* disagreement: in each case the RTL is the authority
and `Wire.lean`/`Step.lean` were wrong).

| # | cut input | was | now | `project.v` |
|---|---|---|---|---|
| a | `streamIn.rxBit` | `false` | bit 0 of the `Sk` group pick (`w[0]`) | 471 (`.rx_bit(w[0])`) |
| b | `memIn.hSet` | `h_wr \|\| h_rd` | `(h_wr \|\| h_rd) & in_data` | 496, 83-84 |
| c | `dbgCtrlIn.dWr*` | arbiter `coreIssue`, full address | `cw_drain`, `a_dbg` offset, `w_dbg` host half | 139, 660-670, 107, 118 |
| d | `Config.core_valid` | `pending && isCfg` | `pending && isCfg && !frz` | 145 |
| e | `memIn.pWe` | `OPG(DG_P0, D_P0_AL)` | `P0` group pick's `we` (`w_p0[14]`) | 485-486, 495 |
| f | `accIn.rD` | `quad` of the `R0` group's byte | per-group data (`R0..R3`) | 374-379 |
| g | `cqIn.clearSticky` | `CTRL.STICKY` bit 1 | bit 2 (`CWOVR`) | 694 |
| h | `threadIn.stop`/`lateSet` | winner bits | valid bits (`mv_valid`) | 570-577 |
| i | `memhaz` event, `glueIn.rdHin` | destination vector | source vector (`c_src`) | 674, 318 |
| j | Debug byte strobes | `isSome` + full address | `w_dbg` + `a_dbg` (the `Strobes.dbgByteWrite` convention) | 123, 661-670 |

New helpers: `dataOff`/`inData`, `dbgOff`/`inDbg`/`hwDbg`, `mvSrc`, `slotValid`,
`arbIn`, `cwDrain`, `pinsOf` (`Wire.lean`).

**Wiring table (every cut input, with the `project.v` line checked).**  "Line"
is the driver expression in `src/project.v`; "input" is the `Wire.lean` (or
`Step.lean`) record field group.  Where the RTL passes a bus, the field is the
matching slice.

| input (cut) | `project.v` | checked driver |
|---|---|---|
| `spiIn` (`SpiPins.Sync`) | 60-66 | `s1 <= {ui_in, uio_in}; s2 <= s1; sp <= s2`, cleared by `!rst_q` |
| `Debug.Reset.step` | 50-56 | `rst_m <= !rst_n ? 0 : 1; rst_q <= rst_m` (reset branch, `Step.lean`) |
| `rqh` | 165 | machine `rqh` shift (`!(rqh[0] && rqh[1])` window); not an RTL register |
| `freezeIn` | 658, 699-702 | `d_wr_dbg`, `freeze <= h_wd[0]; frz <= h_wd[0] & ~h_wd[1]` |
| `lineIn.cfg` | 505, 517 | `cfg[8*LB +: 8*HS_LINE]` (inverse decode `lineCfgOf`) |
| `lineIn.lvl`/`rise`/`fall` | 72-76 | `{3'd0, pins_level}`, `pins_level & ~pins_prev`, `~pins_level & pins_prev` |
| `lineIn.ctlWe`/`ctlD` | 514-519 | `wc[14]`, `wc[2:0]` (`wc = PICKG(DG_LCTL[k])`) |
| `lineIn.symWe`/`symOp`/`symD` | 510-519 | `ws[14]`, `ws[13:8]` decode, `ws[3:0]` (`sh[j] = mv_win & grp==L_SYM & xl==k`) |
| `lineIn.phWe` | 520 | `{hl & o_lrt==PHASE+1, hl & o_lrt==PHASE}` |
| `lineIn.hCtlWe`/`hStatWe` | 521 | `hl & o_lrt==HO_LRT_CTL/STAT` |
| `lineIn.hD` | 521 | `h_wd` |
| `threadIn.ev` | 562-564, 576 | `ev_g[ts] \| PINA_RISE/FALL/EDGE \| ALWAYS`, `& ~frz` |
| `threadIn.db` | 576, 698 | `db[k] & ~frz` |
| `threadIn.disp` | 567, 576 | `(dsp[0] & disp_e[2:0]==k) \| (dsp[1] & disp_e[5:3]==k)` |
| `threadIn.pause`/`npc` | 568, 577 | `(pse[0]&c0)\|(pse[1]&c1)`, `(pse[1]&c1) ? npc[15:8] : npc[7:0]` |
| `threadIn.stop` | 572-577 | `\|stop_mv`, `stop_mv = own & mv_valid & grp==DG_T_STOP` (**valid**, not win) |
| `threadIn.lateSet` | 570-577 | `\|sym_mv & ~t_armed`, `sym_mv = own & mv_valid & grp==DG_L_SYM` (**valid**) |
| `threadIn.lineBeat` | 578 | `l_beat[ln]` |
| `threadIn.hPcWe`/`hStatWe` | 579 | `ht & o_trt==HO_TRT_PC/STAT` |
| `coreIn.runG`/`frz`/`rdata` | 217 | `run_g`, `frz`, `pm_rd[k]` |
| `coreIn.tReady..tW1h` | 552-559 | thread `tc`/`t_pc` bytes from the config image |
| `coreIn.guards` | 630-649 | `gv` (64-bit guard vector) |
| `coreIn.gLine` | 528 | `g_line[5k] = {l_pinb,l_pina,l_sp,l_in[2k+1:2k]}` |
| `coreIn.srcs` | 587-626 | `sv` (512-bit source vector) |
| `coreIn.lIn`/`lCap` | 522 | `l_in[2k +: 2]`, `l_cap[5k +: 5]` |
| `memIn.sReq/sWe/sAddr/sWd` | 476, 493 | `s_req`, `s_we`, `s_addr[11k+:11]`, `s_wd[8k+:8]` |
| `memIn.s0Word`/`s0WWord` | 494 | `s_word[0]`, `s_ww[31:0]` |
| `memIn.pWe`/`pSel`/`pData` | 485-486, 495 | `w_p0[14]`, `w_p0[13:8]` decode, `w_p0[7:0]` |
| `memIn.hSet`/`hWr`/`hAddr`/`hData` | 496 | `(h_wr\|h_rd) & in_data`, `h_wr`, `a_dat[10:0]`, `h_wd` |
| `memIn.ramWord` | 478, 500 | `dm_rd` (RAM output register) |
| `streamIn.cfg*` | 459-469 | `mode/rx, msb`, `cfg_start/len/mark` |
| `streamIn.adv`/`rxWe`/`rxBit` | 470-471 | `OPG(DG_SK,D_SADV)`, `OPG(...,D_SRX)`, `w[0]` |
| `streamIn.rewind`/`flush`/`clrStarved` | 472-473 | `(mctl & w[0]) \| (hctl & h_wd[0])`, `..[1]`, `hctl & h_wd[7]` |
| `streamIn.gnt`/`rdata` | 478 | `s_gnt[k]`, `dm_rd` |
| `streamIn.capEn`/`capPush`/`capRec` | 463, 172 | `cen & ~replay`, `cev`, `{dc, lvl[12:0]}` |
| `streamIn.replay*` | 442-443, 464-465 | `replay & ~frz & valid[0] & tick>=interval`, `late`, valid/word |
| `hostCmdIn`/`hostReadIn`/`hostWrIn` | 85-89 | `sck(s2[8])`, `sck_p(sp[8])`, `cs_n(s2[9])`, `mosi(s2[10])`, `rd_data(in_data)`, `h_land`, `h_land_d` |
| `hostReadIn.rdVal` | 728-788 | `rd_val` register-read decode |
| `cqIn.cw`/`coreIssue`/`isCfg` | 324-346, 139 | `w_cw`, `cw_drain`/`core_issue`, `cw_is_cfg` |
| `cqIn.clearSticky` | 694 | `c_wr_stk & h_wd[2]` (CWOVR) |
| `arbIn` (`Config`) | 136-148 | `cfg_host_now`, `cw_is_cfg`, `core_valid = cw_pending & ~frz & cw_is_cfg` |
| `dbgCtrlIn.h*`/`dWr*`/`cwData` | 660-670, 708-714 | `h_ectl..`, `h_ectl \| (cw_drain & cw_dbg_off==..)`, `cw_pending_data` |
| `dbgCtrlIn.replayValid`/`replayWord` | 438, 441, 465 | `s_replay_valid`, `s_replay_word[31:0]` |
| `dbgCtrlIn.rise`/`fall` | 75-76 | `rise`, `fall` |
| `dbgDigestIn` | 658-659, 704-706 | `d_wr_mctl`, `h_wd[0:1]`, `frz`, `{o_oe,o_out}` |
| `glueIn.wr*`/`hWd` | 652-657 | `c_wr_run/stk/irqen/db/hin/hst`, `h_wd` |
| `glueIn.wFlags`/`wHout` | 323, 348 | `w_flags = PICKG(DG_FLAGS)`, `w_hout = PICKG(DG_HOST_OUT)` |
| `glueIn.rdHin` | 314-320 | `rd_hin[k] = mv_en[k] & c_src==S_HOST_IN` (**source**) |
| `glueIn.conflict`/`memhaz`/`cwOverrun` | 160, 692-694 | sticky registers |
| `glueIn.tLate`/`tOvr`/`lTapmiss`/`sStarved` | 675 | sticky error vectors |
| `outCfgOf` / `outNextPins` / `oenNextPins` | 790-816 | `obind`, `sel`, `lut[idx]`, `oe[idx]`, frozen holds |
| `pinsOf` | 818-820 | `{o_out[13:8], irq, miso}`, `o_out[7:0]`, `o_oe` |
| `conflict` event / clear | 266, 692 | `\|(mv_valid & ~mv_win)`, `c_wr_stk & h_wd[0]` |
| `memhaz` event / clear | 674, 693 | `p_haz \| (\|rd_pd & ~p_rdy)`, `c_wr_stk & h_wd[1]` |
| `Contents` (cfg/pmem/dmem/mout/ram) | 202-212, 431-500 | SRAM macros + configuration cells (stated contract) |

The inputs that are *not* a direct RTL register slice are the configuration
decode inverse (`lineCfgOf`, `outCfgOf`), the program/data memory contents and
the host read decode; they are premises, not wiring bugs (see §3.4.1 and §7).

### 3.3 FINDING 5 — invariants and side conditions are proved

`Inv` (4 fields) is preserved unconditionally; `InvStepOpen` is gone:

* `reqNeThree` — `Mem.reqNext_ne`;
* `rrLt` — `Core.rr_next_lt_six` with `Core.rrOk`;
* `hostAgrees` — `HostPins.agrees_step`, after identifying
  `hostCmdIn s pin = (hostReadIn s pin).toHostCmd` (definitional);
* `staleRdy` — `staleRdy_step`: an unfrozen next land forces `pWe` (which clears
  `RDY`); a frozen next land is the invariant itself; a reset edge clears
  `land`.

`SideConds` is now a theorem, `sideConds (s) (pin) : SideConds s pin`:
`accHit_oneHotOrZero` (as before) and `frozenNoMove` (proved for every state and
pin from `Core.mvEn_zero`, whose `xa = xv && !frz` term is the gate the review
pointed at).  `chip_step_refines` and `trace_refines` no longer take it.

### 3.4 FINDING 6 — the relation, the pin projection and the trace

Done:

* `ChipRel` gained `hostReq` (exact slot relation) and `bank` (latch-image
  relation), and `cw`/`p0` are validity-guarded (`CwRel`, `P0Rel`);
* `pins_of_rel`;
* `trace_refines` is now proved **without** `hstep`/`h0`: it starts at
  `resetState` (`rel_reset : ChipRel (resetState cont) (absChip (resetState cont))`),
  proves `inv_trace` by induction (`inv_reset` + `inv_step`), and takes one step
  with `chip_step_refines`, which handles the reset edge internally via
  `chip_reset_refines_rel`;
* `chip_step_refines` is stated over the *current* related pair
  `ChipRel s m → ... → ChipRel (step s pin) (Machine.step m pin)`.

Not done, and why (see §3.4.1 below): the **premise field bodies** are still the
post-step comparison.  Restating them as current-state facts requires the
machine's per-cycle input records (`LineIn`, `ThreadIn`, `UnitsIn`, `StreamIn`,
`P0Move`, `CwMove`, the guard/source vectors), which `Machine.runStep` builds
inline — no projection functions exist to state "the cut input is the machine's
input".  The bridges (`Bridge.Line.step_bridge'`, `Bridge.Core.step_bridge`,
...) are stated in terms of those machine-side records, so without them the
field cannot be restated and re-derived.  Two groups *were* restated in relation
form (`p0`, `cw`, `streams` via `P0Rel`/`CwRel`/`AbsRelB`, and the new `hostReq`,
`bank`), which is what made the reset edge provable.  This is the remaining work
for the next round.

### 3.4.1 The active-cycle premises (16 fields)

| # | field | bridge | remaining wiring/side condition |
|---|---|---|---|
| 1 | `sync` | `SpiPins.step` vs `Machine.syncNext` | `{ui,uio}` byte split (in `ChipRel.sync`) |
| 2 | `lines` | `Bridge.Line.step_bridge'` | `absCfg (lineCfgOf …) = cfgView`, `PinAgree`, move/host `LineIn` |
| 3 | `threads` | `Bridge.Thread.step_eq` | `absInput (threadIn …) =` the machine's `ThreadIn`; `¬(accept∧disp)`, `¬(pause∧disp)` |
| 4 | `cores` | `Bridge.Core.step_bridge` | `Core.Rel` (guard/source tables, thread file, fetch word), `hJGTab`, `hld` |
| 5 | `units` | `Bridge.Units.*.abs_step` | `absIn` = the machine's `UnitsIn`; `OneHotOrZero` proved (`sideConds`) |
| 6 | `p0` | `Bridge.Mem.p0_step_eq` + `slot_step` | `mvOf (memIn)` = machine pointer move, `served`, landing interface; `req ≠ 3`/`staleRdy` are `Inv` |
| 7 | `streams` | `Bridge.StreamB.abs_step_unfrozen/frozen`, `cutReq_eq` | `absIn (streamIn)` = machine `StreamIn` (+ `BufRel` preservation, open in the bridge) |
| 8 | `host` | `Bridge.Host.linkRelR_step` | `hland`, `hreg`, `hlandD`, `hval`, `hquiet` (all current-state); could be restated this round but the load-bearing `hquiet` is not yet proved |
| 9 | `hostReq` (**new**) | `Bridge.Mem.slot_step` | the host slot update (`hostQNext/Y…`) vs `absSlot` |
| 10 | `ctrl` | `Bridge.Glue.ctrl_bridge` | `CtrlWr`, `ErrTerms`, `CtrlRegs` |
| 11 | `dbg` | `Bridge.Debug.dbg_step_bridge` | its twenty interface equalities |
| 12 | `cw` | `Bridge.CfgWrite.cfg_compose_bridge` | `h19`, `hcfg`/`hisCfg`, `hfrz`, `hreset` |
| 13 | `bank` (**new**) | latch-bank contract | byte image ↔ `Machine.Config` |
| 14 | `contents` (**new**) | machine determinism | `Machine.step m` vs `Machine.step (absChip s)` on the content groups (guard/source/`coreComb` congruence); a machine-vs-machine congruence, not a cut claim.  The reset edge proves it without premises |
| 15 | `out` | `Bridge.Glue.out_bridge` | `Env`/`CvRange`, packing equalities |
| 16 | `oen` | `Bridge.Glue.out_bridge` | as 15 with `oeNext` |

The original 13 are fields 1-8, 10-12, 15-16; the three additions are the two
new relation fields and the machine-determinism group for the contents.

## 4. RTL → cut → ChipCut

* **RTL = cut.** Unchanged: every emitted cut is the specification the generated
  checker proves the extracted RTL equal to (`*_check.py` + `*Equivalence.lean.in`);
  ChipCut calls the cuts' own `step`.
* **Wiring = closure.** `data/raw/lean_coverage_v4_20261121c/closure.txt`
  remains the trusted leaf closure (597 leaves / 6824 bits / 0 UNCLOSED).  The
  table in §3.2 is the human audit of each *input* on top of it; the ten
  mismatches it found were all in the input wiring, not in the closure.
* **Trusted chip-top decode interfaces** (unchanged): `cfgView`, `Machine.Util.hwAt`,
  `Bridge.Host.regRead`/`regVal`/`ramByte`.

## 5. Invariants

`Inv`: `req ≠ 3`; `rr < 6`; `HostPins.Agrees`; the stale-landing condition.
`inv_reset`, `inv_step`, `inv_trace` proved; no open obligations.  `BankRel` moved
from `Inv` into `ChipRel`.

## 6. Traces

See §3.4: `rel_reset` + `inv_trace` + `chip_step_refines`.  `hstep`/`h0` and the
`hinv`/`hsc` hypotheses are gone; the only hypothesis is the active-cycle
`Premises`.

## 7. Known deviations

Carried unchanged: frozen `RLVP`; AMBIG 19 (adjacent host configuration writes);
the stream replay-buffer relation (AMBIG 11/14); core `IR` capture without `load`
and `disp_e` outside dispatch; host `wdata`/`rackv` observability
(`LinkRelR`); `Mem` stale-`RDY` (`Inv`); `isCfgAddr` vs the live mask (AMBIG 4);
and the machine's configuration-image reset through the release window (AMBIG
1/2, the reason `BankRel` is mask-guarded rather than an unconditional byte
equality).

No new RTL/cut/machine disagreement was found by this audit: every mismatch was
in `Wire.lean`/`Step.lean` against the RTL, and was fixed on the ChipCut side.

## 8. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut          # exit 0, 24.4 s from removed ChipCut oleans
lake env lean ..\..\..\data\raw\lean_chipcut_v4_20261121b\axioms.lean   # exit 0, 2.5 s
cd ../../..
git diff --quiet HEAD -- src          # exit 0
```

Full command/exit-code/wall-time log: `data/raw/lean_chipcut_v4_20261121b/commands.log`.
