# W3 discharge: host decode and pin vectors (`HostPinWire.lean`)

File: `lean/Metronome/ChipCut/Discharge/HostPinWire.lean`
(namespace `Metronome.ChipCut.Discharge`), 2026-11-21 (round b: `hPhase`,
`host_open_regVal`, `host_open_quiet` closed).
Toolchain: Lean 4.35.0, core libraries only; `lake build` with
`-DwarningAsError=true` (Lean's own linters on; `linter.unusedVariables`,
`linter.deprecated`, `linter.unusedSimpArgs` off as allowed; the project's
`lakefile.toml` sets `moreLeanArgs = ["-DwarningAsError=true"]`).
Acceptance: `lake build Metronome.ChipCut.Discharge.HostPinWire` exits 0
(Lean build of the file alone 8.6 s / 9.0 s wall on the final content, 12.0 s
build on the first post-merge content; axioms dump 2.2 s; statements dump 2.3 s
— see `commands.log`).

Evidence: `data/raw/lean_chipcut_wire_hostpin_v4_20261121b/` —
`axioms.lean`/`axioms.txt` (no `sorryAx`; the only non-core axioms are the
pre-existing `bv_decide` certificate of `Bridge.Line.and_one_bne_zero_16` and
the `hostDbg_addr8/9/18/19` bit-vector certificates),
`statements.lean`/`statements.txt` (the exact statements of every delivered
theorem, `#check` output), `commands.log`, and the drafts `Scratch*.lean`,
`Section9.lean`.  No `sorry`, no `native_decide`, no edits outside this file,
this note and that directory.

Nothing else was edited: `git status` shows only
`lean/Metronome/ChipCut/Discharge/HostPinWire.lean`, this note and
the evidence directory (all other modifications are the other threads' work).

---

## 0. Exact statements of the delivered fields

`-DwarningAsError=true`, Lean 4.35.0.  `statements.txt` is the `#check` dump.

```lean
theorem wire_pinLvl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.pinView m.sync m.dbg).lvl = (pinAbs s).lvl

theorem wire_pinPrev (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (Machine.pinView m.sync m.dbg).prev = (pinAbs s).prev

theorem wire_pinAgree (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, Bridge.Line.PinAgree (pinAbs s) (lineIn s pin l.val)

theorem wire_hPhase (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hPhase = (Bridge.Line.absIn (lineIn s pin l.val)).hPhase

theorem wire_hCtl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hCtl = (Bridge.Line.absIn (lineIn s pin l.val)).hCtl

theorem wire_hTapmissClr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4, (ltLineIn m l).hTapmissClr =
      (Bridge.Line.absIn (lineIn s pin l.val)).hTapmissClr

theorem wire_hPC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).hPC =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hPC

theorem wire_hStat (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).hStat =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).hStat

theorem wire_beat (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ t : Fin 6, (ltThreadIn m t).beat =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).beat

theorem hcfg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ∀ l : Fin 4,
      (Machine.cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l.val)

theorem dbgWire_hdbg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Machine.Util.hwByte (machHw m) "DBG" 0 "DBG" =
      (if (freezeIn s pin).dbgWrite then some (freezeIn s pin).data.toNat else none)

theorem dbgWire_hESC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrEm0 && !(dbgCtrlIn s pin).hEm0 &&
      (dbgCtrlIn s pin).dWrEm1 && !(dbgCtrlIn s pin).hEm1) = false

theorem dbgWire_hRSC (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrRlv0 && !(dbgCtrlIn s pin).hRlv0 &&
      (dbgCtrlIn s pin).dWrRlv1 && !(dbgCtrlIn s pin).hRlv1) = false

theorem hostReq_open_strobe (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) :
    ¬(s.hostCmd.wr = true ∧ s.hostCmd.rd = true)

theorem host_open_quiet (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) (hspacing : host_sck_spacing s pin) :
    HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
      (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false ∧
        HostCmd.ackBit (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = false

theorem host_open_regVal (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg)
```

Two fields carry an extra hypothesis, each a *named* premise and not a
`Premises` field of the other side:

* `hostReq_open_strobe` takes `hpinv : HostPinInv s` (the new invariant of §1)
  and is the one-line projection `hpinv.wrRd`;
* `host_open_quiet` takes `hpinv` and the pin-timing premise
  `host_sck_spacing s pin` (§2.5).

---

## 1. Delivered theorems, per target field

Every statement below is *verbatim* the named hypothesis field (a `#check`
comparison is in `statements.txt`), quantified over `(s, m, pin)` with only
`hrel : ChipRel s m`, `hinv : Inv s`, `hact : runRst s pin = true` (plus, where
stated, the new invariant `HostPinInv` or the named pin-timing premise).

### `LineThread.WireAgree` (all over `ltLineIn`/`ltThreadIn`, `lineIn`, `threadIn`)

| field | result | theorem |
|---|---|---|
| `pinLvl` | **discharged** | `wire_pinLvl : (pinView m.sync m.dbg).lvl = (pinAbs s).lvl` |
| `pinPrev` | **discharged** | `wire_pinPrev : (pinView m.sync m.dbg).prev = (pinAbs s).prev` |
| `pinAgree` | **discharged** | `wire_pinAgree : ∀ l : Fin 4, PinAgree (pinAbs s) (lineIn s pin l.val)` |
| `hPhase` | **discharged** (was false before the `phWe` fix, §2.1) | `wire_hPhase : ∀ l, (ltLineIn m l).hPhase = (absIn (lineIn s pin l.val)).hPhase` |
| `hCtl` | **discharged** | `wire_hCtl : ∀ l, (ltLineIn m l).hCtl = (absIn (lineIn s pin l.val)).hCtl` |
| `hTapmissClr` | **discharged** | `wire_hTapmissClr : ∀ l, (ltLineIn m l).hTapmissClr = (absIn …).hTapmissClr` |
| `hPC` | **discharged** | `wire_hPC : ∀ t, (ltThreadIn m t).hPC = (absInput …).hPC` |
| `hStat` | **discharged** | `wire_hStat : ∀ t, (ltThreadIn m t).hStat = (absInput …).hStat` |
| `beat` | **discharged** | `wire_beat : ∀ t, (ltThreadIn m t).beat = (absInput …).beat` |
| `hcfg` (`premise_lines`) | **discharged** | `hcfg : ∀ l : Fin 4, (cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l.val)` |

Outside this task's scope: `sym`, `ctl`, `late`, `stop`, `dispatch`, `pause`,
`pauseDisp` (the move picks and the thread priority side condition).

### `StreamDbg.DbgWire`

| field | result | theorem |
|---|---|---|
| `hdbg` | **discharged** | `dbgWire_hdbg : hwByte (machHw m) "DBG" 0 "DBG" = (if (freezeIn s pin).dbgWrite then some (freezeIn s pin).data.toNat else none)` |
| `hESC` (single-drain exclusivity) | **discharged** | `dbgWire_hESC : (dWrEm0 && !hEm0 && dWrEm1 && !hEm1) = false` |
| `hRSC` (single-drain exclusivity) | **discharged** | `dbgWire_hRSC : (dWrRlv0 && !hRlv0 && dWrRlv1 && !hRlv1) = false` |
| `hostctl` (`StreamWire`) | **open, out of scope** | another task; §2.3 |

(`hESH`/`hRSH`, the *other* two "both bytes" fields, were not in the assignment:
they are host-byte-1 × drain-byte-0, which a single drain does not exclude —
they additionally need host-write/drain mutual exclusion.)

### `MemHostCfg`

| field | result | theorem |
|---|---|---|
| `hostReq_open_strobe` | **discharged** under `HostPinInv` | `hostReq_open_strobe : ¬ (s.hostCmd.wr = true ∧ s.hostCmd.rd = true)` |
| `host_open_quiet` | **discharged** under `HostPinInv` + `host_sck_spacing` | `host_open_quiet` |
| `host_open_regVal` | **discharged** | `host_open_regVal : regVal (absChip s) (cfgView s.cont.cfg) = regVal m (cfgView m.cfg)` |

### The new invariant `HostPinInv`

```lean
structure HostPinInv (s : State) : Prop where
  wrRd   : ¬ (s.hostCmd.wr = true ∧ s.hostCmd.rd = true)
  wrBitc : s.hostCmd.wr = true → s.hostCmd.bitc = 0
  rdBitc : s.hostCmd.rd = true → s.hostCmd.bitc = 0
```

* `hostPinInv_reset : HostPinInv (resetState cont)`.
* `hostPinInv_step : HostPinInv s → HostPinInv (step s pin)`.
  Both `wr` and `rd` are set only by `wrNext`/`rdNext`, whose last factor is
  `!isRd`/`isRd` (`step_wr_rd_excl`), and each is set only on a completing byte
  (`wrNext_completing`, `rdNext_completing`), which clears `bitc`
  (`bitcNext_completing`).  So `HostPinInv` is a genuine reachable-state
  invariant.

---

## 2. The three fields that moved this round

### 2.1 `WireAgree.hPhase` — *historical*: the field was false before a `Wire.lean` fix

**Historical witness (kept as evidence, no longer a live obligation).**
With the earlier `ChipCut/Wire.lean` text, `lineIn`'s `phWe` was
`(byte-0 strobe) ++ (byte-1 strobe)`, so the byte-0 strobe landed in **bit 1**
while `Bridge.Line.absIn` reads bit 0 as byte 0.  The witness files are
`Section9.lean` in the evidence directory:

* `hPhase_mach : hwAt (hwOf s) "LRT" 0 "PHASE" = some (0, 0x5A)` (the machine
  reads byte 0 of a `0x5A` write to `0x2410`),
* `hPhase_cut  : (absIn (lineIn s pin 0)).hPhase = some (1, 0x5A)` (the cut
  called it byte 1),
* `hPhase_false : ¬ (hwAt … = (absIn …).hPhase)` for the concrete command state
  `hPhaseState` (a completed write; `ltHw_eq` reduces the field's left side to
  the machine side).

* `hPhase_fixed : (hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE") = (absIn (lineIn …)).hPhase`,
  the *positive* companion check on the same concrete state: with the fixed
  `phWe` the two sides agree (compiled, `Section9_fixed.lean`).

**The fix and the new proof.**  The orchestrator edited `ChipCut/Wire.lean` to
`phWe := (byte-1 strobe) ++ (byte-0 strobe)`, i.e. bit 0 = byte 0, matching the
RTL (`project.v` 520 `h_ph_we = {byte1, byte0}`) and `Line.phF`.  The field is
now provable, and the remaining obligation was only the host map's geometry:

* `hostLocate_phase_byte {a l} (h : hostLocate a = some l) (hreg : l.reg = "PHASE") :
  l.byte < 2`, proved without any case split on a symbolic `hostLocate`: the
  `findSome?` over the block table is unrolled with
  `Array.exists_of_findSome?_eq_some` and the `ite_some` split of the two `if`s
  (`stride`/register match), then the finite table fact
  `phase_bytes_all` (`decide` over the 5-block table, in its `Array.all`-free
  `List.all` form; the `Array.all` form does not reduce) gives `bytes = 2`.
* `hwAt_loc` extracts the located record from a `hwAt (hwOf s) …` hit
  (`hwOf`, `Machine.Util.hwAt`, `Option.some.inj`).
* `phase_pack_any` is the pure packing fact: for `o = some (j, v)` with
  `j < 2` and `v = d`, the word `{byte-1 strobe, byte-0 strobe} ++ …` decodes
  back to `some (j, d)` (and `o = none` to `none`).
* `wire_hPhase` assembles these with `hwAt_val` (the write data byte) after
  `ltHw_eq`.

### 2.2 `hcfg` and `beat` — discharged (`absCfg_lineCfgOf`, `line_cfg_bounds`)

`hcfg` is `(cfgView m.cfg).lines[l] = Bridge.Line.absCfg (lineCfg s l)` with
`lineCfg s l = lineCfgOf ((cfgView …).lines[l]!)`.  `hrel.cfg` identifies the
two views and `getElem!_eq_get` turns the `!` into the entry, so the obligation
is `absCfg (lineCfgOf lc) = lc` for the decoded `lc`.

* Bounds: `bget_lt` (`UInt8`), `foldr_lt` (induction with `256 ^ len` as an
  `omega` atom), `bgetLE_lt`, then `cfgLE_two_lt`/`cfgLE_four_lt`; the
  `nbits`/`nbit` fields are bounded by `Nat.mod_lt`.  `line_cfg_bounds` packages
  the 19 bounds of `(cfgView c).lines[l]`, unfolding `Machine.Config.line`.
* Round trip: `lineCfgOf` packs `EDGE`, `T0EDGE`, `PINS`, `SNAP`, `HOLD` and the
  16/32-bit fields; `absCfg` reads them back with `slice`/`bitAt`.  The
  packing primitives are proved for the generic byte
  `p + 16q + 64·b1 + 128·b2` (`nbits04`, `nbits42`, `nbit6`, `nbit7`,
  `slice04`, `slice42`, `bitAt6`, `bitAt7` — each `cases` on the two flags, then
  `omega` after `Nat.shiftRight_eq_div_pow`/`beq_iff_eq`), plus the `PINS`
  (`slice04p`, `slice44`), `SNAP` and `HOLD` (`holdPin`, `holdLvl`, `holdTap`,
  `holdHen`) forms.  `absCfg_lineCfgOf` assembles the 24 fields with
  `Machine.LineCfg.mk.injEq`.
* `beat`: `Bridge.Line.beat_bridge` at `lc = absCfg (lineCfg s L)` with
  `hpin := wire_pinAgree`, after the pin-view congruence
  `lineComb_pin_congr` (`pinLvl_eq`, `pinPrev_eq`), `hrel.lines` for
  `m.lines[L]`, `hfrz` for the freeze sample, and `thread_line_lt`
  (`LINE` is two bits) for the index bound.

### 2.3 `StreamWire.hostctl` — not a state invariant (other task)

`streamIn`'s `rewind`/`flush` (`Wire.lean` 484-487) are
`(Strobes.streamCtlOf (gw …).data (strobe …) (hwIsSome s "SRT" k "CTL") (hwData s)).rewind`
(and `.flush`), i.e. **the host's `SRT.CTL` byte write ors into them**.  The host
command state `s.hostCmd` is a register the link sets from the pins, so a
*legal* cycle can have `hwIsSome s "SRT" k "CTL" = true` and a `CTL` data byte
with bit 0/1 set: no invariant over states can make the field unconditional
(the bridge's `hrew`/`hflush` really are cycle side conditions, as
`DISCHARGE_STREAMDBG_NOTES.md` §3.2 says).  No cut/machine disagreement is
involved: both readings apply such a rewind identically.  Not part of this
task.

### 2.4 `host_open_regVal` — discharged (`hostRead_eq`)

`Bridge.Host.regVal m cv` is the `.inl` value of
`Machine.hostRead m cv m.host.addr.toNat`, so the field is
`hostRead (absChip s) cv a = hostRead m cv a` at the related address
(`LinkRel.addr`, `hrel.cfg` for the two `cfgView`s) — that is
`host_open_regVal_of`.

`hostRead_eq` proves the congruence by `unfold Machine.hostRead`, the data-window
`if`, `split` on `hostLocate a`, then `split` on the 30-arm
`match l.blk, l.reg with` and one `simp_all only` set.  The lemmas it supplies:

* `ctrl_eq`: the **whole** `ctrl` record (`CtrlRel`'s twelve conjuncts;
  `absChip`'s record is literally the right-hand sides, so `simp only [absChip]`
  then twelve `←` rewrites);
* the five unit registers `hostRead` reads: `absChip_units_a/z/c/n/f`;
* the whole line and thread vectors `absChip_lines_eq`, `absChip_threads_eq`
  (`Vector.ext` of `ChipRel.lines`/`threads`, used by the `ERRSUM` arm's
  `lines.toList.any tapmiss` and `threads.toList.any late/ovr`);
* the existing pointwise congruences `vget_lines`, `vget_threads`,
  `vget_cores_xt/xv/rv/fpc`, `vget_streams_pos/bidx/starved`;
* `streams_any_starved`, the `ERRSUM` arm's `streams.toList.any starved`:
  whole stream vectors are **not** equal (`BufRel` guards `WB`/`NV`), so the
  two-element scan is done pointwise (`toList_any_two`, `vget_toList_any_two`,
  `vget_streams_starved` at `0`/`1`).

### 2.5 `host_open_quiet` — discharged with the named pin-timing premise

The field is
`HostCmd.completing (toHostCmd …) (hostReadIn s pin).toHostCmd = true →
(cmd).wr = false ∧ HostCmd.ackBit … = false`.  Split in two:

* **`wr` conjunction: `quiet_wr`** (state invariant).  `completing` implies
  `bitc = 7`, and `HostPinInv.wrBitc` gives `wr = false` (via
  `Inv.hostAgrees.bitc_eq`/`wr_eq`, which tie the cut's two host-link cuts
  together).
* **`ack` conjunction: `host_sck_spacing`** (named pin-timing premise).  The
  acknowledgement is `rack || hland`, with `hland = hostLand s =
  (cont.ramOwner == 4)`, a data-RAM landing.  A landing is issued by the
  arbiter one to two cycles after a host read request, and the request is only
  issued on a completing byte; `rack` is set by that request and held until
  the landing.  So neither can fall in the *completing* cycle of the next byte:
  `SPEC_V2` §9 bounds `SCK` at `clk/16`, i.e. at least 16 clock cycles between
  `SR` edges (the AMBIG 17/21 SCK-timing coincidence, as the `MemHostCfg`
  notes §3.3 say).  This is a fact of the waveform, not of an arbitrary state: a
  `clk/2`-rate `SCK` satisfies every `ChipRel`/`Inv` state while breaking the
  coincidence, so a named premise is the correct form:

  ```lean
  def host_sck_spacing (s : State) (pin : Machine.PinIn) : Prop :=
    HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
      s.hostRead.rack = false ∧ hostLand s = false
  ```

  `host_open_quiet` then closes `ackBit` by `unfold HostCmd.ackBit` and the two
  projections (`rack` = `s.hostRead.rack`, `hland = hostLand s`).

---

## 3. Proof landmarks in the file

* `protoPins_pinVec`: the machine's `protoPins sy.ui2 sy.uio2` is the cut's
  `Debug.Pins.pinVec` value (`P8..P12` = `s2[15:11]`, `P0..P7` = `s2[7:0]`),
  via `toNat_append'`, `toNat_trunc`, `toNat_ushr` and one `omega`
  (`(x/256 % 256)/8 = x/2048 % 32`).
* `pinLvl_eq`/`pinPrev_eq`: `ChipRel` fixes `sync`/`dbg` (`sync_eq`, `dbg_eq`),
  `Bridge.Debug.level_toNat`/`previous_toNat` and `protoPins_pinVec` close both.
* `wire_pinAgree`: `sel_pad13` and `Bridge.Debug.nbit_and_not`/`nbit_not_and`
  give the three `PinAgree` clauses; the out-of-range pin reads use
  `nbit_of_lt`.
* `ltHw_eq`: the machine's host write of the cycle is `hwOf s`
  (`Bridge.Host.hw_bridge` through `LinkRel`, `Inv.hostAgrees`).
* `hwByte_eq`/`hwAt_val`/`hwAt_loc`: `hwByte` is `some (write data)` exactly on
  the `hwAt` locator hit, and the byte index/block/instance/register are the
  `hostLocate` fields — this makes `hCtl`/`hPC`/`hStat`/`hdbg`/`hPhase`
  *geometry-free* (the only geometry needed is `hPhase`'s "`PHASE` is two
  bytes", §2.1).
* `wire_hTapmissClr` adds `Bridge.Line.bitAt_eq_nbit` to the `hwAt` hit.
* `dbgWire_hESC`/`hRSC`: `hostDbg` at window offset `D` forces the concrete
  address `0x2460+D` (`hostDbg_setWidth` + `bv_decide`), and
  `hostLocate (0x2468/0x2469/0x2472/0x2473)` is decided (`decide`, in the
  `Option.map` tuple form because `Machine.HostLoc` has no `DecidableEq`);
  then `!hEm0` rules out the host half of `dWrEm0`, leaving the drain, and the
  two drain addresses are distinct in a single cycle.
* `step_wr_rd_excl`, `wrNext_completing`, `bitcNext_completing`,
  `hostPinInv_step`, `hostPinInv_reset`, `quiet_wr`: the host command machine's
  one-cycle strobe discipline.
* `hostLocate_phase_byte`, `hwAt_loc`, `phase_pack_any`, `wire_hPhase`: §2.1.
* `hostRead_eq` and its lemmas (`ctrl_eq`, `absChip_units_*`,
  `absChip_lines_eq`, `absChip_threads_eq`, `streams_any_starved`), then
  `host_open_regVal_of`, `host_open_regVal`: §2.4.
* `host_sck_spacing`, `host_open_quiet`: §2.5.
* `bget_lt`/`foldr_lt`/`bgetLE_lt`/`cfgLE_two_lt`/`cfgLE_four_lt`,
  `line_cfg_bounds`, the packing primitives, `absCfg_lineCfgOf`, `hcfg`,
  `thread_line_lt`, `wire_beat`: the line configuration round trip and `BEAT`
  (§2.2).

## 4. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.HostPinWire        # exit 0 (warningAsError from lakefile)
lake env lean ..\..\..\data\raw\lean_chipcut_wire_hostpin_v4_20261121b\axioms.lean
lake env lean ..\..\..\data\raw\lean_chipcut_wire_hostpin_v4_20261121b\statements.lean
```

`commands.log` records the commands, exit codes and wall times.
