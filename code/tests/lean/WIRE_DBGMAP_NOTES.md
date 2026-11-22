# W5 discharge, rounds 2–4: the `DBG`-map byte geometry (`DbgMapWire.lean`)

Written 2026-11-22 (round 2 = per-leaf re-check after the orchestrator's
`Wire.lean` fix; round 3 = the drain decode packaged and the value fields made
unconditional; round 4 = the `RLV` value with the reachable, WV-guarded `WB`
hypothesis).
File: `code/tests/lean/Metronome/ChipCut/Discharge/DbgMapWire.lean`
(namespace `Metronome.ChipCut.Discharge.DbgMapWire`).
Evidence: `data/raw/lean_chipcut_wire_dbgmap_v4_20261122/`.

Acceptance: `lake build Metronome.ChipCut.Discharge.DbgMapWire` exits 0, Lean
4.35.0, core libraries only, `-DwarningAsError=true`.  Final content compile:
6.1 s (module), 6.5 s wall including lake (round 4); round 3: 6.9 s.
`axioms.lean` run: 2.6 s, exit 0.  `axioms.txt`: every delivered theorem depends
only on subsets of `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`,
no `bv_decide` certificate.  No `sorry`, no `native_decide`.

Nothing outside this file, this note and the evidence directory was edited.

---

## 0. The `Wire.lean` fix this round builds on

Cause 1 of round 1 was the cut model: `Wire.dbgCtrlIn.hEm0`/`hRlv0` used
`hwIsSome` (true for a host write of *any* byte of the register) while the RTL
compares the window offset (`src/project.v:662/664`,
`h_em0 = w_dbg & (o_dbg == HO_DBG_EMASK)`).  The orchestrator changed them to

```lean
hEm0  := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0
hRlv0 := byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0
```

and this round re-checks every leaf under that wiring.

## 1. Per-leaf result under the fixed wiring

| leaf | result |
|---|---|
| `dbgHmctl` | **proved** (`dbgHmctl`, round 1, unchanged) |
| `dbgHectl` | **proved** (`dbgHectl`, round 1, unchanged) |
| `dbgHEH` (host half of `EMASK`) | **proved** (`dbgHEH`) — new |
| `dbgHESH` (host-byte exclusivity, `EMASK`) | **proved** (`dbgHESH`) — new |
| `dbgHRH` (host half of `RLV`) | **proved** (`dbgHRH`) — new |
| `dbgHRSH` (host-byte exclusivity, `RLV`) | **proved** (`dbgHRSH`) — new |
| `dbgHEC` (drain half of `EMASK`) | **false** — `dbgHEC_false`, cause 2 only |
| `dbgHRC` (drain half of `RLV`) | **false** — `dbgHRC_false`, cause 2 only |

Round 3 leaves this table unchanged; it removes the obligations that the old
per-port shape left behind — the drain decode and the one-byte facts are now
proved (§3).

`dbgHEH`/`dbgHESH`/`dbgHRH`/`dbgHRSH` have the verbatim `OpenWiring`
statements, quantified over `(s, m, pin)` with `ChipRel`, `Inv`,
`runRst s pin = true`.  The two remaining refutations are `∃`-witnesses that
now use **only** cause 2: a host write and a drained core write of the *same*
register byte in one cycle (`ha = hq = 0x2468` for `EMASK`, `0x2472` for
`RLV`), with the byte-precise host strobes in place
(`wit_hwAt_host_emask0`, `wit_strobes…`).  On that state the machine's
`hwAt (machCw m) … = some (0, 0x3C)` while the cut's `coreOpt2 = none` (the
host wins byte 0, so no byte is "core-selected"), i.e. the two-`Option` /
one-combined-strobe mismatch of SPEC_V2 §13.1.

New machinery (all kernel-checked):

* `hostDbg_of_byteStrobe` / `byteStrobe_of_hostDbg`: a located byte `b` is a
  host write of the byte's window offset and conversely
  (`hostByteStrobe_emask0/1`, `hostByteStrobe_rlv0/1` state the four
  byte-precise equalities);
* `hostDbg_emask0/1_addr`, `hostDbg_rlv0/1_addr`: the four host writes pin the
  address (`0x2468/69`, `0x2472/73`), from `dbgOff_eq_addr`;
* `hwAt_two_lane`: the machine's located host byte decodes to the two-lane
  `if` form;
* `get the drained lane at `EMASK`/`RLV` (`wit_…`) for the witnesses.

## 2. Cause 2 is a statement shape, not a divergence

The machine's `dbgNext` applies the drained core byte first and the host byte
second (`byteWOf`), exactly SPEC_V2 §13.1 ("a host write wins").  The cut's
per-byte port does the same: the drained byte is written unless the host wins
that byte.  So the *register value* agrees in every cycle, including the
collision.  What fails is only the per-port decomposition
`hwAt (machCw m) = coreOpt2 p0 p1` (in a collision the host flag suppresses the
core byte even though the machine's drained `Option` exists).

`byteW2_value` proves the value equality for **every** combination of the two
host/drain byte strobes:

```lean
theorem byteW2_value (x : Nat) (hx : x < 2 ^ 13) (hwd cwd : BitVec 8)
    (h0 h1 d0 d1 : Bool) (hw cw : Option Machine.HostWr) (r : String)
    (hH : hwAt hw "DBG" 0 r =
      (if h0 then some (0, hwd.toNat) else if h1 then some (1, hwd.toNat) else none))
    (hC : hwAt cw "DBG" 0 r =
      (if d0 then some (0, cwd.toNat) else if d1 then some (1, cwd.toNat) else none))
    (h01 : h0 = true → h1 = false) (d01 : d0 = true → d1 = false) :
    bv 13 (byteWOf hw cw x r) =
      writeBytes (bv 13 x) ⟨h0 || d0, h0, hwd, cwd⟩ ⟨h1 || d1, h1, hwd, cwd⟩
```

`h0`/`d0` are the host/drain strobes of lane 0 (`h1`/`d1` of lane 1);
`h01`/`d01` say a single host write (or a single drain) targets one byte.  The
proof is a 9-case analysis (host ∈ {none,0,1} × drain ∈ {none,0,1}); the only
non-trivial step is that the core byte at lane `k` is overwritten by the host
byte at lane `k`, which is `setByte13_same`.

## 3. The register-value facts (the restatement proposal)

`StreamDbg.premise_dbg` consumes `DbgRel`, whose `EMASK`/`RLV` fields are the
register equations `(Machine.step m pin).dbg.emask = …` and `….rlv = …`;
`Bridge.Debug.emask_bridge`/`rlv_bridge` conclude exactly those values through
`dbgNext`.  So the six per-port leaves can be replaced by **two value-level
fields**:

```lean
/-- proposed `DbgWire` field 1 (replaces `hEH`, `hEC`, `hESH`) -/
dbgEmaskValue : (machDbgNext m).emask = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask

/-- proposed `DbgWire` field 2 (replaces `hRH`, `hRC`, `hRSH`; uses the
    existing `hwb`/`happly` fields) -/
dbgRlvValue : (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv
```

Both are delivered here, **unconditionally** in `ChipRel`/`Inv`/`runRst`
(+ `hwb`/`happly` for `RLV`), as `dbgEmaskValue_of` and `dbgRlvValue_of`
(round 3):

```lean
theorem dbgEmaskValue_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (machDbgNext m).emask = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask

theorem dbgRlvValue_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwb : (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv
```

They are thin wrappers over the round-2 `emask_value_of`/`rlv_value_of`, whose
named inputs are now all discharged:

* `hrel : ChipRel s m`, `hact : runRst s pin = true` (plus `hinv` for the host
  decode — the wrappers take `Inv s` because `dbgHEH`/`dbgHRH` do);
* `hH` — the host-lane decode.  **Discharged**: `dbgHEH` proves
  `hwAt (machHw m) "DBG" 0 "EMASK" = hostOpt2 (emaskPort0 i) (emaskPort1 i)`
  (`i = dbgCtrlIn s pin`), and `emask_hostOpt_eq` (new round 3) restates that
  `hostOpt2` value in the byte-strobe `if` shape that `emask_value_of` consumes
  (`rlv_hostOpt_eq` for `RLV`).  The bridge needs only
  `dbgCtrlIn.hEm0/hEm1 = byteStrobe … 0/1` (`rfl` under the fixed wiring) and
  the absorption `(hostStrobe || drain) && hostStrobe = hostStrobe`;
* `hC` — the drain-lane decode.  **Discharged** by the new two-lane lemmas
  `machCw_emask_lane` (`EMASK`, offs 8/9) and `machCw_rlv_lane` (`RLV`, offs
  18/19):

  ```lean
  theorem machCw_emask_lane {s : State} {m : Machine.State} (hrel : ChipRel s m) :
      Machine.Util.hwAt (machCw m) "DBG" 0 "EMASK" =
        (if (cwDrain s && (cwDbgOff s.cq.pendingAddr == ofNat 32 8)) then
            some (0, s.cq.pendingData.toNat)
         else if (cwDrain s && (cwDbgOff s.cq.pendingAddr == ofNat 32 9)) then
            some (1, s.cq.pendingData.toNat) else none)
  ```

  These are the two-lane analogue of the proved one-byte `machCw_hwByte_ectl`,
  with the same geometry: `machCw_eq hrel`, the `cwRuntimeTarget` decode
  (`cwRuntimeTarget_loc` for the located register; `machCw_runtime` packages the
  fact that a runtime drain target is always one of the three `DBG` registers
  with a byte below 2), `hostLocate_emask_off`/`hostLocate_rlv_off` for the
  offsets, and `isCfgAddr_false_of` at `0x2468/0x2469` (`0x2472/0x2473`) to show
  that a cut drain strobe forces the machine's drain condition `hC`
  (`emask_drain_imp_C`, `rlv_drain_imp_C`).  In the false branch, a strobe at
  either offset is impossible by `emask_drain_imp_C`/`rlv_drain_imp_C`, so both
  lanes are `none`; in the true branch, the located register is `EMASK`/`RLV`,
  the byte pins the address (`cwDrain_emask_addr`, `cwDrain_rlv_addr`), and both
  `if`s reduce by `decide`;
* `h01`, `d01` — one byte per source.  **Discharged** by `emask_host_01`,
  `rlv_host_01` (a byte-strobe `if` can only be at one lane) and
  `emask_drain_01`, `rlv_drain_01` (offsets 8 vs 9, 18 vs 19 are distinct);
* the `RLV` fact additionally takes the existing `DbgWire.hwb`/`happly` fields
  and reuses `Bridge.Debug.replayLevels_toNat`/`and_nbits13`, as
  `rlv_bridge` does.

The unchanged round-2 statements remain available and kernel-checked:
`emask_value_of`/`rlv_value_of` (explicit `hH`/`hC`/`h01`/`d01`) and
`byteW2_value` (the 9-case value lemma).  Exact statements of everything are in
`axioms.txt`.

### 3.1 Round 4: the unguarded `hwb` is false, the WV-guarded form is the one

B1 proved that the unguarded `hwb` is false at a reachable state
(`Bridge.StreamBuf.dbgHwb_unguarded_false`; a frozen landing with `WV = 0` puts
the word in the cut's `NB` but in the machine's `WB`) and that the true form is
guarded by `WV` (`Bridge.StreamBuf.dbgHwb_of_wv`, from `AbsRelB`).  This is
exactly what the `RLV` path needs: the machine reads its first replay slot only
when `apply` fires (`Metronome/Debug.lean:319`), and `apply` conjoins
`replayValid`, whose bit 0 is the cut's `WV`
(`ChipCut.Assembly.bitAt_replayValid`).  So the unguarded `hwb` is never needed,
and the consumers should carry the guarded hypothesis.  Delivered:

```lean
theorem rlv_value_of_apply {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hwb : (machApplyLate m).1 = true →
      (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    … (hH hC h01 d01 as in rlv_value_of) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv

theorem dbgRlvValue_of_wv (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwb : (streamAt s 0).wv = true →
      (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv
```

`dbgRlvValue_of` (unguarded `hwb`) is kept unchanged.  `rlv_value_of` keeps its
statement and is now a one-line wrapper over `rlv_value_of_apply` with
`fun _ => hwb`.  Supporting lemmas, all in this file (no new imports; importing
`Bridge.StreamBuf`/`Assembly` would be circular or unnecessary):

* `dbg_vget_streams_zero` — `vget m.streams 0 = m.streams[(0 : Fin 2)]`;
* `dbg_bitAt_replayValid` — bit 0 of `replayValid` is `(streamAt s 0).wv` (the
  local form of `ChipCut.Assembly.bitAt_replayValid`, which cannot be imported);
* `dbg_wb_of_wv` — `ChipRel.streams 0` + `BufRel.wb_of_wv` give the guarded `WB`
  equality directly (the inline form of `Bridge.StreamBuf.dbgHwb_of_wv`).

`dbgRlvValue_of_wv` derives the apply-conditional `WB` fact from `happly`: from
`apply = replay && !frz && valid && decide (…) = true` it extracts
`valid = bitAt replayValid 0 = true`, converts with `dbg_bitAt_replayValid` to
`(streamAt s 0).wv = true`, and applies the guarded `hwb`.  No reachability or
additional side condition is used beyond `ChipRel`/`Inv`/`runRst`.  The only
remaining hypothesis beyond those three is `happly` (an existing `DbgWire`
field), same as `dbgRlvValue_of`.

## 4. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.DbgMapWire        # exit 0
lake env lean ..\..\..\data\raw\lean_chipcut_wire_dbgmap_v4_20261122\axioms.lean
                                                         # exit 0, #check + axioms
```

## 5. Remaining work (outside this file's ownership)

1. Substitute the two value fields into `OpenWiring` (the assembler's `DbgWire`),
   replacing the six `dbg` leaves; use `dbgEmaskValue_of` and
   `dbgRlvValue_of_wv` (the WV-guarded field), not the unguarded `hwb` form.
   The two false witnesses (`dbgHEC_false`, `dbgHRC_false`) stay as regression
   inputs for the *old* per-port shape (same-byte host/drain collision at
   `0x2468`/`0x2472`).
2. Consumers that only need one register may use the value fields directly;
   `happly` remains the `RLV` side condition (an existing `DbgWire` field).  The
   unguarded `hwb` should be dropped from the reachable path
   (`Bridge.StreamBuf.dbgHwb_unguarded_false`).
