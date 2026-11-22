# Bridge notes: cut specs vs the whole-chip machine spec (item 4A)

Evidence dir: `data/raw/lean_bridge_v4_20261121/` (item 4A);
sections 3-4 as extended for item 4P: `data/raw/lean_bridge_v4_20261121c/`
(`axioms.txt`, `commands.log`).
Files: `Metronome/Bridge/{Thread,Mem,Host,CfgWrite}.lean`.  All check with
`lake env lean` exit 0 (Lean 4.35.0, core libs only, no `sorry`, no
`native_decide`); `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound` and, for theorems that go through the cut
specs' `bv_decide` certificates, those certificates
(`*._native.bv_decide.ax_*`, inherited from `HostCmd`/`CoreQueue`/this file's
existing `bv_decide` lemmas; no `sorryAx`).  The cut → RTL direction is the
existing `*_check.py` / `*Equivalence.lean.in` proofs; this file supplies the
cut → `Machine.*` direction so RTL = cut = machine for each component.

Composition: for a cut `C` with `abs : C.State → Machine.Sub` and
`absIn : C.Input → Machine.SubIn`, `C.step s i = Machine.comp (abs s)
(absIn i)` on active cycles; the machine's global reset (`Chip.resetStep`)
is the cut's `resetN = false` branch (each component's reset map is stated).

---

## 1. Threads — `Bridge/Thread.lean`

**Map.** `absState` copies `pc, en, ready, running, armed, late, ovr` one for
one.  `absInput` builds `Machine.ThreadIn`:

| machine field | cut input |
|---|---|
| `trig` | `Thread.trig s i = en && (ev \|\| db)` |
| `beat`, `late`, `stop` | `lineBeat`, `lateSet`, `stop` |
| `dispatch` | `disp` |
| `pause` | `some npc` iff `pause` |
| `hPC`, `hStat` | `some hD.toNat` iff the strobe, else `none` |
| values | `BitVec.toNat`; the machine's `bv 8` is the identity (`bv_toNat`) |

**Theorems.** `pc_bridge`, `en_bridge`, `ready_bridge`, `running_bridge`,
`armed_bridge`, `late_bridge`, `ovr_bridge` (field equalities), assembled by
`step_eq`; `step_reset_eq` (reset), `abs_reset`; `bitAt_eq_nbit` (the cut's
RTL-shaped bit extractor is the machine's `nbit`); `trig_refines` (the cut's
abstract `ev`/`db` are `trigEvent` and `DB[t]` under the `!FRZ` gate) and
`trig_frozen`.

**Side conditions.** `hacc_disp : ¬(accept ∧ disp)` and
`hpause_disp : ¬(pause ∧ disp)` — the two orderings SPEC_V2 leaves implicit
(the cut gives `disp` priority for `READY` and `pause` priority for `RUNNING`,
the machine the opposite).  On a legal cycle `pickThread` only dispatches a
`ready` thread (no trigger is accepted) and a pause targets `XT` while a
dispatch picks a not-running thread, so both are unreachable, not disagreements.

**Disagreements.** None.

---

## 2. Data RAM — `Bridge/Mem.lean`

**Map.** `absP0 : Mem.State → Machine.P0St` (`ptr, dat, rdy, land` directly;
`landRdy ↔ !stale`, observed only when `land`); `reqOf` maps
`req : BitVec 2` + latches to `PReq` (`0→none, 1→fetch, 2→write`; 3→none,
unreachable).  `absSlot` maps the host slot to `HReq`.  Inputs: `mvOf` builds
`P0Move` from `pWe/pSel/pData`; `served = grantP0`; `landNow/ramOut/lane` are
the chip's RAM-output plumbing.

**Theorems.**
`ptr_bridge`, `req_bridge`, `rdy_bridge`, `dat_bridge`, `land_bridge`
(P0 fields), `p0_step_eq` (assembly), `reqAddr_bridge`, `reqData_bridge`
(write latches), `arbiter_eq` (machine priority arbiter = the cut's
`servedIndex`, including "host only while frozen"), `slot_step` (cut host slot
= `slotStep`), `hostNext_slot` (`Host.hostNext` uses the same `slotStep`),
`hLand_next`/`hLane_next` (host landing strobe/lane), `absP0_reset`;
`p0_fetch_req`/`p0_write_req` identify `Machine.p0Req` with the cut's
`mAddr`/`mBe` fetch word/lane and write byte (the requests `ramAccess`
consumes), and `p0_write_addr` proves the byte `ramAccess` writes is the
`mAddr`/`mBe` address (`4*(a/4)+a%4`).  Numeric `BitVec ↔ Nat` plumbing is
proved (`ptrHigh_toNat`, `wordAddr_toNat`, `byteAt_eq_bv`, `al_eq`, `ah_eq`,
`add_one_eq`, …).

**Side conditions.**
* `req ≠ 3` — unreachable (`Mem.stateAt_req_ne_three`).
* `hstaleRdy : land = true → landRdy = false → rdy = false` — a cut invariant:
  a request move in the serve cycle already cleared `RDY` (§9a.3), and the
  machine writes `RDY' = !stale` unconditionally while the cut holds `RDY`.
* `dat_bridge` takes `hlandNow`, `hramOut`, `hlane`: the chip's
  `ramOwner == 3`, `ramOut`, `ramLane` are the cut's `land && !frzd`,
  `ramWord`, `landLane` (interface, not a cut disagreement).

**Disagreement/caveat.** `dat_bridge` and the lane live at the chip level in
the machine (`State.ramOwner/ramLane`), not in `P0St`; the bridge names that
interface explicitly.  The `stale` bit itself is a don't-care outside `land`
(`rdy_bridge` is the observable statement).  No SPEC clause is read two ways.

---

## 3. Host link — `Bridge/Host.lean`

**Map.** `pinOf` maps the cut's sampled pins to `PinView`
(`csn = csN`, `sck = sck`, `sckRise = sck && !sckPrev`, `mosi = mosi`);
`pinOfR` is the same map for the `HostRead` inputs (its `HostCmd` projection
carries the pins).  `LinkRel s m` relates the cut's `HostCmd.State` to the
machine's link state in a chip state `m`:

| cut | machine | note |
|---|---|---|
| `phase` | `phaseOf m.host` | see below |
| `bitc` | `m.host.nbit` | |
| `rx` | `m.host.rx.toNat % 128` | the machine keeps eight bits (`byteIn_eq`) |
| `cmd` | `m.host.cmd` | `cmd = 0 ↔ cut cmd ∉ {0x02, 0x03}`; `cmd ≠ 3` (`cmdZero`, `cmdNe`) |
| `isRd` | `m.host.cmd = 2` | |
| `addr` | `m.host.addr` | |
| `wr` | `m.host.wPend` | |
| `wdata` | `m.host.wData` | **only while `wr`** (the machine tracks the shifting byte) |
| `rd` | `m.host.rPend` | |
| `rack` | `m.host.ldV` | |

`LinkRelR s cmd m` extends `LinkRel` to the read-response registers of
`HostRead`:

* `tx`: `s.tx = m.host.tx` (the shift register MISO comes from);
* `rackv`: `s.rack = true → s.rackv = m.host.ldD` — **conditional**, because the
  machine keeps the register-read value in `ldD` only in the cycle that loads
  `TX`, while `HostRead.rackv` samples `rdVal` every cycle.

The phase register is *relational*: `phaseOf` is the cut's byte state as a
function of the machine's `(nbyte, cmd)` —

* `CMD` ↔ `nbyte = 0`;
* `IGN` ↔ `1 ≤ nbyte` with `cmd = 0` (the machine has no `IGN` state: it walks
  `nbyte = 1, 2, 3` while ignoring the transaction);
* `AH`, `AL`, `DATA` ↔ `nbyte = 1, 2, 3` with `cmd ≠ 0`.

**Theorems.** `linkRel_reset` (power-on); `linkRel_step` assembles one step:
`phase_step` (the phase correspondence above, including the `IGN` case and the
machine's `cmd` decode at the command byte), `nbit_step` (`bitc = nbit`, via the
existing `nbit_bridge`), `rx_step`, `cmdZero_step`, `cmdNe_step`, `isRd_step`,
`wr_step`, `wdata_step`, `rd_step`, `rack_step`, `addr_step`. Supporting
formula lemmas characterise each machine register either by a "hold" formula (no
completed byte: `cmd_hold`, `wP_hold`, `rP_hold`, …) or by a per-byte "complete"
formula (`cmd_complete_zero`, `wP_complete_data`, `rP_complete_low`,
`addr_high`, `addr_low`, …), plus the byte-append arithmetic
(`append_byte`, `trunc_toNat`, `shr8_toNat`, `addr_if_bv`).

**Response path** (`HostRead`): `linkRelR_reset`; the `TX` chain is split into
independent lemmas so the shift and load cases do not interact —
`cut_tx_noshift` (the cut's later load/hold chain), `mach_tx_csHigh`,
`mach_tx_csLow`, `mach_tx_noshift` (the machine's), `mach_tx_shift`,
`tx_shift_bridge` (`x <<< 1 = bv 8 ((x.toNat * 2) % 256)`), `ackv_bridge` (the
byte a landing loads: the waiting register read or the RAM lane) and
`ack_bridge` (the cut's `ack` is the machine's `ldV || ramOwner == 4`) —
assembled by `tx_step`; `rackv_step` (the waiting value), and `linkRelR_step`
which preserves `LinkRelR` under the same interface hypotheses as
`linkRel_step` plus `hlandD` and `hval` below.

**Observable outputs.**

* `hw_bridge`: the host write the machine issues in a cycle is exactly the cut's
  strobe, address and byte —
  `(hostNext …).2 = if s.wr then some ⟨s.addr.toNat, s.wdata.toNat, hostLocate …⟩ else none`.
* `read_req_bridge`: a read the cut requests at a data-RAM address
  (`ramRead = true`) becomes the machine's `HReq.read` request at the address
  `Machine.hostRead` returned (an `∃` over that payload, so the byte-address
  offset arithmetic is not needed); together with `regRead`/`ldV_eq` this fixes
  the register-read side as well (`ldV = rPend && regRead`).
* MISO: `miso_bridge` proves the machine's `bit m.host.tx 7` is the cut's
  `bitAt s.tx 7` (`bit_seven_eq_bitAt`, with `nbit_eq_bit_seven` and
  `bitAt_eq_nbit_seven`), and `miso_pin_bridge` reads that through
  `Machine.pinsOut`: `uo_out[0] = b2n (bitAt s.tx 7)` (`pinsOut_miso`).

**Side conditions** (all named in `linkRel_step`):

* `hland : (m.ramOwner == 4) = i.hland` — the cut's `hland` input is the chip's
  host RAM landing (an interface equality, as in `Bridge/Mem.lean`).
* `hreg : i.rdData = !regRead m cv` — the cut's `rdData` input is the machine's
  test "this read is not a register read".
* `hquiet : completing → wr = false ∧ ackBit = false` — a completing cycle
  carries no write strobe and no acknowledgement. This is a cut invariant (the
  strobe is the cycle *after* a data byte, and `rack`/`hland` are one-cycle
  pulses that cannot overlap an address byte), spelled out rather than proved.
* `hlandD : i.hlandD = ramByte m` — the cut's landing byte is the machine's RAM
  output lane (`bv 8 (nbits m.ramOut.toNat (8 * m.ramLane.toNat) 8)`); the RAM
  service contract is an interface premise (as in `HostRead`).
* `hval : i.rdVal = regVal m cv` — the cut's `rdVal` input is the machine's
  `hostRead` of this cycle (`regVal`, `bv 8` of an `.inl` value and 0 for a
  data-RAM read).

**Disagreements.** None in the behaviour.  The `cmd = 3` value is excluded by
`cmdNe` (the machine only latches `0, 1, 2`), and `wdata` is conditional
because the machine overwrites `wData` with the shifting byte every cycle while
the cut holds it; the two agree whenever the byte is used (`wr`).  `rackv` is
conditional in the same way: `rackv_witness` is a kernel-checked witness (a cut
state with `rackv = 0x5A` and no acknowledgement satisfies `LinkRelR` against
the power-on machine state, whose `ldD = 0`) that `rackv = ldD` cannot be
asserted outside the acknowledgement cycle.  It is unobservable: the cut reads
`rackv` only while `rack`.

**Gaps.** `Host.ctrlNext`'s mailbox/`RUN`/`IRQEN` registers are still not
bridged here (they are other cuts' bridges).  The `hquiet` hypothesis and the
`hlandD`/`hval` interface equalities are stated, not derived from `LinkRel`.

---

## 4. Configuration write — `Bridge/CfgWrite.lean`

**Queue map** (unchanged): `absCw : CoreQueue.State → Machine.CwSt` maps
`addr↔cwa`, `pending↔cwv`, `pendingAddr↔cwqa`, `pendingData↔cwqd` and pins the
bank port quiet; `mvOf` maps the 15-bit `CW` group to `CwMove`; `queue_fields`,
`overrun_bridge`, `cwNext_ovr_false`, `absCw_reset` and `frozen_witness` are as
before.

**Arbiter map.** The cut's nine-bit `Config.Write.addr` is the bank *window
offset*; a machine address is the full host address:

* `offOf a = bv 9 a` (offset of address `a`), `addrOf o = 0x2000 + o.toNat`
  (`0x2000 = LINE_BASE = CFG_LO`), with `offOf_addrOf : offOf (addrOf o) = o`.
* `cfgIn q hostCfg : Config.Input` is the arbiter cut's input in a cycle of the
  machine: `resetN = true`, `hostValid = hostCfg.isSome`,
  `host = ⟨offOf a, bv 8 v⟩`, `coreValid = q.pending && isCfgAddr q.pendingAddr`,
  `core = ⟨offOf q.pendingAddr, q.pendingData⟩`. It is the *machine's*
  `isCfgAddr` (its live configuration map) that decides "configuration
  address"; the RTL's narrower `cfg_address_is_live` (`md2_map.vh`) is discussed
  below.
* `cwOf q c : Machine.CwSt` joins the queue (`absCw`) with the arbiter state:
  `bwp = c.previousWrite`, `hh = c.heldValid`, `hha/hhd = addrOf held`,
  `bpa/bpd = addrOf staged`.
* `coreDrain cw hostCfg` restates the `coreDrain` let of `Machine.cwNext`: the
  queued core write is performed iff no held host write, no host configuration
  write, and no `BWP` interlock.

**Theorems.** `absArb_zero` (the cut's zero arbiters map to the machine's zero
bank port up to `addrOf 0`). `arbiter_bridge` — with no host write arriving
while a held write waits (`h19`):

* `bankWrite = performed.isSome`;
* every performed write `some (a, v)` is the cut's bank write at the window
  offset: `bank = ⟨offOf a, bv 8 v⟩` (so the cut's offset is `a - 0x2000` for a
  full address `a`);
* `next.previousWrite = st.bwp`, `next.heldValid = st.hh`;
* `coreIssue = coreDrain` — the §13.1 arbiter's grant is exactly the machine's
  condition for performing (and draining) the queued core write.

`bv8_toNat` is the byte `toNat` plumbing.

**Disagreement — a new host write while `HH` is pending (AMBIGUITIES #19).**
`adjacent_host_witness`: with `heldValid = true` and a host write arriving in the
same cycle, the cut performs the held write and *drops* the new one
(`next.heldValid = false`, `held` keeps the old address `5`), while the machine
performs the held write and *holds* the new one (`hh = true`,
`hha = bv 16 (addrOf 7)`). Clause §13.1 (the held write is performed before the
new one is considered); the cut's reading is the RTL's (its
`adjacent_host_can_drop` states the same drop), the machine's reading is written
in its `AMBIGUITIES.md` #19 and called unreachable at SPI byte spacing.
`arbiter_bridge` is stated under `h19`, so the agreeing fragment is proved.

**The live-byte mask.** The 9-bit window offset is masked twice in the RTL: the
bank's per-bit `MASK` (`md2_cfg_bank.v`) blanks bits without a latch, and
`cfg_address_is_live` (`md2_map.vh`) rejects the unimplemented gaps and
`OUT[8..13].OE`. `Machine.Config.isCfgAddr` is the machine's map; `AMBIGUITIES.md`
#4 records that it *accepts* `OUT[8..13].OE` (a configuration write that reaches
the bank port but decodes to nothing) where the RTL's live mask rejects the
address entirely. The arbiter bridge is therefore relative to the machine's
`isCfgAddr`; the mask difference is an RTL/machine reading difference on the
machine side (no cut disagreement), so no Lean witness is given for it — the
RTL side is a Verilog constant.

**Gaps (updated).** The staged/`bpa` and held/`hha` payload relations and the
queue/arbiter composition are now stated and proved (below); the remaining
`Config.step`'s `staged.addr` update is still the same unobservable difference.

### 4a. The bank-port payloads

**The window lemma.** `isCfgAddr_list` restates `Machine.Config.isCfgAddr` on the
block list (`Array.any` cannot be reduced by the kernel); `blockOk_all` is the
block table's interval check, kernel-reduced with `decide` (no
`native_decide`), and `isCfgAddr_window` derives `0x2000 ≤ a < 0x21E0` from an
accepted address.  Hence `addrOf_offOf_cfg`/`addrOf_offOf_window`: for a
configuration address (or any address in the window) `addrOf (offOf a) = a`.

**Theorems.**

* `staged_bridge` — when the machine performed `some (a, v)`, the cut's stage is
  `⟨offOf a, bv 8 v⟩` (`Config.stage_captures` plus `arbiter_bridge`).
* `performed_window` — a performed write is a window address
  `0x2000 .. 0x2200`: the held `HH` write (a 9-bit offset plus the base), a host
  write at a configuration address (`hcfg`), or the queued core write at a
  configuration address.
* `bpa_of_performed`, `staged_bpa` — on a performed cycle the machine's
  `bpa`/`bpd` (full address and byte) are `bv 16 (addrOf staged.addr)` and
  `staged.data`.
* `held_bridge` — when the machine holds a host write (`hh = true`), `hha`/`hhd`
  are `bv 16 (addrOf held.addr)` and `held.data`; under `h19` the cut's
  `heldValid` and the machine's `hh` coincide (`arbiter_bridge`).
* `payload_bridge` packages the three payload statements (offset form,
  machine `bpa`/`bpd`, held `hha`/`hhd`) under `h19` and `hcfg`.

**Side condition — `hcfg`.** A host configuration write is a configuration
address: `hostCfg = some (a, v) → isCfgAddr a = true`.  In the chip step this is
`hwIsCfg` (`Machine.Chip.runStep` passes `hw` to `cwNext` only when
`Config.isCfgAddr w.addr`); the cut's nine-bit offset is only the low nine bits
of the machine address, so `addrOf` recovers it exactly when the address is in
the window.

**Disagreement — a representation difference when nothing is performed.**
`staged_idle_witness`: with an empty queue and nothing performed the cut's stage
still holds the core payload (`staged.addr = offOf 0x2010 = 0x10`) while the
machine zeroes `bpa`/`bpd`.  The machine's bank applies a stage only on `BWP`
(`Machine.cfgNext`), and the cut's stage only matters when `staged` is delivered,
so this is unobservable; it is why the payload theorems are stated on a
performed/held write rather than unconditionally.

### 4b. The queue and the arbiter composed

`drain_bridge`: with `i.coreIssue` the arbiter's `coreDrain` (and the adapter's
decode equality `hisCfg : i.isCfg = isCfgAddr (CWQ.ADDR)`), the cut's
`CoreQueue.drain` is the machine's internal drain condition.  Without `hisCfg`
the two differ when the decode leaf and the machine's map disagree.

`queue_fields_arb` is `queue_fields` for the free `coreIssue`: the machine's
queue registers (`cwa`, `cwv`, `cwqa`, `cwqd`) after `Machine.cwNext (cwOf q c)
hostCfg (mvOf i) false` are the cut's after `CoreQueue.step q i`.

`cfg_compose_bridge` composes the two cuts against one machine step:

* the queue registers are `queue_fields_arb`;
* `mach.st.bwp = arb.next.previousWrite` and `mach.st.hh = arb.next.heldValid`
  (the reverse direction of `arbiter_bridge`);
* `arb.coreIssue = coreDrain (cwOf q c) hostCfg` — the arbiter's grant is the
  machine's drain condition, so feeding it to the queue is the machine's
  composition.

**Side conditions.** `hreset`, `hfrz = false` (the machine's `cwNext` takes the
freeze flag; the frozen cycle is not part of this step), `h19` (AMBIGUITIES
#19), `hisCfg` and `hcore`.

### 4c. Remaining gaps

* The `hcfg` gate and the `hisCfg` decode equality are interface premises (the
  chip step's `hwIsCfg` and the adapter's `cw_is_cfg`); the machine's
  `isCfgAddr`/the RTL live mask difference (AMBIGUITIES #4) is unchanged.
* `cfg_compose_bridge` is a one-step theorem; the multi-cycle bank-port
  discipline (§1 W+2 visibility, `Machine.cfgNext`) is not composed here.


---

## Reproduce

```
cd code/tests/lean
lake build Metronome.Bridge.Host Metronome.Bridge.CfgWrite     # -DwarningAsError=true
lake env lean Metronome/Bridge/Host.lean
lake env lean Metronome/Bridge/CfgWrite.lean
```

`#print axioms` commands and output: `data/raw/lean_bridge_v4_20261121c/`
(`axioms.txt`, `commands.log`; the generated `#print axioms` file is
`data/raw/lean_bridge_v4_20261121c/scratch/Axioms.lean`).
