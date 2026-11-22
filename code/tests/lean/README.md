# Metronome v4 verification in Lean

The first proof covers the shared configuration write port in
[SPEC_V2 §13.1](../../../wiki/SPEC_V2.md#131-configuration-written-by-the-cores-cwal-cwah-cwd).
It uses the `u_cfg_arb` and `u_cfg_stage` instances in
[the chip top](../../../src/project.v) and the logic in
[md2_cfg_bank.v](../../../src/md2_cfg_bank.v). The second cut covers the host
write strobe and byte counter in [md2_host.v](../../../src/md2_host.v) and
discharges the first proof's `Config.SpacedHost` premise through the actual
chip-top `cfg_host_now` filter. The third cut closes the address decode that
the host filter previously left opaque: for every 16-bit address, the
elaborated host qualification `in_cfg & cfg_address_is_live(ha)` and the
elaborated core `cw_is_cfg` both agree with "the address is inside the
configuration window and the elaborated latch bank has a non-zero mask byte at
that offset". The same check ties the two arbiter address buses to that
offset: the host subtracts `CFG_LO`, the core takes the low nine bits, and the
window is nine-bit aligned and at most 512 bytes, so the nine-bit bus carries
the full offset. The fourth cut is the core pending-write queue of
[the chip top](../../../src/project.v): the `cw_addr` counter, the one-deep
`cw_pending` / `cw_pending_addr` / `cw_pending_data` entry and the sticky
`cw_overrun` flag against SPEC_V2 §13.1. It holds a queued write byte for byte
until it drains, drains it with the accepted address and byte, drops a `CW.D`
that cannot be accepted and sets `CWOVR`, and composes a queued configuration
write with the arbiter grant from `Metronome.Config`.

## Run the checks

With Python 3, Yosys and Elan's `lake` on PATH, run from the repository root:

```text
python code/tests/lean/verify.py
python code/tests/lean/verify.py --mutations
```

The project pins Lean 4.35.0 and uses Lean's bundled libraries. The RTL bridge
was tested with Yosys 0.70+190 from the local OSS CAD Suite. The full check
re-elaborates the current RTL every time. The mutation command also tests
spacing, priority, held address, held data, stage capture, the top-level
feedback connection, the host write gate, the host bit counter, the chip-top
host filter and five core-queue regressions: a missing drain clear, a wrong
latched address, acceptance while the entry is occupied, a drain without the
freeze gate, and a missing `CWOVR` clear. The address-decode cases add a
permissive line decode, a core-only address-bit swap, a non-live bank byte
that gains a latch, and a core arbiter address wiring change. All mutations
run on temporary copies of `src/`. Decode proofs whose generated Lean source is
byte-identical to an accepted case are reused within a run; the source hash is
still regenerated for every case.

In a Windows PowerShell session where the tools are installed at the project
defaults, add them to the session's PATH:

```powershell
$cad = "$env:USERPROFILE/tools/oss-cad-suite"
$env:PATH = "$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"
```

Run `lake build` from this directory to check the model and its proofs without
Yosys. To keep the generated Lean input, source hash and tool output, add
`--artifacts-dir build/lean-check` to the Python command. Use a fresh artifact
directory for each run. To replay a retained `baseline.lean`, run
`lake env lean -j1 -DwarningAsError=true <path-to-baseline.lean>` from this directory
after `lake build`.

## Whole-chip refinement (ChipCut capstone, 2026-11-22)

The per-module cuts below are composed into one chip model, `ChipCut.step`
([Metronome/ChipCut](Metronome/ChipCut)), wired as
[the chip top](../../../src/project.v) wires them. The model is related to the
Lean machine spec `Machine.step` ([Metronome/Machine](Metronome/Machine)) by
`ChipRel`. The headline theorem is in
[Assembly.lean](Metronome/ChipCut/Assembly.lean):

```lean
theorem trace_refines' (pins : Nat → Machine.PinIn) (cont : Contents)
    (tables : Tables) (initial : InitialConditions cont)
    (env : ∀ n, PinPremises (cutStateAt pins (resetState cont) n) (pins n)) (n : Nat) :
    ChipRel (cutStateAt pins (resetState cont) n)
            (machineStateAt pins (absChip (resetState cont)) n)
```

`pins_of_rel` turns `ChipRel` into equality of `uo_out`, `uio_out` and `uio_oe`
(including IRQ and MISO) at every sampled cycle. `trace_refines'_all` also
carries the capture-buffer and held-landing relations.

| Hypothesis group | Fields | Status |
|---|---|---|
| `Tables` (constant) | 8 decode tables: sources, guards, jump guards, destination kind, payload, FLAGS/P0/CW codes, ports, stream/line codes | Closed propositions over string-named tables. Lean cannot reduce the parsed names in the kernel, so each is checked by compiled evaluation (`decode_check_*.lean`, all 0 failures). Trusted. |
| `InitialConditions cont` | `ramOwner = 0`; `MaskedZero cont.cfg` (implemented `CFG_MASK` bits clear, as the RTL latches reset); config image size | Conditions on the start state. |
| `PinPremises` (per cycle) | `host_sck_spacing`; `stream_mode_quiet` | Pin/usage contracts, see Limitations. |

`trace_premises_satisfiable` and `trace_premises_satisfiable_active` prove the
hypotheses can be met. The first uses idle pins and zeroed contents. The second
releases reset, runs one active cycle in which stream 0 raises a fetch request,
then resets again. Everything else the composition needs is derived along the
trace, including the latch bank under the real 480-byte `CFG_MASK`
(`BankWire.lean`), the configuration-write release window (`WindowWire.lean`),
move-group packing and AMBIG 19 (`PremiseWire.lean`), and the stream, landing,
capture and invariants.

Check it with `lake build Metronome.ChipCut.Assembly` (warnings are errors).
`#print axioms trace_refines'` gives `propext`, `Classical.choice`,
`Quot.sound` and 96 `bv_decide` certificate axioms; both witness theorems use
only the first three. Evidence is in
`data/raw/lean_chipcut_final_v4_20261122/`.

**Trusted base:**
- Yosys elaboration of `src/`
- the Python RTLIL extraction and adapters
- the generated per-cut equivalences and structural checks
- the hand-written top-level wiring in `ChipCut/Wire.lean` and `Step.lean`
- the digital latch, clock-gate and SRAM-macro contracts
- native evaluation behind the `bv_decide` certificates
- compiled evaluation of the eight tables

Strict coverage (`coverage_check.py --strict`,
`data/raw/lean_coverage_v4_20261122b/`) shows 100 % of 8,962 cell occurrences
read by a cut or named structural check, 0 unclosed free leaves and 24/24 output
bits. Coverage identifies the source of each free leaf; it does not compare the
`Wire.lean` expression against the RTL net.

**Limitations:**
- The theorem is about sampled digital behaviour from the modelled reset state.
  It says nothing about silicon timing, and the witnesses do not show sustained
  operation.
- `host_sck_spacing` forbids a byte-completing SCK edge from coinciding with a
  register-read acknowledgement or a host data-RAM landing. This is stronger
  than the SCK ≤ clk/16 rate: the RAM-landing part depends on arbitration
  (S0/S1/P0 can delay host service). SPEC §9's 12-cycle service budget implies
  it, but the RTL gives no unconditional bound.
- `stream_mode_quiet` lets a stream's effective mode change only with no read in
  flight, no second replay slot and no pending byte (`LD = RQ = NV = PV = 0`
  before, `PV = 0` after). A simultaneous rewind does not excuse it. This is
  stricter than SPEC §9a.13, which only makes such a change unspecified until the
  next rewind. A settled startup (TX prefetch with `WV = 1` is allowed), host
  configuration, `RUN` and fixed-mode transfers are covered.

**Findings made by the composition proofs:**
- Eight wiring errors in the hand-written chip model, each fixed and each
  confirmed against `src/project.v`. The RTL was unchanged by all of them:
  - bus packers had item 0 high;
  - the bank was fed from the arbiter rather than the registered stage;
  - the core thread-select polarity was wrong;
  - the stream CAP parameter was set on both streams;
  - the PHASE byte strobes were in the wrong order;
  - a CFG write gated the shifter data write;
  - the replay-valid bit order was wrong;
  - the EMASK/RLV byte-0 strobes fired for any byte.
- One machine-spec transcription error: `RLVP` must hold while frozen. Fixed in
  `Machine/Debug.lean`; lockstep re-run 25/25 passed.
- Proved, unreachable or unobservable spec corners, each recorded with a
  witness: AMBIG 1/2, 11, 14 and 19.

Two independent read-only reviews checked the capstone (Codex gpt-6.2-sol).
The first found the earlier statement vacuous (the release-window premise was
false at reset) and the latch bank unmodelled. Both are fixed, and the second
review found no remaining blocker.

## Claims and assumptions

| Claim | Lean theorem | Conditions |
|---|---|---|
| The extracted transition matches the independent priority specification, including next state and 9-bit address / 8-bit data paths. | `rtlStep_eq_step` | All two-state values at the cut. Payloads are symbolic, including uninitialized registers. |
| The two transitions have identical state and outputs at any cycle. | `rtlStateAt_eq`, `rtl_trace_result` | Any finite prefix of the sampled input sequence, with the same initial state. |
| Two consecutive active cycles cannot both issue a bank write. | `rtl_trace_spacing` | A sampled reset first, then any host and core stimulus. Reset remains released across the two cycles being compared. |
| A host byte beats a core contender when the bank is ready. After a busy cycle, the held byte issues with the original address and data on the following active cycle. | `rtl_trace_host_service` | A sampled reset first and no adjacent host strobes. A reset can discard a pending byte. |
| An eligible core request uses the port when it is ready and neither host source needs it. An issued write loads the address/data stage and sets its strobe. | `core_granted`, `stage_captures` | Local grant premises and active reset release for capture. These facts transfer through `rtlStep_eq_step`. |
| The extracted host `wr`/`bitc` transition matches the SPI write specification for every state and input. | `Host.rtlStep_eq_step` | `st` and `is_rd` are free per-cycle inputs, so their own next-state equations are outside the cut. |
| A host write strobe implies the next bit count is zero, and a bit count other than 7 excludes a write strobe. | `Host.wr_next_bitc_zero`, `Host.bitc_ne_seven_excludes_wr` | Proven on the specification and transferred to the extracted equations. |
| Adjacent host strobes in cycles `n+1` and `n+2` are impossible for arbitrary sampled inputs. | `Host.trace_spacing`, `Host.rtl_trace_spacing` | Does not include cycle 0, whose `wr` is the arbitrary power-up value. A sampled reset edge leaves `Host.resetState`. |
| The chip-top `cfg_host_now` net is exactly `u_host.wr & in_cfg & cfg_address_is_live(ha)`, so `host_valid` implies the host write. | `Compose.chipHostValid_implies_wr`, `Compose.chip_host_valid_implies_host_wr`, Python exact-AND check | Structural check expands only scalar AND cells and treats the live decode as one leaf here; that leaf is covered by the decode cut below. Yosys elaboration and the adapter are trusted. |
| Adjacent chip-top `host_valid` samples are impossible from cycle 1 onward. | `Compose.host_valid_spacing` | Uses the host trace theorem; cycle 0 is covered by the reset-state composition below. |
| The host filter is spaced when the composed trace starts in the reset state, and the existing configuration service theorem then applies. | `Compose.spaced_of_top`, `Compose.config_host_service_from_top` | Cycle 0 is vacuous under `wr = false`; `Host.powerup_boundary_witness` shows the premise is needed. Host payload is symbolic; the decode site is now separately covered below. |
| The maximal runs of non-zero bank bytes are exactly the mask-byte indicator, and the emitted `liveBytes` vector equals "MASK byte is non-zero". | `Decode.runs_match_mask`, `Decode.liveBytes_eq_mask` | Kernel `decide` over all 480 offsets. `bankMask` is the `MASK` parameter of the elaborated `u_cfg` instance. |
| Interval membership in those runs agrees with the per-byte flag lookup for every address. | `Decode.maskLive_eq_byteFlag` | `bv_decide` over the 16-bit address. |
| The elaborated host qualification `in_cfg & cfg_address_is_live(ha)` equals the mask rule at every 16-bit address. | `Decode.rtlHostQual_eq_spec` | `rtlInCfg` and `rtlLive` are translated from the actual top nets; the Python adapter checks `cfg_host_now = u_host.wr & in_cfg & live`. |
| The elaborated core `cw_is_cfg` equals the same mask rule at every 16-bit address. | `Decode.rtlCoreLive_eq_spec` | The adapter checks that the `cw_is_cfg` net is a leaf of the arbiter's `core_valid` cone. |
| An accepted address's 16-bit window offset is below 512, and the core's low-nine-bit address is that offset's nine-bit value. | `Decode.offset_fits_nine`, `Decode.core_low_bits_are_offset` | `CFG_LO` is nine-bit aligned and the window span is at most 512. The adapter checks `host_addr = a_cfg[8:0]`, `a_cfg = ha - CFG_LO`, `core_addr = cw_pending_addr[8:0]`, and that the `in_cfg` span equals the bank `BYTES`. |
| Boundary and non-vacuity facts hold on the actual decoded nets: `0x2000` and `0x21D7` live, `0x201D` a hole, `0x20D0` a partial `0x03` byte, `0x21DF` inside `in_cfg` but mask-zero, `0x21E0` out of window, `0x1FFF` wraps below the base. | `Decode.first_live`, `Decode.last_live`, `Decode.hole_201D`, `Decode.partial_byte`, `Decode.host_tail_indexed_not_live`, `Decode.out_of_window`, `Decode.wrapped_below`, and the per-site `host_*`/`core_*` facts | Concrete kernel `decide`; the per-site facts use the translated nets. |
| The extracted core queue transition matches the independent SPEC_V2 §13.1 specification: address counter, pending flag, queued address and byte, sticky flag. | `CoreQueue.rtlStep_eq_step` | Every state value and the 15-bit picked CW group are symbolic; `frz`, `cfg_core_issue`, `cw_is_cfg` and the `CTRL.STICKY` clear leaf are free. |
| A queued write is held byte for byte until it drains; a drain delivers the accepted address and byte; a drain without acceptance empties the entry, so one accepted entry is delivered once. | `CoreQueue.trace_held_until_drain`, `CoreQueue.trace_drain_delivers_accepted`, `CoreQueue.trace_drain_empties` | No reset edge and no drain between acceptance and delivery. A reset discards a queued entry. |
| Every `CW.D` is accepted or sets `CWOVR`; a dropped write leaves the queued payload untouched; `CWOVR` is sticky until its documented clear. | `CoreQueue.accepted_or_overrun`, `CoreQueue.no_silent_overwrite`, `CoreQueue.overrun_sticky`, `CoreQueue.overrun_cleared` | Active cycle. The clear leaf is `c_wr_stk & h_wd[2]`; a simultaneous drop still sets the flag. |
| An accepted `CW.D` loads the counter value and write byte and increments the counter; `CW.AL`/`CW.AH` load one address byte and hold the other. | `CoreQueue.accept_loads`, `CoreQueue.accept_increments`, `CoreQueue.low_load`, `CoreQueue.high_load`, `CoreQueue.low_load_bytes`, `CoreQueue.high_load_bytes` | Active cycle. `CW.AL` wins when both codes decode. The byte identities carry a native certificate (see below). |
| A frozen queue keeps its entry and never drains; a concurrent `CW.D` is dropped and flagged. | `CoreQueue.frz_holds` | `frz` is a free per-cycle input in this cut; its own next-state belongs to the freeze cut. |
| A queued configuration write reaches the bank port with its original nine-bit address and byte under the arbiter's grant premises, and drains in that cycle. | `CoreQueue.queued_cfg_reaches_arbiter`, `CoreQueue.queued_cfg_drains` | Arbiter free (`heldValid = previousWrite = hostValid = false`), `core_valid = true`; the adapter checks `core_valid = cw_pending & ~frz & cw_is_cfg` and the arbiter payload connections. |
| A second `CW.D` while the entry is occupied and not draining is dropped and sets `CWOVR`; the same write into an empty queue is accepted. | `CoreQueue.overrun_witness` | Concrete kernel `decide`; shows the occupied-and-not-draining premise is needed. |

The state is sampled around a rising clock edge. With reset asserted at that
edge, the model clears the stage strobe before evaluating the arbiter, since
`we1` has an asynchronous clear. The arbiter's held-valid register clears
synchronously. The theorem abstracts the reset synchronizer and assumes an
assertion between sampled edges is represented by an input cycle with reset
low. The model's `adjacent_host_can_drop` theorem gives a concrete control
trace showing why the host-spacing premise matters.

The host cut uses the same cycle convention: `Host.stateAt inputs initial n`
is the register state during cycle `n`. Its local facts constrain the strobe
in cycles `n+1` and `n+2`; the pair in cycles 0 and 1 would involve the
arbitrary power-up `wr`, so the composition starts from `Host.resetState`
after the preceding sampled reset edge. `Host.powerup_boundary_witness` is the
concrete control showing why that premise is necessary.

## Proof boundary

Yosys elaborates the actual chip top and lowers the modules to RTLIL
cells. The Python adapter checks their clock, reset and point-to-point wiring,
including the stage-to-arbiter feedback, the stage outputs to the bank, and
`u_host` clock/reset/output connections. It then emits a Lean function from
the cells and register connections. Lean checks equality by Boolean case
analysis and reduction, then lifts that equality to traces by induction. The
check audits axiom dependencies. The configuration equivalence and trace
equality use none; the host equivalence uses Lean's standard `propext`,
`Classical.choice` and `Quot.sound`; the decode equalities add a documented
native certificate axiom. The queue equivalence `CoreQueue.rtlStep_eq_step` and
its trace lift use `propext` and `Quot.sound`; the byte-packing corollaries add
a per-theorem native certificate. The spacing and service corollaries use
`propext`.

For the host cut, `DffCone` indexes only the supported combinational shapes
(`$mux`, `$and`, `$or`, `$not`, `$eq`, `$ne`, `$add`, plus the decode's
`$ge`, `$lt`, `$sub`, `$shiftx` and `$logic_*`) and resolves the two register
inputs from `bitc` and `wr`. A reachable unsupported cell, a bus that cannot
be resolved to slices or assembled bits, a missing driver or a second register
driver fails the extraction.
`st` and `is_rd` are bound as free per-cycle inputs, which over-approximates
the real circuit and is sound for the safety properties. The chip-top check
expands `cfg_host_now` through scalar `$and` cells only and requires the
leaves `u_host.wr`, `in_cfg` and the live decode leaf, in that order. An OR or
bypass at the root therefore fails closed.

The address-decode cut translates the two decode cones and the `a_cfg`
subtraction from the actual top nets. It reads `CFG_LO` from that subtraction,
the window span from the `in_cfg` comparison, and the bank `MASK` parameter
from the specialized `u_cfg` module. The adapter checks that
`cfg_host_now = u_host.wr & in_cfg & live`, that `cw_is_cfg` is a leaf of the
arbiter's `core_valid` cone, and that the two arbiter address ports are exactly
`a_cfg[8:0]` and `cw_pending_addr[8:0]`. It also checks every bank byte against
the mask: a non-zero byte has one clock gate and exactly its masked latch set,
the gate is enabled by `we1` and an `addr1`-only select, each latch has the
expected data, output, reset and gate nets, zero bits and bytes are tied to
`q = 0`, and a zero byte has no gate or latch. The window must be nine-bit
aligned and no larger than 512 bytes; that is a checked precondition, not a
proved property of a future map. The gate's own address comparator is proved
by the latch-bank cut below.

The core-queue cut translates the five register inputs from the chip top. It
binds `rst_q`, the picked 15-bit `w_cw`, `frz`, `cfg_core_issue`, `cw_is_cfg`
and the documented clear leaves `c_wr_stk` and `h_wd` as free per-cycle inputs
(`DffCone.leaf`). A leaf may be a driven net: the whole-bus driver is dropped
and the net becomes an opaque input, which over-approximates the circuit and is
sound for the safety properties. A partial overlap with another bound bus fails
the extraction. The adapter checks `u_cfg_arb.core_addr = cw_pending_addr[8:0]`,
`core_data = cw_pending_data` and that the `core_valid` cone is exactly
`(cw_pending & ~frz) & cw_is_cfg` with a real `$not` on `frz`. The two
non-byte-aligned register shapes are supported directly: a bit may be read out
of a multi-bit cell output, and a scalar logic operand may be a slice of a
bound bus (translated to a one-bit comparison). Both extensions stay
fail-closed: an unknown cell, a missing driver or an unresolvable bus still
fails extraction. The queue equivalence itself needs no native certificate;
the byte-packing identities `pack_take`, `pack_low` and `pack_high` use
`bv_decide`, so `accept_increments` and the two `*_load_bytes` corollaries add a
per-theorem native certificate axiom like the decode cut. `rtlStep_eq_step`
uses only `propext` and `Quot.sound`.

The decode theorems that use Lean's `bv_decide` (the two full-address
equalities, the interval/flag equivalence and the offset bound) bit-blast the
goal and check a SAT certificate with Lean's native LRAT checker. `#print
axioms` on the equalities therefore shows a per-theorem `bv_decide`
native-certificate axiom in addition to `propext`, `Classical.choice` and
`Quot.sound`, and the runner checks that `sorryAx` is absent. The run/mask
theorems, the boundary facts and the structural checks are kernel reduction or
Python checks. The native certificate checker is the only trust added beyond
Yosys, the RTLIL adapter and the JSON parameter reader.

The trusted bridge is Yosys elaboration plus the Python RTLIL adapter and its
port mapping. It supports whole buses, contiguous slices, bit assembly of
permuted buses, scalar logic, equality, inequality, addition, subtraction,
unsigned comparison, indexed shifts, muxes and the register forms used by
these cones. Unsupported cells and connections fail the check. The
configuration cut starts at the arbiter's request ports and ends at the
latch-bank inputs. The host cut starts at the sampled `rst_n`, `sck`, `sck_p`
and `cs_n` module ports and ends at the next `wr`/`bitc` values; its
`st`/`is_rd` values are free. The core-queue cut starts at the picked CW group
and the free `frz`, `cfg_core_issue`, `cw_is_cfg` and clear leaves and ends at
the five register values; the arbiter grant that produces `cfg_core_issue` is
proved separately and composed. SPI framing and strobe spacing, core request
retention and overrun, payload content, latch visibility, the synchroniser
analog behaviour and physical timing each require separate evidence. Existing
v4 lockstep and Yosys induction remain independent checks.

**Elaboration defines.** The hardened flow sets `VERILOG_DEFINES =
["USE_IHP_SRAM", "USE_IHP_CELLS"]` (`src/config.json`). The data-RAM cut
(`mem_check.py`) elaborates with `-D USE_IHP_SRAM`, so it sees the IHP macro
boundary. The other cuts use the shared recipe without defines, which selects
the behavioural SRAM and cell models. The only `ifdef` regions in `src/` are
those cell and macro instantiations (`md2_cfg_bank.v` clock gate and latch,
`md2_dmem.v`/`md2_pmem.v` macros, `cells_behav.v`); the enable, select and
next-state logic the cuts prove sits outside them. The bank cut therefore
checks `cfg_lgcp_beh`/`cfg_dlhrq_beh` connections where silicon has
`sg13cmos5l_lgcp_1`/`sg13cmos5l_dlhrq_1` with the same pins; that the
behavioural models match the library cells is trusted (see
`src/cells_behav.v`). A change that moves proved logic behind one of these
defines would need the recipe updated.

## Latch-bank cut

The fourth structural cut proves the bank's per-byte clock-gate comparator and
the masked write contract (`bank_check.py`, `BankEquivalence.lean.in`,
`Metronome/Bank.lean`). `verify.py` runs it once on the baseline and, with
`--mutations`, on its five bank-specific mutants (evidence under
`<artifacts-dir>/bank/`); `bank_check.py` also runs standalone.

### What is checked

`bank_check.py` re-elaborates the design with the same Yosys recipe as
`verify.py`, then:

1. Runs the shared structural check (`verify.check_bank_mask`): every non-zero
   `MASK` byte has exactly one clock gate and its exact latch set, the gate is
   an AND of `we1` with an `addr1`-only selector, and each latch samples the
   matching `data1` bit, drives its `q` bit and shares the byte's gated clock.
2. Extracts the gate enable cone of **every live byte** as a Lean function of
   `(we1, addr1[8:0])`. Extraction is fail-closed: an unsupported cell, a
   register in the cone, an undriven or sliced net, or a second driver raises
   `UnsupportedRTL`. A small `DffCone` subclass decodes Yosys's one-bit
   `$logic_not`, which is how `addr1 == 0` is lowered.
3. Emits Lean that proves, per live byte `k`,
   `enable_k we1 addr1 = (we1 && addr1 == k)` at all 512 addresses and both
   strobe values (`enable{k}_spec`, `bv_decide`), and collects those `284`
   cones into one gate list with their theorems.
4. Proves the **whole family** from that list, without case analysis over the
   480 offsets: one list induction (`any_enable_spec`) turns "each cone is its
   own comparison" into "at index `k` the family opens exactly the gate at `k`
   and nothing else" (`enableAt_spec`), and one kernel reduction
   (`liveAt_addrOf`) ties the gate offsets to the non-zero `MASK` bytes.
5. Instantiates `Metronome.Bank`'s independent specification **without a
   hypothesis**: the phase/step read equality (`bank_step_read`), the write
   contract (`bank_write_exact_all`, `bank_write_others_all`), mutual exclusion
   of the extracted gates (`rtl_gates_exclusive`), and concrete witnesses on the
   elaborated `MASK` (a live gate that opens, a hole that has no gate, a write to
   a hole that changes nothing).

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| Live byte `k`'s gate enable is exactly `we1 && addr1 == k` for every address. | `BankEquivalence.enable{k}_spec` (one per live byte, 284 today) | `bv_decide` over the extracted cone; the enable depends only on `we1` and `addr1` by construction (fail-closed extraction). |
| At byte index `k` the family opens exactly the gate at `k` and no other: `enableAt k we1 addr1 = we1 && addr1 == k && liveAt k`. | `BankEquivalence.any_enable_spec` (list induction), `BankEquivalence.enableAt_spec` (the elaborated family, 284 gates / 480 offsets) | No hypothesis and no per-offset case split. The index `k` is any 9-bit address; a mask-zero or out-of-window index yields `false`. |
| The family's live offsets are exactly "the elaborated `MASK` byte is non-zero". | `BankEquivalence.liveAt_addrOf`, `liveAt_of_live`, `liveAt_of_hole`, `liveBytes_getLsb` | Kernel reduction over the 480 offsets. `liveBytes` is the same bit vector the address-decode cut uses. |
| On a live byte the extracted gate is the specification gate; on a mask-zero byte there is no gate. | `BankEquivalence.enableAt_eq_gateOpen`, `BankEquivalence.enableAt_hole` | Follows from the two rows above. |
| A transparency phase of the extracted gate family has the read value of the specified write step. | `BankEquivalence.bank_step_read`, `Bank.phase_read_of_live_gates` | Latch wiring from the structural check; the mask-zero offsets are unobservable (`Bank.read_zero`). |
| An issued write to byte `k` sets exactly its mask bits to `data1 & MASK` and leaves every other byte unchanged. | `BankEquivalence.bank_write_exact_all`, `bank_write_others_all` | Now unconditional: the phase is the *extracted* family, the state carries the elaborated mask. |
| Two distinct extracted gates are never enabled together. | `BankEquivalence.rtl_gates_exclusive`, `Bank.gateOpen_exclusive` | Live gates reduce to the arithmetic rule; a mask-zero byte has no gate. |
| A write to a mask-zero offset changes nothing. | `BankEquivalence.bank_hole_noop`, `Bank.write_mask_zero` | Concrete hole witness read from the elaborated `MASK` parameter. |

`Metronome.Bank` is an independent specification: 480 bytes with a mask byte
each, `read` masking unmasked bits to zero, and an abstract single-step
transparency phase. `step_of_gates` keeps the *strict* family form for an ideal
gate family; the extracted one satisfies `phase_read_of_live_gates`, which is
the form that holds at a mask-zero offset. Physical latch timing is out of
scope: the gate's own latency, latch hold/setup, clock skew, the E1/E2
separation and the "no two adjacent strobes" spacing rule are not modeled here;
the phase is one atomic step, justified by the timing comment at the top of
[md2_cfg_bank.v](../../../src/md2_cfg_bank.v).

### Run it

```text
python code/tests/lean/bank_check.py                # baseline
python code/tests/lean/bank_check.py --mutations    # plus planted regressions
```

Both need `lake` and `yosys` on `PATH` and write evidence into
`data/raw/lean_bank_v4_20261119/` by default (`--artifacts-dir` for elsewhere):
the generated Lean, its full log, a parsed axiom audit, tool versions, and
`run_status.txt` with each case's own verification exit code and whether it
matched the expectation (baseline accepted, mutants rejected). A rejected bank
exits non-zero.

`run_mutations()` plants five regressions on temporary copies of `src/` (never
the repository):

| Mutation | Rejected by |
|---|---|
| `bank_wrong_addr`: one live byte's comparator selects the next offset | the per-byte equivalence `enable{k}_spec`, hence `enableAt_spec`; `bv_decide` prints the counterexample (`addr1 = 7`, `we1 = true`) |
| `bank_addr_bit`: every comparator ignores address bit 0, so each gate covers two offsets | the per-byte equivalence (counterexample at the first live byte) |
| `bank_shared_addr`: two live bytes select the same offset, so two gates open for one address | the per-byte `enable{k}_spec` of the moved byte (the canonical run fails at `enable1_spec`, before `enableAt_spec` is reached); gate count, latch sets and enable shape are unchanged, so the structural check cannot see it. No current mutant is caught only by the family theorem. |
| `bank_no_we1`: the gate enable drops `we1` | the structural check (the gate is no longer an AND of `we1` with a selector) |
| `bank_we1_polarity`: the gate enable inverts `we1` | the structural check (`we1` is no longer a direct input of the gate AND) |

### Trust added

Nothing beyond what the suite already trusts. The per-byte equalities use
`bv_decide`; on the current map every one reports only `propext`,
`Classical.choice` and `Quot.sound`, and no native LRAT certificate axiom is
emitted, because each goal is 10 free bits. The family assembly is a list
induction plus two kernel reductions (`decide`) over the 480 offsets, which add
`propext` only; the induction step closes with a hand-written absorption lemma
(`or_and_self`), not with `bv_decide`, so it cannot introduce a certificate.
(An earlier draft did close that step with `bv_decide` and did emit
`any_enable_spec._native.bv_decide.ax_1_5`; the file now records
`[propext, Quot.sound]` for `any_enable_spec` and no native axiom anywhere, so
the bank cut adds no certificate.) `#print axioms` in the generated file is
parsed by `bank_check.py`, which fails the case if `sorryAx` appears; a future
native certificate would show up in `<case>.axioms.txt` like the decode cut's.
Yosys, the RTLIL adapter, the JSON parameter reader and the structural check are
the same trust base the rest of the Lean suite already uses.

### Timing

`python code/tests/lean/bank_check.py --mutations
--artifacts-dir data/raw/lean_bankfamily_v4_20261120` exited 0 on 2026-11-20 and
took 6930 s wall clock (115 min) on a 10-core i5-1245U laptop that was carrying
several other Lean/Yosys runs at the time; `stdout.log` in that directory records
the per-case outcomes and `run_status.txt` the exit codes. Per case, from the
artifact timestamps: baseline 981 s, `bank_wrong_addr` 214 s, `bank_addr_bit`
5503 s, `bank_shared_addr` 46 s, and the two structural mutants about 5 s each.
Replaying the retained baseline file alone on the quiet machine —
`lake env lean -j1 -DwarningAsError=true
data/raw/lean_bankfamily_v4_20261120/baseline.bank.lean` from this directory —
takes 38 s for the whole 172 KB file, so the machine load, not the proof, was the
dominant cost. `bank_addr_bit` is the expensive mutant: it breaks all 284 cones,
so all 284 per-byte `bv_decide` goals fail and each searches for its own
counterexample. A single-cone mutant (`bank_wrong_addr`, `bank_shared_addr`)
costs about the same as the baseline.

Replacing the 284 per-byte `bv_decide`s would be the next speed lever, but they
are the semantic (not syntactic) link from each extracted cone to its
comparison, so they stay.

### Remaining gaps

None in the family statement itself: `enableAt_spec` covers all 512 nine-bit
addresses and `liveAt_addrOf` covers all 480 window offsets, so the composition
no longer assumes anything about the gate family. What remains is what the cut
never modelled:

* physical latch/clock-gate timing: gate latency, hold/setup, skew, the E1/E2
  separation and the no-two-adjacent-strobes spacing rule (RTL and timing
  obligations, tracked elsewhere);
* the `MASK` parameter itself: the cut reads it from the elaborated instance and
  proves the RTL matches it; whether the mask is the intended map is a design
  question for [md2_map.vh](../../../src/md2_map.vh);
* `BASE`: the structural check requires the bank to sit at window offset 0
  (`BASE == 0`), and the family theorem relies on that; a future map with a
  non-zero `BASE` fails the check closed rather than proving something wrong.

## Host SPI command cut

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its own mutants (evidence under `<artifacts-dir>/hostcmd/`).

### Run it

```text
python code/tests/lean/hostcmd_check.py                       # baseline
python code/tests/lean/hostcmd_check.py --mutations           # plus five mutants
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the defaults write into
`data/raw/lean_hostcmd_v4_20261120/` (or `--artifacts-dir`). A rejected baseline
or an accepted mutant exits non-zero. `run_status.txt` records each case's own
Lean/Yosys exit code and whether it matched the expectation.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted next byte state is the SPEC_V2 §9 equation. | `HostCmd.rtlPhase` | Every state and input value symbolic. |
| The extracted next bit count is the specification's. | `HostCmd.rtlBitc` | Every state and input value symbolic. |
| The extracted receive shift register is the specification's `{rx[5:0], MOSI}` shift. | `HostCmd.rtlRx` | Every state and input value symbolic. |
| The extracted command latch `is_rd` latches exactly `byte == 0x03` in `ST_CMD` and holds otherwise. | `HostCmd.rtlIsRd` | Every state and input value symbolic. |
| The extracted 16-bit address register is the specification's: `ADDR[15:8]` then `ADDR[7:0]`, and `addr + 1` on a strobe or acknowledgement. | `HostCmd.rtlAddr` | Every state and input value symbolic. |
| The extracted write strobe is the specification's. | `HostCmd.rtlWr` | Every state and input value symbolic. |
| The extracted write data register, read request and read acknowledgement follow the specification. | `HostCmd.rtlWdata`, `HostCmd.rtlRd`, `HostCmd.rtlRack` | Every state and input value symbolic. |
| The command-byte history variable follows the specification's completion equation. | `HostCmd.rtlCmd` | The variable is not an RTL register; its definition is built from gates that all feed the RTL `st`/`is_rd` next-state cones, and the adapter rejects the design otherwise. |
| The extracted transition equals the specification transition. | `HostCmd.rtlStep_eq_step` | All ten register values; assembled from the component equalities. |
| The extracted trace equals the specification trace at every cycle. | `HostCmd.rtlStateAt_eq`, `HostCmd.rtl_trace_result` | Same initial state, any finite prefix. |
| A write strobe occurs only in `ST_DATA`, at the eighth rising edge of a data byte, with reset released and `CS_N` low. | `HostCmd.wr_only_in_data`, `HostCmd.rtl_trace_wr_only_in_data` | No other state or input can produce `wr`. |
| A write strobe never occurs in a read transaction. | `HostCmd.isRd_no_wr`, `HostCmd.rtl_trace_isRd_no_wr` | `isRd = true` in the strobe cycle. |
| A write strobe never occurs in the command byte, an address byte or an ignored transaction. | `HostCmd.not_data_no_wr`, `HostCmd.ign_holds` | `phase ≠ ST_DATA`; `ST_IGN` holds until `CS_N` high or reset. |
| A write strobe in cycle `n+1` (after a sampled reset at cycle 0) belongs to a transaction whose command byte was `0x02`. | `HostCmd.trace_wr_cmd`, `HostCmd.rtl_trace_wr_cmd` | The sampled reset edge makes the `Tagged` invariant hold from cycle 1. Without it, `HostCmd.rtl_cmd_premise_witness` gives a power-up state with `cmd = 0x03` whose cycle-1 strobe is high, so the premise is needed. |
| `CS_N` high returns the byte state to `ST_CMD` and clears the bit count. | `HostCmd.cs_high_resets`, `HostCmd.rtl_trace_cs_high` | Any prior state. |
| The completing `ST_AL` edge enters the first data byte with the loaded address. | `HostCmd.al_enters_byteStart`, `HostCmd.rtl_al_enters_byteStart` | Write transaction (`isRd = false`); `bitc = 7`, reset released, `CS_N` low, rising `SCK`. |
| The first data-byte strobe is at the AL-loaded address. | `HostCmd.first_data_strobe`, `HostCmd.rtl_first_data_strobe` | Eight rising `SCK` edges and no read acknowledgement during the byte. |
| A clean burst of `k+1` data bytes strobes `base, base+1, …, base+k`. | `HostCmd.data_strobe_index`, `HostCmd.rtl_data_strobe_index` | `ByteStart` at the loaded address, every edge a rising `SCK` edge with reset released, no `rack`/`hland` acknowledgement in the burst. |
| The same burst from the completing `ST_AL` edge: `base` is the address that edge loads. | `HostCmd.trace_al_burst_index`, `HostCmd.rtl_trace_al_burst_index` | The `ST_AL` completion premises, then the clean-burst conditions of the row above. |
| Consecutive strobes are one address apart. | `HostCmd.next_data_strobe`, `HostCmd.rtl_trace_next_data_strobe` | Strobe state plus eight clean rising edges; a reset or acknowledgement breaks the step. |
| The `Metronome.Host` `wr`/`bitc` trace is this machine's projection. | `HostCmd.host_stateAt`, `HostCmd.rtl_host_stateAt` | `st`/`is_rd` are the state registers, not free inputs. |
| The composed `Config.SpacedHost` premise holds for this machine's write strobe. | `HostCmd.spaced_of_hostcmd`, `HostCmd.rtl_spaced_of_hostcmd` | Only `initial.wr = false` (cycle 0 is otherwise the arbitrary power-up value). |
| `Compose.config_host_service_from_top` holds with `st`/`is_rd` supplied by this machine. | `HostCmd.config_host_service_from_hostcmd`, `HostCmd.rtl_config_host_service_from_hostcmd` | Configuration reset/active/valid premises as in `Compose`; `initial.wr = false`. |

#### What stays free

The host command machine no longer has `st` or `is_rd` as free inputs. The
per-cycle sampled inputs that remain free in this cut are `resetN`, `sck`,
`sckPrev`, `csN`, `mosi`, `rdData` and `hland`; the cookie-cutter `inCfg` and
`live` filter leaves, the unrelated configuration-input fields (`rest`) and the
configuration state also remain inputs. `MOSI` is sampled symbolically; the
synchroniser chain and the SPI pin timing are outside this cut. The read path
(`tx`, `rackv`, `miso`, `rd_val`) is not modelled beyond the `rack` flag that is
part of the command machine's input side; the byte received from MISO is not
proved.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `hostcmd_read_strobes` | a read data byte also asserts `wr` | `rtlWr` (counterexample: `ST_DATA`, `bitc = 7`, `isRd = true`) |
| `hostcmd_al_next` | `ST_AL` next state is `ST_IGN` instead of `ST_DATA` | `rtlPhase` |
| `hostcmd_cs_hold` | the `CS_N`-high branch no longer assigns `st <= ST_CMD` | `rtlPhase` (counterexample: `csN = true`) |
| `hostcmd_no_addr_step` | `addr_i` does not increment on `wr` | `rtlAddr`, so `data_strobe_index` cannot hold |
| `hostcmd_addr_bytes_swap` | the `ST_AL` load puts the received byte in the high half | `rtlAddr` |

All five are rejected by the generated Lean, not by an extraction failure.

### Trust added

* Yosys elaboration and the RTLIL adapter are the same trust base as the rest of
  the Lean suite. The cut reads only the `md2_host` instance, its ports and the
  register names/widths; it checks the clock/reset connections and that
  `byte_in = {rx, mosi}`.
* The emitter's `HostCone` adds two Yosys cell shapes locally (`$logic_not` and
  `$pmux`; the shared `rtlil.py` is unchanged). Each `$pmux` select must be an
  equality or zero test of one common bus against distinct constants, which
  makes the branches mutually exclusive; every other shape, an unresolvable bus,
  a second register driver or an unclaimed select fails extraction.
* The command-byte history variable `cmd` is a checked modelling step, not a
  register: its definition may use only gates reachable from the `st` and
  `is_rd` register **D** buses (the register Q buses are the cut's state
  leaves). The adapter reports how many RTL gates it used (six today) and
  rejects any gate outside those two cones.
* The component equalities and the trace corollaries use `bv_decide`. On the
  current design the accepted run carries per-theorem native certificate
  axioms (`rtlWr._native.bv_decide.ax_1_6` and friends) in addition to
  `propext`, `Classical.choice` and `Quot.sound`; `sorryAx` is absent and the
  runner rejects it. The certificate checker is the only trust added beyond
  Yosys, the adapter and the JSON parameter reader.

### Remaining gaps

* The specifications cover `st`, `bitc`, `rx`, `is_rd`, `addr`, `wr`, `wdata`,
  `rd` and `rack`. `tx`, `rackv`, `miso` and the `rd_val` sample are covered
  by the [host read path cut](#host-read-path-cut-hostread_checkpy).
* SPI mode-0 framing, the two-flop synchronisers, `sck_p`, and the physical
  timing/setup-hold of the pins are not modelled. `sck`, `sckPrev` and `csN` are
  sampled levels; a glitch or a metastable sample is outside the model.
* The reset synchroniser and the asynchronous behaviour between sampled edges
  are abstracted as in the rest of the suite; `resetN` is a sampled input.
* The `cmd` history variable is not an RTL register. The theorems about the
  command byte therefore rely on the checked cone restriction plus the
  `rtlCmd` equality, not on a register readback. A future RTL change that
  removes the `is_rd`/`st` cones would fail extraction rather than silently
  weaken the claim.
* The composition theorem still takes `inCfg`/`live` (the address-decode cut),
  the configuration-input suffix, and the sampled SPI inputs as free. Payload
  content and latch visibility remain with the configuration and bank cuts.
* The address burst statement assumes no read acknowledgement; an
  acknowledgement legitimately advances `addr` by the RTL `addr_i` equation, and
  the theorem states that condition rather than hiding it.

## Core-control cut (`w_cw`, `frz`, `CTRL.STICKY`)

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its own mutants (evidence under `<artifacts-dir>/corectl/`).

### What was free

The core-queue cut (`Metronome.CoreQueue`, `CoreQueueEquivalence.lean.in`) proof
`rtlStep_eq_step` binds five chip-top nets as free per-cycle inputs:

| leaf in the queue cut | chip-top net | status after this cut |
|---|---|---|
| `w_cw` (15 bits) | `pick(hits(mv_en, grp_v, DG_CW), c_dst, c_dat)` | proved: the winning move's `{1, dst, data}` |
| `frz` (1 bit) | `frz` register | proved: SPEC §12.3 next state, and low from reset until the trigger |
| `c_wr_stk` + `h_wd` (the clear leaf `c_wr_stk & h_wd[2]`) | `w_ctl & (o_ctl == HO_CTRL_STICKY)` with `h_wd[2]` | proved: host write of `CTRL.STICKY` with bit 2 |
| `cfg_core_issue` | arbiter `core_issue` | still free here (arbiter cut) |
| `cw_is_cfg` | `cfg_address_is_live(cw_pending_addr)` | still free here (decode cut) |

`corectl_check.py` re-elaborates the design with `verify.py`'s Yosys recipe, cuts
the three cones out of the chip top, emits a Lean module from the cells and
proves it equal to `Metronome/CoreCtl.lean`, an independent statement of
SPEC_V2 §6, §9 and §12.3. It then instantiates the queue's own theorems with
those values.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted `we` bit of `w_cw` is set exactly when some enabled move's destination is in group `DG_CW`. | `rtlWcw_we`, `CoreCtl.word_we` | `mv_en`, `grp_v`, `c_dst`, `c_dat` symbolic. `bv_decide` over the 120-bit input. |
| The extracted `w_cw[13:8]` and `w_cw[7:0]` are the first contender's `c_dst` and `c_dat`. | `rtlWcw_dst`, `rtlWcw_data`, `CoreCtl.chain_at_0..5` | Same. `bv_decide`. |
| Exactly one enabled move targets `DG_CW`: `w_cw` is that move's `{1, dst, data}`, i.e. `we = 1`, `dst = c_dst_k`, `data = c_dat_k`. | `rtlWcw_unique_0..5` (one per move index k), `CoreCtl.word_unique_0..5` | The unique-hit hypothesis is that move's `contenderAt` bit; the six index theorems cover every unique-hit cycle. |
| No enabled move targets `DG_CW`: `w_cw = 0`, so the queue sees no `CW.D`/`CW.AL`/`CW.AH`. | `rtlWcw_none`, `CoreCtl.word_none` | Six per-move "not a contender" facts. |
| The whole extracted word is the specification's `{we, dst, data}` pack. | `rtlWcw_eq_pack`, `CoreCtl.makeWord_fields`, `CoreCtl.makeWord_we/dst/data` | `makeWord_fields` is the only 23-bit `bv_decide` identity; the packing round trip is exact. |
| The extracted freeze triple matches SPEC §12.3 for every state and input: reset clears it, a `DBG` write sets `FREEZE' = d[0]` and `FRZ' = d[0] && !d[1]`, otherwise `FRZ' = FREEZE`, always `FRZD' = FRZ`. | `rtlFreezeStep_eq_step`, `CoreCtl.freeze_next`, `frz_next`, `frzd_next` | Reset, `d_wr_dbg` and `h_wd` symbolic. No `bv_decide`: the cells are mux/and/not and the proof is `rfl`-level after unfolding. |
| From reset, `FRZ` is low until the first `DBG` write whose bit 0 is set; a running machine and a STEP cannot raise it. | `rtl_trace_freeze_low`, `CoreCtl.trace_freeze_low` | Induction over the sampled input sequence; one-cycle `resetN` and "no trigger" hypotheses per cycle. |
| A `DBG` write of `0x01` freezes from the next cycle; `0x03` (STEP) runs exactly one cycle and freezes again; a write with bit 0 clear releases. | `rtl_trace_frz_of_trigger`, `rtl_trace_frz_one_cycle`, `CoreCtl.frz_of_freeze_write`, `frz_of_step_write`, `frz_of_release_write`, `frz_holds` | STEP's second cycle assumes no `DBG` write in the running cycle. |
| The extracted `c_wr_stk` is exactly "host write to the `CTRL.STICKY` byte", and the clear leaf is that write with bit 2 set. | `rtlSticky_eq_spec`, `rtlStickyLeaf_eq_spec`, `CoreCtl.stickyLeaf_spec` | 16-bit `bv_decide` against the host map's `HA_CTRL_BASE + HO_CTRL_STICKY`. |
| The elaborated `CWOVR` clear term `c_wr_stk & h_wd[k]` selects `k = 2`, the documented `STICKY` bit. | `stickyBit_spec`, `rtlStickyLeaf_eq_spec` | `k` is read from the `cw_overrun` next-state term; the queue cut takes that term whole, so this only ties its bit index to SPEC_V2 §13.1. |
| The extracted `d_wr_dbg` is exactly "host write to the `DBG.DBG` byte", so the freeze trigger is a real host write. | `rtlDbgWrite_eq_spec`, `rtl_trace_frz_of_host_trigger` | Same, `HA_DBG_BASE + HO_DBG_DBG`. |
| The elaborated decode constants are the documented ones: the `CW` pick's six group comparators read `DG_CW`, its destination comparators read `D_CW_AL/AH/D`, and the two strobes' base, span and offset are the host map's. | `codes_spec` (plus the adapter's constant checks) | `codes_spec` proves `ctrlOffset < ctrlSpan`, `dbgOffset < dbgSpan` and `58/59/60`; the adapter rejects a cell whose constant differs from the header before Lean runs. |
| The queue's `CW.D`/`CW.AL`/`CW.AH` decode is a statement about the winning move's destination, and `CW.D`'s byte is that move's data. | `queue_writeData`, `queue_writeLow`, `queue_writeHigh`, `queue_cwData` | Any contender exists; then `writeData ↔ word.dst == D_CW_D` etc. |
| A `CW.D` the queue cannot take sets `CWOVR`; a host write to `CTRL.STICKY` with bit 2 clears it; nothing else clears it; a frozen queue holds. | `cwD_dropped_sets_overrun`, `overrun_cleared_by_sticky`, `overrun_sticky_unless_sticky`, `frozen_queue_holds`, `queue_hostClear` | Instantiates `CoreQueue.no_silent_overwrite`, `overrun_cleared`, `overrun_sticky`, `frz_holds` with the extracted leaves. |
| With `FRZ` low, a pending configuration write presents itself to the arbiter. | `coreValid_of_queue` | `pending`, `fz.frz = false` and `cw_is_cfg` are premises; the arbiter grant is the arbiter cut's. |
| Two contenders in one group: the lower move index wins and the later move's data is not written. No contender: the word is zero. | `CoreCtl.two_contenders_first_wins`, `no_contender_zero` | Concrete kernel `decide` on the specification. |

#### What the RTL does when more than one move hits

SPEC_V2 §6 defines it: sticky `CONFLICT` is set and only the lowest
`(core, move index)` takes effect. The six moves are core 0 moves 0-2 then core 1,
so the RTL's `hits` priority mask picks the first enabled move of the group, and
`rtlWcw_dst`/`rtlWcw_data` say the word is that move's. Two same-group moves in
one instruction are rejected by the assembler
(`code/host2/metronome2_tools/asm.py`, "write the same group ... the hardware
would set CONFLICT") unless the guards are `if`/`ifnot` exclusive, but two
*core* instructions dispatched in one cycle can still collide, and there the
hardware resolution above is the contract. This cut proves the resolution; the
`CONFLICT` flag cone (`mv_valid & ~mv_win` through `same_key`) is not part of
this cut.

### Run it

```text
python code/tests/lean/corectl_check.py                # baseline
python code/tests/lean/corectl_check.py --mutations    # plus planted regressions
```

Both need `lake` and `yosys` on `PATH`, build `Metronome.CoreCtl`, and write
evidence into `data/raw/lean_corectl_v4_20261120/` by default
(`--artifacts-dir` for elsewhere): the generated Lean, its full log, a parsed
axiom audit, tool versions, and `run_status.txt` with each case's own exit code
and whether it matched the expectation. A rejected cone exits non-zero.
`check_corectl(src_dir_or_json, out_dir, *, lake, yosys, case)` is importable like
`bank_check.check_bank`, and `run_mutations(snapshot, out_dir, lake, yosys)`
plants the regressions on temporary copies of `src/` (never the repository).

| Mutation | Rejected by |
|---|---|
| `pick_ignores_we`: the `hits` mask drops `mv_en`, so a disabled move wins its group | `rtlWcw_we` (a counterexample: an enabled-only tie) |
| `pick_wrong_group`: `w_cw` is `PICKG(DG_FLAGS)`, the flags group's winner | the adapter: the `CW` pick's comparators read `DG_FLAGS`, not `DG_CW` |
| `frz_wrong_reset`: the freeze register resets set | `rtlFreezeStep_eq_step` (wrong reset value) |
| `frz_never_clears`: `frz <= frz \| freeze`, so a freeze never lifts | `rtlFreezeStep_eq_step` |
| `sticky_wrong_offset`: the `STICKY` comparator uses the next offset | the adapter: the elaborated offset is not `HO_CTRL_STICKY` |
| `sticky_wrong_block`: the `STICKY` strobe watches the `DBG` block | the adapter: the cone no longer has one subtraction and one span comparison, and the base is not `HA_CTRL_BASE` |
| `sticky_no_write`: `w_ctl \| (o_ctl == HO_CTRL_STICKY)`, so an address alone clears | `rtlSticky_eq_spec` (counterexample at `wr = false`) |
| `sticky_wrong_bit`: the `CWOVR` clear takes `h_wd[3]` | `stickyBit_spec` (`3 = 2` fails) and then `rtlStickyLeaf_eq_spec` |

### Trust added

Yosys elaboration, the RTLIL adapter and the generated Lean are the same trust
base the rest of the suite uses. The adapter is extended locally (in
`corectl_check.py`, not in `rtlil.py`) for the shapes these cones need: Yosys's
`$reduce_or`/`$reduce_bool` (the `~|` priority mask), `$logic_not` on a whole
address bus (the `== 0` offset test), wide `$and`/`$or` with a broadcast hit bit
(the 15-bit `pick` select), a one-bit `$mux` as a Lean `Bool` (the freeze
triple), and a compact bus assembly that names a contiguous run of bits (a whole
bound bus, a driven output or a slice of a bound bus) once and shifts it into
place instead of emitting one term per bit. Every extension stays fail-closed:
an unsupported cell, an undriven net, a partially overlapping bus or a second
driver raises `UnsupportedRTL`, and the emitted expression is checked by the
Lean proof, so an assembly that dropped a bit would fail the equivalence rather
than pass silently.

`bv_decide` adds per-theorem native-certificate axioms for
`makeWord_fields._native.bv_decide` (23 bits), `rtlWcw_we/dst/data` (120 bits),
and `rtlSticky_eq_spec`/`rtlDbgWrite_eq_spec` (16-bit address). `#print axioms`
records them, and the runner rejects `sorryAx`. The freeze theorems use only
`propext`; the composition theorems use `propext`, `Classical.choice` and
`Quot.sound` plus the certificates of the theorems they rewrite with.

The host-map constants (`DG_CW`, `D_CW_AL/AH/D`, `HA_CTRL_BASE`, `HSPAN_CTRL`,
`HO_CTRL_STICKY`, `HA_DBG_BASE`, `HSPAN_DBG`, `HO_DBG_DBG`) are read from
`src/md2_map.vh` and `src/md2_defs.vh`; every constant found in the elaborated
cells must equal the header's, so a drifted decode fails instead of redefining
the specification. That header reading is the same trust `verify.py` already
places in the generated map for its `decode_*` mutations.

### Remaining gaps

* **`mv_en` scheduling.** The bundle is a per-cycle input: dispatch, guards, the
  `md2_core` freeze gate and the register file that produce `mv_en`, `c_dst` and
  `c_dat` are not in this cut. So "some move is enabled" is not yet tied to a
  thread's PC or to `RUN`/`FRZ`.
* **`DG_MAP`.** `grp_v` is bound free; the destination-to-group lookup
  (`DG_MAP` in `md2_map.vh`, a 320-bit table indexed by `c_dst`) is not proved
  here, so `grp` is "the group the core believes", not necessarily the map's.
* **Host link.** `h_wr`, `ha` and `h_wd` are free; the SPI framing that makes
  `h_wr` a real write and `ha` a real address is the host cut's and the pin
  timing's business.
* **`CONFLICT`.** The multi-hit flag is not proved (see above); the pick's
  resolution is.
* **Freeze transparency.** The register equation and the trace lift are proved;
  SPEC §12.3's "deleting the frozen cycles gives the same state sequence" is
  not, and physical freeze behaviour stays with the k-induction bench.
* **Timing.** The latch visibility, setup/hold and 60 MHz closure are out of
  scope, as in the other cuts.

## Host write-decode cut (`hostmap_check.py`)

This cut proves that a host write `(h_wr, ha, h_wd)` reaches exactly the target
the host map assigns: the block the address falls in, the register byte or
memory word it writes, and nothing else.  The specification side is
[Metronome/HostMap.lean](Metronome/HostMap.lean), a hand-written table of the
map; the RTL side is `src/project.v`, elaborated by Yosys and cut by
[hostmap_check.py](hostmap_check.py), which emits
`HostMapEquivalence.lean.in` into a Lean module and proves the equalities.

Files of this cut:

| Path | Role |
|---|---|
| [Metronome/HostMap.lean](Metronome/HostMap.lean) | independent map: block base/span table, the 43 register addresses, the write-selection list, the count lemmas, the write-data contracts |
| [hostmap_check.py](hostmap_check.py) | Yosys elaboration, structural adapter, cone extraction, Lean emission, mutation runs, evidence |
| [HostMapEquivalence.lean.in](HostMapEquivalence.lean.in) | proof template (settings, namespace, write-data corollaries, axiom audit) |
| `data/raw/lean_hostmap_v4_20261120/` | evidence of the accepted run: generated Lean, Lean log, axiom audit, tool versions, `run_status.txt` |

`Metronome.lean` is unchanged, so `lake build` does not build this module; use
`lake build Metronome.HostMap` (or `lake env lean Metronome/HostMap.lean`), as
the other cuts do.

### The map the cut checks

Block windows (`HA_*_BASE`, `HSPAN_*`, `CFG_LO` of `src/md2_map.vh`), all half
open and pairwise disjoint:

| Block | Base | Span | Host-visible use |
|---|---|---|---|
| `prog` | `0x0000` | `0x1000` | two program memories, `0x0800` each |
| `data` | `0x1000` | `0x0800` | data RAM bytes |
| `cfg` | `0x2000` | `0x01E0` | configuration window (line/thread/stream/output bytes, live-byte mask) |
| `ctrl` | `0x2400` | `0x0010` | `RUN`, `STICKY`, `IRQEN`, `DOORBELL`, `HOSTIN`, `HOSTSTAT` |
| `lrt` | `0x2410` | `0x0020` | four lines at `+8`, `PHASE`(2), `CTL`, `STAT` |
| `trt` | `0x2440` | `0x000C` | six threads at `+2`, `PC`, `STAT` |
| `srt` | `0x2450` | `0x0008` | two streams at `+4`, `CTL` |
| `dbg` | `0x2460` | `0x0020` | `DBG`, `MCTL`, `ECTL`, `EMASK`(2), `RLV`(2) |

The 43 writable register bytes are `HostMap.regAddrs`, in the order of the
extracted enable list: six `ctrl`, sixteen `lrt` (`4 × {PHASE low, PHASE high,
CTL, STAT}`), twelve `trt`, two `srt`, seven `dbg`.  `HOSTOUT`, `ID`,
`ERRSUM`, `LRT.SYM`, `LRT.INS`, `DBG.MISR`, `ACC`, `FLAGS`, `FPC` and the
unmapped addresses in [Metronome/HostMap.lean](Metronome/HostMap.lean)
(`readOnlyAddrs`) are read-only and must enable nothing.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| Every block's `in_*` flag is exactly membership in the map's window. | `rtlIn{Prog,Data,Cfg,Ctrl,Lrt,Trt,Srt,Dbg}_spec` | `bv_decide` over all 65536 addresses; the spec base/span are the hand-written table, not the header. |
| Every block's `a_*` offset bus is `ha - base`. | `rtlOff{...}_spec` | Same; the adapter checks that each is a `$sub` of `ha` with a constant. |
| The eight regions never both claim one address. | `regions_exclusive` | `HostMap.blockCount_le_one` (`bv_decide` over the 8-window table) composed with the eight region equalities. |
| Each register write enable is "host write at exactly that byte". | `enCtrlRun_spec` … `enDbgRlv1_spec` (one per byte, 43) | `bv_decide` over `(w, ha)`; the address literal is built from `md2_map.vh` and must match `HostMap.regAddrs` at that position (`enables_snoc_spec`). |
| The program memory is written by a host write in the core's half of the program window. | `enProg0_spec`, `enProg1_spec` | `w && a < 0x0800` / `w && 0x0800 ≤ a < 0x1000`. |
| The program write's word address and byte lane are the map's `[10:3]` and `[2:0]`. | `rtlProgWord_spec`, `pmBe_spec` | Word `(ha - base) >>> 3`, lane one-hot `1 << (ha - base)[2:0]`; the adapter checks `u_pmem*.addr` selects `a_prg[10:3]` when `pm_we*` fires and `be = pm_be`. |
| The data RAM host write is a host write in the data window, with the map's byte address. | `hSet_spec`, `dataWe_spec`, `enData_spec`, `rtlDataAddr_spec` | `h_set = (h_wr \| h_rd) & in_data`; `h_set & h_wr = h_wr & in_data`; `u_mem.h_addr = a_dat[10:0]`, `h_d = h_wd`. |
| A configuration byte is written exactly by a host write at a live window address. | `enCfg_spec` | `w && inRegion .cfg a && live`; `live` (`cfg_address_is_live`) is a free leaf, owned by the address-decode cut. |
| At most one write enable fires per host write, counting the configuration strobe. | `at_most_one`, `enables_snoc_spec` | The extracted enable list plus `enCfg` evaluates to `HostMap.enabledSels`; the count of `enabledSels` is at most one for every `(live, w, ha)`. |
| Read-only or unmapped addresses enable nothing. | `no_write_{2405,2407,2408,240F,2413,2414,2464,2465,246A,246B,246C,246D,2470,2471,1800,1FFF,21E0,21FF,2480,24FF,FFFF}` | 21 concrete addresses; each is proved to have no selection in the map, then the count is zero for either strobe value. |
| `CTRL.STICKY` is write-1-to-clear for the three sticky bits. | `rtlStickyConflict_spec`, `rtlStickyMemhaz_spec`, `rtlStickyOverrun_spec`, `sticky_conflict_cleared`, `sticky_memhaz_cleared`, `sticky_overrun_cleared`, `sticky_conflict_held`, `sticky_conflict_set` | Flop input cones with reset released; `ev`, `q`, `stk`, the `h_wd` sticky bit are free. A write of 1 clears a quiet flag; a write of 0 holds; an event still sets. |
| `CTRL.DOORBELL` is a one-cycle word unless frozen. | `rtlDoorbell_spec`, `doorbell_write_pulse`, `doorbell_write_idle`, `doorbell_frozen_hold`, `doorbell_frozen_adds` | `db`'s input cone; `frz` and the write are free. A non-frozen write loads `h_wd[5:0]`; the next non-frozen cycle clears it; a frozen cycle holds, and a write while frozen is ORed in rather than dropped. |
| `CTRL.HOSTIN` sets `INV` and loads the mailbox. | `rtlInv_spec`, `rtlMailbox_spec`, `hostin_sets_inv`, `hostin_loads_mailbox` | `inv`'s and `inb`'s input cones; the core-read leaf `|rd_hin` is free. |

Everything is stated over 16-bit addresses (17 bits with the strobe); no case
split over addresses is done by hand.  The count idiom is
`HostMap.bitCount`, an exact 8-bit accumulator over a `List Bool` (all lists
here are shorter than 256).

### What the adapter checks (and what stays free)

Yosys elaboration uses the same recipe as `verify.py`
(`read_verilog -I src ...; hierarchy -check; proc; opt_clean; write_json`).
`hostmap_check.py` then, fail-closed:

* resolves `ha`, `h_wr`, `h_wd` and checks `u_host.addr/wr/wdata` are them;
* checks each `a_*` is a `$sub` of `ha` with a constant operand, and each
  `in_*` is a `$lt` of that offset with a constant, recording both constants in
  the log (the constants themselves are judged by Lean, against the map table);
* checks `cfg_host_now` is `$and($and(h_wr, in_cfg), live)` and binds the
  `live` leaf;
* checks `u_pmem0/1.we`, `.be = pm_be`, and `.addr` is a mux on the core
  strobe taking `a_prg[10:3]` when writing and `fadr[8k +: 8]` otherwise;
* checks `u_mem.h_set`, `.h_wr`, `.h_addr = a_dat[10:0]`, `.h_d = h_wd`;
* extracts each register enable as a function of `(h_wr, ha)` from the
  elaborated net (or the `h_*_we` port bit of the line/thread instance, or the
  `hctl` net of the stream instance);
* extracts each write-data cone from the register's input, strips the
  synchronous-reset mux (requires the reset branch to be all zero) and binds
  the documented leaves.

The cut's free per-cycle inputs are `h_wr`, `ha`, `h_wd`, the `live` decode,
the sticky event terms (`conflict_ev`, `memhaz_ev`, `cw_write_data`,
`cw_accept`), `frz`, `c_wr_*`, `rd_hin`, and the register values themselves.
A named net that combinational logic drives is bound as an opaque leaf, which
over-approximates the circuit and is sound for the safety statements.

Local adapter extensions (all in `hostmap_check.py`, `rtlil.py` unchanged):
`$shl` (the byte-lane one-hot), binding raw unnamed net bits (the `live` leaf,
single `h_wd` bits) and the register-reset mux strip.  Everything else is the
shared `corectl_check.VectorCone`.

### Mutations

`python code/tests/lean/hostmap_check.py --mutations` runs the baseline and four
planted regressions on temporary copies of `src/` (never the repository).  Each
mutant is rejected by the generated Lean; the counterexample printed by
`bv_decide` is the address (and strobe) that exposes it.

| Mutation | Change | Rejected by | Counterexample |
|---|---|---|---|
| `hostmap_overlap` | `a_srt` subtracts `HA_DBG_BASE - 1` (`0x245F`), so the stream window overlaps `DBG` | `rtlInSrt_spec`, hence `regions_exclusive` | `a = 0x2466` (inside both `srt` and `dbg`) |
| `hostmap_thread_instance` | thread `k`'s `STAT` strobe uses `i_trt == (k+1) % NT` | `enThread0Stat_spec` (then `enThread1Stat_spec`, …) | `a = 0x2443` (thread 1's `STAT`) |
| `hostmap_pm_lane` | `pm_be = 8'd1 << (7 - a_prg[2:0])` | `pmBe_spec` | `a = 0xFFFF` |
| `hostmap_readonly_write` | `d_wr_mctl` decodes `HO_DBG_MISR` (`0x2464`, read-only) instead of `HO_DBG_MCTL` | `enDbgMctl_spec` (and would fail `no_write_2464`) | `a = 0x2461` |

### Trust added

Yosys elaboration, the RTLIL adapter and the generated Lean are the same trust
base as the rest of the suite.  Beyond that:

* `bv_decide` adds per-theorem native-certificate axioms (Lean's LRAT checker)
  for the region/enable/memory equalities and for
  `HostMap.selList_count_le_one` and `HostMap.blockCount_le_one`; e.g. the
  accepted run records `rtlInCtrl_spec._native.bv_decide.ax_1_8`,
  `enCtrlRun_spec._native.bv_decide.ax_1_5`,
  `pmBe_spec._native.bv_decide.ax_1_7`,
  `selList_count_le_one._native.bv_decide.ax_1_32` and
  `blockCount_le_one._native.bv_decide.ax_1_27`.  `#print axioms` records them
  per theorem in `<case>.axioms.txt`, and the runner rejects `sorryAx`.  The
  composition theorems (`at_most_one`, `enables_snoc_spec`, the read-only
  facts, `regions_exclusive`) carry the certificates of the theorems they
  rewrite with.  Two groups carry none of their own: the offset equalities
  (`rtlOff*_spec`) are closed by definitional reduction after unfolding, because
  the extraction is literally the `$sub`-of-`ha` cone the adapter requires; and
  `rtlInProg_spec` reduces without a certificate.  The write-data equalities are
  Bool case analysis over mux/and/not cells: `rtlStickyOverrun_spec`,
  `sticky_conflict_cleared` and `hostin_sets_inv` use `propext` only,
  `rtlInv_spec` uses none, and `rtlDoorbell_spec` uses
  `propext`/`Classical.choice`/`Quot.sound`.  (A rejected mutant's log can show
  `sorryAx` in declarations downstream of its first failing theorem; the case is
  rejected on the non-zero exit before that test, and an accepted case never
  contains it.)
* The adapter's structural checks above (port wiring, mux selects, cell
  shapes) are Python checks on the elaborated JSON.
* The reset-mux strip is a checked modelling step: the mux select must be
  `rst_q` and its reset branch all zero; otherwise extraction fails.
* The map table in `Metronome/HostMap.lean` is hand-written from
  `md2_map.vh`.  The Python reads the header for the enable addresses it emits,
  and `enables_snoc_spec` forces the emitted order and addresses to equal the
  hand table, so a header change without a matching table change fails the
  proof rather than redefining the map.

### Remaining gaps

* **Reset semantics.**  The write-data theorems are about the input cone with
  the reset branch removed (checked zero).  Asserting reset and the resulting
  cycle are the register file's and the simulation benches' business.
* **Concurrent drivers.**  `d_wr_ectl`, `d_wr_em0/1`, `d_wr_rlv0/1` are host
  strobe OR a core drain term; only the host term is proved here.  The core
  path is the configuration/queue cut's.  Similarly the sticky bits' event
  terms and the doorbell's `frz` are free.
* **Reads.**  The host read path (`h_rd`, `rd_val`, `in_data` as the read
  qualifier, `HOSTOUT`/`ID`/`ERRSUM`/status readback) is not covered; this cut
  is about writes.
* **`cfg_address_is_live`.**  `cfg_host_now` is proved to be
  `h_wr & in_cfg & live`; the mask decode itself is the address-decode cut's
  and stays a free leaf, so a configuration write is "a write to a live window
  byte" relative to that leaf.
* **Data-RAM queueing.**  `u_mem` registers `h_set/h_wr/h_addr/h_d` and performs
  the write later; the cut proves the request and its address/data, not the
  queue's timing.
* **Program memory macro.**  The cut proves the strobe, word address and
  one-hot byte lane into `md2_pmem`; the SRAM macro's byte-enable behaviour is
  `md2_pmem`'s.
* **Host framing.**  `h_wr`, `ha`, `h_wd` are sampled inputs; the SPI framing
  that produces them is the host cut's, and physical timing is out of scope
  everywhere.
* **Map maintenance.**  `Metronome/HostMap.lean` duplicates the generated
  header's numbers on purpose; a legitimate map change needs both edits, and
  the proof fails until then.

### Run it

From the repository root, with `lake` (Lean 4.35.0) and `yosys` on `PATH`:

```text
python code/tests/lean/hostmap_check.py                              # baseline
python code/tests/lean/hostmap_check.py --mutations                  # plus four mutants
python code/tests/lean/hostmap_check.py --mutations --artifacts-dir <fresh dir>
```

The defaults write into `data/raw/lean_hostmap_v4_20261120/`; the directory
must not exist.  Evidence per case: `<case>.lean` (the generated module),
`<case>.log` (Yosys command, extracted bases/spans, full Lean output),
`<case>.axioms.txt` (parsed `#print axioms`), plus `tools.log`, `lake.log`,
`stdout.log` and `run_status.txt` (each case's own exit code and whether it
matched the expectation).  A rejected baseline or an accepted mutant exits
non-zero.

The accepted run recorded on 2026-11-20 is
`data/raw/lean_hostmap_v4_20261120/`: `python code/tests/lean/hostmap_check.py
--mutations --artifacts-dir data/raw/lean_hostmap_v4_20261120` exited 0 in
580 s wall clock on a 10-core i5-1245U laptop (baseline about 110 s, each
mutant about 95 s; the Lean proof of the 64 KB generated file is about 80 s of
that, the rest is Yosys and the extraction).

`check_hostmap(src_dir_or_json, out_dir, *, lake, yosys, case)` and
`run_mutations(snapshot, out_dir, lake, yosys)` are importable, like the other
cuts.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/hostmap/`).

## Host read path cut (`hostread_check.py`)

The cut is `hostread_check.py`, `Metronome/HostRead.lean` and
`HostReadEquivalence.lean.in`.

### What this cut adds

The host command cut (`hostcmd_check.py`, `Metronome/HostCmd.lean`) proves the
command/address/data phase machine and stops at the read request `rd` and the
acknowledge latch `rack`.  This cut covers the response path:

| Piece | RTL | Lean |
|---|---|---|
| Response registers | `tx`, `rackv` of `src/md2_host.v` | `Metronome.HostRead.State`, `txNext`, `rackvNext` |
| Read map | `rd_val` mux of `src/project.v` | `Regs`, `rdValSpec` |
| MISO pin | `u_host.miso` -> `uo_out[0]` | `rtlMiso` |
| Side-effect freedom | `h_rd` fan-out | Python structural check + `read_no_write` |

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| A register read requested in cycle `R` latches `rack` and the `rd_val` of `R`, and loads `TX` at the end of `R+1`. | `HostRead.register_read_response` | `rd` high, `rd_data` low, reset released and `CS_N` low in `R` and `R+1`, and the loading edge is idle or the eighth edge of the previous byte (`hkeep`, the RTL's "a load in the same cycle as a shifting `SR` is lost"). |
| The eight `SR` edges of a data byte clock out the byte MSB first, one bit per `SR`. | `HostRead.read_byte_msb`, `HostRead.shifted_bit` | No acknowledgement lands during the byte; reset released and `CS_N` low on all eight edges. |
| The eighth edge issues the next request at the same address; two idle cycles later the next byte is loaded with the `rd_val` of the request cycle and `ADDR` has stepped by one. | `HostRead.read_slot_step`, `HostRead.read_slot` | Cycles 8 and 9 idle (`sr` low), reset released, `CS_N` low, no landing and not a data-RAM address in cycle 8. |
| Slot `k` of a clean burst is at `a0 + k` and carries `sentByte k`: slot 0 the byte already loaded, slot `k+1` the `rd_val` sampled in the request cycle that slot `k` ended with. | `HostRead.read_burst_index` | Each slot is eight `SR` edges plus two idle cycles (SCK at clk/10 or slower; SPEC_V2 §9 requires clk/16), no acknowledgement inside a slot, request cycles not data-RAM addresses. |
| A data-RAM landing loads `TX` with `hland_d` and steps `ADDR`; `TX` holds it across the idle cycles; the byte clocked out is `hland_d`. | `HostRead.ram_landing_sending`, `HostRead.sending_frame_range`, `HostRead.ram_byte_msb` | The RAM service contract is an interface premise (`hland`/`hland_d` are inputs; see gaps). |
| A read transaction raises no write strobe and never loads `wdata`. | `HostRead.read_no_write` | `isRd`, reset released. |
| The elaborated host link is this machine's transition, register by register. | `rtlPhase` .. `rtlRackv`, `rtlStep_eq_step` | Every register value symbolic.  The address register is the one stated hypothesis `AddrOk` (see gaps). |
| The elaborated transition's trace is the specification trace, so every byte-level theorem above holds of the RTL. | `rtlStateAt_eq`, `rtl_register_read_response`, `rtl_read_byte_msb` | `AddrOk` at every cycle, as in `rtlStep_eq_step`. |
| The elaborated `rd_val` mux is `rdValSpec` at **every** 16-bit address and for every value of the observable state. | `rtlRdVal_eq_spec` | `bv_decide` over 16 address bits and 415 free state bits; no `sorryAx`; carries a per-theorem native certificate axiom. |
| Program memory, the data RAM, the configuration window (D14) and unmapped addresses read 0. | `HostRead.program_reads_zero`, `data_reads_zero`, `config_reads_zero`, `zero_outside`; `rtlRdVal_program_zero`, `rtlRdVal_data_zero`, `rtlRdVal_config_zero`, `rtlRdVal_unmapped` | Address-range hypotheses of the ISA map (`0x0000`, `0x1000..0x17FF`, `0x2000..0x21DF`, outside the five register blocks). |
| `CTRL.ID` reads `0xA2` whatever the machine state. | `HostRead.id_reads_version`, `rtlRdVal_id` | `MD_VERSION = 2`; the adapter requires the elaborated constant to agree (`mdVersion`). |
| Register layouts are bit-exact: `STICKY`, `HOSTSTAT`, `ERRSUM`, `DBG`, `LRT.CTL`, `TRT.STAT`, `SRT.POSH`, the `DOORBELL` hole. | `sticky_layout`, `hoststat_layout`, `errsum_layout`, `dbg_layout`, `lrt_ctl_layout`, `trt_stat_layout`, `srt_posh_layout`, `doorbell_reads_zero` | Kernel `decide` on the specification; the RTL side follows from `rtlRdVal_eq_spec`. |
| The elaborated `rd_val` mux equals the map for every value of its 200 don't-care bits. | `rtlRdValX_eq_spec`, `rtlRdVal_dontcare_irrelevant` | `bv_decide`; the free vector width is checked against the zero reading. |
| The pin that carries MISO is `tx[7]` with no extra register. | `rtlMiso_eq_tx7` | The adapter checks `uo_out[0]` is the `u_host.miso` net, uniquely driven by the host instance. |
| `h_rd` drives nothing but the data-RAM host request slot. | Python structural check (`check_read_top`) + `read_no_write` | `h_rd`'s only consumer is `h_set = (h_wr | h_rd) & in_data`; inside `md2_mem` the request slot registers are the only state it reaches; a read request carries `hqw = 0`, so the RAM access is a read. |

### Trust added

* Yosys elaboration, the RTLIL adapter and the generated Lean: the same base as
  the rest of the suite.
* `ReadCone` extends the adapter in `hostread_check.py` (the shared `rtlil.py` is
  unchanged) with `$pmux` (shared decode), `$logic_not`, `$reduce_or`, `$mul`
  with one constant operand (only the documented index constants
  `2, 3, 4, 5, 8, 12, 16`), dynamic `$shiftx` of any width and `$shr`/`$shl` of a
  constant amount.  Everything stays fail-closed: a `$mul` with two
  non-constant operands, a negative-capable signed shift amount, an unsupported
  cell or an unresolvable bus raises `UnsupportedRTL`.
* Checked modelling steps (adapter, structural):
  * `byte_in` is `(mosi, rx)` and is read as the specification's `byteIn`;
  * `addr_i` is a mux of `addr` and `addr + 1` selected by `wr | rack | hland`,
    and is read as the specification's `addrInc` (`check_address_increment`);
  * `miso` is the host instance's port, net-aliased to `uo_out[0]`;
  * `in_data` is `(ha - HA_DATA_BASE) < HSPAN_DATA`;
  * the `rd_val` cone's five block subtractions and window spans are exactly the
    header's, and the specification's literals equal `src/md2_map.vh`.
* `bv_decide` adds per-theorem native LRAT certificate axioms for the component
  equalities (`rtlPhase`, `rtlRx`, `rtlTx`, ...), for `rtlRdVal_eq_spec` and for
  `rtlMiso_eq_tx7`.  `#print axioms` is recorded in `<case>.axioms.txt` and the
  runner rejects `sorryAx`.

### Gaps

* **The address register equation is a hypothesis.**  `rtlStep_eq_step` takes
  `AddrOk`: `(rtlStep state input).addr = addrNext state input`.  The host
  command cut proves exactly that equation for the same cone
  (`HostCmd.rtlAddr`), so it is not re-proved here; a reader must compose the
  two cuts to get an unconditional transition theorem.  The read path's own
  equations (`tx`, `rackv`) and the byte-level theorems do not depend on it
  except through `Sending`'s address field.
* **The RAM service contract is an interface premise.**  `hland`/`hland_d` are
  inputs of this cut: it proves that a landing loads `TX` with `hland_d` and
  that the byte clocked out is that value, but not that the arbiter delivers the
  byte of the *requested address* within the window.  The window (no `SR`
  between the landing and the slot) is an explicit premise.  The arbiter and
  `md2_dmem` timing remain separate evidence.
* **SCK spacing.**  `read_burst_index` requires eight `SR` edges plus two idle
  cycles per slot (period at least 10 clk).  SPEC_V2 §9 requires clk/16, which
  satisfies it; a *register* read needs the load at the end of `R+1` to be
  before the next `SR`, which is the same premise stated as `hkeep`.
* **Physical timing.**  Setup/hold, the two-flop synchronisers, `sck_p` and the
  60 MHz closure are out of scope, as in the other cuts.
* **`rd_val` don't-cares (closed 2026-11-21).**  Yosys `proc` leaves 200 `x`
  bits in the `rd_val` cone: whole 8-bit arms of the intermediate `$N
d_val`
  muxes it builds for the nested `if`/`case`.  `rtlRdVal` reads them as 0.
  The adapter also generates `rtlRdValX`, the same cone with every `x` bit read
  from a free vector `xs` (`DontCareCone`; the number of free bits must equal
  the zero reading's count or extraction fails), and
  `rtlRdValX_eq_spec` proves it equals `rdValSpec` for **every** `xs`.  So no
  don't-care arm reaches the read value, and a synthesis flow may tie them to
  anything, including a function of other signals, because the statement holds
  pointwise.  `rtlRdVal_dontcare_irrelevant` states the agreement.  The
  `hostread_default_x` mutant (unmapped thread and stream offsets read `8'bx`)
  is accepted by the zero reading and rejected only by `rtlRdValX_eq_spec`.
* **`mdVersion`.**  The specification's `MD_VERSION` is the literal 2, checked
  against `src/md2_defs.vh`; a version bump must update the specification.

### Run it

```text
python code/tests/lean/hostread_check.py                # baseline
python code/tests/lean/hostread_check.py --mutations    # plus planted regressions
```

Both need `lake` and `yosys` on `PATH` and write into
`data/raw/lean_hostread_v4_20261120/` by default (`--artifacts-dir` elsewhere):
the generated Lean, its log, the parsed axiom audit, tool versions and
`run_status.txt` with each case's own exit code.  The baseline builds
`Metronome.HostRead` with `lake env lean` (the module is not part of the default
library target).

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/hostread/`).


### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `hostread_sticky_layout` | `CTRL.STICKY` reads the three sticky flags in the wrong order | `rtlRdVal_eq_spec` |
| `hostread_default_nonzero` | the default of the read mux is `0x5A`, so program, RAM, configuration and unmapped addresses read it | `rtlRdVal_eq_spec` (hence the zero corollaries) |
| `hostread_phase_slice` | `LRT.PHASE` reads the high half of the phase bus | `rtlRdVal_eq_spec` |
| `hostread_tx_early` | `TX` loads in the request cycle (`rd \| hland`) instead of the acknowledge cycle | `rtlTx`, hence `rtlStep_eq_step` |
| `hostread_ackv_swap` | `ackv` swaps the register value and the RAM byte | `rtlTx` |
| `hostread_miso_lsb` | `MISO` is `tx[0]` | `rtlMiso_eq_tx7` |
| `hostread_default_x` | unmapped thread and stream offsets read `8'bx` | `rtlRdValX_eq_spec` only (the zero reading still matches; run `data/raw/lean_hostread_v4_20261121/`, exit 0, 7/7 mutants rejected) |

A late variant (an extra acknowledge register, so `TX` loads one cycle after the
acknowledge) was tried and fails closed at extraction instead: the injected
register leaves a net the adapter cannot resolve, which is also a rejection but
a structural one.  The request-cycle load above is the timing regression that
the generated Lean itself catches.

### Timing

`python code/tests/lean/hostread_check.py --mutations
--artifacts-dir data/raw/lean_hostread_v4_20261120` exited 0 on 2026-11-20.  The
artifact timestamps give the cost: the baseline case (Yosys, extraction, the
163 KB generated proof and its `bv_decide`s) takes about 27 s and each mutant
about 25 s, so the whole run is roughly 3 minutes on the 10-core i5-1245U
laptop.  The largest single proof is `rtlRdVal_eq_spec` (16 address bits plus
415 free state bits over 134 cells).

## SPI pin layer cut (`Metronome.SpiPins`, `spipins_check.py`)

Status: baseline accepted and all mutants rejected on 2026-11-21, Lean 4.35.0,
Yosys 0.70+190, branch `metronome-v4.0`. Evidence in
`data/raw/lean_spipins_v4_20261121/`.

`Metronome.HostCmd` proves the host command machine from per-cycle sampled
inputs `sck`, `sckPrev`, `csN`, `mosi`. This cut closes the layer below it: the
three pin synchronisers of `src/project.v` and the `u_host` port wiring, plus a
mode-0 SPI pin waveform, so that "a pin-level write transaction produces host
write strobes" is a statement about the elaborated RTL and the pins.

### Files

| Path | Contents |
|---|---|
| `code/tests/lean/Metronome/SpiPins.lean` | Specification: `Sync`/`step` (SPEC_V2 §2), `hostInput`, latency lemmas, the pin clock `srAt`, byte assembly, `Clean`, `transaction_strobes` |
| `code/tests/lean/spipins_check.py` | Fail-closed extraction of `s1`/`s2`/`sp` and the `u_host` wiring, generated Lean, axiom audit, mutants |
| `code/tests/lean/SpiPinsEquivalence.lean.in` | Generated-proof template (equality, wiring, trace, composed headline) |
| `data/raw/lean_spipins_v4_20261121/` | stdout, per-case Lean sources and logs, axioms, `tools.log`, `lake.log`, `run_status.txt` |

### Run it

```text
python code/tests/lean/spipins_check.py                       # baseline
python code/tests/lean/spipins_check.py --mutations           # plus five mutants
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the defaults write into
`data/raw/lean_spipins_v4_20261121/` (or `--artifacts-dir`, which must be a fresh
directory). A rejected baseline or an accepted mutant exits non-zero.
`run_status.txt` records each case's own Lean/Yosys exit code and whether it
matched the expectation.

### Measured commands (this machine, 2026-11-21)

| Command | Exit | Wall |
|---|---|---|
| `lake build Metronome.HostCmd` | 0 | 2 s (already built) |
| `lake build Metronome.SpiPins` | 0 | 13-15 s (rebuild) |
| `lake env lean Metronome/SpiPins.lean` | 0 | 11-20 s |
| `lake env lean <generated>` (baseline) | 0 | ~5 s |
| `python code/tests/lean/spipins_check.py` | 0 | 23-29 s |
| `python code/tests/lean/spipins_check.py --mutations` | 0 | 78-98 s |
| `git diff --quiet HEAD -- src` | 0 | - |

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The elaborated synchroniser next state is SPEC_V2 §2's `s1' = raw`, `s2' = s1`, `sp' = s2`, all zero while `rst_q` is low. | `rtlStep_eq_step`, `rtlS1`, `rtlS2`, `rtlSp` | Every register value and input value symbolic. |
| The `u_host` connections are `sck = s2[8]`, `sck_p = sp[8]`, `cs_n = s2[9]`, `mosi = s2[10]`, `rst_n = rst_q`. | `hostSck_eq`, `hostSckPrev_eq`, `hostCsN_eq`, `hostMosi_eq` (wiring identities are the extraction's structural check; the theorems prove the emitted expressions are the specification's fields) | Extraction rejects any other bit; every register value symbolic. |
| The word the host link receives is `hostInput`'s word. | `hostWord_eq` | Every register value, `rst`, `rdData`, `hland` symbolic. |
| The elaborated trace is the specification trace at every cycle. | `rtlSyncAt_eq` | Any input trace and initial state. |
| The host-link input trace of the pins through the elaborated RTL is the specification's `hostInputs`. | `rtlHostInputs_eq` | Any pin trace, any reset trace. |
| A pin level reaches the host two cycles later; `sck_p` three cycles later. | `sck_at`, `csN_at`, `mosi_at`, `sckPrev_at` | `rst_q` high in the two (three) cycles between. |
| The host's `SR` in cycle `m` is exactly the pin rise held in cycle `m-2`, while pin `CS_N` is low. | `sr_at`, `sr_pins`, `rtl_sr_pins` | `CS_N` low in every cycle, reset released, `initial = resetState`. |
| Every pin rise is one `SR`; no `SR` without a pin rise. | `sr_eq_pinRise`, `sr_of_pinRise`, `sr_of_not_pinRise` | Same, plus `pinRise`'s definition (cycles 0-2 cannot rise). |
| The MOSI bit an `SR` samples is the pin MOSI of two cycles earlier. | `mosi_pins_at` | Reset released in those two cycles. |
| Eight rising edges with bits `b7..b0` deliver that byte to the byte completion. | `byte_chain`, `byte_at`, `byte8_bits` | `Clean` window, `period ≥ 1`, MOSI bits as stated. |
| The command byte, address bytes and a data byte complete into the next phase. | `complete_cmd`, `complete_ah`, `complete_al`, `byte_strobe`, `data_step` | Eight edges, `CS_N` low, reset released, no acknowledgement. |
| A pin-level write transaction `[0x02, AH, AL, d0..dk]` produces `wr` with `(addr, wdata) = ({AH,AL}+j, dj)` in the cycle after byte `j`'s eighth edge. | `transaction_strobes` (specification trace), `rtl_transaction_strobes` (elaborated trace) | `period ≥ 2`, `first ≥ 3`, `3 ≤ nbytes`, reset released, `CS_N` low, exactly the listed rises, MOSI stability, no acknowledgement. |

`AtPhase`/`AtByte` are abbreviations ("phase `p`, bit count 0, no strobe,
address `a`, some shift-register content"); the receive register content is
never named by the caller, so the byte chain stays small.

### Timing premises, and why

* **`period ≥ 2` (`hp`).** The trace samples one pin level per clock, so each
  SCK phase must last at least one cycle to be representable: a high phase and
  a low phase of at least one cycle. This is the minimum the proofs need
  (`prog_advance`, `strobe_settle`, `settle_prog`). SPEC_V2 §9's "keep SCK at or
  below clk/16" gives `period ≥ 16`; the extra margin is a physical
  setup/hold and metastability requirement that the discrete model does not
  represent, not a proof obligation.
* **`first ≥ 3` (`hf`).** `pinRise` is `false` in cycles 0-2: the synchronisers
  are zero out of reset, so the host cannot see a rise before cycle 2, and
  `sck_p` needs a third cycle. Starting the transaction at or after cycle 3
  keeps the pin model and the specification in agreement from the first edge.
* **MOSI stability (`hbit`).** SCK and MOSI go through the same two-stage
  chain, so the bit the host samples at an `SR` is the pin MOSI of the cycle in
  which SCK is first sampled high (`m-2`). The premise states exactly that:
  `bit (raws (srAt ... - 2)) 10 = bit8 (bytes m) (7 - k)`. In a mode-0
  waveform, where the master changes MOSI on a falling edge and the low phase
  lasts at least one cycle, this is the usual setup requirement: the bit must
  be valid at the rising edge. A MOSI change coincident with the first high
  cycle, a glitch, or a metastable sample is outside the model.
* **`CS_N` low everywhere (`hcs`) and reset released (`hreset`).** Both are
  sampled levels in the whole transaction; a `CS_N` high in the middle would
  reset the byte state (a separate `HostCmd` theorem) and is not part of a
  transaction.
* **Exactly the listed rises (`hrise`, `honly`).** The byte framing assumes no
  extra edge between the byte edges; `Clean`'s `nosr` field is discharged from
  `honly` plus `srAt` monotonicity.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `spipins_sck_from_s1` | `u_host.sck` takes `s1[8]`: one synchroniser stage dropped for SCK only | Structural check: `u_host.sck is not s2[8]` |
| `spipins_cs_mosi_swap` | `CS_N` and `MOSI` reach the host on each other's pins | Structural check: `u_host.cs_n is not s2[9]` |
| `spipins_sckp_from_s2` | `u_host.sck_p` takes `s2[8]`: the edge detector loses its third delay | Structural check: `u_host.sck_p is not sp[8]` |
| `spipins_sp_stage_dropped` | `sp <= s2` becomes `sp <= s1` | Generated Lean: `rtlSp` cannot prove `state.s1 = state.s2` |
| `spipins_s2_bypass` | `s2 <= s1` becomes `s2 <= {ui_in, uio_in}` | Structural check: `s1` is then unused, `opt_clean` removes it, and the extraction refuses the design (`s1: missing net`) |

The extraction is fail-closed: a register with an initial value, an
asynchronous reset on `s1`/`s2`/`sp`, a second driver, a different clock, a
`rst_q` that is not the asynchronously cleared reset register, or any other
`u_host` connection bit is rejected before any proof runs.

### Trust added

* Yosys elaboration and the RTLIL adapter are the same trust base as the rest
  of the Lean suite. No new cell shapes are needed: the synchroniser cones are
  `$mux` + `$dff`, and the four host port bits are read through
  `DffCone.expression`, the adapter's own expression builder (no private
  API, no local cell decoding).
* The extraction checks that `s1`, `s2`, `sp` are 16-bit plain registers on
  `clk` with no initial value and exactly one driver, that `rst_q` is the
  asynchronously cleared reset register fed from `rst_n`, and that the `u_host`
  connections are exactly the four bits above plus `rst_n = rst_q`. Anything
  else fails extraction, so the generated Lean cannot silently prove something
  weaker.
* The host-word expressions are built **from the actual net bit** found in the
  design, not from the specification: a wrong connection changes the emitted
  expression and the corresponding theorem fails (see the mutants).
* `bv_decide` native certificates. The accepted run's audit shows `propext`,
  `Classical.choice`, `Quot.sound` and per-theorem
  `*.bv_decide.ax_*` certificates; `sorryAx` is absent and the runner rejects
  it. This is the same trust class as `hostcmd_check.py`.

### Gaps

* The pins are **sampled** levels: metastability, sub-cycle glitches, physical
  setup/hold and the asynchronous behaviour of `rst_m`/`rst_q` between clock
  edges are not modelled. `rst_q` enters the cut as a free per-cycle input,
  exactly as in every other cut of the suite; the structural check only makes
  sure it really is the reset synchroniser's output.
* Only the write path is composed. The read path (`TX`, `MISO`, `rd_val`) is a
  separate cut (`hostread_check.py`).
* The transaction assumes `CS_N` low for the whole burst and exactly the listed
  SCK rises; a premature `CS_N` high or an extra edge is outside the premises.
* `bytes` is a free function: the theorem states what the pins clock in, not
  that a particular program is what was intended.
* `first ≥ 3` and `period ≥ 2` are model premises, not silicon measurements;
  the 60 MHz clock and clk/16 SCK give `period = 16` in a real capture.
* The composed headline (`rtl_transaction_strobes`) is stated on the
  *elaborated* trace via `rtlHostInputs`; it still takes the address-decode
  side (`hack`, the no-acknowledgement premise) as a hypothesis, like
  `HostCmd.transaction_strobes`.

### Reading the evidence

`data/raw/lean_spipins_v4_20261121/`:

| File | Contents |
|---|---|
| `stdout.log` | Full run transcript (Yosys log, extraction facts, Lean output, mutation outcomes) |
| `run_status.txt` | One line per case: outcome, real exit code, expectation |
| `tools.log` | `lake --version`, `yosys -V` |
| `lake.log` | `lake build Metronome.SpiPins` |
| `baseline.spipins.lean` | Generated extraction + template, exactly what Lean checked |
| `baseline.log`, `baseline.axioms.txt` | Lean output and `#print axioms` records |
| `<mutant>.spipins.lean`, `<mutant>.log` | Same for each mutant that reached Lean |

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/spipins/`).

## Data-RAM arbiter cut (`mem_check.py`)

Item 3F of the verification plan: the data-RAM arbiter, pointer `P0` and the
host request slot of [src/md2_mem.v](../../../src/md2_mem.v), with the data-RAM
wrapper [src/md2_dmem.v](../../../src/md2_dmem.v) reduced to its SRAM macro
boundary (the macro is a black box, `src/md2_sram_bb.v`).

| Path | Role |
|---|---|
| [Metronome/Mem.lean](Metronome/Mem.lean) | independent specification: state, grants, the served access, pointer moves, landing, freeze, traces (SPEC_V2 §6.1–6.2, §9, §9a.4, §12.3–12.4; SPEC v1 §6.1, §9a.2–9a.3) |
| [mem_check.py](mem_check.py) | Yosys elaboration (`-D USE_IHP_SRAM`), chip-top and macro-boundary checks, cone extraction, Lean emission, mutation runs, evidence |
| [MemEquivalence.lean.in](MemEquivalence.lean.in) | proof template: per-register and per-output equalities, the trace lift, the specification's corollaries on the RTL trace, axiom audit |
| `data/raw/lean_mem_v4_20261121/` | evidence of the accepted run (generated Lean, logs, axiom audit, tool versions, `run_status.txt`) |

The module is not part of the default library target, so `lake build` does not
build it; use `lake build Metronome.Mem` (or `lake env lean
Metronome/Mem.lean`), as the other cuts do.  `verify.py` does not run this cut
yet: the hook tuple to add is
`("mem", mem_check, mem_check.check_mem)` in `verify.py`'s per-cut dispatch,
after `import mem_check` (`check_mem(src_dir_or_json, out_dir, *, lake, yosys,
case="baseline")`, `run_mutations(snapshot, out_dir, lake, yosys)`).

### Run it

```text
python code/tests/lean/mem_check.py                      # baseline
python code/tests/lean/mem_check.py --mutations           # plus eight mutants
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the defaults write into
`data/raw/lean_mem_v4_20261121/` (`--artifacts-dir`, which must not exist yet).
A rejected baseline or an accepted mutant exits non-zero.  `run_status.txt`
records each case's own Lean/Yosys exit code and whether it matched the
expectation.  Every Lean run has a 900 s timeout and a single retry when the
process dies without a diagnostic (a transient crash under machine load has
been observed; a retry is logged in `<case>.log`).

### What is cut

Yosys elaborates the real chip top with `-D USE_IHP_SRAM`, so `md2_dmem`
instantiates the black-box `RM_IHPSG13_1P_512x32_c2_bm_bist` rather than the
behavioural array.  The adapter then:

1. Checks `u_mem`'s clock, `rst_n = rst_q`, `frz`, `frzd`, the two stream
   request/write/address/data ports, `s0_word = s_word[0]`,
   `s0_wword = s_ww[31:0]`, `p_we = w_p0[14]`, `p_d = w_p0[7:0]`, `p_sel`,
   `p_rdy`/`p_dat`/`p_haz` and `h_wr`/`h_d`/`h_land`/`h_land_d`.
2. Checks the host request strobe structurally: `u_mem.h_set` is the `Y` of an
   AND whose operands are `in_data` and the `Y` of an OR of `h_wr` and `h_rd`
   (exactly `(h_wr | h_rd) & in_data`, cf. `check_read_top` in
   `hostread_check.py`).  It also checks that `u_host.hland`/`hland_d`/`rd_data`/
   `rd` are those same nets, so the landing theorem is about the nets the host
   read cut consumes.
3. Checks that the RAM port is the wrapper's: `ren/we/addr/be/wd/rd` of `u_dmem`
   are `m_ren/m_we/m_addr/m_be/m_wd/m_rd`, and that `u_dmem`'s macro instance
   `u_sram` has `A_CLK/A_ADDR/A_DIN/A_DOUT/A_WEN` on `clk/addr/wd/rd/we`,
   `A_MEN = ren | we`, `A_REN = ren & ~we`, `A_DLY = 1`, every `A_BIST_*` tied
   to 0, and **every bit of `A_BM[8k..8k+7]` equal to `be[k]`** (the byte-mask
   replication).  This is the `md2_dmem` "lane/byte-enable logic"; the macro's
   storage and timing stay outside.
4. Extracts the fifteen registers (`ptr`, `rq`, `rqa`, `rqd`, `p_rdy`,
   `p_dat`, `land`, `plane`, `lok`, `hq`, `hqw`, `hqa`, `hqd`, `h_land`,
   `hlane`) and the nine RAM-port/arbiter outputs
   (`s_gnt`, `m_we`, `m_ren`, `m_addr`, `m_be`, `m_wd`, `p_haz`, `h_land_d`,
   plus the registered `p_rdy`/`p_dat`/`h_land`) into Lean definitions.

`MemCone` (local to `mem_check.py`; the shared `rtlil.py` is unchanged) adds the
shapes these cones need: `$mul` with one constant operand (the `8 * lane`
part-select), `$shl`/`$shr` with a symbolic amount (the one-hot byte lane),
`$reduce_or`/`$reduce_bool` (`|s_req`, `rq != 0`) and `$logic_not` (`rq == 0`).
A contiguous slice of a *driven* bus is read as one shifted truncation, a
concatenation is assembled field by field, and an `$add` with a constant zero
addend (Yosys's `8*lane + 0` for a part select) is folded away.  Every
extension is fail-closed: an unsupported cell, an unresolvable or ambiguous
bus, a second driver or a partially overlapping slice raises `UnsupportedRTL`.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted next state is the specification's, register by register: `PTR`, `REQ`, the write request's address/data latches, `RDY`, `D`, the landing triple (`land`, lane, "may raise RDY"), the host slot (`hq`, `hqw`, `hqa`, `hqd`), the landing strobe and its lane. | `rtlPtr`, `rtlReq`, `rtlReqAddr`, `rtlReqData`, `rtlRdy`, `rtlDat`, `rtlLand`, `rtlLandLane`, `rtlLandRdy`, `rtlHostQ`, `rtlHostWr`, `rtlHostAddr`, `rtlHostData`, `rtlHLand`, `rtlHLane` | Every state and input value symbolic.  Unconditional (the equations are total; the unused request code is unreachable, see below). |
| The extracted transition equals the specification transition. | `rtlStep_eq_step` | Assembled from the fifteen register equalities. |
| The extracted outputs (`s_gnt`, `m_we`, `m_ren`, `m_addr`, `m_be`, `m_wd`, the hazard event, `h_land_d`, and `p_rdy`/`p_dat`/`h_land`) are the specification's. | `rtlSGnt`, `rtlMWe`, `rtlMRen`, `rtlMAddr`, `rtlMBe`, `rtlMWd`, `rtlHazEvent`, `rtlHLandD`, `rtlPRdy`, `rtlPDat`, `rtlHLandOut`, `rtlOuts_eq_outs` | Same. |
| The elaborated trace is the specification trace. | `rtlStateAt_eq`, `rtl_trace_result`, `rtl_trace_outputs` | Any finite prefix, any initial state. |
| At most one requester is served per cycle, in the order S0, S1, P0, host: every pair of grants is mutually exclusive (an S0 grant excludes S1/P0/host, etc.). | `grants_exclusive`, `rtl_trace_grants_exclusive`, `grantP0_excludes_host`, `grantP0_excludes_s0`, `grantP0_excludes_s1`, `grantS0_excludes_p0` | All values symbolic. |
| The served requester is the highest-priority pending one, with a **one-cycle bounded wait**: a request visible in cycle `n` is served in `n` itself when nothing higher is pending; a request set at the end of `n-1` is visible in `n`. | `grantS0_served`, `grantS1_served`, `grantP0_served`, `grantHost_served`, `request_set_visible`, `rtl_trace_p0_served`, `rtl_trace_host_served`, `rtl_trace_request_visible` | No higher-priority request, reset released for the register equation; the host is also served in any frozen cycle (§12.3). |
| A pointer write served in cycle `n` presents the latched address and byte: word `reqAddr[10:2]`, byte lane `reqAddr[1:0]`, the byte replicated to four lanes. | `served_write_ports`, `rtl_trace_p0_write`, `byteAddr_p0_write`, `writeByte_p0` | `grantP0`, `REQ = write`. |
| A pointer fetch served in cycle `n` reads `PTR`, lands at the end of `n+1` and makes its byte visible with `RDY` in `n+2` (§6.2), from the word presented in `n+1`, in `PTR[1:0]`. | `served_fetch_ports`, `served_fetch_lands`, `landing_captures`, `landing_sets_rdy`, `trace_p0_read_lands`, `rtl_trace_p0_read_lands` | No pointer move in the serve or landing cycle (§9a.3), no frozen cycle in either and `FRZD` low in the landing cycle (§12.3), reset released. |
| `MEMHAZ` is raised exactly when a pointer move replaces an unserved request; a move in the serve cycle, or a move with nothing pending, raises none (§9a.2). | `haz_replaced`, `no_haz_when_served`, `no_haz_without_request`, `rtl_trace_haz_replaced`, `rtl_trace_no_haz_when_served`, `pending_none` | `pWe`/state premises only. |
| A new host request overwrites an unserved one (§9a.4) and a served one clears the slot. | `rtlHostQ`, `rtlHostWr`, `rtlHostAddr`, `rtlHostData` | Every value symbolic (no "unserved" distinction needed: the equations are the `if (h_set) … else if (gh)` priority). |
| A host read served in cycle `n` lands in `n+1` with the served request's lane of the word the RAM presents in `n+1` — the host read cut's landing premise, discharged in terms of the RAM word input. | `trace_host_read_lands`, `rtl_trace_host_read_lands` | `grantHost` in `n`, `hqw = 0`, reset released. |
| With the SRAM macro contract, that byte is the data-RAM byte at the served address. | `RamContract`, `trace_host_read_data`, `rtl_trace_host_read_data` | `RamContract ram word addr : ∀ n, word (n+1) = ram (addr n)`; `addr` is the arbiter's `m_addr`. |
| In a frozen cycle only the host is served, the pointer holds and `dat` is the only change (the landing exception, captured once because `FRZD` is low). | `frozen_holds`, `frozen_access_is_host`, `frozen_landing_captures`, `rtl_trace_frozen` | `FRZ`, no pointer move, reset released. |
| A served S0 edge-capture push is a whole-word write: all four lanes, the 32-bit record; an ordinary byte write enables exactly the addressed lane. | `s0_word_write`, `byte_write_lane`, `rtl_trace_s0_word_write` | `grantS0 ∧ s0Word`, or "not a whole-word write". |
| The request slot's fourth code is unreachable: reset leaves 0, and a code 3 can only come from a state that already has it. | `reqNext_three`, `reqNext_ne`, `stateAt_req_ne_three`, `rtl_trace_req_ne_three` | A sampled reset at cycle 0. |

### What stays free

The per-cycle inputs are the whole arbiter interface: `resetN`, `frz`, `frzd`,
`sReq`, `sWe`, `sAddr`, `sWd`, `s0Word`, `s0WWord`, `pWe`, `pSel`, `pData`,
`hSet`, `hWr`, `hAddr`, `hData` and the SRAM word `ramWord`.  Everything that
produces those values is another cut or another team's evidence:

* `pWe`/`pSel`/`pData` are the winning move of the `P0` write group
  (`w_p0[14]`, `w_p0[7:0]` and the `p_sel` decode of `w_p0[13:8]`).  The adapter
  checks that `p_we` and `p_d` are those bits; the four-way select decode
  against `md2_defs.vh` (`D_P0_AL/AH/W/R`) is **not** checked here — it is the
  move-pick cut's business (`corectl_check.py` proves the pick, not the decode).
* `s_req`/`s_we`/`s_addr`/`s_wd`/`s0_word`/`s0_wword` are the stream units'
  outputs (`md2_stream.v`); the stream contract (one request held until served,
  `LD`/`WV`/`PV` timing) is not modelled.
* `hSet`/`hWr`/`hAddr`/`hData` come from the host link; the chip-top `h_set`
  filter is checked structurally, and `h_wr`/`ha`/`h_wd` are the host cut's nets.
* `frz`/`frzd` come from the freeze cut (`Metronome.CoreCtl`, `corectl_check.py`),
  which proves `FRZ`'s own next state; this cut treats them as per-cycle inputs,
  so the "`FRZD' = FRZ`" link between two cycles is a premise of
  `trace_p0_read_lands` (`(inputs (n+1)).frzd = false`), not re-proved.
* `ramWord` is the SRAM macro's `A_DOUT`.  The macro's storage and its
  "read presented in `s` → word at the output in `s+1`" timing are **not**
  modelled: `RamContract` states the timing as a premise of the landing
  theorems.  The macro's byte mask (`A_BM`) and port wiring are checked
  structurally.

### Trust added

* Yosys elaboration, the RTLIL adapter and the generated Lean: the same base as
  the rest of the suite.  This cut reads the specialized `md2_mem`/`md2_dmem`
  modules, their port directions and the macro instance.
* `MemCone` extends the adapter **locally** (`rtlil.py` is unchanged) with the
  shapes listed above.  Each is fail-closed.  The field-wise assembly increments
  the run length (a per-run truncation width), and the emitted expression is
  checked by the Lean proof, so an assembly that dropped a bit would fail the
  equivalence rather than pass silently.
* The SRAM macro is a black box (`(* blackbox *)` in `src/md2_sram_bb.v`); the
  cut's use of `-D USE_IHP_SRAM` is what makes the boundary visible.  Nothing is
  claimed about the macro's contents, latency, bit-mask implementation or BIST.
* `bv_decide` on `rtlSGnt` and `frozen_access_is_host` emits per-theorem native
  LRAT certificate axioms (`rtlSGnt._native.bv_decide.ax_1_19`,
  `frozen_access_is_host._native.bv_decide.ax_1_7`); `rtlStep_eq_step`,
  `rtlOuts_eq_outs`, `rtlStateAt_eq`, `rtl_trace_host_read_lands`,
  `rtl_trace_p0_read_lands` and `rtl_trace_frozen` otherwise use only
  `propext`, `Classical.choice` and `Quot.sound`.  `#print axioms` is recorded in
  `<case>.axioms.txt`; `sorryAx` is absent from the accepted case, and
  `-DwarningAsError=true` makes a `sorry` a hard error before the audit anyway.
  (A rejected case's audit shows `sorryAx` for the declarations downstream of
  the theorem that failed, because Lean recovers from an error with `sorry`;
  such a case is reported as `rejected by Lean`, never as "used sorryAx", since
  the exit code is checked first.)  The native certificate checker is the only
  trust added beyond Yosys, the adapter and the JSON reader.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `mem_p0_over_s1` | P0 is served while S1 requests (`gp` drops the stream-idle condition and `gs1` is gated off by `gp`) | `rtlReq` (the request-slot equation no longer agrees; the grant/address equations disagree too) |
| `mem_host_first` | the host is served whenever it asks (`gh = hq`), ahead of every stream and the pointer | `rtlHostQ` (the slot is cleared in a cycle the specification holds it) |
| `mem_host_lane` | the host landing takes `hqa[2:1]` instead of `hqa[1:0]` | `rtlHLane` |
| `mem_host_no_overwrite` | a new host request no longer overwrites an unserved one (`if (h_set & ~hq)`) | `rtlHostQ` (with the slot occupied and a served request the RTL now clears instead of overwriting) |
| `mem_p0_rdy_early` | `RDY` is raised in the serve cycle (`gp & lok & ~frz`) instead of one cycle later | `rtlRdy` |
| `mem_ptr_wrap_1024` | the pointer wraps at 1,024 bytes (`ptr[9:0] + 1`) instead of 2,048 | `rtlPtr` |
| `mem_s0_word_be` | the S0 whole-word write loses its all-lane mask (`4'hF & (1 << lane)`) | `rtlMBe` |
| `mem_dmem_lane` | `md2_dmem`'s byte-mask replication swaps lanes 0 and 1 | the structural macro-boundary check (`u_sram.A_BM: bit 0 is not be[0]`) |

Seven of eight are rejected by the generated Lean (the reported theorem is the
first failing declaration); one is a structural rejection.  A first attempt at
`mem_p0_rdy_early` (`gp & (rq == RQ_FETCH)`) removed the last read of the `lok`
register, so Yosys optimised it away and the extraction failed closed before
Lean ran; the mutant above keeps every register live.

### SPEC ambiguities and RTL/SPEC differences (reported, not fixed)

1. **`p_we` in a frozen cycle.**  SPEC_V2 §12.3 says a frozen cycle has no
   moves, so `P0` holds.  `md2_mem.v` is stricter in intent but total in form:
   `ptr`, `rq` and `p_rdy` are still updated by `p_we` inside a frozen cycle
   (only the *serve* logic is gated by `frz`).  The specification keeps the same
   total equations, and the freeze claim is stated with `pWe = false` — which
   is exactly the SPEC's "no moves" condition.  A pointer move in a frozen
   cycle would be a real deviation; it is unreachable because the core does not
   dispatch while frozen.
2. **The host landing lane when a new request is set in the served cycle.**
   `hlane <= hqa[1:0]` samples the *current* slot unconditionally, so a host
   request set in the same cycle the previous one is served leaves the landing
   in `s+1` using the new address's lane while the strobe refers to the served
   (old) read.  Host writes are at least one SPI byte apart, so this is
   unreachable; the cut proves the landing for the served request's address
   without needing a "no new request" premise, and does not model the
   unreachable combination.
3. **Pointer-request code 3.**  The 2-bit `REQ` has three documented values; the
   fourth (`2'd3`) behaves as a pending fetch in the RTL.  `reqNext_three` and
   `stateAt_req_ne_three` show it is unreachable from reset, so no theorem
   depends on it.
4. **`RDY` and a frozen landing cycle.**  §12.3 says `RDY` "updates in the first
   unfrozen cycle as usual".  In the RTL, `p_rdy` is set by
   `land & lok & ~frz`, so the landing deferred by a freeze is raised in the
   first unfrozen cycle — consistent with the prose, but only under the
   premise that `land` is still set then (it is, because `land` is held while
   `frz`).  The cut proves the unfrozen case and states the landing/dat
   exception separately.
5. **No SPEC sentence fixes the byte lane of a host landing.**  §6.2 gives
   `a[1:0]` little-endian and §9 says the byte is loaded at the end of `s+1`;
   the "lane of the served request's address" is read out of that pair, and the
   cut proves it.  A reader who expects the lane to be re-derived from the word
   address at landing time would be wrong: the RTL latches it at the serve.

### Gaps

* The SRAM macro's timing and storage (`RamContract`) are a premise; a change to
  the macro or to `md2_dmem`'s A_DLY/A_REN behaviour is not covered.
* The whole-word write (S0 edge capture) is proved as *the arbiter's port
  behaviour*; the record contents (`{DC[18:0], PIN[12:0]}`) come from the stream
  and the pin synchronisers.
* `p_sel`'s four-way decode of the winning move's destination code is free (see
  "what stays free").
* Physical timing — setup/hold, the macro's setup/hold and output delay, the
  60 MHz closure — is out of scope, as in the other cuts.
* The host read cut's `hland`/`hland_d` premise is now discharged in terms of
  `ramWord`; composing the two cuts (replacing `input.hland`/`hlandD` of
  `Metronome.HostRead` by this module's outputs) is a mechanical step that is
  documented here but not yet written as a Lean composition theorem.

### Timing

`python code/tests/lean/mem_check.py --mutations --artifacts-dir
data/raw/lean_mem_v4_20261121` exited 0 on 2026-11-21 and took 224 s wall clock
on a 10-core i5-1245U laptop that was carrying other Lean/Yosys runs.  The RTL
snapshot was `src/` at HEAD `b7b4068`; the baseline log records its SHA-256
(`434c6ae6…`), and `git diff --quiet HEAD -- src` is true.  The baseline case
(Yosys, extraction, the 26 KB generated proof and its ~30 theorems) took 13.9 s
of Lean; the mutants took 13.1–29.0 s of Lean each (`mem_p0_over_s1` 29.0 s,
`mem_host_first` 14.7 s, `mem_host_lane` 16.0 s, `mem_host_no_overwrite` 16.9 s,
`mem_p0_rdy_early` 16.0 s, `mem_ptr_wrap_1024` 15.3 s, `mem_s0_word_be` 13.1 s;
`mem_dmem_lane` is rejected before Lean).  The largest generated expression is
`m_wd` (32 bits from a byte-replicating concatenation); no individual equality
dominates the baseline.  An earlier run of the same command took 244 s (22.4 s
of baseline Lean) on a busier machine, so the spread is machine load rather than
proof content.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/mem/`).

## Thread cut notes (SPEC_V2 sections 4, 5, 9, 12.3)

Evidence: `data/raw/lean_thread_v4_20261121/` (baseline plus six mutants).
Code: `Metronome/Thread.lean` (specification), `thread_check.py` (adapter,
generator, mutations), `ThreadEquivalence.lean.in` (proof template).

Run (PowerShell, from the repository root):

```powershell
$cad = "$env:USERPROFILE/tools/oss-cad-suite"
$env:PATH = "$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"
python code/tests/lean/thread_check.py --mutations --artifacts-dir data/raw/lean_thread_v4_20261121
```

The Python entry point is `thread_check.check_thread(src_dir_or_json, out_dir,
*, lake, yosys, case="baseline") -> {ok, outcome, exit, ...}`.  It raises
`ThreadRejected` on a failed proof or a `sorryAx` audit, `UnsupportedRTL` on a
structural/wiring failure, and `ThreadCrashed` if the Lean process dies without
a verdict (a crash is retried once and is never counted as a rejected mutant).
`run_mutations(snapshot, out_dir, lake, yosys)` returns
`(case, rejected, stage, code)` records.  The `verify.py` hook is the tuple

```python
("thread", thread_check, thread_check.check_thread)
```

`verify.py` itself was not edited in this task.

### What is proved

Two cuts, both re-elaborating the current `src/` with `verify.py`'s Yosys recipe
(`read_verilog -I src ...; hierarchy -check -top tt_um_brentius_metronome; proc;
opt_clean; write_json`).

#### Module cut: `md2_thread` next state

The adapter extracts all seven registers (`pc`, `en`, `ready`, `running`,
`armed`, `late`, `ovr`) of the elaborated `md2_thread` module through
`rtlil.DffCone`.  The module's reset is synchronous, so `rst_n` is an input of
the extracted `rtlStep` and the reset branch is part of the proved equality.  The
specification `Metronome.Thread.step` is written from SPEC_V2 §4 (state, trigger,
disarm, late, stop), §5 (dispatch and pause) and §9 (`PC`/`STAT` bytes), with
the freeze gate discussed below.

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted seven-register transition equals the SPEC §4/§5/§9 transition, including the reset sample. | `rtlStep_eq_step` | Every state value and every sampled input symbolic. `bv_decide` per field, in the adapter's `BitVec`/`Bool` form. |
| The extracted trace equals the specification trace at every cycle. | `rtlStateAt_eq`, `rtl_trace_result` | Same initial state, any finite sampled input sequence. |
| `READY` and `RUNNING` stay exclusive on the extracted trace. | `rtl_trace_exclusive`, plus the spec-side `Exclusive`, `exclusive_reset`, `exclusive_step` | `READY` and `RUNNING` are exclusive from reset: a dispatch clears `READY` and an accepted trigger needs both clear. |
| A trigger while busy sets the sticky `OVR`, even in the cycle a host `STAT` write clears it, and a quiet cycle cannot set it. | `rtl_trace_ovr_of_busy_trigger`, plus `ovr_set`, `ovr_set_beats_clear`, `ovr_quiet`, `ovr_clear`, `ovr_sticky` | Active cycle (`resetN = true`); §9 sticky-set rule. |
| A trigger while busy is dropped: `READY` and `ARMED` are unchanged (only a same-cycle dispatch or `BEAT` may change them). | `no_accept_while_busy`, `drop_trigger_ready`, `drop_trigger_armed` | Active cycle; no dispatch in the cycle for `READY`, no `BEAT` for `ARMED`. |
| A dispatch clears `READY` and sets `RUNNING`; a pause clears `RUNNING` and loads `npc`; a host `PC` write beats the pause. | `dispatch_clears_ready`, `dispatch_sets_running`, `pause_clears_running`, `pause_sets_pc`, `host_pc_beats_pause` | Active cycle; `dispatch_sets_running` also needs no pause, `pause_sets_pc` no host write. |
| An accepted trigger sets `READY` and `ARMED`; a `BEAT` disarms unless an accepted trigger is in the same cycle; otherwise `ARMED` holds. | `accept_sets_ready`, `accept_sets_armed`, `armed_beat`, `armed_hold` | Active cycle; `accept_sets_ready` needs no dispatch. |
| `EN` follows a host `STAT` write (bit 3) over `T.STOP`, and `T.STOP` clears it. | `host_en_beats_stop`, `stop_clears_en` | Active cycle; `stop_clears_en` needs no host write. |
| `LATE` is sticky: a late symbol move sets it over a same-cycle clear, a bit-4 write clears a quiet flag, otherwise it holds. | `late_set`, `late_clear`, `late_sticky` | Active cycle; §9 sticky-set rule. |
| The RTL's two implicit resolutions hold on the extracted transition. | `rtlRunning_pause_dispatch`, `rtlPc_host_beats_pause`, `rtlOvr_set_beats_clear`, `rtlEn_host_beats_stop`, `rtlArmed_accept_beats_beat` | Transferred from the spec facts through `rtlStep_eq_step`. |

#### Chip-top cut: the six `g_thr[k].u` instances

`clk` and `rst_n` are checked structurally (top clock, `rst_q`); `h_d` is
checked to be `h_wd`.  The output pins are checked to be the `t_pc`/`t_en`/
`t_ready`/`t_running`/`t_armed`/`t_late`/`t_ovr` slices.  Every input cone is
extracted fail-closed with the upstream nets bound as free per-cycle leaves.

| Claim | Theorem (per `k = 0..5`) | Conditions |
|---|---|---|
| `ev` is the SPEC §4 event decode, gated by `~frz` (§12.3). | `rtlEvIn{k}_eq_spec` | Free leaves; the table is `machine.json`/`md2_defs.vh` codes 1..24 and 28, plus the thread's line pin edges (25..27) and `ALWAYS = !READY && !RUNNING` (29). `NONE` (0) and 30/31 never fire. |
| `db` is the thread's doorbell bit gated by `~frz`. | `rtlDbIn{k}_eq_spec` | Free doorbell register and `frz`. |
| `disp` is "a core dispatches this thread". | `rtlDisp{k}_eq_spec` | `dsp[c] & (disp_e` slice `== k)`, both cores. |
| `pause` is "the executing core retires a pausing instruction for this thread". | `rtlPause{k}_eq_spec` | `pse[c] & (xt` slice `== k)`. |
| `npc` is the pausing core's byte: core 1's high half, else core 0's low half. | `rtlNpc{k}_eq_spec` | `pse[1] & (xt[5:3] == k)` selects the high byte. |
| `stop` is one of this thread's own enabled moves to `DG_T_STOP`. | `rtlStop{k}_eq_spec` | Six move slots; "own" by core 0/1 `xt` slice; `mv_valid` and `grp_v`. |
| `late_set` is one of its own enabled symbol moves while `ARMED = 0`. | `rtlLate{k}_eq_spec` | Same, with `DG_L_SYM` and `!t_armed[k]`. |
| `line_beat` is `l_beat[LINE]`. | `rtlBeat{k}_eq_spec` | `LINE = tc[2:1]`, `TRIG = tc[7:3]`. |
| The `PC`/`STAT` write enables are `w_trt & i_trt == k & o_trt == offset`. | `rtlPcWe{k}_eq_spec`, `rtlStatWe{k}_eq_spec` | `w_trt = h_wr & a_trt < HSPAN_TRT`, `i_trt = a_trt >> 1`, `o_trt = a_trt & (HS_TRT-1)`; offsets 0 and 1 from `md2_map.vh`. |
| The two `TRT` bytes of thread `k` are inside `HostMap`'s `trt` window and decode to `(k, offset)`. | `hostMap_trt_{k}_PC`, `hostMap_trt_{k}_STAT` | Concrete addresses from `HA_TRT_BASE`/`HS_TRT`/`HO_TRT_*`; `decide` against `Metronome.HostMap`. |

The event table is also cross-checked outside Lean: `thread_check.py` requires
`code/md2/machine.json`'s `triggers` list to be exactly the SPEC order and reads
every `T_*` constant from `src/md2_defs.vh` (requiring code == index), and it
reads `HA_TRT_BASE`, `HSPAN_TRT`, `HS_TRT`, `HO_TRT_PC`, `HO_TRT_STAT`,
`DG_L_SYM` and `DG_T_STOP` from the generated headers, requiring the documented
values.  A drifted header fails the check before Lean runs.

#### Free leaves and premises

The chip-top cut binds these per-cycle nets as opaque inputs (all are upstream
of the thread instances): `frz`, `l_beat`, `l_tap`, `fl`, `flp`, `inv`, `invp`,
`l_parise`, `l_pafall`, `t_ready`, `t_running`, `t_armed`, `db`, `dsp`,
`disp_e`, `pse`, `xt`, `npc`, `grp_v`, `mv_valid`, `h_wr`, `ha`, `h_wd`, and
the instance's `tc` configuration byte.  Binding these is an over-approximation
that is sound for the universal statements proved, and the statements name them,
so the claim is "given these SPEC quantities, each instance input is the SPEC
quantity".

The module cut's only premises are the SPEC ones inside `step` (its `hv` inputs
are the thread's own `ev`/`db`/`disp`/`pause`/`stop`/`late_set`/`line_beat` and
the host bytes) plus `resetN = true` for the active-cycle facts.

### Mutations

Six regressions on temporary copies of `src/` (never the repository); all six
are rejected by the generated Lean.

| Mutation | Change | Rejected by |
|---|---|---|
| `thread_pause_dispatch` | dispatch beats a same-cycle pause for `RUNNING` | `rtlStep_eq_step` (`running` field) and `rtlRunning_pause_dispatch` |
| `thread_pc_pause_wins` | a pause beats a host `PC` write | `rtlStep_eq_step` (`pc` field) and `rtlPc_host_beats_pause` |
| `thread_ovr_clear_wins` | the host `STAT` clear beats a same-cycle overrun set | `rtlStep_eq_step` (`ovr` field), `rtlOvr_set_beats_clear`, and the spec-side `ovr_set_beats_clear` |
| `thread_ev_not_frozen` | `.ev(ev)`, `.db(db[k])` (no `~frz`) | `rtlEvIn{k}_eq_spec` / `rtlDbIn{k}_eq_spec` (counterexample at `frz = true`) |
| `thread3_line2_beat` | instance 3's `ln` is forced to line 2 | `rtlBeat3_eq_spec` (and `rtlEvIn3_eq_spec` for the pin edges) |
| `thread_always_ignores_running` | `ALWAYS` drops the `!RUNNING` term | `rtlEvIn{k}_eq_spec` (counterexample at `RUNNING = true`) |

Measured outcomes and exit codes are in the evidence `run_status.txt`; the
summary is repeated at the end of this file after the acceptance run.

### Acceptance run

```
python code/tests/lean/thread_check.py --mutations \
  --artifacts-dir data/raw/lean_thread_v4_20261121
```

exited **0** on 2026-11-21, wall clock **765 s** (12 min 45 s) on a 10-core
i5-1245U laptop, with Lean 4.35.0 and Yosys 0.70+190.  `run_status.txt`:

| Case | Outcome | Lean exit | Expectation |
|---|---|---|---|
| `baseline` | accepted | 0 | ok |
| `thread_pause_dispatch` | rejected by `rtlStep_eq_step` (real counterexample) | 1 | ok |
| `thread_pc_pause_wins` | rejected by `rtlStep_eq_step` (bv_decide abstained: it found no counterexample and no proof, so the equality is still unproved) | 1 | ok |
| `thread_ovr_clear_wins` | rejected by `rtlStep_eq_step` (real counterexample) | 1 | ok |
| `thread_ev_not_frozen` | rejected by `rtlEvIn{k}_eq_spec` and `rtlDbIn{k}_eq_spec` (counterexamples at `frz = true`) | 1 | ok |
| `thread3_line2_beat` | rejected by `rtlEvIn3_eq_spec` and `rtlBeat3_eq_spec` (counterexample `tc = 0xFF`, `beat = 7`) | 1 | ok |
| `thread_always_ignores_running` | rejected by `rtlEvIn{k}_eq_spec` (counterexample at `RUNNING = 1`, `READY = 0`) | 1 | ok |

Per-case Lean wall time from the artifact timestamps: baseline 94 s,
`thread_pause_dispatch` 131 s, `thread_pc_pause_wins` 83 s,
`thread_ovr_clear_wins` 77 s, `thread_ev_not_frozen` 77 s,
`thread3_line2_beat` 78 s, `thread_always_ignores_running` 146 s (the machine
carried other work in that interval; the same cases took 68-94 s in an earlier
run).  The baseline generated file is 195 KB and the `ev` equality is the
expensive goal (~76 free bits: the event table plus the per-instance `ALWAYS`
bits).  The `rtlPc_host_beats_pause` mutant is rejected by `bv_decide`
*abstaining* rather than by a witness; the proof is still not closed, so the
mutant cannot pass, but the log says "potentially spurious counterexample"
rather than naming an assignment.

Baseline axiom audit (`baseline.axioms.txt`): the module equality and its trace
lift carry only `propext`, `Classical.choice` and `Quot.sound`; `exclusive_step`
and the chip-top equalities (event decode, stop/late, `line_beat`, and the two
host write enables) carry their per-theorem `_native.bv_decide` certificate
axioms.  No `sorryAx` appears in the baseline records; a mutant's failed
declarations do record `sorryAx`, which is why the runner rejects, not accepts,
those cases.


### Trust added

* Yosys elaboration, the RTLIL adapter and the generated Lean are the same trust
  base as the rest of the Lean suite.  The adapter is extended locally (in
  `thread_check.py`, not in `rtlil.py`) for `$logic_not` on a whole bus,
  `$reduce_or`/`$reduce_bool`, and bitwise `$and`/`$or`/`$not` on the six-bit
  move vectors; every extension is fail-closed (`UnsupportedRTL` on an unknown
  cell, an undriven bit, a partial bus or a second driver).
* `bool_of` builds one-bit cones in `Bool`: a one-bit `$mux` is rebuilt branch by
  branch as a Lean `if` (a `BitVec 1` branch cannot be mixed with a `Bool` one),
  other data cells are compared with zero, and logic cells are used directly.
* Binding a *driven* net as a free leaf (`opaque`) is a checked modelling step:
  the adapter rejects overlapping leaves and tied-off nets, and each theorem
  states the formula in terms of the leaf, so the over-approximation is explicit.
* `bv_decide` adds per-theorem native LRAT certificate axioms.  The module-cut
  equality and its trace lift use only `propext`, `Classical.choice` and
  `Quot.sound`; `exclusive_step` and every chip-top equality carry a
  `_native.bv_decide` axiom (recorded in `<case>.axioms.txt`).  The runner
  parses `#print axioms` and rejects `sorryAx`.
* Header constants are read from `src/md2_map.vh` and `src/md2_defs.vh` and
  required to be the documented values; `HostMap`'s own `base`/`span`/`inRegion`
  are imported (not copied) for the `TRT` address tie.

### SPEC ambiguities and RTL/SPEC differences (reported, not fixed)

1. **Pause vs dispatch for one thread.**  SPEC §4 gives `disp => READY' = 0,
   RUNNING' = 1` and `pause => RUNNING' = 0, PC' = npc` without an order.  §5
   makes the two cases target different threads in a legal state (`pause` is
   `XT`, `disp` picks a `READY` thread, and `READY`/`RUNNING` are exclusive), so
   the order is unobservable in a legal run.  The cut binds both as free inputs,
   so it must state one: `step` follows the RTL (pause beats dispatch) and
   `rtlStep_eq_step` proves the RTL does.  The same holds for `READY'` when a
   dispatch and an accepted trigger coincide (dispatch wins in the RTL; `accept`
   needs `!busy`, so it cannot fire for a dispatched thread in a legal run).
2. **`ARMED` under `READY`/`RUNNING`.**  No invariant relates `ARMED` to
   `READY`/`RUNNING`: a pause leaves `ARMED` set with neither claim.  This is
   consistent with §4 (only a `BEAT` disarms) and is not a difference.
3. **Thread reset values.**  §4 does not state reset values; the RTL clears all
   seven registers.  `rtlStep_eq_step` checks that equation rather than assuming
   it.
4. **Frozen cycles.**  §12.3 says a frozen cycle has no trigger acceptance and
   no moves, while host writes still apply.  The RTL implements this on the
   *input* side (`ev & ~frz`, `db[k] & ~frz`) and lets the upstream core/move
   logic suppress `disp`/`pause`/`stop`/`late_set`; this cut proves the two
   gates it can see and leaves the rest to the leaves.  No SPEC conflict.
5. **`LATE` set source.**  §4 conditions the late flag on the *thread* ("by a
   thread whose `ARMED` is 0"), and the chip-top cut proves the `own` term.  The
   `late_set` leaf is the winning-move-independent OR over the thread's own
   moves, so a losing write group still sets it, as §4 says.

### Gaps

* The core side (`dsp`, `pse`, `disp_e`, `xt`, `npc`, `mv_valid`, `grp_v`) is
  free here; scheduler, round-robin cursor and `DG_MAP` are other cuts.
* `frz` is free in the module cut; its own next state and the SPEC 12.3
  transparency statement belong to the freeze cut (`Metronome.CoreCtl`).
* The `t_ready`/`t_running` inputs of `ALWAYS` are the instance's own outputs,
  bound free per cycle: the cut proves the decode formula, not that the
  registers hold a particular value.
* Physical timing, the reset synchroniser's analog behaviour and the 60 MHz
  closure are out of scope, as in the other cuts.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/thread/`).

## Stream cut (`S0`, `S1`): `Metronome.Stream`, `stream_check.py`

Lean cut of [md2_stream.v](../../../src/md2_stream.v) against
[SPEC_V2 §6.3](../../../wiki/SPEC_V2.md#63-streams-k--01), §12.3 (freeze and the
landing exception), §12.4 (edge capture into S0) and §13.2 (edge replay from
S0).  Both `CAP` variants of the module are covered: `g_s[0].u` is S0
(`CAP = 1`) and `g_s[1].u` is S1 (`CAP = 0`).

| File | Contents |
|---|---|
| `Metronome/Stream.lean` | the specification written from the SPEC text, plus its own consequences |
| `StreamEquivalence.lean.in` | the generated-Lean template: per-field equalities, the whole-transition theorem, the trace lift, the axioms audit |
| `stream_check.py` | Yosys elaboration, fail-closed cone extraction, emitter, mutations, CLI |
| `data/raw/lean_stream_v4_20261121/` | evidence of the accepted run (`--mutations`) |

Hook for `verify.py` (not added here; `verify.py` is owned by another cut):

```python
("stream", stream_check, stream_check.check_stream)
```

### Run it

```text
python code/tests/lean/stream_check.py
python code/tests/lean/stream_check.py --mutations
python code/tests/lean/stream_check.py --mutations --artifacts-dir data/raw/lean_stream_v4_20261121
```

Both need Lean 4.35.0 (`lake`) and Yosys on `PATH`.  The command re-elaborates
`src/` every time, writes `<case>.stream.lean`, `<case>.log`,
`<case>.axioms.txt`, `tools.log`, `lake.log`, `run_status.txt` (the actual
per-case exit code) and `stdout.log` into the artifact directory, and excludes
`sorryAx`.  `--artifacts-dir` must not exist yet.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted `POS` next state is §6.3's. | `CapOne.rtlPos_eq`, `CapTwo.rtlPos_eq` | All fourteen register values and all sampled inputs symbolic. |
| The extracted `BIDX` next state is §6.3's. | `rtlBidx_eq` | Same. |
| The extracted `BA` next state is §6.3's byte steps (1), §12.4's whole-word write (4) and §13.2's whole-word read (4). | `rtlBa_eq` | Same. |
| The extracted `CUR` next state is §6.3's `LB` load and receive assembly. | `rtlCur_eq` | Same. |
| The extracted `CV`, `WB`, `WV`, `RQ`, `LD`, `PEND`, `PV`, sticky `STARVED` next states are §6.3's, §12.3's and §13.2's. | `rtlCv_eq`, `rtlWb_eq`, `rtlWv_eq`, `rtlRq_eq`, `rtlLd_eq`, `rtlPend_eq`, `rtlPv_eq`, `rtlStarved_eq` | Same.  `WB`/`WV` include §12.3's landing exception and §13.2's `apply` shift. |
| The extracted §13.2 buffer slot `NB`, `NV` is the second slot of the two-deep buffer (inert in a `CAP = 0` stream). | `rtlNb_eq`, `rtlNv_eq` | Same. |
| The extracted combinational outputs are §6.3's `Sk.BIT` (`CV && !END && CUR[b]`), `Sk.BYTE`, the guards `END`/`MARK`/`BYTE`, the request lines (`BA`, `PEND`, `WB`, read/write, whole-word) and §13.2's replay presentation. | `rtlBit_eq`, `rtlByteOut_eq`, `rtlGEnd_eq`, `rtlGMark_eq`, `rtlGByte_eq`, `rtlReq_eq`, `rtlReqWe_eq`, `rtlReqAddr_eq`, `rtlReqWdata_eq`, `rtlReqWord_eq`, `rtlReqWword_eq`, `rtlReplayValid_eq`, `rtlReplayWord_eq` | Same. |
| The extracted transition equals the specification transition. | `rtlStep_eq_step` | Assembled from the fourteen field equalities. |
| The extracted output word equals the specification's. | `rtlOut_eq_out` | Assembled from the thirteen output equalities. |
| The extracted trace equals the specified trace at every cycle. | `rtlStateAt_eq`, `rtl_trace_step` | Any finite prefix, same initial state. |
| A rewind in cycle `n` rewinds the stream whatever else happens. | `Stream.rewind_overrides`, `rtl_trace_rewind` | A sampled reset edge in the same cycle has priority, so it is excluded. |
| Rewind does not suppress a same-cycle `PEND` load. | `Stream.rewind_pend_lands` | Receive completion with `PV` served in the same cycle. |
| A transmit advance with no byte is ignored and sets `STARVED`. | `Stream.adv_without_cur`, `rtl_trace_adv_without_cur` | No buffered word, so the "ignored" part is observable. |
| A byte end with no buffered word clears `CV` and sets `STARVED`. | `byte_end_without_word_starves` | |
| An advance inside a byte increments `BIDX` only. | `advance_inside_byte` | |
| `Sk.BIT` is `CUR[b]`, `b = MSB ? 7-BIDX : BIDX`, and 0 in receive, capture and replay. | `bit_is_cur_bit`, `bit_zero_receive`, `bit_zero_capture` | |
| A completed receive byte lands in `PEND` with `PV' = 1`, or is dropped with `STARVED' = 1` when `PV && !g`. | `received_byte_lands`, `received_byte_dropped` | |
| A flushed byte is the partial assembly, and the receive path never writes a bit it did not receive, so the unfilled bits are 0. | `flush_lands_cur`, `nsh_writes_one_bit`, `padOK_zero`, `padOK_bit`, `flush_pads_zeros` | The padding statement carries the `PadOK` invariant (the assembly register has no bit outside the positions written so far). |
| A write request exists only in receive mode or in §12.4's capture mode; transmit never writes. | `write_only_in_receive`, `transmit_no_write`, `byte_write_is_pend_at_ba`, `req_spec` | |
| §12.4: a pushed record lands in `WB` with `PV' = 1` and `POS' = POS + 4`, or is dropped with `STARVED' = 1`; a served record write clears `PV` and adds 4 to `BA`. | `capture_push_lands`, `capture_push_dropped`, `capture_write_served`, `capture_word_request` | |
| §13.2: `apply` shifts the second slot into the first, a landing fills the first slot when it is empty (else the second), a served replay read adds 4 to `BA` and `POS`, and the read request is the "not at END, nothing in flight, buffer not full" rule. | `replay_apply_shifts`, `replay_landing`, `replay_landing_second`, `replay_read_served`, `replay_request_rule`, `replay_late_starves`, `replay_valid_spec` | `apply`/`late` are inputs (the chip top computes them). |
| A frozen cycle updates nothing in the stream but the landing bucket. | `frozen_holds` | Rewind and the `STARVED` clear still act, so they are hypotheses. |
| `STARVED` is sticky until a `CTL` bit 7 clear, and a simultaneous starve event keeps it set. | `starved_sticky`, `starved_clear`, `starved_event_beats_clear`, `trace_starved_persists`, `rtl_trace_starved_persists` | |
| A sampled reset edge leaves the reset state. | `reset_step`, `trace_reset` | `cap = true`; a `CAP = 0` stream has no §13.2 slot registers, so those two fields are carried unchanged instead. |

The specification's own consequences are proved on `Metronome.Stream.step`
without any RTL; the `rtl_*` theorems are the same statements on the extracted
transition, obtained by rewriting with `rtlStep_eq_step` / `rtlStateAt_eq`.

### Premises and what stays free

* **The RAM is outside the cut.** `gnt` (the arbiter grant), `rdata` (the RAM
  output word) and the §6.2 read timing — "a read served in cycle `s` has its
  word at the RAM output during `s+1` and the requester loads it at the end of
  `s+1`" — are per-cycle inputs.  The stream never sees a request/response
  handshake beyond `RQ`/`LD`/`PV` and `gnt`, so the cut says *what the stream
  does when served*, not *when it is served*.  Arbiter priority (S0 first, §6.2)
  and the RAM macro are not part of this claim.
* **`FRZ`/`FRZD`** are sampled inputs; §12.3's freeze register (`FREEZE`,
  `FRZ'`, `FRZD'`) is a separate cut (`Metronome.CoreCtl`).
* **Capture control.** `cap_push` is §12.4's `cev` already gated by `CEN` and
  `!FRZ`; `cap_rec` is `{DC, PIN[12:0]}`.  The `DC` counter, `EMASK` and the
  edge detect are chip-top logic, not this module.
* **Replay control.** `replay_apply` and `replay_late` are §13.2's
  `apply`/`late` comparisons against the record's `DC` field and the replay
  timer; `RLV` itself is updated outside the stream.  The cut proves the
  stream-side buffer, the read request, `POS`/`BA` stepping and the `late`
  starve input, not the timer.
* **Configuration** `cfg_mode`, `cfg_msb`, `cfg_start`, `cfg_len`, `cfg_mark`
  are the latch-bank values of the configuration cut (§1: a write is seen two
  cycles later).  The cut shows the stream consumes them; it does not prove the
  host write path to them.
* **Move/host decode.** `adv`, `rx_we`, `rx_bit`, `rewind`, `flush` and
  `clr_starved` are the combined move and host requests of §6.3 (`Sk.ADV`,
  `Sk.RX`, `Sk.CTL`), not the move-bundle pick or the SPI host write.
* **Physical timing** (setup/hold, the 60 MHz closure, the RAM's access time)
  is out of scope, as in the other cuts.

### SPEC ambiguities and RTL/SPEC differences (reported, not fixed)

1. **`WV` and the last lane.** §6.3 clears `WV` when the consumed lane is
   `BA[1:0] == 3`.  The first draft of `Metronome.Stream` omitted that term and
   the equivalence proof rejected it (`rtlWv_eq`); the specification now has the
   clause.  The RTL is the one that follows the SPEC text here.
2. **Rewind and `PEND`/`STARVED`.** §6.3's rewind bullet ends "`PEND` and
   `STARVED` are unchanged".  Read literally as "a rewind cycle never changes
   them" this contradicts the same section's `if done: PEND' = NSH` and "a
   sticky flag set in the same cycle as a host clear stays set" (§9).  The
   specification takes the reading the RTL implements: the rewind assignment
   list does not include `PEND`/`STARVED`, so a byte completed in a rewind cycle
   still loads `PEND` (`rewind_pend_lands`) and a starve event still sets
   `STARVED` (`starved_sticky`, `rewind_overrides` omits both).
3. **"No read is in flight" (§13.2).**  The replay request rule reads this as
   `!RQ && !LD`, the two halves of the §6.2 read handshake, exactly as §6.3
   writes the transmit request (`elif !WV && !RQ && !LD`).  A looser reading
   (only `!RQ`) would request one cycle earlier in the branch where a word has
   just landed into a previously empty buffer; the RTL waits for the landing,
   and the cut proves the RTL's rule (`replay_request_rule`).
4. **§12.3's landing exception under replay.**  §12.3 says a landing is
   captured "into the stream's `WB`".  Under `ECTL.RPL` the RTL captures a
   landing that occurs in a frozen cycle into `NB` instead (and re-uses `NB` on
   the first unfrozen cycle), so the two-deep buffer order survives the freeze.
   The specification models that (`NB'` in `Metronome.Stream.nbNext`,
   `landing`), which is a refinement of §12.3's wording, not a contradiction.
5. **`MODE`, `MSB`, `START` "take effect at the next rewind".**  The RTL does
   not latch them; they are consumed live (`cfg_mode`, `cfg_msb`, `cfg_start`).
   §9a.13 makes a mid-flight change "unspecified until the next rewind", so the
   specification consumes the live values too and the clause is a host contract
   (§12.5), not an RTL latch.
6. **`CAP = 0` has no `NB`/`NV`.**  §13.2's two-deep buffer exists only in a
   capture stream.  The specification carries the two fields inert for
   `cap = false` (and gates their reset/rewind rules on `cap`), so one
   specification covers both elaborated variants.  Those two equalities are
   `state.nb = state.nb` / `state.nv = state.nv` for S1.
7. **Water-tightness of `push`.** §12.4 defines `push` in an *unfrozen* cycle.
   The module takes `cap_push` as an input and does not gate `push` with `!FRZ`
   itself; the top gates `cev` with `~frz`, and the frozen branch of the always
   block suppresses the update anyway, so the specification's frozen rule is
   what the hardware does.  A future top that drives `cap_push` while frozen
   would starve the stream (§12.4's `push && PV && !g`), which the specification
   allows and the RTL does too.

### Trust added

* Yosys elaboration and the Python RTLIL adapter, as in the rest of the suite
  (`elaborate` uses `verify.py`'s recipe: `read_verilog -I src`, `hierarchy
  -check -top`, `proc`, `opt_clean`, `write_json`).
* Local cone extensions in `stream_check.py` (the shared `rtlil.py` is
  unchanged): `$mul` with one constant operand (the `8 * BA[1:0]` lane scale),
  `$shl`/`$shr` with a variable amount (`(bitin & bit) << b`), a byte-wide
  `$shiftx` part-select, `$reduce_bool` (`BIDX != 0`), and `$and`/`$or`/`$not`
  on whole bytes.  Every extension is fail-closed: an unknown cell, a
  non-constant multiply, an unexpected width, an undriven net, a second register
  driver or an unresolvable bus raises `UnsupportedRTL`.
* The cut reads only the `md2_stream` instances: it checks `CAP`, the clock and
  reset connections, that every state register is a plain `$dff` of the
  expected width, that no other register exists, that a `CAP = 0` stream has no
  `NB`/`NV` register, and the exact set of module ports.
* `bv_decide` on the per-field equalities.  On the accepted run they carry
  per-theorem native LRAT certificate axioms (recorded in
  `<case>.axioms.txt`, e.g. `rtlBa_eq._native.bv_decide.ax_1_7`); no `sorryAx`
  appears and the runner rejects it.
* The proof tactic `spec_close` (unfold, `simp`, then
  `repeat (first | rfl | bv_decide | split <;> simp_all | contradiction)`) is a
  *proof search*, not an assumption: Lean checks every step.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `stream_msb_index` | `bsel = cfg_msb ? ~bidx : bidx` becomes `bsel = bidx` | `rtlCur_eq` (the bit position feeds `NSH`; `rtlPend_eq` and `rtlBit_eq` would also fail) |
| `stream_no_adv_starve` | `starve_tx` drops the `~cv` arm | `rtlStarved_eq` |
| `stream_rewind_keeps_pv` | the rewind block leaves `pv` | `rtlPv_eq` |
| `stream_write_when_stalled` | the receive `done` path always loads `PEND` | `rtlPend_eq` |
| `stream_flush_unpadded` | `nsh` takes `rx_bit` without `bitin` | `rtlPend_eq` (a flushed byte gains a bit it never received) |
| `stream_end_is_mark` | `Sk.END` compares `POS` with `MARK` | `rtlGEnd_eq` |
| `stream_capture_ba_one` | a served capture record advances `BA` by 1 | `rtlBa_eq` (S0 only; S1 has no capture path) |
| `stream_replay_pos_one` | a served replay read advances `POS` by 1 | `rtlPos_eq` (S0 only) |

The first mutant's rejection line is in `rtlCur_eq`, the first generated theorem
in file order whose cone the changed selector reaches; Lean reports the first
failing declaration, not all of them.

`run_mutations()` returns `(case, rejected, stage, exit)` per case and raises if
any mutant is accepted; `run_status.txt` records the real exit codes, and the
`stage` string names the generated declaration that failed (Lean reports the
first failing declaration of the file, not all of them).  The rejected cases'
`*.axioms.txt` contain `sorryAx` because Lean substitutes `sorry` for the
declaration it could not prove; the accepted baseline's audit does not.

### Evidence

`python code/tests/lean/stream_check.py --mutations
--artifacts-dir data/raw/lean_stream_v4_20261121` exited **0** on 2026-11-21 and
took **767 s** wall clock on a 10-core i5-1245U laptop (Lean 4.35.0, Yosys
0.70+190).  From `run_status.txt` in that directory:

| Case | Exit | Expectation |
|---|---|---|
| `baseline` | 0 | accepted (26 registers, 427 gates, both `CAP` variants) |
| `stream_msb_index` | 1 | rejected at `rtlCur_eq` |
| `stream_no_adv_starve` | 1 | rejected at `rtlStarved_eq` |
| `stream_rewind_keeps_pv` | 1 | rejected at `rtlPv_eq` |
| `stream_write_when_stalled` | 1 | rejected at `rtlPend_eq` |
| `stream_flush_unpadded` | 1 | rejected at `rtlPend_eq` |
| `stream_end_is_mark` | 1 | rejected at `rtlGEnd_eq` |
| `stream_capture_ba_one` | 1 | rejected at `rtlBa_eq` |
| `stream_replay_pos_one` | 1 | rejected at `rtlPos_eq` |

The accepted baseline file is 76 KB and runs in about 50 s of Lean; the mutants
cost roughly the same each (a failed field aborts that field's proof, so a
mutant is not cheaper).  `git diff --quiet HEAD -- src` was true before and
after the run: every mutation is applied to a temporary copy.

Every top-level theorem carries only `propext`, `Classical.choice`,
`Quot.sound` and the per-theorem `bv_decide` native certificate axioms listed in
`baseline.axioms.txt`; `Metronome.Stream`'s own consequences are
`propext`/`Quot.sound` only.

### Gaps

* **The capture/replay control logic** (`DC`, `EMASK`, `cev`, the replay timer,
  the `apply`/`late` comparisons, the `RLV` register) is outside the module cut:
  the stream-side behaviour is proved, the chip-top computation that drives
  `cap_push`, `replay_apply` and `replay_late` is not.
* **Arbiter and RAM.**  §6.2's priority order, the one-access-per-cycle rule,
  the served-in-`s`/output-in-`s+1` timing and address wrap are premises.  In
  particular "a transmit stream advanced at most once per cycle does not set
  `STARVED`" (§10 item 5) needs the arbiter, so it is not proved here.
* **The landing group.**  §12.3 also says the pointer's `RDY`/`D` land the same
  way; only the stream side is proved.
* **`STARVED`'s consumers** (`ERR`, `ERRSUM` bit 5, `IRQ`) are §9's, not this
  cut.
* **Replay mirror property.**  §13.2's "if a capture starts with an `ECTL`
  write and a replay with another, the replayed level equals the captured
  level" is a chip-level property of the `DC`/`RLV` logic; this cut only proves
  that the stream presents `WB` and applies the shift.
* **Physical timing** (`setup`/`hold`, the 60 MHz closure, RAM access) as in
  the other cuts.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/stream/`).

﻿# Engine data units: counter, shifter, LFSR/CRC and accumulator

This note covers the Lean cut for the four data units of SPEC_V2 §6.1:
`md2_counter` (three instances), `md2_shifter` (two), `md2_lfsr` (two) and the
elaborated `md2_acc` (one, `NM = 6` move slots and `NR = 4` scratch bytes), as
instantiated in [project.v](../../src/project.v).

* Specification: [Metronome/Units.lean](Metronome/Units.lean), written from
  SPEC_V2 §6.1 and the SPEC v1 §6.1 it cites, plus the destination codes of
  [ISA_TABLES_V2.md](../../wiki/ISA_TABLES_V2.md) and the RTL port-code maps in
  project.v.
* Extracted RTL: `units_check.py` re-elaborates the design with `verify.py`'s
  Yosys recipe, checks the chip-top wiring of the unit instances, and emits
  [UnitsEquivalence.lean.in](UnitsEquivalence.lean.in) filled with one
  `rtlStep` per unit (every register sampled) and the output cones.
* Run: `python code/tests/lean/units_check.py --mutations
  --artifacts-dir data/raw/lean_units_v4_20261121`.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted counter `V` is `LO`/`HI`/`DEC` of SPEC v1 §6.1, saturating at zero. | `Counter.rtlV`, `Counter.rtlStep_eq_step` | Every state and input symbolic. `sel = 3` (not a documented destination) is `DEC`, matching the RTL's `sel[1]` test; the group decode never emits it. |
| The extracted `Z` output is `V == 0`. | `Counter.rtlZ_eq_spec`, `Counter.zOut` | Same. |
| The extracted `LO`/`HI`/`DEC` port-code mux is the documented code map (0/1/2). | `Counter.rtlSel0..2_eq_spec`, `Counter.selOf` | Checked against the elaborated priority mux. |
| The extracted shifter `D`, `CNT`, `LEN`, `MSB` are SPEC v1 §6.1: `LD` loads `D` and `LEN ? LEN : 8`, `SH` shifts `v[0]` in and decrements saturating, `CFG` sets `LEN`/`MSB`. | `Shifter.rtlDr`, `Shifter.rtlCnt`, `Shifter.rtlLen`, `Shifter.rtlMsb`, `Shifter.rtlStep_eq_step` | Every state and input symbolic. A data move and a `SHk.CFG` move in one cycle both take effect, `LD`/`SH` using the cycle's `LEN` (SPEC_V2 §6: moves read cycle-`t` state). |
| The extracted shifter outputs are `O = MSB ? D[7] : D[0]` and `DONE = (CNT == 0)`. | `Shifter.rtlO_eq_spec`, `Shifter.rtlDone_eq_spec` | Every state symbolic. |
| The extracted LFSR `S` is `ST`/`B0..B3` of SPEC v1 §6.1, with `fb = S[0] ^ v[0]`. | `Lfsr.rtlS`, `Lfsr.rtlStep_eq_step` | Every state and input symbolic. Codes 5..7 do not select a documented write and hold (the RTL `default:`). |
| The extracted LFSR port-code mux is the documented map (ST = 0, B0..B3 = 1..4). | `Lfsr.rtlSel0..1_eq_spec`, `Lfsr.selOf` | Checked against the elaborated priority mux. |
| The extracted accumulator `A`, `Z`, `C`, `N`, `R0..R3` are SPEC v1 §6.1 for the winning op: `LD`/`ADD`/`SUB`/`AND`/`OR`/`XOR`/`CMP`, carry `r[8]`, no-borrow `A >= v`, `CMP` leaves `A`, the four `Rk` groups independent. | `Acc.rtlA`, `Acc.rtlZ`, `Acc.rtlC`, `Acc.rtlN`, `Acc.rtlR`, `Acc.rtlStep_eq_step` | `OneHotOrZero input.hit`: at most one move writes the `ACC` group (SPEC_V2 §6). `LD`/`AND`/`OR`/`XOR` hold `C`; SPEC v1 names `C'` only for `ADD`/`SUB`/`CMP`. |
| The per-slot ALU plus the one-hot hit mask equals "select the winner, then apply its op and its data". | `Acc.slotsPacked_eq_winner`, `Acc.slotsPacked_onehot`, `Acc.slotsPacked_zero`, `Acc.winnerResult_eq_slot`, `Acc.winnerResult_zero` | Explicit `OneHotOrZero` premise; `unpack_pack` proves the 13-bit `{wa,wc,cy,z,n,res}` round trip. |
| The elaborated per-slot op code `case` is the documented destination map `ACC.LD..CMP` (7..13) → op codes 0..6, with the RTL `default:` = CMP. | `Acc.rtlSel0..5_eq_spec`, `Acc.opCodeOf` | Each 3-bit slice proved as a function of the full 36-bit destination bus. |
| The extracted transitions equal the specification at every cycle. | each unit's `rtlStateAt_eq`, `rtl_trace_result` | Same initial state, any finite prefix; for `Acc`, every sampled cycle must satisfy `OneHotOrZero`. |

Spec-level facts: `Counter.dec_zero`, `Counter.dec_one`, `Shifter.loadCount_zero`
(`LEN = 0` means 8), `Shifter.shiftCount_zero`, `Lfsr.stepBit_noFeedback`,
`Acc.oneHotOrZero_shift` (every one-hot vector satisfies the premise),
`Acc.cmp_leaves_a`.

### Chip-top wiring checked structurally

`units_check_top` fails closed on:

* clock and reset of every instance: `clk` is the top clock port, `rst_n` is the
  synchronised `rst_q` net;
* `d == g_cn[k].w[7:0]`, `we == g_cn[k].w[14]` for each counter; the picked
  15-bit `{we, dst, data}` word's low byte and write bit;
* the shifters: `d == g_sh[k].w[7:0]`, `we == g_sh[k].w[14]`,
  `cfg_d == g_sh[k].c[4:0]`, `cfg_we == g_sh[k].c[14]`;
* the LFSRs: `d == g_lf[k].w[7:0]`, `we == g_lf[k].w[14]`, and `poly` is a
  32-bit contiguous slice of the configuration bus;
* the accumulator: `hit == acc_hit`, `sel == acc_sel6`, `d == c_dat`,
  `r_we == r_we`, `r_d == r_d`;
* every destination and group constant in the op strobes: for `CNTk.LO/HI`,
  `SHk.SEL`, `LFk.ST/B0..B2` and the four `Rk` strobes, the `dsteq(c_dst, D)`
  comparators cover every 6-bit destination slice with the header's `D_*`
  constant, and the six `hits` group comparators read the header's `DG_*`
  constant. The `DEC`, `B3` and shifter `LD` destinations are the port-code
  fallback and have no comparator, exactly as in project.v.

The shifter's one-bit `sel` is the `OPG(SHk, SHk.SH)` net itself (there is no
named `g_sh[k].sel` net); its cone is checked for the `D_SHk_SH` and `DG_SHk`
constants. That the group decode assigns destination `d` to group `DG_SHk`
(`DG_MAP`) is **not** proved here, as in the core-control cut.

### Premises

* **Accumulator one-hot.** `Acc.rtlStep_eq_step` and the trace lift take
  `OneHotOrZero input.hit`. In the RTL `hit = HITG(DG_ACC)` is one-hot by the
  `hits` priority function, so the premise is the module contract, not an extra
  assumption about reachable behaviour; the adapter checks that the `hits`
  group comparators read `DG_ACC`. The exact `hits`/`pick` priority is proved
  for the `CW` group in `Metronome.CoreCtl`, not for `ACC` here.
* `hit = 0` means no write: all four flags and `A` hold.
* Unused port codes: counter code 3 is `DEC`; LFSR codes 5..7 hold; accumulator
  code 7 is the RTL `default:` (`wa = wc = false`, `res = v`). None is
  reachable from `acc_sel6`, `op_lo/op_hi` or the LFSR strobes.
* `POLY` is a configuration input, not state; whether the host map writes the
  intended polynomial is the configuration cut's business.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `unit_counter_wrap` | `DEC` wraps at zero instead of saturating | `Counter.rtlV` / `rtlStep_eq_step` |
| `unit_counter_bytes_swap` | `LO` writes the high byte and `HI` the low byte | `Counter.rtlV` |
| `unit_shifter_len_zero` | `LEN = 0` loads a count of 0 instead of 8 | `Shifter.rtlCnt` |
| `unit_lfsr_feedback_bit` | `ST` feeds back `d[1]` instead of `d[0]` | `Lfsr.rtlS` |
| `unit_acc_sub_carry` | `SUB` reports no-borrow only for `A > v`, not `A >= v` | `Acc.rtlC` |
| `unit_acc_cmp_writes_a` | `CMP` writes `A` | `Acc.rtlA` |

Each is a statement-level failure of the generated Lean. `unit_counter_wrap`
and the shifter/LFSR byte mutations leave the candidate assignment in the log;
the accumulator mutants get a concrete counterexample from `bv_decide`.

### Run and evidence

`python code/tests/lean/units_check.py --mutations
--artifacts-dir data/raw/lean_units_v4_20261121` exited 0 on 2026-11-21 and
took 2,001 s wall clock (33 min) on the project laptop while other agents were
also running Lean/Yosys. `run_status.txt` records each case's own exit code:
baseline `accepted` / 0, and all six mutants rejected with Lean exit 1.
`stdout.log` has the outcomes, `tools.log` the tool versions, `baseline.log`
the full Lean output and `baseline.axioms.txt` the parsed `#print axioms`
audit (no `sorryAx`). The mutants' own `<case>.axioms.txt` files do contain
`sorryAx`: Lean's error recovery elaborates a failed proof with `sorry`, so
those dumps are expected to be dirty, which is exactly why they are not
accepted. `units_check.py` fails an accepted case whose audit mentions
`sorryAx`.

Two operational notes: `run_lean` retries once when Lean exits with a code
outside {0, 1} (Windows cold starts and concurrent runs produced occasional
tool crashes with no output); and the accumulator proofs are the expensive
part (four `bv_decide` goals over the 82-bit `a`/`z`/`c`/`n` cones and the
70-bit `R` cone), so a full mutation run costs about half an hour.

### Trust added

* Yosys elaboration and the RTLIL adapter are the suite's usual trust base.
  `UnitCone` (in `units_check.py`, not `rtlil.py`) adds Yosys's `$pmux`
  (`case`), `$xor`, multi-bit `$and`/`$or`, `$reduce_or`/`$reduce_bool` and
  `$logic_not`, plus `$gt`/`$le`. Every one-bit cell output is bound as
  `BitVec 1`; conditions convert with `!= 0`. Fail-closed: a `$pmux` is decoded
  only when all selects are distinct equality/zero tests of one bus, and an
  unsupported cell, a missing driver, a second register driver or an
  unresolvable bus raises `UnsupportedRTL`.
* The header constants `D_CNT*`, `D_SH*`, `D_LF*`, `D_ACC_*`, `DG_ACC`,
  `DG_R0..R3`, `DG_SH*`, `DG_CNT*`, `DG_LF*` are read from `src/md2_defs.vh`
  and `src/md2_map.vh`; every comparator the adapter finds must match them.
* `bv_decide` emits per-theorem native-certificate axioms (LRAT). The
  `*.axioms.txt` files record them; no theorem depends on `sorryAx`
  (`units_check.py` rejects a case that does). `rtlZ_eq_spec`, `rtlDone_eq_spec`,
  `rtlSel0..2_eq_spec`, `rtlCnt`, `rtlLen` and `rtlS` (LFSR) use only
  `propext`, `Classical.choice` and `Quot.sound`; the larger equalities carry
  their own certificate axioms.

### Gaps

* The write-group pick and `DG_MAP` (which destination belongs to which group)
  are outside the cut; `hit`, the op strobes and the port-code muxes are
  checked against the documented constants and code maps, not against the
  destination-to-group table.
* The move bus, guard evaluation, `CONFLICT` resolution and the `(core, move
  index)` priority that make `hit` one-hot-or-zero are not part of this cut.
* The accumulator equality holds only under that premise; a multi-hot `hit`
  is outside the module's contract (the RTL ORs several ALU results, which is
  not "apply the winner").
* Physical timing, clock gating and the 60 MHz closure are not modelled, as in
  the other cuts.
* Header-derived constants and the generated map are trusted to be the intended
  configuration; `POLY` values and `LEN`/`MSB` configuration contents are
  host-map questions.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/units/`).

## Move resolution cut (`moves_check.py`)

The chip-top move resolution of SPEC_V2 §6, proved in Lean against the
elaborated netlist. This is item 3G of the verification plan, the last piece the
core-control cut left out: the destination → write-group map, the `mv_win`
blocking, the `conflict_ev` term, each unit's `pick` word, the sticky
`CONFLICT` / `MEMHAZ` registers and the two source side effects.

| File | Role |
|---|---|
| `Metronome/Moves.lean` | independent specification of §6, written by hand |
| `MovesEquivalence.lean.in` | proof template for the arbitration, map, sticky and side-effect cones |
| `moves_check.py` | Yosys elaboration, fail-closed extraction, table generator (`--check`), Lean emission, mutations, evidence |
| `data/raw/lean_moves_v4_20261121/` | evidence of the accepted run: generated Lean, logs, axiom audit, tool versions, `run_status.txt` |

`Metronome.lean` is unchanged, so `lake build` does not build this module; use
`lake build Metronome.Moves` (or `lake env lean Metronome/Moves.lean`), as the
other cuts do.

### What the spec says

SPEC_V2 §6, read literally:

* both cores' moves read the cycle-`t` state and write at the end of the cycle;
  slot `k = 3*core + move` is the priority order ("lowest (core, move index)");
* the destination ports are partitioned into write groups
  (`machine.WRITE_GROUPS`): `L.SYM` is "the three symbol ports of one line,
  resolved to the executing thread's line", `T.STOP` is "per thread", `FLAGS`,
  `ACC`, each `Rk`, `SHk`, `SHk.CFG`, `CNTk`, `LFk`, `P0`, `Sk`, `Lk.CTL`,
  `HOST.OUT`, `CW`; `NULL` has no group;
* if two or more enabled moves target one group in a cycle, sticky
  `CONFLICT' = 1` and only the lowest `(core, move index)` takes effect;
* source side effects happen only for enabled moves: reading `HOST.IN` clears
  `INV`; reading `P0.D` while `P0.RDY == 0` sets sticky `MEMHAZ`;
* `CTRL.STICKY` is write-one-to-clear, bit 0 `CONFLICT`, bit 1 `MEMHAZ`,
  bit 2 `CWOVR` (§9, §13.1).

The destination → group table is transcribed from `code/md2/machine.json`
(`dst` order, `write_groups` order, codes 61..63 unused). `moves_check.py
--check` regenerates it and fails if the transcription, the header's `DG_MAP` or
`machine.json` drift.

### Cycle boundary and free leaves

Everything in the arbitration is combinational plus the two sticky registers.
The cut binds these chip-top nets as free per-cycle inputs:

| leaf | used by | status |
|---|---|---|
| `mv_en` (6), `c_dst` (36), `c_src` (36), `c_dat` (48) | every move cone | the core pipeline (dispatch, guards, `md2_core`'s own freeze gate) is not in this cut |
| `xl` (4), `xt` (6) | `mv_win`, the line picks | the executing line/thread, from the core's `xl_o`/`xt_o` |
| `grp_v` (30) | arbitration, pick words | proved separately (`rtlGrpV_spec`); the cones compose by rewriting |
| `h_wr`, `ha` | the `CTRL.STICKY` strobe | the host cut's; the byte's identity is re-proved here |
| `c_wr_hin` | the `INV` next state | host-map cut's strobe |
| `p_haz`, `p_rdy` | `memhaz_ev` | the data-RAM cut's |

`grp_v` is bound free only so the arbitration cones stay small; the map is a
separate theorem and the two compose (`mapOf` is the specification's group bus,
`validBits`/`winBits`/`conflictOf` take it as an argument).

### Claims

`Metronome.Moves` (the specification) states, and the generated Lean proves
about the elaborated cells:

| Claim | Theorem | Conditions |
|---|---|---|
| Slot order is `(core, move index)`: `k = 3*core + m`. | `slot_order` | `k < 6` |
| A move is valid iff enabled and its group is not `DG_NONE`. | `validAt` (definition), `rtlValid_spec` | six slots, symbolic `mv_en`/`grp_v` |
| The key of a move is its group, except `L.SYM` (also the line) and `T.STOP` (also the thread). | `sameKey`, `sameKey_comm`, `sameKey_self` | symbolic slots |
| `mv_win` is exactly "valid and no earlier valid slot with the same key". | `winAt_spec`, `rtlWin_spec` | six slots, symbolic `mv_en`, `grp_v`, `xl`, `xt` |
| Two distinct winners never share a key. | `winners_unique` | `i ≠ j`, both `winAt` |
| `conflict_ev = |(mv_valid & ~mv_win)` iff two valid moves share a key (hence iff a key has two or more valid moves). | `conflictEv_eq_pairSameKey`, `conflictEv_iff_pairs`, `conflict_of_two`, `conflict_witness`, `rtlConflictEv_spec` | six slots |
| `pick(hits(...))` returns the lowest-index contender's `{we, dst, data}`; `we` is set iff some move contends. | `pickWord_we`, `pick_first_*`, `pick_we_iff`, `hitAt_valid`, `pick_is_winner_0..5`, `rtlWord*_spec` (23 unit words) | group constant is the elaborated comparator's; `pick_is_winner_k` needs the group to be a real code |
| Each unit's word is the spec pick: `{1, dst, data}` of the group's winner. | `rtlWord{Flags,Cw,P0,HostOut,R0..R3,Sh0,Sh1,Sh0Cfg,Sh1Cfg,Cnt0..2,Lf0,Lf1,S0,S1,Line0..3Ctl}_spec` | symbolic `mv_en`, `grp_v`, `c_dst`, `c_dat` |
| Each line's `L.SYM` word is `pick` over that line's winners. | `rtlSymWordSym0..3_spec`, `symMask_bit`, `hitOr` | symbolic `mv_win`, `grp_v`, `xl`, `c_dst`, `c_dat` |
| The elaborated `DG_MAP` lookup is the `machine.json` table for all 64 destination codes. | `machineTable_spec`, `rtlGrpV_spec`, `rtlGrpV_mapOf` | symbolic 36-bit `c_dst`; `rfl`-level, no bit-blast |
| `CONFLICT` is the sticky step: reset clears, an event sets, a clear-only cycle clears, an event beats a simultaneous clear. | `rtlConflictStep_spec`, `rtl_conflict_sticky`, `sticky_reset`, `sticky_event`, `sticky_clear`, `sticky_hold`, `sticky_event_beats_clear`, `sticky_stays_set`, `trace_sticky_low`, `trace_sticky_set` | register value free; `ev` free; the clear leaf is `c_wr_stk & h_wd[0]` |
| `MEMHAZ` is the same sticky step with bit 1. | `rtlMemhazStep_spec`, `sticky_*` | as above |
| The `CONFLICT`/`MEMHAZ` clears are host writes of `CTRL.STICKY` with bit 0/1; a write of another byte clears nothing. | `rtlSticky_spec` (`c_wr_stk = wr & (ha == 0x2401)`), `rtlConflictStep_spec`, `rtlMemhazStep_spec` | 16-bit address; the host map's byte is `HA_CTRL_BASE + HO_CTRL_STICKY` |
| A `HOST.IN` read clears `INV` only when the move is enabled; a host `HOSTIN` write wins in the same cycle. | `readAt_disabled`, `readsOf_ne_zero`, `rtlRdHin_spec`, `invNext`, `inv_reset`, `inv_host_write`, `inv_read_clears`, `inv_hold`, `rtlInvStep_spec`, `rtl_inv_read` | `mv_en`, `c_src`, `c_wr_hin` symbolic |
| A `P0.D` read while `!RDY` raises `MEMHAZ`; a disabled move's read does not. | `memhazEvent`, `memhazEventOf`, `memhaz_of_read`, `memhaz_none`, `rtlRdPd_spec`, `rtlMemhazEv_spec`, `rtl_memhaz_read` | `p_haz`, `p_rdy`, `mv_en`, `c_src` symbolic |

All theorems are over symbolic inputs; `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound` plus, where `bv_decide` is used, that
theorem's native-certificate axiom. The runner rejects `sorryAx`. A *rejected
mutant* can show `sorryAx` in declarations downstream of its first failing
theorem (Lean fills the failed proof); the case is rejected on the non-zero exit
before that test, and an accepted case never contains it (the accepted run's
`baseline.axioms.txt` has none).

### What the adapter checks (fail-closed)

`moves_check.py` elaborates with `verify.py`'s recipe and:

* checks `grp_v`, `mv_valid`, `mv_win`, `conflict_ev`, every word net and the
  register nets by width and name;
* requires every word's six `hits` comparators to test one and the same
  documented `DG_*` code (read from `md2_map.vh`), so a per-slot group, a
  non-constant operand or an undocumented code fails before Lean runs;
* requires each line pick's group comparator to be `DG_L_SYM` and its line
  comparator to be that line's index;
* reads the `CONFLICT` clear bit from the register's next state and the
  `MEMHAZ` bit likewise, and the `CTRL.STICKY` byte from the strobe's `$sub`,
  `$lt` and offset constant (the same `extract_strobe` the core-control cut
  uses), so a moved map fails closed;
* extracts the destination lookup's index as the *`Nat` product* `5*d`. The RTL
  evaluates `5*c_dst[6k +: 6]` in 32 bits; the adapter requires the product to
  fit 32 bits (`factor * (2**len - 1) < 2**width`), so the unsigned value is
  the `Nat` product. That makes the table proof `rfl`-level instead of a
  320-bit barrel-shifter bit-blast.

Local adapter extensions (in `moves_check.py`, `rtlil.py` unchanged): wide
`$not` (the `~mv_win` complement), wide `$shiftx` (the 320-bit table lookup),
`$mul`/`$shr`/`$shl` with a constant operand, and a Nat-form index. Everything
stays fail-closed: an unsupported or unbounded cell raises `UnsupportedRTL`.

### Mutations (temporary copies of `src/`, never the repository)

`python code/tests/lean/moves_check.py --mutations` runs the baseline and eight
planted regressions. All were rejected on the accepted run:

| Mutation | Change | Rejected by |
|---|---|---|
| `moves_map_entry` | `DG_MAP` entry 60 (`CW.D`) becomes `FLAGS` | `rtlGrpV_spec` (`rfl` fails) |
| `moves_null_group` | `NULL`'s `DG_MAP` entry becomes a group | `rtlGrpV_spec` |
| `moves_same_key_line` | `same_key` drops the `L.SYM` line test | `rtlWin_spec` (counterexample) |
| `moves_win_highest` | the blocking scan takes `j > k`, so the highest index wins | `rtlWin_spec` |
| `moves_conflict_three_way` | `conflict_ev` only looks at slots 0 and 1 | `rtlConflictEv_spec` |
| `moves_clear_beats_event` | `(conflict_ev | conflict) & ~clear` | `rtlConflictStep_spec` |
| `moves_valid_no_group` | `mv_valid[k] = mv_en[k]` (the `NULL` test is dropped) | `rtlValid_spec` |
| `moves_hits_ignores_en` | the `hits` mask drops `mv_en` | the unit-word theorems |

### Trust added

Yosys elaboration, the RTLIL adapter and the generated Lean are the same trust
base as the rest of the suite. Beyond that:

* `bv_decide` adds per-theorem native-certificate axioms for `rtlWin_spec`,
  `rtlConflictEv_spec`, `rtlSticky_spec`, `rtlMemhazEv_spec`,
  `rtlInvStep_spec` and the 27 word theorems; `#print axioms` records them.
* The map proof is `rfl`-level after the index is emitted as a `Nat` product;
  the product bound is a checked adapter precondition, not a proof obligation.
* The spec table is hand-transcribed; `--check` regenerates it from
  `machine.json` and compares it with `md2_map.vh`, and `machineTable_spec`
  proves the elaborated table is the generated one, so a table edit without the
  others fails the proof rather than redefining the specification.

### Remaining gaps

* **Single-winner reading of the line picks.** `rtlSymWord*_spec` proves the
  line word is the RTL's OR-of-masked-words over the line's winner bits. That
  it is one winner's word uses `winners_unique` (two `L.SYM` winners of one
  line share a key) and is argued, not mechanised: the mask's one-hotness is
  not composed with `hitOr` in Lean. The 23 unit words are proved against the
  single-winner `pickWord` directly because `hits` already applies the prefix
  mask.
* **`mv_en` provenance.** The dispatch, the guards and `md2_core`'s freeze gate
  that produce `mv_en`, `c_dst`, `c_src`, `c_dat` are free; so is the core's
  `xl`/`xt`. "Some move is enabled" is not yet tied to a thread's PC or to
  `RUN`/`FRZ`.
* **Host link.** `h_wr`, `ha` and `c_wr_hin` are free; the SPI framing and the
  host-map decode that make them real writes are the host cuts'.
* **Memory port.** `p_haz` and `p_rdy` are free; the data-RAM arbiter's timing
  is the memory cut's.
* **Freeze transparency.** The sticky flags keep updating while frozen, as the
  RTL does (the freeze gates the cores and the queue, not `conflict`/`memhaz`);
  that is the RTL's behaviour, not a §6 claim, and §12.3's freeze equivalence is
  the core-control cut's.
* **Timing.** The one-level priority on `mv_en` and the 320-bit table lookup at
  60 MHz are physical-timing questions, out of scope everywhere.

### Run it

From the repository root, with `lake` (Lean 4.35.0) and `yosys` on `PATH`:

```text
python code/tests/lean/moves_check.py --check                  # table drift only
python code/tests/lean/moves_check.py                          # baseline
python code/tests/lean/moves_check.py --mutations              # plus the eight mutants
python code/tests/lean/moves_check.py --mutations --artifacts-dir <fresh dir>
```

The defaults write into `data/raw/lean_moves_v4_20261121/`; the directory must
not exist yet. `check_moves(src_dir_or_json, out_dir, *, lake, yosys, case)`
returns the report dictionary and raises `MovesRejected` on a rejected cut;
`run_mutations(snapshot, out_dir, lake, yosys)` returns one
`(case, rejected, stage, exit)` record per mutant. Each case runs two generated
files — `<case>.moves.lean` (map, arbitration, sticky, side effects) and
`<case>.words.lean` (the 27 pick words) — with a 900 s timeout each, and
`run_status.txt` records the real exit codes.

The `verify.py` hook is the tuple `("moves", moves_check,
moves_check.check_moves)`.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/moves/`).

## Line cut (SPEC_V2 section 3): notes

The line `l = 0..3` is [src/md2_line.v](../../src/md2_line.v), one module
instantiated four times by `g_ln` in [src/project.v](../../src/project.v)
(around line 504).  This cut takes the line's configuration window, the winning
moves, the host-write enables, the synchronised pins and the freeze flag as
inputs, cuts the fifteen register next-state cones and the nine combinational
outputs out of the elaborated design, and proves them equal to
[Metronome/Line.lean](Metronome/Line.lean), an independent statement of
[SPEC_V2 §3](../../wiki/SPEC_V2.md#3-lines-l--03) (§3.1 configuration and state,
§3.2 beat generator, §3.2a hold, §3.3 follower mode and edge-sourced tap 0,
§3.4 taps/fired/`TAPMISS`, §3.5 capture/snapshot/input symbol, §3.6 output
symbol and commit), §12.1 (`LIVE`/`PINA`/`PINB` pins) and §12.3 (freeze), plus
the module header's precedence note (generator, then a move to `Lk.CTL`, then a
host write of `PHASE`/`CTL`/`STAT`).

Files of this cut:

| Path | Role |
|---|---|
| [Metronome/Line.lean](Metronome/Line.lean) | independent specification: state, config, inputs, the generator/hold/tap/capture/commit sub-functions, `step`, one-step consequences and traces |
| [line_check.py](line_check.py) | Yosys elaboration, chip-top and window structural checks, layered cone extraction, Lean emission, mutation runs, evidence |
| [LineEquivalence.lean.in](LineEquivalence.lean.in) | the trace-lifting part of the proof template |
| `data/raw/lean_line_v4_20261121/` | evidence of the accepted run (generated Lean, logs, axiom audit, tool versions, `run_status.txt`) |

`Metronome.lean` is unchanged, so the default `lake build` does not build this
module; use `lake build Metronome.Line` (or `lake env lean Metronome/Line.lean`).

### How the cut is built

The module's fifteen registers are `ph run arm ren held first sc sp fired w sn
rem staged committed tapmiss`.  Its internal wires are extracted **in layers**:
each intermediate net is emitted as its own definition whose cone binds the
earlier layers to their *specification* expressions, and proves the
corresponding equation.  The final `rtlStep` binds all layers, so each register
equation is the same formula on both sides and closes by `rfl`.

Layer order (spec expression on the right):

| Net | Specification |
|---|---|
| `edg` | `edge state input` |
| `e0` | `e0 state input` |
| `runa` | `runa state input` |
| `inwin` | `inwin state input` |
| `start` | `start state input` |
| `accept` | `accept state input` |
| `n` | `sum17 state input` |
| `over` | `over state input` |
| `nxw` | `nxw state input` |
| `nx` | `nx state input` |
| `th` | `holdTap input` |
| `h_tok` | `holdTok state input` |
| `hold` | `hold state input` |
| `adv` | `adv state input` |
| `wrap` | `wrap state input` |
| `beat` | `beat state input` |
| `miss_ev` | `missEv state input` |
| `fired_next` | `firedNext state input` |
| `snap` | `snap state input` |
| `ph_c` | `phC state input` |
| `ph_f` | `phF state input` |
| `run_c` | `runC state input` |
| `arm_c` | `armC state input` |
| `ren_c` | `renC state input` |
| `run_f` | `runF state input` |
| `starting` | `starting state input` |
| `staged_n` | `stagedNext state input` |
| `seg` | `seg state` |
| `pina`, `pinb`, `pina_rise`, `pina_fall` | `pina input`, … |

Outputs that are not one net are separate finals: `rtlTapOut` is `{TAP2, TAP1,
TAP0}`, `rtlInSymOut` is `{LUT1, LUT0}`, `rtlCapValue` is `{REM, SN}`.
`tap` and `in_sym` cannot be bound as leaves (their bits are the outputs of
per-bit cells), so they are assembled from the bound leaves inline.

The emitter flattens the RTL's `$and`/`$or` trees in source operand order, so
the specification's chains (written in the SPEC's order) are the same terms; a
different operand order fails the equation instead of being hidden by `simp`.
Comparisons are emitted as `decide (a < b)` (Lean's `<` on `BitVec` is a
proposition) and the specification's `tlt0/1/2` are `Bool` definitions with the
same insertion.  Yosys's `x = d; if (b) x = e;` lowering (`b ? (b ? e : 0) : d`)
is bridged by `ite_ite_zero` / `ite_ite_false` in the specification.

### Claims

| Claim | Theorems | Conditions |
|---|---|---|
| Every intermediate net of the module is its specification sub-function. | `rtlEdg_eq` … `rtlStagedN_eq`, `rtlSegValue_eq`, `rtlPinaIn_eq`, `rtlPinbIn_eq`, `rtlPinaRiseIn_eq`, `rtlPinaFallIn_eq` (32 layer theorems) | The layer's cone with all earlier layers bound; every state and input value symbolic. |
| The beat generator is SPEC §3.2: `edge`, `e0`, `runa`, `inwin`, `start`, `accept`, `n`, `over`, `nx`, `wrap`, `beat`. | `rtlEdg_eq`, `rtlE0_eq`, `rtlRuna_eq`, `rtlInwin_eq`, `rtlStart_eq`, `rtlAccept_eq`, `rtlN_eq`, `rtlOver_eq`, `rtlNxw_eq`, `rtlNx_eq`, `rtlWrap_eq`, `rtlBeatOut_eq` | Same. `inwin` is the windowed form of §3.2. |
| The hold is SPEC §3.2a: `th`, `h_tok`, `hold`, with `HELD' = hold` outside a freeze. | `rtlTh_eq`, `rtlHTok_eq`, `rtlHold_eq`, `rtlAdv_eq`, `rtlHeld` | Same; `HELD` is the one register the RTL gates explicitly on `!frz`. |
| The taps, fired bits and `TAPMISS` are SPEC §3.4: `cross_k`, `next_k`, `cur_k`, `TAPk`, `en_k`, `miss_ok`, `miss_ev`, `fired_next`. | `rtlMissEv_eq`, `rtlFiredNext_eq`, `rtlTapOut_eq`, `rtlFired`, `rtlTapmiss` | Same.  `TAPMISS` is sticky until a host `STAT` write of bit 0. |
| Capture, snapshot, input symbol (§3.5) and the working samples. | `rtlW`, `rtlSn`, `rtlRem`, `rtlInSymOut_eq`, `rtlCapValue_eq` | Same; `SN' = W'`, `REM' = IN[1]`, `CAP = {REM, SN}`. |
| The output symbol and commit (§3.6), including the start commit and `FIRST`. | `rtlStagedN_eq`, `rtlCommitted`, `rtlStaged`, `rtlFirst`, `rtlStarting_eq`, `rtlStart_commits` (spec) | Same; a write in the boundary/start cycle is committed. |
| Precedence: generator < move to `Lk.CTL` < host write. | `rtlRunC_eq`, `rtlArmC_eq`, `rtlRenC_eq`, `rtlRunF_eq`, `rtlPhC_eq`, `rtlPhF_eq`, `host_ctl_wins`, `move_ctl_wins`, `run_generator`, `host_phase_wins` | Host `CTL` wins over a move; a move wins over the generator; host `PHASE` writes win over both. Reset released. |
| The fifteen register next states are the specification's. | `rtlPh`, `rtlRun`, `rtlArm`, `rtlRen`, `rtlHeld`, `rtlFirst`, `rtlSc`, `rtlSp`, `rtlFired`, `rtlW`, `rtlSn`, `rtlRem`, `rtlStaged`, `rtlCommitted`, `rtlTapmiss` | Every register and input value symbolic. |
| The elaborated transition equals the specification transition. | `rtlStep_eq_step` | Every state and input value symbolic; assembled from the register theorems. |
| The extracted trace is the specification trace, so the specification's trace theorems hold of the RTL. | `rtlStateAt_eq`, `rtl_trace_result` | Same initial state, any finite prefix. |
| A sampled reset edge leaves `resetState`. | `reset_step`, `stateAt_one_reset`, `rtl_trace_reset` | `rst_n` low at that edge. |
| A frozen `FOLLOW = 0` cycle with no move and no host write leaves every register unchanged, so deleting it gives the same state sequence. | `frz_step_holds`, `trace_frz_holds`, `rtl_trace_frz_holds` | `frz`, no `Lk.CTL` move, no `L.SYM`/`L.DB`/`L.XOR` move, no host `PHASE`/`CTL`/`STAT` write, `FOLLOW = 0`, reset released. |
| In follower mode a frozen cycle clears `SC` and nothing else. | `frz_follow_sc` | §3.3's `SC' = 0` is unconditional; this is the specification's rule, not an RTL difference. |
| With `FOLLOW = 0` the boundary is exactly the phase wrap, i.e. `PH + INC >= MOD` when the line advances. | `beat_eq_wrap`, `beat_of_advance` | The SPEC §3.2 equation, stated as one cycle. |
| A hold only lengthens beats. | — | **Not proved** (see gaps). |
| The chip-top wiring is the documented one: each instance has `clk`, `rst_n = rst_q`, `frz`, its `cfg` window slice and its output nets; each host-write enable is `w_lrt & i_lrt == k & o_lrt == offset`. | Python checks in `line_check.check_line_top`, `check_enable` | Structural; the move pick (`pick(...)`) is not in this cut. |

### Premises and free leaves

* `cfg` — the line's 32-byte window — is a free input; the latch-bank and
  host-map cuts cover its content.  The adapter checks that each `c_*` field net
  is exactly the window byte slice of the hand-written table (`LINE_FIELDS`,
  from `machine.LINE_REGS`) and that `md2_map.vh`'s `HO_LINE_*` constants agree.
* `lvl`, `rise`, `fall` are free 16-bit vectors; the pin synchronisers and the
  `RISE`/`FALL` derivation are the chip-top / §2 business.
* `ctl_we`/`ctl_d` (a move to `Lk.CTL`) and `sym_we`/`sym_op`/`sym_d` (the
  winning `L.SYM`/`L.DB`/`L.XOR` move of this line) are free per-cycle inputs.
  The move pick (`pick(...)` and the `sh` mask) is **not** proved here; only its
  instance wiring is checked.  `h_wd` is free; the host enable decode is checked
  structurally as above, the host SPI framing is the host cut's.
* `frz` is a free per-cycle input here; its own next state is the core-control
  cut's (`DBG`/`FREEZE`/`FRZ`).
* The reset synchroniser is abstracted: `rst_n` is a sampled input (`rst_q` at
  the chip top).

### Trust added

* Yosys elaboration and the shared RTLIL adapter: the same trust base as the
  rest of the suite.
* A local adapter extension in `line_check.py` (the shared `rtlil.py` is
  unchanged): `$pmux` (with the shared exclusive-select check), `$logic_not`,
  `$reduce_or`/`$reduce_bool`, `$gt`, `$le`, `$xor`, multi-bit
  `$and`/`$or`/`$not`, scalar `$shiftx`, and a `Bool`/`BitVec` split (a one-bit
  bus is a Lean `Bool`).  Everything is fail-closed: an unsupported cell, an
  unexpected width, an ambiguous or undriven bus, or a second register driver
  raises `UnsupportedRTL`.
* The concatenation assembler merges runs of one bus into a single slice.  The
  suite's `hostread_check.assemble_fields` keeps `count` unchanged in its run
  merge (every run is emitted as one bit); `line_check.assemble` fixes that
  locally and is the version used here.
* The emitter flattens `$and`/`$or` chains in source operand order and wraps
  `<`, `<=`, `>`, `>=` in `decide`.  Both are visible in the generated Lean and
  are checked by the layer equations: a different operand order or a missing
  `decide` fails the proof rather than passing silently.
* `pack3_bits` and `pack4_bits` in the specification use `bv_decide` (Lean's
  native LRAT checker).  The accepted run records
  `pack4_bits._native.bv_decide.ax_1_7` as an axiom of
  `rtl_trace_frz_holds` (and of every proof that uses it); no other theorem
  carries a native certificate, and `sorryAx` is absent everywhere.  This is
  the only trust added beyond Yosys, the adapter and the header reader.
* The window table (`LINE_FIELDS`) duplicates `machine.LINE_REGS` and the
  header's `HO_LINE_*` on purpose; a map change needs both edits and fails the
  header check until then.  The same is true of the LRT offsets used for the
  host enables.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `line_frz_held` | `held <= hold` (the `!frz` hold is dropped) | `rtlHeld` |
| `line_host_ctl_loses` | `run_f = run_c` (a move beats the host `CTL` write) | the structural check: the host mux disappears, so `run_f` aliases `run_c` and the layer cone refuses the already-bound net |
| `line_tapmiss_not_sticky` | `tapmiss <= miss_ev` (no sticky hold) | `rtlTapmiss` |
| `line_commit_staged` | the boundary/start commit takes `staged`, not `staged_n` | `rtlCommitted` |
| `line_tap0_cross` | tap 0's phase crossing compares `c_t1` instead of `c_t0` | `rtlMissEv_eq` (the first cone that reads `cur_k[0]`; `rtlTapOut_eq` would also fail) |
| `line_cfg_offset` | `c_t1` reads the `T2` window bytes | the structural window-slice check (`md2_line.c_t1: not window bytes 6+`) |
| `line2_cfg_slice` | line 2's `cfg` instance slice is one byte high | the structural instance check (`g_ln[2].u.cfg: not window bytes 64..95`) |

The no-op mutation candidate `assign tk[0] = c_t0 → c_t1` is **accepted by the
RTL**: `tk[0]` is dead (the `g_t0` branch wires `c_t0`/`e0` directly), so the
mutation changes nothing.  That is why the tap-0 mutant targets `ph_cross`
instead.

### SPEC ambiguities and RTL/SPEC differences observed (reported, not fixed)

1. **`sym_op = 3`.** `project.v` decodes the symbol write to `sop` ∈ {0 SYM,
   1 DBIT, 2 XOR}; the RTL `case` default makes an impossible `3` behave like
   XOR.  SPEC §3.6 defines only the three operations.  The specification takes
   the RTL's default (XOR) and documents it.
2. **Frozen follower `SC`.** §3.3's `SC' = 0` in follower mode is
   unconditional, so a frozen follower cycle clears `SC`.  §12.3's "no line
   advances" does not list `SC`; the freeze theorem here is therefore stated
   for `FOLLOW = 0` (full state hold) plus `frz_follow_sc` (follower clears
   `SC` only).  This is the SPEC's own rule; the RTL obeys it.
3. **`tk[0]` is dead.** `assign tk[0] = c_t0;` is never read: the `k = 0`
   generate branch uses `c_t0` and `e0` directly.  Harmless, but it means a
   mutation there is a no-op.
4. **Yosys's default-arm lowering.** `staged_n` is emitted as
   `sym_we ? (sym_we ? <case> : 0) : staged`.  This is a syntactic artefact of
   the blocking assignment; `ite_ite_zero` bridges it.
5. **`<=`/`<` are propositions in Lean but `Bool` cells in the netlist.**  The
   adapter wraps relational cells in `decide`; the specification's `tlt*` are
   `Bool` definitions.  No semantic difference.

### Remaining gaps

* **A hold only lengthens beats** (SPEC §3.2a's first consequence) is not
  proved.  The cut proves the one-cycle `hold`/`HELD` equations and the freeze
  hold, not the cycle-count bound.
* **Trace-level beat period.**  `beat_of_advance` is the SPEC's one-cycle
  statement; a theorem of the form "over a trace with `HOLD = 0`, `BEAT` every
  `ceil(MOD/INC)` cycles" is not proved (it needs arithmetic over the trace).
* **Move pick and host enable semantics.**  `ctl_*`, `sym_*` and the host
  enables are free inputs; the chip-top check only ties the enables to
  `w_lrt & i_lrt == k & o_lrt == offset` and the outputs/window.  The
  `pick(...)` priority and the `L.SYM` group's `same_key`/`CONFLICT` behaviour
  are the core-control cut's business.
* **Configuration content.**  `cfg` is free; the window slice wiring is checked,
  the latch bank's content and the host map are elsewhere.
* **Physical timing.**  Pin synchronisers, the `RISE`/`FALL` derivation, the
  hold's read-back latency and 60 MHz closure are out of scope, as everywhere.
* **`FRZ`'s own next state** is the core-control cut's; this cut takes `frz`.
* **`frz` and `snap`/`cap`.**  The cut proves `snap = 0` under a freeze and
  hence `SN`/`REM` hold; it does not model the analog synchroniser behaviour.

### Run it

From the repository root, with `lake` (Lean 4.35.0) and `yosys` on `PATH`:

```text
python code/tests/lean/line_check.py                                   # baseline
python code/tests/lean/line_check.py --mutations                       # plus seven mutants
python code/tests/lean/line_check.py --mutations --artifacts-dir <fresh dir>
```

Defaults write into `data/raw/lean_line_v4_20261121/`; the directory must not
exist.  Evidence per case: `<case>.line.lean` (the generated module),
`<case>.log` (Yosys command, snapshot SHA-256, the checked window table, the
full Lean output), `<case>.axioms.txt` (parsed `#print axioms`), plus
`tools.log`, `lake.log`, `stdout.log` and `run_status.txt` (each case's own exit
code and whether it matched the expectation).  A rejected baseline or an
accepted mutant exits non-zero; `sorryAx` in an accepted case is rejected.

The accepted run recorded on 2026-11-21 is
`data/raw/lean_line_v4_20261121/`: `python code/tests/lean/line_check.py
--mutations --artifacts-dir data/raw/lean_line_v4_20261121` exited 0 in 128 s
wall clock on the 10-core i5-1245U laptop.  Per case, from the artifact
timestamps: baseline 18 s (Yosys elaboration plus the ~69 KB generated proof,
whose Lean run is about 5 s), `line_frz_held` 22 s, `line_host_ctl_loses` 11 s
(structural), `line_tapmiss_not_sticky` 16 s, `line_commit_staged` 19 s,
`line_tap0_cross` 29 s (its failing goal print makes the log 199 KB),
`line_cfg_offset` 5 s and `line2_cfg_slice` 6 s (structural).  `Line.lean`
itself builds in about 4 s.

`check_line(src_dir_or_json, out_dir, *, lake, yosys, case="baseline")` and
`run_mutations(snapshot, out_dir, lake, yosys)` are importable like the other
cuts.

**`verify.py` hook tuple:** `("line", line_check, line_check.check_line)` — i.e.
the suite should call `line_check.check_line(src, out_dir, lake=lake,
yosys=yosys, case=case)` for the baseline and for each case, and treat a raised
`LineRejected`/`UnsupportedRTL` as a rejection.  (`verify.py` is unchanged by
this task.)

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/line/`).

## Core cut: the two `md2_core` instances (`Metronome.Core`)

Item 3E: the two cores of [SPEC_V2 §5](../../../wiki/SPEC_V2.md), §6, §7 and §12.3,
against the elaborated `src/md2_core.v` instances in the chip top.

| Path | Role |
|---|---|
| [Metronome/Core.lean](Metronome/Core.lean) | independent specification written from the SPEC text: state, inputs, decode, guards, source vector, control, dispatch, watchers, outputs, next state, the §5 consequences and the trace theorems |
| [core_check.py](core_check.py) | Yosys elaboration, structural adapter (`CoreCone`, fail-closed), cone extraction for both `C` variants, Lean emission, mutation runs, evidence |
| [CoreEquivalence.lean.in](CoreEquivalence.lean.in) | per-variant proof template: register and output equalities, `rtlStep_eq_step`, `rtlOut_eq_out`, trace lift, axiom audit |
| `data/raw/lean_core_v4_20261121/` | evidence of the accepted run: generated Lean, per-case logs, axiom audit, tool versions, `run_status.txt` |

`Metronome.lean` is unchanged, so `lake build` does not build this module; use
`lake build Metronome.Core` (or `lake env lean Metronome/Core.lean`), as the other
cuts do. `verify.py` does not yet run this cut; the hook tuple is
**`("core", core_check, core_check.check_core)`**.

### What the cut checks

1. **Both variants.** `src/project.v` instantiates `md2_core #(.C(k), .NT(NT))
   u_core` in `g_core[0]` and `g_core[1]`. `core_modules()` finds the two
   specialised modules by their `hdlname` and `parameter_default_values`
   (`C = 0/1`, `NT = 6`) and rejects anything else. `check_core_top()` checks
   each instance's `clk`, `rst_n = rst_q`, `frz`, `run_g`, `rdata = pm_rd[k]`,
   `fetch_en = fen[k]`, `fetch_addr = fadr[8k+7:8k]` and `disp_o = dsp[k]`, so the
   two cuts are the real chip instances and the two variants differ only in `C`.
2. **Encoding.** `check_fields()` requires every decode net (`i_pause`,
   `i_jmode`, `i_imm`, `i_cond`, `i_jcond`, `i_g[0..2]`, `i_s[0..2]`,
   `i_d[0..2]`) to be exactly the documented `IR` slice, and `check_jg()`
   requires `jg[j]` to be `grd[JUMP_GUARDS[j]]` for the 32 entries of
   `wiki/ISA_TABLES_V2.md`. A drifted field or table fails closed.
3. **Registers and outputs.** For each variant the adapter binds the register
   `Q` buses and the 18 module inputs, then translates the seven register `D`
   cones and all 15 output cones to Lean. `rtlStep`/`rtlOut` are those cones;
   the per-field theorems prove each equal to `step`/`out`, and
   `rtlStep_eq_step`/`rtlOut_eq_out` assemble the whole transition.
4. **Trace lift.** `rtlStateAt_eq` (via `run_congr`), `rtl_trace_result` and the
   two §5 timing theorems lifted to the extracted trace.

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted `XV'` is SPEC §5's (`reset` → 0, `frz` → hold, else `load`). | `Rtl0/1.rtlXv` | Every state and input value symbolic. |
| The extracted `RV'`, `FPC'`, `XT'`, `XL'`, `RR'` and `IR'` are SPEC §5's. | `rtlRv`, `rtlFpc`, `rtlXt`, `rtlXl`, `rtlRr`, `rtlIr` | Same. |
| The extracted transition is the specification for every state and input. | `rtlStep_eq_step` | Assembled from the seven register equalities. |
| The extracted `fetch_en`, `fetch_addr`, `pause_o`, `npc_o`, `disp_o`, `disp_e`, `xt_o`, `xl_o`, `mv_en`, `mv_src`, `mv_dst`, `mv_data` are the specification's. | `rtlFetchEn`, `rtlFetchAddr`, `rtlPause`, `rtlNpc`, `rtlDisp`, `rtlDispE`, `rtlXtO`, `rtlXlO`, `rtlMvEn`, `rtlMvSrc`, `rtlMvDst`, `rtlMvData` | Same. `mv_data` covers the 512-bit source vector and the three 8-bit move slots. |
| §12.3 readback `CST.XV`, `CST.RV` and `FPC` are the state registers. | `rtlDbg` | Same. |
| The extracted outputs are the specification's. | `rtlOut_eq_out` | Assembled from the fifteen output equalities. |
| The extracted trace equals the specification trace at every cycle. | `rtlStateAt_eq`, `rtl_trace_result` | Any finite prefix, same initial state. |
| A trigger in cycle `t` with an idle core executes its first instruction in `t + 3` (dispatch in `n`, execute in `n + 2`). | `trace_dispatch_idle`, `rtl_trace_dispatch_idle` | Idle (`XV = RV = 0`), not frozen, reset released in cycle `n`; ready thread bound to `c`; `frz` low and reset released in `n + 1`. |
| A taken jump on a non-pausing instruction costs one idle cycle; the target executes two cycles after the jump. | `trace_jump_idle`, `rtl_trace_jump_idle` | `XV`, `jmp`, not frozen, reset released in `n`; `frz` low and reset released in `n + 1`. |
| A frozen cycle holds every register: `next = state`. | `frz_holds` | `frz` high and reset released. |
| A frozen cycle fetches nothing, jumps nothing, pauses nothing, dispatches nothing and enables no move. | `frz_no_fetch` | `frz` high. |
| No move is enabled outside an unfrozen execute cycle. | `mvEnAt_zero`, `mvEn_zero` | `XV = 0` or frozen. |
| `free` is `pse` or an idle core, and while `free` and `XV` the instruction in `X` is a pause that retires. | `free_iff`, `free_no_execute` | The only X-stage instruction that coexists with a dispatch is a pause; it clears `XV`. |
| `disp` needs a free core and a candidate; it sets `RR' = (e+1) mod 6`; `RR` otherwise holds. | `disp_iff`, `disp_rr_next`, `rr_only_on_disp` | Reset released, not frozen for the `RR` equations. |
| The circular scan `RR, RR+1, … (mod 6)` equals the priority chain the RTL implements. | `firstCandOf_eq_win`, `dispThread_eq`, `winOf_atmost` | The cursor is a thread index (`rrOk`). |
| The cursor stays a thread index. | `rr_next_lt_six`, `dispE_toNat_le_five`, `rrNext_toNat_lt_six` | Reset, freeze and dispatch included. |
| While `XV`, `FPC` is one past the word captured into `IR`; a frozen cycle holds both. | `xv_fpc_invariant` | Core form of §5's `FPC = PC(IR) + 1` (see "Ambiguities" below). |
| On `load`, `IR` takes the memory output. | `irNext_of_load` | The RTL also captures without `load`; see below. |

`SelIdx_toNat_lt_six` is the one-hot fact the cursor bound needs; it and
`firstCandOf_eq_win`, `winOf_atmost`, `rrNext_toNat_lt_six` are kernel `decide`
over the six threads / 512 candidate–cursor pairs, so they add no certificate.

### Premises and free leaves

Per cycle the extracted transition is a function of exactly these leaves:

* the state (`xv`, `rv`, `fpc`, `xt`, `xl`, `rr`, `ir`);
* the 18 `md2_core` input ports: `rst_n`, `frz`, `run_g`, `rdata`, `t_ready`,
  `t_core`, `t_line`, `t_pc`, `t_w0c`, `t_w1c`, `t_w0h`, `t_w1h`, `guards`,
  `g_line`, `srcs`, `l_in`, `l_cap` (`clk` is the register clock).

Nothing else is bound. In particular the cut does **not** model: the thread
file (so `READY`, `CORE`, `LINE`, `PC`, `W0C/W1C/W0H/W1H` are free inputs, not
the `md2_thread` outputs), the program memories (`rdata` is a free 64-bit word,
not `u_pmem0/1`), the global guard/source builders in `project.v` (`guards` and
`srcs` are free, with the core's own `ZERO/IMM/L.IN/L.CAP` overrides modelled),
the line units (`l_in`, `l_cap` free), the freeze registers (`frz` free — the
`corectl` cut proves them), or `RUN_global` (`run_g` free).

### Trust added

Yosys elaboration and the shared RTLIL adapter are the same trust base the rest
of the suite uses. Locally added cell shapes (in `core_check.py`, `rtlil.py`
unchanged): `$mul` (the `8 * i_s` and `N * xl` index multiplies), wide
`$shiftx` (indexed part selects of the 512-bit source vector, the 20-bit
`l_cap` and the 32-bit `jg`), `$reduce_or`/`$reduce_bool` (`|cand`,
`w0c != 0`), `$logic_not` (`code == 0`), wide `$not` (`~t_core`), wide
`$and`/`$or` (broadcast masks, the source vector and the thread selectors),
one-bit `$mux` as a Lean `Bool`, and `$pmux` with the same mutually-exclusive
select proof the host cut uses (no `$pmux` occurs in this module today). Each
extension stays fail-closed: an unknown cell, an undriven bus, a partial
overlap or a second driver raises `UnsupportedRTL`.

The field and jump-table checks read the same numbers as
`wiki/ISA_TABLES_V2.md` (which is generated from `code/md2/machine.py`; the
generated `src/md2_defs.vh` carries them too). Nothing is read from the header
at run time for the Lean side — the constants live in `Metronome/Core.lean` and
the proofs show the elaborated cells implement them.

`bv_decide` adds per-theorem native LRAT certificate axioms
(`rtlXv._native.bv_decide.ax_1_47` and friends) on top of `propext`,
`Classical.choice` and `Quot.sound`; `#print axioms` records them and
`core_check.py` rejects `sorryAx`. The certificate checker is the only trust
added beyond Yosys, the adapter and the constant tables.

### Ambiguities and RTL/SPEC differences (reported, not fixed)

1. **`IR` capture without `load`.** SPEC §5 writes `XV' = load; if load: IR' =
   the word at the memory output`. `md2_core.v` captures the memory output in
   every unfrozen cycle (`if (!frz) ir <= rdata;`). The model follows the RTL.
   The extra capture is unobservable: `XV' = load`, so a word taken without
   `load` is never decoded, and on `load` the two rules agree (`irNext_of_load`).
   This is the one place where the model is the RTL's rule rather than the
   pseudocode line; making the specification's version a separate `step` would
   only rename the same observable-machine argument.
2. **Freeze qualification.** §5 writes `free = pse || (!XV && !RV)` and does not
   qualify `jmp`/`pse`/`load`/`fetch` with the freeze; §12.3 then says a frozen
   cycle does not execute, jump, pause, fetch or dispatch. The model and the RTL
   both use the §12.3 form (`xa = xv && !frz`, `ra = rv && !frz`,
   `free = pse || (!xv && !rv && !frz)`), and `frz_holds` is the §12.3 statement.
   So §5 is read as the unfrozen-cycle rules, as §12.3 says.
3. **`FPC = PC(IR) + 1`.** §5 states `FPC = PC(IR) + 1 mod 256` as a state
   invariant. The core does not hold a `PC(IR)` register: `FPC` *is* the R-stage
   address, and the thread's `PC` may be redirected to a watcher handler at
   dispatch without changing `PC[e]`. The provable core form is
   `xv_fpc_invariant`: whenever `XV'` holds, `FPC` has advanced one past the
   word captured into `IR` (or a frozen cycle held both). §12.3's readback rule
   ("while `XV`, the executing instruction is at `FPC - 1`") is the same fact.
4. **Field positions and the jump table.** `src/md2_defs.vh` (generated) and
   `wiki/ISA_TABLES_V2.md` (generated from the same `code/md2/machine.py`)
   agree on every instruction field and on all 32 `JUMP_GUARDS` entries; the
   adapter checks both against the elaborated cells, so no difference was
   found. `i_pause`/`i_jmode`/… are direct `IR` slices.
5. **`disp_e` when nothing dispatches.** Both sides default to 0; `RR'` is only
   written on `disp`, so the default is unobservable. `dispE` is nevertheless a
   module output and is proved for all inputs.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `core_rr_plus_one` | `after_rr` uses `g >= rr + 1`, so the circular order starts at `RR + 1` | `Rtl0.rtlFpc` |
| `core_rr_every_cycle` | the `XT`/`XL`/`RR` update is not gated on `disp_o`, so `RR` advances every unfrozen cycle | `Rtl0.rtlXt` |
| `core_ifnot_uses_c` | the `ifnot` move guard uses `C` instead of `~C` | `Rtl0.rtlMvEn` |
| `core_jmp_ignores_pause` | a taken jump on a pausing instruction also redirects the fetch | `Rtl0.rtlRv` |
| `core_load_ignores_jmp` | the R word loads even when a jump or a pause drops it | `Rtl0.rtlXv` |
| `core_watcher_order` | watcher 1 is tested before watcher 0 | `Rtl0.rtlFpc` |
| `core_frz_not_hold` | the `!frz` guard on the register update is dropped, so a frozen cycle moves `XV`/`RV`/`FPC`/`XT`/`XL`/`RR` | `Rtl0.rtlXv` |
| `core1_wrong_binding` | core 1 dispatches the threads bound to core 0 (`mine = ~t_core` for both) | `Rtl1.rtlRv` (the C = 0 variant is unaffected, which shows the two variants are cut separately) |

`run_mutations()` reports, per mutant, `(case, rejected, stage, exit)`. The run
below recorded `run_status.txt` from the cases' own exit codes; the rejecting
theorem is the first declaration the Lean run reported (`core_check.failed_theorem`
maps the error line back to the generated `theorem`).

| Case | Outcome | Exit | Rejecting theorem |
|---|---|---|---|
| `baseline` | accepted, 259 / 257 extracted signals | 0 | — |
| `core_rr_plus_one` | rejected | 1 | `Rtl0.rtlFpc` |
| `core_rr_every_cycle` | rejected | 1 | `Rtl0.rtlXt` |
| `core_ifnot_uses_c` | rejected | 1 | `Rtl0.rtlMvEn` |
| `core_jmp_ignores_pause` | rejected | 1 | `Rtl0.rtlRv` |
| `core_load_ignores_jmp` | rejected | 1 | `Rtl0.rtlXv` |
| `core_watcher_order` | rejected | 1 | `Rtl0.rtlFpc` |
| `core_frz_not_hold` | rejected | 1 | `Rtl0.rtlXv` |
| `core1_wrong_binding` | rejected | 1 | `Rtl1.rtlRv` |

`core_rr_plus_one` and `core_rr_every_cycle` also break the two trace timing
theorems; Lean stops at the first failing declaration, so the table names one.

### Timing

`python code/tests/lean/core_check.py --mutations
--artifacts-dir data/raw/lean_core_v4_20261121` exited 0 on 2026-11-21 and took
2057 s wall clock (34 min) on the 10-core i5-1245U laptop, which was carrying
other Lean/Yosys runs at the same time. Per case, from the artifact timestamps
(Yosys ≈ 70 s each, then one Lean process): baseline 187 s,
`core_rr_plus_one` 120 s, `core_rr_every_cycle` 151 s, `core_ifnot_uses_c`
146 s, `core_jmp_ignores_pause` 248 s, `core_load_ignores_jmp` 131 s,
`core_watcher_order` 154 s, `core_frz_not_hold` 108 s, `core1_wrong_binding`
271 s. The baseline file alone is 81 KB and checks both variants in one
`lake env lean` run; replaying it on a quiet machine takes about 190 s.

### Remaining gaps in the emitted proofs

The two variants are checked in one file, so a failure in either fails the
case; `Rtl0`/`Rtl1` names in `run_status.txt` say which. The proofs split the
work per register and per output; `mv_data` is the only 500-plus-bit goal (the
512-bit source vector and three 8-bit move slots), and it is a single
`bv_decide` goal per variant.

### Gaps

* **Thread file.** `t_ready`, `t_core`, `t_line`, `t_pc`, the watcher codes and
  handlers are free inputs. "Trigger in `t` → `READY` in `t+1`" is §4's, not
  this cut's; the timing theorem here starts from the dispatch cycle. Dispatch's
  `READY[e]' = 0`, `RUNNING[e]' = 1`, pause's `PC[XT]' = npc` are thread state
  and are not proved here.
* **Program memory.** `rdata` is a free word. That the SRAM returns the word at
  `FPC` one cycle after the address is presented (`md2_pmem`, `md2_mem`) is not
  modelled; `fetch_addr`/`fetch_en` are proved as the core's outputs, not as a
  memory contract.
* **The global `guards`/`srcs` builders.** `project.v` builds `gv`, `sv`,
  `g_line` from the line/flag/stream/pointer units; this cut starts at the
  core's ports, with the core's own four source-slot overrides modelled. The
  §6 "single-bit sources occupy bit 0" convention is the source builder's job.
* **Timing and physical behaviour.** The three-stage pipeline is proved as
  cycle equations and the two §5 consequence rows are trace theorems over the
  core; the 60 MHz closure, the SRAM read latency and the register setup/hold
  are out of scope, as in the other cuts.
* **`CONFLICT`.** The §6 multi-move conflict resolution is the `corectl` cut's
  (`w_cw`, the lowest `(core, move index)` wins); `mv_en`/`mv_dst` are proved
  here per move, the arbiter/priority logic is not.
* **Source and destination semantics.** The move bus is proved (enable, source
  index, destination index, 8-bit data with the four core-local slots);
  whether a destination or source code means what the ISA table says is the
  units' business.

### Run it

```text
python code/tests/lean/core_check.py                # baseline
python code/tests/lean/core_check.py --mutations    # plus the eight regressions
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the defaults write into
`data/raw/lean_core_v4_20261121/` (or `--artifacts-dir`), which must not exist
yet. A rejected baseline or an accepted mutant exits non-zero. `run_status.txt`
records each case's own Lean/Yosys exit code and whether it matched the
expectation; `<case>.log` keeps the Yosys recipe, the source hash and the whole
Lean output, and `<case>.axioms.txt` the parsed `#print axioms` audit. The
accepted run's `run_status.txt` is `baseline` `accepted` `0` `ok` and every
mutant `rejected (...)` `1` `ok`.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/core/`).

## Pin-level host transactions (Metronome v4, `HostPins`)

Status: `Metronome.HostPins` accepted by Lean 4.35.0 (`lake env lean
-DwarningAsError=true`, exit 0, 15 s) and the composed RTL file accepted by
`python hostpins_check.py` (exit 0, 70 s) on 2026-11-21, branch
`metronome-v4.0`, Yosys 0.70+190. Evidence in
[data/raw/lean_hostpins_v4_20261121](../../../data/raw/lean_hostpins_v4_20261121).

This cut composes the three finished host cuts into statements about the *pins*:

| Finished cut | What it gives | How this cut uses it |
|---|---|---|
| `Metronome.SpiPins` (`spipins_check.py`) | pin synchronisers, `u_host` wiring, the mode-0 write waveform, `transaction_strobes` | the write headline's strobe and the pin-level read clock (`srAt`, `pinRise`, `mosi_pins_at`) |
| `Metronome.HostCmd` (`hostcmd_check.py`) | the byte/address state machine, `rtlAddr` | the read address phase (the command machine's own lemmas) and the `AddrOk` discharge |
| `Metronome.HostRead` (`hostread_check.py`) | `TX`/`rackv`, `rdValSpec`, `rtlRdVal_eq_spec`, `rtlMiso_eq_tx7` | the read slot chain and the read map |
| `Metronome.HostMap` (`hostmap_check.py`) | the write table, `enabledSels`, `enabledSels_le_one` | the write target statement |

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| A pin-level write transaction `[0x02, AH, AL, d0..]` strobes `(A+j, dj)` and the host map enables **at most one** target there. | `transaction_write_target` | `2 ≤ period`, `3 ≤ first`, `3 ≤ nbytes`, reset released, `CS_N` low, the listed `SCK` rises and MOSI bits, no acknowledgement. |
| At a real strobe the enabled list *is* the map's selection list. | `enabledSels_true` | none. |
| In the program window exactly one target is enabled, and it is a program-memory byte; the register, data-RAM and configuration entries are off. | `count_prog` | `a < 0x1000`. |
| In the data window exactly one target is enabled: the data-RAM byte. | `count_data` | `0x1000 ≤ a < 0x1800`. |
| In the configuration window the only candidate is the window byte, enabled exactly when the byte is live. | `count_cfg` | `0x2000 ≤ a < 0x21E0`. |
| In the register window the only candidates are the 43 register bytes (the other three entries are off). | `count_reg` | `0x2400 ≤ a < 0x2480`. |
| A pin-level read transaction `[0x03, AH, AL, dummy..]` drives the read machine: slot `k`'s request cycle has `rd = true` and `addr = {AH,AL}+k`, no write strobe, and the eight MISO bits of slot `k` are the `rd_val` sampled in that request cycle, MSB first. | `transaction_read_bytes` | `3 ≤ period`, `3 ≤ first`, `3 ≤ nbytes`, reset released, `CS_N` low, the listed rises and MOSI bits of the three address bytes, no landing (`hland = false`), the slot request cycles are not data-RAM addresses (`rdData = false`), no acknowledgement in the address phase and none in the slot windows. |
| The eight edges of one read data byte, with idle gaps, shift out the byte and leave `AfterByte`; one slot then loads the next byte from its request cycle and starts `a+1`. | `sending_byte_pins`, `read_slot_pins` | the byte's window's reset/`CS_N`/`SR` facts, no other edge, no acknowledgement in the window. |
| From `Sending` at slot 0, every slot's byte and the next slot's `Sending` follow by induction. | `read_burst` | `4 ≤ nbytes`, the slot windows' reset/`CS_N`/`SR`/ack facts, `rdData` false at every request cycle. |
| The address phase `0x03/AH/AL` enters `ST_DATA` with the loaded address, raises `rd`, keeps `rack` clear and leaves `TX` zero, so slot 0 finds a `Sending` state. | `read_open` | `3 ≤ period`, the three bytes' waveform, no acknowledgement before the AL completion, no landing. |
| The read machine's trace projects onto the command machine's on the nine shared registers. | `Agrees`, `agrees_step`, `agrees_stateAt` | none (the `cmd` history variable is irrelevant to every next-state equation). |
| **Negative witness:** a `CS_N`-high cycle raises no `SR`, no completion and no write strobe. | `witness_cs_high_no_strobe` | `i.csN = true`. |
| **Negative witness:** an `SCK` pin that is high in every sampled cycle has no rising edge from cycle 3 on, so there is no `SR` at all: a one-cycle SCK period is not representable. | `witness_no_rise_of_always_high`, `witness_no_sr_of_always_high` | `SCK` high in every cycle, reset released, `CS_N` low, `3 ≤ m`. |
| **Negative witness:** a two-cycle SCK period puts the load cycle `+3` after the eighth edge, past the next slot's first edge (`+2`): `3 ≤ period` is needed, not `2 ≤ period`. | `witness_read_load_late` | none. |
| **RTL:** the read extract's address field is the command cut's transition, so `HostRead.AddrOk` is discharged from `HostCmd.rtlAddr` and the read path's step and trace theorems hold of the elaborated design. | `rtlAddr_bridge` (`rfl`), `rtlAddrOk`, `rtlReadStep_eq_step`, `rtlReadStateAt_eq`, `rtlReadInputs_stateAt_eq` | none. |
| **RTL:** the bit on the elaborated MISO pin in slot `k` is `rdValSpec({AH,AL}+k)` at that slot's request cycle. | `rtl_transaction_read_bytes` | the spec premises plus `hval`: the `rd_val` input of a cycle is the elaborated mux of the address register and the register file. |
| **RTL:** the elaborated host link's strobe is the pin transaction's and the host map enables at most one target. | `rtl_transaction_write_target` | the spec premises; the shared-register trace equality `SpiPins.rtl_stateAt_eq` carries the elaborated link to the specification. |

`#print axioms` (recorded in `axioms.txt`, no `sorryAx` anywhere): the structural
lemmas use `propext`/`Classical.choice`/`Quot.sound`; every `bv_decide`-closed
table or component equality adds its own per-theorem native certificate
(`*.bv_decide.ax_*`), as in the other cuts. The negative witnesses use **no**
`native_decide`, `bv_decide` or `decide` on an open goal: `witness_cs_high_no_strobe`
and `witness_read_load_late` are `simp`/`omega` on the definitions,
`witness_no_rise_of_always_high` is case analysis with `simp [pinRise, …]`, and
`witness_no_sr_of_always_high` composes them with `SpiPins.sr_eq_pinRise`.

### Premises, and why each is needed

* **`2 ≤ period` (write) / `3 ≤ period` (read).** The trace samples one pin level
  per clock, so each SCK phase must cover a cycle. The write framing needs one
  cycle per phase (`SpiPins`' own premise). The read path needs one more cycle:
  the eighth edge's request pulse occupies `+1`, the acknowledge latches at `+2`
  and `TX` loads at `+3`, while the next slot's first edge is `period` cycles
  after the eighth edge — so `period ≥ 3` is exactly "the load lands before the
  next edge" (`witness_read_load_late` shows the failure at `period = 2`).
  `HostRead.read_burst_index` states `10` because it indexes a fixed ten-cycle
  slot grid; this file indexes the actual clock (`srAt`), and `3` is what the
  load-before-edge argument needs. SPEC_V2 §9's clk/16 (`period ≥ 16`)
  satisfies both.
* **`3 ≤ first`.** `pinRise` is false in cycles 0-2 (the synchronisers are zero
  out of reset), so starting at or after cycle 3 keeps the pin model and the
  specification in agreement from the first edge.
* **`hreset` / `hcs`.** Reset released and `CS_N` low for the transaction;
  `witness_cs_high_no_strobe` shows a `CS_N`-high cycle produces no `SR` and no
  strobe, and `HostCmd.trace_cs_high` is why a mid-transaction `CS_N` high is not
  part of a transaction.
* **`hrise` (bounded) and `honly`.** Exactly the transaction's rising edges:
  `hrise` for `k < 8 * nbytes` (the rises the bytes use) and `honly` ("every pin
  rise is one of the listed `srAt` cycles"). Note: `SpiPins.transaction_strobes`
  (reused for the write side) still asks `hrise` for *all* `k`; the read-side
  theorems in this file are stated with the bounded form. **Weakening the write
  headline to the bounded form is a gap** (it would mean re-running
  `transaction_strobes`' internal `data_step` chain with bounded premises).
* **`hbit`.** MOSI stability: the bit an `SR` samples is the pin MOSI of two
  cycles earlier, so the bit must hold across the rise and the cycle before it.
* **`hcmd`.** The command byte is `0x02` (write) or `0x03` (read); without it the
  machine ignores the rest of the transaction (`HostCmd`'s `ST_IGN`).
* **`hack` (write).** No read acknowledgement during the write burst: `rack` or a
  data-RAM landing would step `addr` (`HostCmd.addr_inc`).
* **`hnoland`, `hrdData` (read).** No data-RAM landing during the transaction,
  and the slot request cycles are not data-RAM addresses: together they say the
  read is a *register* read, so the slot's byte comes from `rd_val` rather than
  the RAM service.
* **`hackAddr`, `hackSlot` (read).** No acknowledgement lands in the address
  phase or inside a data slot. These are exactly `HostRead`'s own `hack`
  premises, bounded to the transaction. For the RTL's `rd` pulse they hold —
  `rd` is a one-cycle pulse raised *after* the completing `AL`/`DATA` edge, so the
  only acknowledge cycle is the request cycle's successor, which lies before the
  slot's first edge — but **deriving them from the `rd` equation is a gap**: it
  needs the per-edge bit-count chain of the address bytes (the chain
  `sending_byte_pins` already carries for the data bytes).
* **`hval` (RTL).** The `rd_val` input of a cycle is the elaborated mux of the
  address register and the register file. `rd_val` is a *free input* of the read
  cut (`HostRead` proves it against `rdValSpec` for every address and register
  state); the composed theorem ties it to the map, not to the chip's other
  registers.

### What is discharged, and what stays assumed

* **`HostRead.AddrOk` is discharged.** The composed `rtlStep` for the read cut
  takes its address field from the command cut (`extract_read_noaddr` binds the
  other ten registers; `hostread_check.check_address_increment` still pins
  `addr_i` to the `addr`/`addr + 1` mux selected by `wr | rack | hland`). The
  bridge is then `rfl` and `rtlAddrOk` is `HostCmd.rtlAddr` on the shared
  registers, so `rtlReadStep_eq_step` and every trace theorem of the read path
  hold of the RTL without a hypothesis. This is a checked modelling step: the
  read cut's own address cone is *not* syntactically the command cut's (it
  aliases `addr_i` and `byte_in` as leaves), so the two cones cannot be related
  by rewriting with `HostCmd.rtlAddr`; the substitution plus
  `check_address_increment` and the `byte_in = {rx, mosi}` layout check are what
  justify it.
* **`HostRead`'s own step/trace theorems** (`rtlStep_eq_step`, `rtlStateAt_eq`)
  are re-used verbatim in the generated file; only the `AddrOk` hypothesis is
  gone.
* **Assumed, not proved here:** the pin levels are sampled (metastability,
  sub-cycle glitches and physical setup/hold are out of scope in every cut); the
  `MISO` pin path is `tx[7]` with no extra register (the read cut's
  `rtlMiso_eq_tx7`, re-used); the write payload's *effect* (register file, SRAM
  macro, latch bank) is the host-map, program-memory and bank cuts' business;
  `hval` ties `rd_val` to the map but the register file itself is not modelled.

### Files

| Path | Role |
|---|---|
| [Metronome/HostPins.lean](Metronome/HostPins.lean) | specification and pin-level composition: `Agrees`, `readInputs`, the byte/slot/burst lemmas, `read_open`, `transaction_read_bytes`, the map table and `transaction_write_target`, the witnesses |
| [hostpins_check.py](hostpins_check.py) | re-elaborates the chip top, reuses the three cuts' extractors and templates, emits the composed Lean, runs it, audits axioms, two mutants |
| [HostPinsEquivalence.lean.in](HostPinsEquivalence.lean.in) | the composed proof template: `rtlAddr_bridge`/`rtlAddrOk`, the trace equalities, `rtl_transaction_read_bytes`, `rtl_transaction_write_target`, axiom audit |
| `data/raw/lean_hostpins_v4_20261121/` | `lean.log`, `lean_build.log`, `axioms.txt`, `run_status.txt`, and `rtl/` (`stdout.log`, `baseline.log`, `baseline.hostpins.lean`, `baseline.axioms.txt`, `tools.log`, `lake.log`, `run_status.txt`), `rtl_mutants/` |

`Metronome.lean` is unchanged, so the default `lake build` does not build this
module; use `lake build Metronome.HostPins` (or `lake env lean
Metronome/HostPins.lean`), as the other cuts do.

### Measured commands (2026-11-21, this machine, 10-core i5-1245U)

| Command | Exit | Wall |
|---|---|---|
| `lake env lean -DwarningAsError=true Metronome/HostPins.lean` | 0 | 15 s |
| `lake build Metronome.SpiPins Metronome.HostRead Metronome.HostMap` | 0 | 1 s (already built) |
| `lake build Metronome.HostPins` | 0 | 1-12 s |
| `lake env lean` on the axiom audit file | 0 | 3 s |
| `python code/tests/lean/hostpins_check.py --artifacts-dir data/raw/lean_hostpins_v4_20261121/rtl` | 0 | 70 s (Yosys + extraction + the generated 1300-line proof) |
| `python code/tests/lean/hostpins_check.py --mutations --artifacts-dir .../rtl_mutants` | 0 | 158 s (both mutants rejected) |
| `git diff --quiet HEAD -- src` | 0 | - |

### Mutants (`hostpins_check.py --mutations`, temporary copies of `src/`)

| Mutation | Change | Rejected by |
|---|---|---|
| `hostpins_tx_early` | `TX` loads in the request cycle (`rd \| hland`) instead of the acknowledge cycle | the read cut's `rtlTx` in the composed file (an unsolved goal in `rtlStep`'s `tx` field) |
| `hostpins_sck_from_s1` | `u_host.sck = s1[8]`: one synchroniser stage dropped for SCK | the pin cut's structural check (`u_host.sck is not s2[8]`) |

### Gaps

* **Write side, `hrise` bound.** `transaction_write_target` reuses
  `SpiPins.transaction_strobes`, which asks the rises for *all* `k`, not just
  `k < 8 * nbytes`. Weakening it means re-running that proof's `data_step` chain
  with bounded premises; the read-side theorems here already use the bounded
  form.
* **`hackAddr` / `hackSlot` (read).** Stated as premises, not derived from the
  RTL `rd` pulse (see above). For a real read they hold; the derivation needs
  the address phase's per-edge bit-count chain.
* **`hval`.** The composed read theorem ties the `rd_val` *input* to the map; it
  does not model the chip's register file, and the read cut's `Regs` are a free
  trace.
* **RAM service.** A data-RAM read's byte still comes from the RAM service
  contract (`hland`/`hlandD`), which is an interface premise of the read cut;
  this cut only states that a *register* read never lands.
* **`honly`/`hcs` are global.** The transaction's premises say "no other pin
  rise, `CS_N` low everywhere"; a real capture that keeps clocking after `CS_N`
  rises is outside them (as in `SpiPins`).
* **Physical timing.** Setup/hold, the synchronisers' analog behaviour and the
  60 MHz closure are out of scope, as in every other cut.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/hostpins/`).

## Chip-top debug, pin-replay, program-memory and reset cut (`Debug.lean`)

Item 3I of the verification plan: the last chip-top logic of
[src/project.v](../../../src/project.v) that the other Lean cuts leave outside
their boundaries.

| Path | Role |
|---|---|
| [Metronome/Debug.lean](Metronome/Debug.lean) | specification written from SPEC_V2 §1, §2, §5, §9, §9a.8, §12.2, §12.4, §13.1, §13.2 |
| [debug_check.py](debug_check.py) | Yosys elaboration (`-D USE_IHP_SRAM`), fail-closed extraction, Lean emission, mutation runs, CLI, evidence |
| [DebugEquivalence.lean.in](DebugEquivalence.lean.in) | proof template: per-cone equalities, three trace lifts, trace consequences, axiom audit |
| `data/raw/lean_debug_v4_20261121/` | evidence of the accepted run |

The module is not part of the default library target, so `lake build` does not
build it; use `lake build Metronome.Debug` (or `lake env lean
Metronome/Debug.lean`). The project's `lakefile.toml` already passes
`-DwarningAsError=true`, and the module builds clean (no warnings, including
deprecations).

### Run it

```text
python code/tests/lean/debug_check.py
python code/tests/lean/debug_check.py --mutations
python code/tests/lean/debug_check.py --mutations --artifacts-dir data/raw/lean_debug_v4_20261121
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the defaults write into
`data/raw/lean_debug_v4_20261121/` (`--artifacts-dir` must be a fresh
directory). A rejected baseline or an accepted mutant exits non-zero.
`check_debug(src_dir_or_json, out_dir, *, lake, yosys, case="baseline")` returns
the report dictionary and raises `DebugRejected`; `run_mutations(snapshot,
out_dir, lake, yosys)` returns `(case, rejected, stage, exit)` records. The
`verify.py` hook tuple is

```python
("debug", debug_check, debug_check.check_debug)
```

### Measured commands (this machine, 2026-11-21)

| Command | Exit | Wall |
|---|---|---|
| `lake build Metronome.Debug` | 0 | 0.4 s (already built; 3.8 s on the first run) |
| `lake env lean -DwarningAsError=true Metronome/Debug.lean` | 0 | 4.5 s |
| `python code/tests/lean/debug_check.py` | 0 | about 45 s |
| `python code/tests/lean/debug_check.py --mutations --artifacts-dir data/raw/lean_debug_v4_20261121` | 0 | 185.5 s |
| `git diff --quiet HEAD -- src` | 0 | - |

Tools: Lean 4.35.0 (`lake` 5.0.0-src+eb6cafb), Yosys 0.70+190. The accepted
baseline generated file is 52,930 bytes; its Lean run is about 24 s, and the
mutants cost 9-37 s each (Yosys plus the generated proof). The baseline file has
50 `#print axioms` records, 46 of them carrying a `bv_decide` native certificate;
`sorryAx` appears in none. The `lakefile.toml` already passes
`-DwarningAsError=true`, and both `lake build Metronome.Debug` and the direct
`lake env lean` run print no warning or error.

### Claims

#### (a) Pin level and edge vectors (SPEC_V2 §2, §13.2)

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted `pins_level` is `(PIN & ~mask) \| (RLV & mask)` with `mask = EMASK & {13{RPL}}`. | `Pins.rtlPinsLevel_eq` | `s2` (16), `rlv`, `emask` (13), `replay` symbolic. |
| The extracted `pins_prev` is the same substitution on `sp`/`rlv_prev`. | `Pins.rtlPinsPrev_eq` | Same. |
| The extracted `lvl` is `{3'd0, pins_level}`: pins 13..15 read 0. | `Pins.rtlLvl_eq`, `Pins.rtl_lvl_high_zero` | Structural check requires `lvl[15:13]` tied to 0. |
| The extracted `rise`/`fall` are `level & ~previous` / `~level & previous`, zero above. | `Pins.rtlRise_eq`, `Pins.rtlFall_eq` | The 13-bit level/previous gate buses are leaves (`pl`, `pp`); the top 3 bits are checked tied 0. |
| Masked pins read `RLV` whatever the pad holds; unmasked pins read `s2`/`sp`. | `Pins.rtl_level_masked`, spec `Pins.level_masked`, `level_unmasked`, `level_replay_ignores_pad` | `bv_decide` over the 13-bit lanes. |
| With `RPL = 0` the level is the synchronised pins. | `Pins.level_no_replay` | |
| A rise and a fall of one pin cannot coincide; an edge vector is nonzero exactly when the level changed. | `Pins.rise_fall_exclusive`, `Pins.edge_nonzero` | Spec-side. |
| The risen/fallen vector of the extracted level/previous lanes. | `Pins.rtl_rise_level`, `Pins.rtl_fall_level` | Composition by rewriting the two lane equalities. |

#### (b1) Execution digest (SPEC_V2 §12.2)

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted `MEN` next state is `d_wr_mctl ? h_wd[0] : MEN`. | `Digest.rtlMen_eq` | State and input symbolic. |
| The extracted `MISR` next state is `MCTL[1] ? 0 : (MEN && !FRZ ? CRC step : M)`, with `D = {OEN, OUT}` and polynomial `0x04C11DB7`. | `Digest.rtlMisr_eq` | State and input symbolic; the reset mux is part of the equation. |
| The extracted digest transition and trace are the specification's at every cycle. | `Digest.rtlStep_eq_step`, `rtlStateAt_eq`, `rtl_trace_result` | Any finite sampled input sequence, reset included. |
| A frozen cycle without an `MCTL` clear holds `M` on the extracted trace. | `Digest.rtl_trace_misr_frozen` | `frz`, no clear bit, reset released. |
| Spec consequences: a `MCTL` bit-1 write clears, a frozen or disabled cycle holds, an advancing cycle is the shift xor conditional-poly xor `D`. | `misr_clear`, `misr_frozen_holds`, `misr_advances`, `misr_disabled_holds` | |
| `D`'s low half is `OUT[13:0]` and its high byte `OEN[7:0]`. | `Digest.dataVec_split` | |

#### (b2) Edge capture and replay (SPEC_V2 §12.4, §13.1, §13.2)

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted replay timer is `{1'b0, DC} + 1`; the record interval is `{1'b0, WB[31:13]}`. | `Ctrl.rtlTick_eq`, `Ctrl.rtlInterval_eq` | `dc`, `WB` symbolic. |
| `replay_apply` is `RPL && WV && !FRZ && DC + 1 >= WB.DC`; `replay_late` is the strict comparison. | `Ctrl.rtlApply_eq`, `Ctrl.rtlLate_eq` | Symbolic; `WV = s_replay_valid[0]`. |
| `replay_levels` is `RLV` or, on apply, `(RLV & ~EMASK) \| (WB[12:0] & EMASK)`. | `Ctrl.rtlReplayLevels_eq`, `Ctrl.replay_levels_masked` | Masked bits come from the record. |
| `cev` is `CEN && !RPL && !FRZ && ((RISE\|FALL)[12:0] & EMASK) != 0`. | `Ctrl.rtlCev_eq`, `cev_spec`, `cev_off`, `cev_replay` | `RPL` takes priority over `CEN`. |
| The extracted `ECTL` replay/cen bits take the host byte on a same-cycle host write, else the drained core byte, else hold; a host write wins over a core drain. | `Ctrl.rtlReplay_eq`, `Ctrl.rtlCen_eq`, spec `host_ectl_wins`, `core_ectl_wins`, `rtl_trace_ectl_host_wins` | Byte-split (see differences). |
| The extracted `EMASK` next state takes each byte from the host or core write independently, else holds. | `Ctrl.rtlEmask_eq` | |
| The extracted `RLV` next state is the applied/shifted levels with the host/core byte write over the byte it targets. | `Ctrl.rtlRlv_eq` | |
| `RLV` of the previous cycle holds in a frozen cycle. | `Ctrl.rtlRlvPrev_eq` | |
| The extracted `DC` next state: `ECTL` write clears (also frozen), `FRZ` holds, apply clears, capture off (no replay) clears, an edge event sets 1, otherwise count and saturate at `2^19-1`. | `Ctrl.rtlDc_eq`, spec `dc_write_clears`, `dc_idle_zero`, `dc_edge_sets_one`, `dc_saturates`, `frozen_holds` | |
| The extracted capture/replay transition and trace are the specification's. | `Ctrl.rtlStep_eq_step`, `rtlStateAt_eq`, `rtl_trace_result` | Any finite sequence. |
| A frozen cycle with no `ECTL`/`EMASK`/`RLV` write holds the whole block on the extracted trace; an `ECTL` write clears `DC`; a host `ECTL` write wins. | `Ctrl.rtl_trace_frozen`, `rtl_trace_dc_ectl`, `rtl_trace_ectl_host_wins` | |

#### (c) Program-memory port muxing (SPEC_V2 §5, §9, 9a.8)

| Claim | Theorem / check | Conditions |
|---|---|---|
| The extracted strobes are `we0 = h_wr && in_prg && !a_prg[11]`, `we1 = ... && a_prg[11]`. | `Pmem.rtlPmWe0_eq`, `rtlPmWe1_eq`, `rtl_pm_exclusive` | `hWr`, `inPrg`, `a_prg` symbolic. |
| The extracted byte lane is `1 << a_prg[2:0]`, never zero, and lane `k` is enabled exactly by the low three address bits `k`. | `Pmem.rtlPmBe_eq`, `rtl_pm_lane_nonzero`, spec `be_low3`, `be_ne_zero` | |
| The extracted port address is the host word address `a_prg[10:3]` on a write, else the core's `fadr[7:0]`/`fadr[15:8]`. | `Pmem.rtlPmAddr0_eq`, `rtlPmAddr1_eq`, `rtl_pm_port0`, `rtl_pm_port1` | The address mux select is the strobe net. |
| The instance wiring is the map's: `u_pmem0/1.we = pm_we*`, `.be = pm_be`, `.wd = h_wd`, `.ren = fen[k]`, `.clk = clk`. | Python `extract_pmem` | Fail-closed. |
| The `md2_pmem` macro boundary is the contract: `A_ADDR = addr`, `A_DIN` is the write byte replicated eight times, `A_BM` is `be[k]` replicated eight times, `A_WEN = we`, `A_REN = ren & ~we`, `A_MEN = ren \| we`, `A_DLY = 1`, `A_DOUT = rd`, BIST tied 0. | Python `_pm_macro_check` | `-D USE_IHP_SRAM`; the macro is a blackbox (`src/md2_sram_bb.v`). |
| A host write takes the port, so a same-cycle fetch is presented the host's word address (9a.8 calls the word undefined). | `Pmem.port_host`, `rtl_pm_port0` | The word's *content* is the macro's and is not modelled. |

#### (d) Reset synchroniser (SPEC_V2 §1)

| Claim | Theorem | Conditions |
|---|---|---|
| The extracted first stage is tied high on a released edge; the second samples `rst_m`. | `Reset.rtlRstM_eq`, `Reset.rtlRstQ_eq` | Structural check: both are `$adff` with `ARST = rst_n`, active-low, value 0, posedge `clk`. |
| The extracted reset transition and trace are the specification's. | `Reset.rtlStep_eq_step`, `rtlStateAt_eq`, `rtl_trace_result` | Any sampled `rst_n` sequence. |
| After a sampled reset `rst_q` is low, still low one cycle later (release needs two edges), and high after two released edges. | `Reset.rtl_trace_rstq_low`, `rtl_trace_rstq_low_one_more`, `rtl_trace_rstq_after_two`, spec `rstq_shift`, `rstm_high` | Sampled-cycle model only. |

### Premises and free leaves

Each per-cycle leaf is also the input of another cut or an interface, so the
claim is "given these SPEC quantities, each extracted cone is the SPEC
quantity". The leaves are:

| Leaf | Where it comes from | Status here |
|---|---|---|
| `s2`, `sp` (16) | the pin synchronisers, `Metronome.SpiPins` (`spipins_check.py`) | per-cycle leaves of the pin cones (the level/previous vectors); the Ctrl cone does not read them |
| `rlv`, `rlv_prev`, `emask`, `replay`, `cen`, `dc` | this cut's own registers | state of the extracted transitions |
| `h_wd` (8), `h_ectl`, `h_em0`, `h_em1`, `h_rlv0`, `h_rlv1` | host-map decode (`HostMap`, `hostmap_check.py`) | free |
| `d_wr_ectl`, `d_wr_em0/1`, `d_wr_rlv0/1` | host strobe **or** core drain | free; the drain term is `cw_drain & (cw_dbg_off == offset)`, i.e. `cw_drain`/`cw_pending_*` of `Metronome.CoreQueue` |
| `cw_pending_data` (8) | the queued core write byte (`CoreQueue`) | free |
| `frz` | `Metronome.CoreCtl` (freeze/step) | free |
| `frzd` | `CoreCtl`'s previous freeze | **not referenced** by these cones (no FRZD consumer in the debug/pin/program/reset logic); nothing to bind |
| `s_replay_valid` (2), `s_replay_word` (32/64) | the Stream cut's `replay_valid`/`replay_word` (`Metronome.Stream`, `stream_check.py`) | free; only bit 0 of the valid vector and the low 32-bit record word are read |
| `o_oe` (8), `o_out` (14) | the output-pin registers (`SPEC_V2 §8`, the Glue agent's `gpio`/output cut) | free |
| `rise`, `fall` (16) | (a)'s derived edge vectors | free; only the low 13 bits are bound (the top three are checked tied 0) |
| `h_wr`, `in_prg` | host map strobe and program-window decode (`HostMap`) | free |
| `a_prg` (16), `fadr` (16), `fen` (2) | the host map offset and the core cut's fetch address/enable (`Metronome.Core`) | free |
| `rst_q` | (d)'s `rst_q` (the reset cut's abstraction) | free per cycle; structural check ties the debug registers to that net |
| `rst_n` | the chip pin | sampled per-cycle input |

* **Pins.** The 13-bit level/previous gate buses are bound as leaves `pl`/`pp`
  for the `lvl`/`rise`/`fall` cones; the high three bits of those nets must be
  tied to 0 (checked) so the zero extension is a structural fact.
* **Digest.** `MEN` and `M` are this cut's own state; `d_wr_mctl` is the
  host-map `MCTL` strobe; `o_oe`/`o_out` are the output-pin registers in this
  cycle.
* **Capture/replay.** `frz` is `CoreCtl`'s; a drained core write is a free
  runtime write (the queue owns `cw_drain`); the stream owns
  `replay_valid`/`replay_word`.
* **Program memory.** The SRAM macro is a blackbox; its storage, latency and
  BIST are not modelled.
* **Reset.** `rst_n` is a sampled per-cycle input, as in every other cut.

### SPEC ambiguities and RTL/SPEC differences (reported, not fixed)

1. **`cev` gating.** §12.4 defines `cev = CEN && ((RISE|FALL)[12:0] & EMASK) !=
   0` "in an unfrozen cycle". The RTL also gates it with `!RPL`; §13.2's "`RPL`
   takes priority over `CEN`" is the authority, so the specification includes
   both `!RPL` and `!FRZ` and the equality proves the RTL form.
2. **`DC` while frozen.** §12.4's `DC' = !CEN ? 0 : …` is stated for an unfrozen
   cycle; §12.3 says `DC` holds in a frozen cycle. The RTL's priority is
   `ECTL` write (also frozen) → `!FRZ` hold → apply/clear → `cev` → count. The
   specification follows exactly that order, so a frozen cycle with `CEN = 0`
   *holds* `DC` rather than clearing it, and a frozen `ECTL` write clears it.
   This is consistent with §12.3 and §12.4 read together, but a reader of
   §12.4 alone could expect the clear to win in every cycle.
3. **Byte-split host/core priority.** §13.1 says a runtime drain happens
   "before a host write in the same cycle, which wins". In the RTL `ECTL`,
   `EMASK` and `RLV` are updated byte by byte (`h_ectar ? h_wd : cw_pending_data`
   per byte), so a host write to one byte and a core drain to the *other* byte
   of the same register both take effect. The specification models the
   byte-split and proves the per-byte host priority (`host_ectl_wins`,
   `rtl_trace_ectl_host_wins`); it does not claim whole-register supersession.
4. **Replay interval width.** §13.2's `WB.DC` is `WB[31:13]` (19 bits) and `DC`
   is 19 bits; the RTL compares the 20-bit `{1'b0, DC} + 1` with
   `{1'b0, WB[31:13]}`. `Ctrl.tick`/`Ctrl.interval` are 20-bit, exactly the RTL,
   so the top bit is always 0 and the comparison is the SPEC's.
5. **`RLV` previous while frozen.** The RTL holds `rlv_prev` in a frozen cycle
   (`if (!frz)`), so a replayed `pins_prev` holds too. §12.3's "the pads keep
   their levels" and §13.2's "the pad is ignored" support this; the
   specification states it as a register equation.
6. **Program-memory fetch in a write cycle.** §9 says host writes take the port
   and 9a.8 says a same-cycle fetch returns an undefined word. The RTL muxes the
   port address on the write strobe, so the fetch is presented the host's word
   address and reads a word of the program image (the host writes one byte lane).
   The cut proves the deterministic port muxing and leaves the word's content to
   9a.8 and the macro contract; it does not claim the fetched byte is undefined.
7. **Reset model.** Only the sampled-cycle behaviour is modelled. The
   asynchronous assertion between sampled edges, metastability and the release
   flop's analog timing are outside the model.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `misr_poly` | `MISR_POLY = 0x04C11DB6` | generated Lean: `Digest.rtlMisr_eq` (counterexample) |
| `misr_frozen` | the digest advances in a frozen cycle (`else if (men)`) | structural: `misr: the bound leaf i.frz is not used` |
| `replay_mask_ignores_emask` | `replay_mask = {13{replay}}` | structural: `pins_level: the bound leaf emask is not used` |
| `ectl_core_beats_host` | a drained core write beats a same-cycle host write to `ECTL` | structural: `replay: the bound leaf i.hEctl is not used` |
| `dc_not_cleared` | an `ECTL` write no longer restarts `DC` | generated Lean: `Ctrl.rtlDc_eq` |
| `pins_high_s2` | `lvl = {s2[15:13], pins_level}` | structural: `lvl: bits 13..15 are not tied to 0 (SPEC_V2 §2)` |
| `pm_be_shift_one` | the program byte lane is `1 << (a_prg[2:0] + 1)` | generated Lean: `Pmem.rtlPmBe_eq` |
| `rstq_one_stage` | `rst_q <= 1'b1` (one-stage release) | structural: `rst_m: missing net` (`opt_clean` removes the now-dead first stage) |

Four mutants are rejected by the generated Lean and four by a fail-closed
structural check. The structural rejections are the honest outcome: each removes
a bound leaf or a documented structural fact, so the cut refuses the design
before proving anything weaker. The `pins_high_s2` and `rstq_one_stage`
rejections are the same class as the SPI-pin cut's `spipins_s2_bypass`, where
`opt_clean` removes a dead stage.

### Trust added

* Yosys elaboration with `verify.py`'s recipe plus `-D USE_IHP_SRAM` (as
  `mem_check.py`), the shared RTLIL adapter and the generated Lean: the suite's
  usual trust base.
* `DbgCone` (local to `debug_check.py`; the shared `rtlil.py` is unchanged) adds
  `$logic_not`, `$reduce_or`/`$reduce_bool`, `$xor`, `$gt`/`$le`, `$shl` and
  multi-bit `$and`/`$or`/`$not`. Every shape is fail-closed: an unexpected
  width, an unsupported cell, an unbound or multiply driven net, a partially
  claimed bus or a shorted constant raises `UnsupportedRTL`.
* The concatenation assembler merges exact runs of bound buses; any bit it
  cannot place goes through the per-bit path and fails if undriven.
* Checked modelling steps: the high three bits of `lvl`/`rise`/`fall` are tied
  to 0; every bound leaf must appear in the cone that should use it (a
  disconnected leaf fails closed); `rst_m`/`rst_q` must be the active-low
  `rst_n`-cleared flops; the `md2_pmem` macro wiring and lane replication are
  checked; the address mux select is the strobe net.
* `bv_decide` adds per-theorem native LRAT certificate axioms, recorded in
  `<case>.axioms.txt` (e.g. `Pins.rtlPinsLevel_eq._native.bv_decide.ax_1_11`,
  `Digest.rtlMisr_eq._native.bv_decide.ax_1_13`). `#print axioms` is parsed and
  an accepted case with `sorryAx` is rejected. The certificate checker is the
  only trust added beyond Yosys, the adapter and the map headers.
* The SRAM macro is a blackbox. Nothing is claimed about its storage,
  registered-read latency, bit-mask implementation or BIST; `A_DLY = 1` and the
  port wiring are the contract's checked part.

### Gaps

* **MISR error escape.** §12.2's "a random error escapes with probability about
  2^-32" is a literature property of the 32-bit MISR for this input width; it is
  not proved.
* **Replay mirror property.** §13.2's "the replayed level equals the captured
  level" needs the capture stream, record memory and the `DC` field to be
  composed; this cut proves the per-cycle substitution (`replay_levels_masked`),
  `apply`/`late` and the `DC` restart, not the trace-level mirror.
* **Free leaves, not composed in Lean.** `cw_drain`/`cw_pending_*` (queue cut),
  the host decodes, `s_replay_valid`/`s_replay_word` (stream cut), `o_oe`/`o_out`
  (output-pin registers), `fen`/`fadr` (core cut) and `in_prg` are per-cycle
  inputs. Composing them is rewriting, as in the other cuts, and is not written
  as a Lean theorem here.
* **Program-memory contents and timing.** The macro's read timing, byte-mask
  behaviour and BIST are the blackbox contract; 9a.8's "undefined word" is
  stated as the port behaviour.
* **Reset timing.** Asynchronous assertion between sampled edges,
  metastability, release latency and the reset tree's physical behaviour are
  outside the discrete model.
* **Physical timing.** 60 MHz closure, setup/hold, pin synchroniser
  metastability and the replay timer's real-time period are out of scope, as in
  every other cut.
* **`DC`/`MISR` long-run properties.** "One read after millions of cycles"
  (MISR) and the 8.7 ms saturation (DC) are consequences of the per-cycle
  equations but not stated as trace theorems.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/debug/`).

## Glue cut notes (SPEC_V2 6, 6.1, 7, 8, 9, 12.1, 12.3)

The chip-top glue of [src/project.v](../../../src/project.v) that no earlier cut
covers: the source and guard vectors, the per-line `g_line` bundle, the control
registers, the flag pair, the host mailbox, the `ERR`/`IRQ` pair, and the output
pin registers and buses.  This is item 3H of the verification plan.

| Path | Role |
|---|---|
| [Metronome/Glue.lean](Metronome/Glue.lean) | independent specification, written from the SPEC text |
| [GlueEquivalence.lean.in](GlueEquivalence.lean.in) | generated-proof template (per-slot equalities, the step, the trace lift, the axiom audit) |
| [glue_check.py](glue_check.py) | Yosys elaboration, fail-closed cone extraction, Lean emission, mutations, evidence |
| `data/raw/lean_glue_v4_20261121/` | evidence of the accepted run: generated Lean, logs, axiom audit, tool versions, `run_status.txt` |

`Metronome.lean` is unchanged, so `lake build` does not build this module; use
`lake build Metronome.Glue` (or `lake env lean Metronome/Glue.lean`).

**`verify.py` hook tuple** (not added here; `verify.py` is owned by another cut):

```python
("glue", glue_check, glue_check.check_glue)
```

with `check_glue(src_dir_or_json, out_dir, *, lake, yosys, case="baseline") ->
{ok, outcome, exit, ...}` raising `GlueRejected` on a failed proof or a
`sorryAx` audit and `UnsupportedRTL` on a structural/wiring failure, and
`run_mutations(snapshot, out_dir, lake, yosys) -> [(case, rejected, stage,
exit)]`.

### Run it

```text
python code/tests/lean/glue_check.py                     # baseline
python code/tests/lean/glue_check.py --mutations         # plus eight mutants
python code/tests/lean/glue_check.py --mutations --artifacts-dir <fresh dir>
```

Both need `lake` (Lean 4.35.0) and `yosys` on `PATH`; the default evidence
directory is `data/raw/lean_glue_v4_20261121/`, and `--artifacts-dir` must not
exist yet. A rejected baseline or an accepted mutant exits non-zero.
`run_status.txt` records each case's own Lean/Yosys exit code and whether it
matched the expectation; `sorryAx` is rejected in an accepted case.  Every Lean
run has a 900 s timeout and one retry when the process dies without a
diagnostic.

PowerShell (project defaults):

```powershell
$cad = "$env:USERPROFILE/tools/oss-cad-suite"
$env:PATH = "$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"
python code/tests/lean/glue_check.py --mutations --artifacts-dir data/raw/lean_glue_v4_20261121
```

### Claims

| Claim | Theorem | Conditions |
|---|---|---|
| Source slot `k` of the elaborated `srcs` is the ISA table's source `k`, for all 64 slots: `FLAGS.LO/HI`, `PINS.LO/HI`, `ACC`, `R0..R3`, `SHk.D/O`, `CNTk.LO/HI`, `LFk.B0..B3`, `LFk.O`, `P0.D`, `Sk.BIT/BYTE`, `HOST.IN`. | `rtlSrc0_spec` … `rtlSrc63_spec` (one per slot) | The source leaves are free per-cycle inputs. Slots beyond `machine.SRC` (39..63) prove the vector reads 0 (9a.1); the four core-local slots (`ZERO`, `IMM`, `L.IN`, `L.CAP`) are zero in the global vector because each core substitutes them (`Metronome.Core` proves the core's own overrides). |
| Guard slot `k` of the elaborated `guards` is the ISA table's guard condition `k`, for all 64 slots. | `rtlGuard0_spec` … `rtlGuard63_spec` | Same. Guards 62..63 prove the vector reads false; `HOST.OUTE` is `!OUTV` (6.1). |
| Line guard bundle `k` is `{PINB, PINA, SP, IN1, IN0}` of line `k`: `g_line[5k +: 5]`. | `rtlGLine0_spec` … `rtlGLine3_spec` | The line outputs are free; the five line-relative guard slots of the *global* vector read 0 (`guardAt_lineRelative`). |
| Single-bit sources occupy bit 0 with zero high bits (6). | `srcAt_singleBit` | The six single-bit slots (`SHk.O`, `LFk.O`, `Sk.BIT`). |
| `RUN_global`, `IRQEN`, `IRQ`, `ERR`, `DB`, `F`, `FP`, `INB`, `INV`, `INVP`, `OUTB`, `OUTV` are the specification's next states at every state and input. | `rtlRunG_spec`, `rtlIrqEn_spec`, `rtlIrq_spec`, `rtlErr_spec`, `rtlDb_spec`, `rtlFl_spec`, `rtlFlp_spec`, `rtlInB_spec`, `rtlInv_spec`, `rtlInvp_spec`, `rtlOutB_spec`, `rtlOutv_spec` | The host-write strobes, the picked `FLAGS`/`HOST.OUT` words, `h_wd`, the `HOST.IN` read bus, `frz`, `rst_q` and the sticky/event terms are free. `rtlFl`'s cone has one Yosys `x` bit, bound as a free `Bool` input (the equality holds for every value, so the don't-care cannot reach the flag register). |
| The elaborated transition is the specification transition. | `rtlStep_eq_step` | Assembled from the eleven field equalities. |
| The elaborated trace is the specification trace at every cycle. | `rtlStateAt_eq`, `rtl_trace_result` | Any finite prefix, same reset start. |
| A frozen cycle holds `FP`; a frozen cycle holds a doorbell pulse and adds the written bits (12.3). | `rtl_trace_flp_frozen`, `rtl_trace_db_frozen` | Lifted to the elaborated trace. |
| `IRQ` is low from reset until an `IRQEN` write enables it. | `rtl_trace_irq_quiet` | No reset edge and `IRQEN = 0` in every earlier cycle. |
| Each output's table index is 8/12.1's `{SEG(LINE), b2, b1, b0}` with the `LIVE` substitutions, or 0 when unbound. | `rtlIdx0_spec` … `rtlIdx13_spec` | The `BIND`/`SEL` bytes, the line's `COMMITTED`, `PINA`/`PINB` and `SEG` are free. |
| Each `OUT` and `OEN` register is `LUT[idx]` / `OE[idx]`, held while frozen and cleared by reset. | `rtlOut0_full` … `rtlOut13_full`, `rtlOe0_full` … `rtlOe7_full` | Every configuration field is free (`BIND`, `SEL`, `LUT`, `OE`, `COMMITTED`, `PINA`, `PINB`, `SEG`). |
| The three pin buses are 8's: `uo_out = {OUT[13:8], IRQ, MISO}`, `uio_out = OUT[7:0]`, `uio_oe = OEN`. | `rtlPins_spec` | `o_out`, `o_oe`, `irq` and `miso` are free; the structural check requires the exact port wiring bit for bit. |

Spec-side consequences (proved on `Metronome.Glue.step`, no RTL):
`step_reset`, `irq_of_disabled`, `irq_of_outv`, `irq_of_err`, `err_iff`,
`db_frozen_hold`, `db_frozen_keeps`, `flp_frozen_holds`, `invp_frozen_holds`,
`fl_set`, `fl_clear`, `fl_other`, `inv_host_write`, `inv_read_clears`,
`inv_hold`, `outv_host_write`, `outv_host_clear`, `runG_host_write`,
`outNext_frozen`, `oeNext_frozen`, `outNext_reset`, `oeNext_reset`, `pins_eq`,
`lineGuard_at`, `srcAt_beyond`, `guardAt_beyond`, `srcAt_singleBit`,
`setFlag_at`, `setFlag_other`.

### Premises and free leaves

The cut starts at the chip-top nets and never reaches into another block:

* **Sources**: `fl`, `pins_level` (the synchronised/replayed pin levels, 2 and
  13.2), `acc_a`, `acc_r`, `sh_d`, `sh_o`, `cn_v`, `lf_s`, `p_dat`, `s_bit`,
  `s_byte`, `inb`.  The RTL's `lvl` is `{3'd0, pins_level}`, so the spec carries
  the thirteen-bit level vector and zero-extends it.
* **Guards**: the same plus `sh_done`, `cn_z`, `acc_z`, `acc_c`, `acc_n`, `inv`,
  `outv`, `p_rdy`, `s_end`, `s_mark`, `s_bb`, `l_run`; `g_line` reads `l_in`,
  `l_sp`, `l_pina`, `l_pinb`.
* **Control registers**: the host-write strobes `c_wr_run`, `c_wr_irqen`,
  `c_wr_db`, `c_wr_hin`, `c_wr_hst`, the picked words `w_flags` and `w_hout`,
  `h_wd`, `rd_hin` (the `HOST.IN` read bus), `frz`, `rst_q`, and the
  sticky/event terms `conflict`, `memhaz`, `cw_overrun`, `t_late`, `t_ovr`,
  `l_tapmiss`, `s_starved`.  The cut binds the five strobes rather than
  `w_ctl`/`o_ctl`, because the host-map cut's `enCtrl*_spec` theorems already
  prove each strobe is "a host write of that `CTRL` byte"; the picked words are
  the move-resolution cut's `rtlWordFlags_spec`/`rtlWordHostOut_spec`; `rd_hin`
  is `Metronome.Moves.readsOf`; `frz` is `Metronome.CoreCtl`'s; the other terms
  are the move, queue, thread, line and stream cuts'.
* **Output pins**: the `cfg` window fields `obind`, `sel`, `lut`, `oe` (the
  latch-bank cut covers their content), `l_comm`, `l_pina`, `l_pinb`, `l_seg`
  (the line cut), `frz` and `rst_q`.

### What the adapter checks (fail-closed)

`glue_check.py` re-elaborates `src/` with `verify.py`'s Yosys recipe
(`read_verilog -I src …; hierarchy -check -top; proc; opt_clean; write_json`)
and then:

* reads `machine.SRC` and `machine.GUARD_CONDS` from `code/md2/machine.json` and
  requires every generated `S_*`/`G_*` constant of `src/md2_defs.vh` to be the
  table's index (and the set to be complete: 39 + 62);
* reads the *arm comments* of `srcAt` and `guardAt` in `Metronome/Glue.lean` and
  requires them to be the machine tables in order, so the hand transcription
  cannot drift; the arm *values* are pinned by the per-slot equalities against
  the RTL;
* reads `D_FLAGS_SET` from `src/md2_defs.vh` and `flagsSetDst` from the Lean
  module and requires them equal;
* requires `uio_out = o_out[7:0]`, `uio_oe = o_oe` and
  `uo_out = {o_out[13:8], irq, miso}` bit for bit, so the pin map is checked
  structurally before its equality;
* for every output `k`, requires `g_out[k].obind/.sel/.lut` and (for `k < 8`)
  `g_out[k].g_oe.oe` to be exactly the `cfg` window bytes at
  `HAI_OUT_BASE - CFG_LO_I + HS_OUT*k + HO_OUT_BIND/SEL/LUT/OE`, so a moved map
  window fails before Lean runs;
* extracts every cone with `GlueCone`, which adds Yosys's indexed-bit-write
  lowering `$shift(A, $neg(zext(idx)))` (admitted only when the negated bus's
  top bit is the constant zero), a wide mux whose select is a net slice, and
  binds Yosys `x` bits as free `Bool` inputs.  Everything is fail-closed: an
  unsupported cell, an undriven net bit, a partial bus overlap, a second
  register driver or a register with an initial value raises `UnsupportedRTL`;
  every output register is checked to be a plain `$dff` on the top clock.

The `$shift`/`$neg` decode, the sliced-select mux and the `x`-as-free-input
binding are the only adapter extensions beyond
`moves_check.MovesCone`/`corectl_check.VectorCone` (the shared `rtlil.py` is
unchanged).  A register whose next state *uses* an `x` bit would fail its
equality rather than prove something weaker.

### Trust added

* Yosys elaboration and the RTLIL adapter: the same trust base as the rest of
  the suite.  The extraction reads only top-level net names, the `cfg` window
  bytes and the register cells of this cut.
* `bv_decide` on the per-slot and per-register equalities.  The accepted run's
  `baseline.axioms.txt` records all 187 theorems with `propext`,
  `Classical.choice`, `Quot.sound` and, where `bv_decide` bit-blasts a goal,
  that theorem's native LRAT certificate (`rtlFl_spec._native.bv_decide.ax_1_20`,
  `rtlIdx{k}_spec._native.bv_decide.ax_*`, `rtlGLine{k}_spec._native.bv_decide.ax_*`).
  `sorryAx` is absent and the runner rejects it.  The parser joins the
  pretty-printer's wrapped axiom lists, so the audit is complete.  The
  certificate checker is the only trust added beyond Yosys, the adapter and the
  JSON/header readers.
* The header reader (the `S_*`/`G_*`/`HO_OUT_*`/`HAI_OUT_BASE`/`CFG_LO_I`
  constants) is the same trust the other cuts place in the generated map.

### Mutations (temporary copies of `src/`, never the repository)

| Mutation | Change | Rejected by |
|---|---|---|
| `glue_source_slot` | `FLAGS.LO` and `FLAGS.HI` exchange slots in `srcs` | `rtlSrc4_spec` / `rtlSrc5_spec` (the first failing declaration) |
| `glue_guard_polarity` | `gv[G_ACC_Z] = ~acc_z` | `rtlGuard24_spec` |
| `glue_err_misses_cwovr` | `ERR` drops the `CWOVR` term (13.1) | `rtlErr_spec` |
| `glue_irq_ignores_err` | `IRQ` ignores `IRQEN[1]`: a present sticky error drives the interrupt even when it is not enabled | `rtlIrq_spec` |
| `glue_flp_not_frozen` | `FP` updates in a frozen cycle | `rtlFlp_spec` |
| `glue_db_not_held` | the doorbell is not held while frozen | `rtlDb_spec` |
| `glue_out_not_frozen` | the `OUT` registers update in a frozen cycle | `rtlOut{k}_full` (the first failing output; all fourteen fail) |
| `glue_uo_out_irq` | `uo_out` bit 1 is `outv`, not `irq` | the structural pin check: `uo_out[1]: the IRQ register is not in the design` (with `IRQ` off the pin, Yosys removes the unused register, so the extraction fails closed) |

The actual per-case outcome and exit code are in `run_status.txt`; the stage
string names the generated declaration Lean reported first (the checker maps the
first error line back to its `theorem`/`def`).

### SPEC ambiguities and RTL/SPEC differences (observed, reported, not fixed)

1. **`guards` slots 27..31 are zero.**  7 makes `L.IN0`, `L.IN1`, `L.SYNC`,
   `L.PINA` and `L.PINB` line-relative, and the chip top supplies them per line
   through the five-bit `g_line` bundle the core substitutes for its executing
   line.  The global vector therefore reads 0 at those five indices; the cut
   proves both halves (`rtlGuard27_spec` … `rtlGuard31_spec`, `rtlGLine{k}_spec`)
   instead of inventing a global value.
2. **`FLAGS` index and value.**  6.1 writes `SET n`/`CLR n` without naming the
   encoding; the RTL takes `n = data[3:0]` and `SET` exactly for destination
   code `D_FLAGS_SET` (5), every other `FLAGS` destination writing 0.  The
   specification takes the RTL's encoding and pins both constants
   (`flagsSetDst`, checked against the header).
3. **`ERR` includes `CWOVR`.**  9 lists `CONFLICT`, `MEMHAZ`, `CWOVR` (13.1),
   every thread's `LATE`/`OVR`, every line's `TAPMISS` and every stream's
   `STARVED`; `ERRSUM` (9) has the same terms in bits 5..0.  The cut proves the
   `ERR` term (`rtlErr_spec`); `ERRSUM`'s readback is the host-read cut's.
4. **`HOST.OUTE` polarity.**  6.1 says "Guard `HOST.OUTE` is `!OUTV`"; the
   global vector stores the complemented bit (`gv[G_HOST_OUTE] = ~outv`) and the
   cut proves that, so the guard slot itself is already "the wire is free".
5. **`PINS.HI`.**  6 says unused high bits read 0; `PIN[12:0]` is thirteen
   bits, so `PINS.HI` is `{3'd0, PIN[12:8]}` (`rtlSrc7_spec`).
6. **Doorbell width.**  `DB` is `NT = 6` bits; a `DOORBELL` write uses
   `h_wd[5:0]` and the upper two host bits are ignored (9's "writing bit t").
7. **`INV` and the move read.**  6's "reading `HOST.IN` clears `INV`" is the
   move-resolution cut's `rd_hin`; this cut takes that bus as a free leaf and
   proves the mailbox side (`rtlInv_spec`, `inv_read_clears`).
8. **Yosys `x` in the `FLAGS` cone.**  `fl`'s next-state cone contains one `x`
   bit (the uninitialised lookahead of the single clocked `always` block, masked
   by the reset mux).  The adapter binds it as a free `Bool` input, and
   `rtlFl_spec` proves the equality for both values, so the don't-care is
   provably unobservable rather than silently tied to 0.
9. **No RTL/SPEC difference was found** in the sources, guards, `g_line`,
   control registers, mailbox, `ERR`/`IRQ` or output pins beyond the encodings
   listed above; the RTL and the SPEC text agree.

### Gaps

* **Pin-level and pin-timing provenance.**  `pins_level` is a free leaf: the
  two synchronisers and the replay substitution (2, 13.2) are the SPI-pin and
  stream cuts' business.  `l_pina`/`l_pinb`/`l_seg`/`l_comm` are free leaves as
  well (the line cut proves them).
* **Configuration content.**  The `BIND`/`SEL`/`LUT`/`OE` bytes are free; the
  latch-bank cut owns their content and the host-map cut their addresses.
* **Move and host decode.**  The `FLAGS`/`HOST.OUT` words, the `CTRL.*` write
  strobes and `h_wd` are free; the move-resolution and host-map cuts prove
  them, so this cut states what the glue does *given* those quantities.
* **`IRQ` to a pad and `MISO`.**  `miso` is a free leaf (the host read cut);
  the pin map is proved as a wiring identity, physical pad timing is not
  modelled.
* **Freeze transparency.**  The register equations and three frozen-cycle
  statements are proved; 12.3's "deleting the frozen cycles gives the same
  state sequence" for the whole chip is the core-control cut's and the
  k-induction bench's.
* **`#print axioms` of a rejected case.**  A rejected mutant's audit contains
  `sorryAx` downstream of its first failing theorem (Lean fills the failed
  proof); the case is rejected on the non-zero exit before the audit test, and
  an accepted case never contains it.
* **`bv_decide` abstention.**  A mutant can be rejected because `bv_decide`
  abstains ("potentially spurious counterexample", or a goal outside its
  fragment) rather than by naming an assignment.  The proof is still not
  closed, which is what the exit code records.

### Measured run

```
python code/tests/lean/glue_check.py --mutations \
  --artifacts-dir data/raw/lean_glue_v4_20261121
```

exited **0** on 2026-11-21 and took **1078 s** (17 min 58 s) wall clock on a
10-core i5-1245U laptop carrying other work, with Lean 4.35.0 and Yosys
0.70+190.  The RTL snapshot is `src/` at HEAD `b7b4068`
(SHA-256 `434c6ae6…`, recorded in `baseline.log`), and
`git diff --quiet HEAD -- src` is true before and after: every mutation is
applied to a temporary copy.  `run_status.txt`:

| Case | Outcome | Lean/Yosys exit | Expectation |
|---|---|---|---|
| `baseline` | accepted: 187 theorems (64 sources, 64 guards, 4 `g_line`, 12 control, 14 `OUT`, 8 `OEN`, pins, step, trace lift) | 0 | ok |
| `glue_source_slot` | rejected by `rtlSrc4_spec` | 1 | ok |
| `glue_guard_polarity` | rejected by `rtlGuard24_spec` | 1 | ok |
| `glue_err_misses_cwovr` | rejected by `rtlErr_spec` | 1 | ok |
| `glue_irq_ignores_err` | rejected by `rtlIrq_spec` | 1 | ok |
| `glue_flp_not_frozen` | rejected by `rtlFlp_spec` | 1 | ok |
| `glue_db_not_held` | rejected by `rtlDb_spec` | 1 | ok |
| `glue_out_not_frozen` | rejected by `rtlOut0_full` (all fourteen fail) | 1 | ok |
| `glue_uo_out_irq` | rejected by the structural pin check (`uo_out[1]: the IRQ register is not in the design`) | 1 | ok |

The baseline generated file is 150 KB; its Lean run is about 90 s (Yosys
elaboration and extraction take the rest of the ~2 min per case; each mutant
costs roughly the same).  `lake build Metronome.Glue` builds clean with
`-DwarningAsError=true` (the lakefile sets it), and the generated file is
checked with `lake env lean -j1 -DwarningAsError=true`, so a deprecated name or
an unused simp argument fails the case.

The accepted `baseline.axioms.txt` records all 187 theorems (the parser joins
the pretty-printer's wrapped lists); no entry mentions `sorryAx`.  The native
certificates are `rtlFl_spec` (one free `x` bit and the 16-bit flag byte),
`rtlIdx{k}_spec` (the index assembly) and `rtlGLine{k}_spec`; the source and
guard slots, the mailbox registers, `rtlPins_spec` and the trace lift carry
none of their own beyond `propext`/`Classical.choice`/`Quot.sound`.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/glue/`).

## Chip-top operation strobes: item 3J notes

Status: **baseline accepted and all eight mutants rejected** on 2026-11-21,
Lean 4.35.0, Yosys 0.70+190, branch `metronome-v4.0`, RTL snapshot SHA-256
`434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b`
(`git diff --quiet HEAD -- src` true before and after the run).
Evidence: [`data/raw/lean_strobes_v4_20261121/`](../../../data/raw/lean_strobes_v4_20261121).

This cut closes the last chip-top glue the coverage inventory
([`COVERAGE.md`](COVERAGE.md)) listed as uncovered: the per-unit operation
strobes that `project.v` computes from the picked write-group winner with the
`hits` / `dsteq` / `OPG` macros, plus the pointer port select, the line symbol
operation, the stream control merge and the debug-register write strobes.  The
unit, memory, line, stream and debug cuts took those nets as free per-cycle
leaves; the generated theorems here state them over the move bus and the
documented host decode.

### Files

| Path | Role |
|---|---|
| [`Metronome/Strobes.lean`](Metronome/Strobes.lean) | independent specification: `opg` on the pick, the one-hot fact, the selector maps, the stream control merge, the DBG write strobes |
| [`strobes_check.py`](strobes_check.py) | Yosys elaboration, fail-closed structural checks, cone extraction, Lean emission, mutations, evidence |
| [`StrobesEquivalence.lean.in`](StrobesEquivalence.lean.in) | generated-proof template (imports, options, namespace, body, axiom audit) |
| `data/raw/lean_strobes_v4_20261121/` | accepted run: generated Lean, logs, axiom audit, tool versions, `run_status.txt` |
| `data/raw/lean_coverage_v4_20261121b/` | read-only coverage re-run after the cut |

`Metronome.lean` is unchanged, so the default `lake build` does not build this
module; use `lake build Metronome.Strobes` (or `lake env lean
Metronome/Strobes.lean`).

**`verify.py` hook tuple:** `("strobes", strobes_check,
strobes_check.check_strobes)` — i.e. call
`strobes_check.check_strobes(src, out_dir, lake=lake, yosys=yosys, case=case)`
for the baseline and each case, and treat a raised
`StrobesRejected`/`UnsupportedRTL` as a rejection.  `verify.py` itself was not
edited by this task.

### Run it

```powershell
$cad = "$env:USERPROFILE/tools/oss-cad-suite"
$env:PATH = "$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"
python code/tests/lean/strobes_check.py --mutations `
  --artifacts-dir data/raw/lean_strobes_v4_20261121
```

`--artifacts-dir` must be a fresh directory.  A rejected baseline or an accepted
mutant exits non-zero.  Each case writes three generated files and their logs:
`<case>.opg.lean` (the 22 `OPG` strobes and the accumulator hit mask),
`<case>.sel.lean` (counter/LFSR selectors, `p_sel`, the line `sop`, the six
accumulator op-code slices) and `<case>.ctl.lean` (stream control, `cap_en`, the
DBG strobes), plus `<case>.axioms.txt`, `tools.log`, `lake.log`, `stdout.log`
and `run_status.txt`.  Each Lean run has a 900 s timeout and one retry when the
process dies without a diagnostic.

Measured on the 10-core i5-1245U project laptop, 2026-11-21:

| Command | Exit | Wall |
|---|---|---|
| `lake build Metronome.Moves` (already built) | 0 | 4 jobs |
| `lake build Metronome.Strobes` | 0 | 11 s first, 3 s warm |
| `python code/tests/lean/strobes_check.py` (baseline) | 0 | 32 s |
| `python code/tests/lean/strobes_check.py --mutations --artifacts-dir data/raw/lean_strobes_v4_20261121` | 0 | **381 s** |
| `python code/tests/lean/coverage_check.py --artifacts-dir data/raw/lean_coverage_v4_20261121b` | 0 | 106 s |
| `git diff --quiet HEAD -- src` | 0 | - |

Per case the Lean cost is about 10 s (`opg` on a small mutant) to 60 s; the
baseline's three files are 112 KB + 21 KB + 15 KB, and the `opg` file's 36
`bv_decide` goals are the bulk.  Yosys elaboration is ~10 s of each case.

### Claims

#### The strobe rule

| Claim | Theorem | Conditions |
|---|---|---|
| The group mask `hitsMask` is at most one-hot. | `Strobes.hitsMask_atMostOne` | `bv_decide` over `(en, grp, G)` (41 bits). |
| For any one-hot-or-zero mask, "some set hit has destination `D`" is "the pick's `we` is set and its destination is `D`". | `Strobes.dsteqMask_pick` | `atMostOne hit`; `bv_decide` over 96 bits. |
| **`OPG(G, D)` is the winner's `we && dst == D`.** | `Strobes.opg_eq_pick` (“the strobe rule”) | Unconditional; `hitsMask_atMostOne` discharged. |
| A strobe implies the group has a winner, and gives its destination. | `Strobes.opg_imp_we`, `Strobes.opg_imp_dst` | |
| Two distinct destinations of one group never fire together. | `Strobes.opg_exclusive` | `D1 ≠ D2`; used for the counter `LO`/`HI` and the LFSR ports. |
| A one-hot mask is zero or one-hot, so `OneHotOrZero` holds. | `Strobes.atMostOne_cases`, `Strobes.atMostOne_oneHotOrZero` | |
| **The Units cut's accumulator premise.** | `Strobes.accHit_oneHotOrZero` | `HITG(DG_ACC)` is zero or one-hot from the priority mask. |

#### The unit selectors

| Claim | Theorem | Conditions |
|---|---|---|
| The counter map is `LO` = 0, `HI` = 1, `DEC` = 2; `LO` and `HI` are exclusive. | `Strobes.counterSel_lo/hi/dec`, `Strobes.counterSel_of_opg`, `Strobes.counter_ops_exclusive` | Reuses `Units.Counter.selOf`. |
| The LFSR map is `ST` = 0, `B0..B3` = 1..4; any two ports are exclusive. | `Strobes.lfsrSel_st/b0/b1/b2/none`, `Strobes.lfsrSel_of_opg`, `Strobes.lfsr_ops_exclusive` | Reuses `Units.Lfsr.selOf`. |
| The shifter map is `LD` = 0, `SH` = 1 (the RTL's `sel` is the `SH` strobe). | `Strobes.shifterSel_ld/sh` | |
| The pointer map is `AL` = 0, `AH` = 1, `W` = 2, `R` (and any other code, including no winner) = 3. | `Strobes.p0Sel_al/ah/w/r` | |
| The line symbol map is `SYM` = 0, `DBIT` = 1, `XOR` = 2 (the RTL `default:`). | `Strobes.lineSop_sym/dbit/xor` | |
| The accumulator op codes are `ACC.LD..CMP` = 7..13 → 0..6, else CMP. | `Strobes.accSel_eq` | Reuses `Units.Acc.opCodeOf`. |
| The packed word's destination and data fields round-trip, so the strobe statements can be phrased on the pick. | `Strobes.pack_dst`, `Strobes.pack_data`, `Strobes.pack_data_0/1` | `bv_decide` over `{we, dst, data}`. |

#### The extracted cones (one theorem per strobe/selector)

| Extracted net | Theorem | Spec |
|---|---|---|
| `g_cn[k].op_lo`, `.op_hi` (k = 0..2) | `rtlOpgCnt{k}Lo_spec`, `rtlOpgCnt{k}Hi_spec` | `opg en grp dst dgCnt{k} dCnt{k}Lo/Hi` |
| `g_lf[k].op_st`, `.op_b0..b2` (k = 0..1) | `rtlOpgLf{k}St_spec`, `rtlOpgLf{k}B{0,1,2}_spec` | `opg … dgLf{k} dLf{k}St/B0/B1/B2` |
| shifter `sel` (k = 0..1) | `rtlOpgSh{k}Sh_spec`, `rtlSelSh{k}_spec` | `opg … dgSh{k} dSh{k}Sh`, then `shifterSel` |
| stream `mctl`, `adv`, `rx_we` (k = 0..1) | `rtlOpgS{k}Ctl/Adv/Rx_spec` | `opg … dgS{k} dS{k}Ctl/Adv/Rx` |
| `acc_hit` | `rtlAccHit_spec`, `rtlAccHit_oneHotOrZero` | `hitsMask en grp dgAcc`; `Units.Acc.OneHotOrZero` |
| counter `sel` (k = 0..2) | `rtlSelCn{k}_spec`, `rtlSelCn{k}_opg` | `counterSel` of the two strobes |
| LFSR `sel` (k = 0..1) | `rtlSelLf{k}_spec`, `rtlSelLf{k}_opg` | `lfsrSel` of the four strobes |
| `p_sel` | `rtlPSel_spec`, `rtlPSel_word` | `p0Sel (slice w 8 6)`, and `p0Sel` of the pick's destination |
| `g_ln[k].sop` (k = 0..3) | `rtlLineSop{k}_spec`, `rtlLineSop{k}_word` | `lineSop (slice ws 8 6)`, and of the `L.SYM` pick word |
| `acc_sel6[3m +: 3]` (m = 0..5) | `rtlAccSel{m}_spec` | `accSel cDst m` = `Units.Acc.opCodeOf` of the slot's code |
| stream `rewind`, `flush`, `clr_starved` (k = 0..1) | `rtlRewindS{k}_spec/_word`, `rtlFlushS{k}_spec/_word`, `rtlClrS{k}_spec` | `streamCtlOf` of the move and host bits |
| stream `cap_en` (k = 0..1) | `rtlCapEnS{k}_spec` | `capEn cen replay = cen && !replay` |
| `cw_dbg_off` | `rtlCwDbgOff_spec` | zero-extended `cw_pending_addr - HA_DBG_BASE` |
| `d_wr_ectl/em0/em1/rlv0/rlv1` | `rtlDbg{Ectl,Em0,Em1,Rlv0,Rlv1}_spec` | host DBG write OR core drain at the byte offset |

All 80 theorems are stated over symbolic inputs; the `_word` variants compose
with `Metronome.Moves`' `pickWord` (and therefore, by rewriting, with its
generated `rtlWord*_spec`/`rtlSymWord*_spec` theorems), and
`rtlAccHit_oneHotOrZero` is stated exactly as the `OneHotOrZero input.hit`
premise of `Metronome.Units.Acc.rtlStep_eq_step`.

### Premises and free leaves

Each the generated theorem's arguments is a free per-cycle leaf; the claim is
"given these SPEC quantities, the extracted cone is the SPEC quantity".

| Leaf | Width | Used by | Provenance |
|---|---|---:|---|
| `mv_en` | 6 | every `OPG` and `acc_hit` cone | core pipeline (dispatch, guards, `md2_core` freeze gate): `Metronome.Core` / not in a Lean module |
| `grp_v` | 30 | every `OPG` and `acc_hit` cone | `DG_MAP` lookup: `Metronome.Moves.rtlGrpV_spec` (`moves_check.py`) |
| `c_dst` | 36 | every `OPG`, `acc_hit`, `acc_sel6` cone | the six moves' destinations: `Metronome.Core` |
| `c_dat` | 48 | none of these cones (the strobes read only destinations); listed for the `opg` spec | `Metronome.Core` |
| `w_p0` | 15 | `p_sel` | `PICKG(DG_P0)`: `Moves.rtlWordP0_spec` |
| `g_ln[k].ws` | 15 | `sop[k]` | the line's `L.SYM` pick: `Moves.rtlSymWord{k}_spec` |
| `g_s[k].w`, `g_s[k].mctl` | 15, 1 | stream `rewind`/`flush` | `PICKG(DG_Sk)` (`Moves.rtlWordS{k}_spec`) and this cut's `rtlOpgS{k}Ctl` |
| `w_srt` | 1 | stream control | host map (`in_srt`): `HostMap`, `hostmap_check.py` |
| `a_srt` | 16 | stream host decode | `a_srt = ha - HA_SRT_BASE`: host map |
| `h_wd` | 8 | stream control (host `SRT.CTL` bits 0/1/7) | host command machine (`HostCmd`) |
| `cen` | 1 | `cap_en` | `DBG.ECTL.CEN` register: `Metronome.Debug` (`Ctrl`) |
| `replay` | 1 | `cap_en` | `DBG.ECTL.RPL`: `Metronome.Debug` |
| `w_dbg`, `a_dbg` | 1, 16 | DBG strobes | host map (`in_dbg`) |
| `cw_drain`, `cw_pending_addr` | 1, 16 | DBG strobes | core queue: `Metronome.CoreQueue` (`cw_drain`, `cw_pending_addr`) |

Three modelling notes:

* **`o_srt` and `o_dbg` are `{16'd0, a_*}`.**  Those nets carry constant zero
  high bits, so the cut binds `a_srt`/`a_dbg` (16 bits) and reads the RTL's own
  zero extension through the cone.  The comparison is then the 32-bit one the
  RTL performs, not an over-approximated free 32-bit bus.
* **`g_s[k].mctl` is bound free in the stream-control cone** although this cut
  proves it: the theorem is universally quantified over it, and substituting
  `rtlOpgS{k}Ctl` is a rewrite.  The same is true of `g_s[k].w`, whose
  `_word` theorems substitute `pickWord`.
* **`h_wd` appears only in the stream-control cones**; the DBG strobes do not
  read the write data (the byte-split host/core data mux is `Metronome.Debug`'s).

### Mutations (temporary copies of `src/`, never the repository)

`python strobes_check.py --mutations` plants eight regressions on temporary
copies of `src/`; all eight are rejected by the generated Lean (no structural
rejection among them):

| Mutation | Change | Rejected by |
|---|---|---|
| `strobes_counter_swap` | `op_lo` tests `D_CNT*_HI` and `op_hi` tests `D_CNT*_LO` | `rtlOpgCnt0Lo_spec` / `rtlOpgCnt0Hi_spec` (concrete counterexample) |
| `strobes_lfsr_b1` | `op_b1` uses `D_LF*_B2`'s code | `rtlOpgLf0B1_spec` |
| `strobes_shifter_ld` | `D_SHSH` uses the `LD` destination codes, so the shifter `SH` strobe tests `LD` | `rtlOpgSh0Sh_spec` / `rtlOpgSh1Sh_spec` |
| `strobes_p0_swap` | `p_sel` maps `AH` → 1 and `W` → 2 the other way round | `rtlPSel_spec` (`sel` file) |
| `strobes_rewind_no_host` | `rewind = mctl & w[0]` (the host `SRT.CTL` bit is dropped) | `rtlRewindS0_spec` / `rtlRewindS1_spec` |
| `strobes_sop_dbit` | the line `sop` maps `DBIT` to `XOR` and the default to `DBIT` | `rtlLineSop0_spec` … `rtlLineSop3_spec` |
| `strobes_dbg_em1` | `d_wr_em1`'s core-drain term compares with `HO_DBG_EMASK` (byte 0) | `rtlDbgEm1_spec` |
| `strobes_acc_highest` | `acc_hit = hits(mv_en, reversed grp_v, DG_ACC)`, so with two ACC contenders the highest `(core, move index)` wins | `rtlAccHit_spec` (and its `OneHotOrZero` corollary would be false) |

Measured outcomes are in `run_status.txt`; each rejected case records its own
Lean exit code 1 and `expectation ok`.  A rejected case's `axioms.txt` contains
`sorryAx` (Lean's error recovery); the accepted baseline's does not, and
`strobes_check.py` fails any accepted case whose audit mentions it.

### Trust added

* Yosys elaboration (`read_verilog -I src …; hierarchy -check; proc; opt_clean;
  write_json`), the shared RTLIL adapter (`rtlil.DffCone`) and
  `corectl_check.VectorCone`, and the generated Lean: the same trust base as the
  rest of the suite.  No new cell shape was needed for these cones, with one
  exception: the six accumulator op-code slices reuse
  `units_check.extract_acc_sel` (its `UnitCone` already decodes the `$pmux`
  `case`).
* The extraction checks, before any proof runs:
  * every `OPG` cone's six group comparators are one and the same documented
    `DG_*` constant (via `moves_check.word_groups`), so a per-slot group, a
    non-constant operand or an undocumented code fails;
  * `p_sel`'s destination comparators are exactly `D_P0_AL/AH/W`;
  * each line `sop`'s comparators are exactly `D_L_SYM`/`D_L_DBIT`;
  * `cw_dbg_off` is a 32-bit `$sub` of the zero-extended `cw_pending_addr` and
    the constant `HA_DBG_BASE`;
  * the header constants are the documented ones (`DG_*`, `D_*`, `HSPAN_SRT = 8`,
    `HS_SRT = 4`, `HO_SRT_CTL = 2`, `HA_DBG_BASE = 0x2460`, DBG offsets 2/8/18).
* The destination constants of the `OPG` strobes are deliberately **not**
  checked structurally: the Lean equality compares the cone against the module's
  hand-written constant, so a drifted destination is a counterexample rather
  than a redefinition of the specification.
* `bv_decide` adds per-theorem native LRAT certificate axioms
  (`rtlOpgCnt0Lo_spec._native.bv_decide.ax_1_8`, …; `pack_data` and the
  `atMostOne` lemmas also carry one).  `#print axioms` is recorded per theorem
  in `<case>.axioms.txt`, and the runner rejects `sorryAx`.  The certificate
  checker is the only trust added beyond Yosys, the adapter and the header
  reader.

### Coverage effect (read-only re-run)

`python code/tests/lean/coverage_check.py --artifacts-dir
data/raw/lean_coverage_v4_20261121b` exits 0 and still reports the inventory of
the *other* 20 cuts (coverage_check imports a fixed checker list, so it does not
see this cut): 90.74 %, 830 uncovered cells, 35 UNCLOSED leaves.  That is
expected; the numbers below come from this cut's own extraction, elaborated with
the same recipe (`-D USE_IHP_SRAM`) and walked with the same driver index, and
are recorded with the exact 830 cell names in
`data/raw/lean_strobes_v4_20261121/coverage_effect.txt`.

* **All 830 uncovered cells are read by this cut's cones** (the cut reads 904
  cells in total; 74 of them were already covered by other cuts).
  Breakdown: `project.v:281` 138 `$and` + 138 `$eq`; `:283` 115 `$and` + 115
  `$logic_not` + 92 `$reduce_or`; `:307` 132 `$eq`; `:396` 2 + 2; `:409` 3 + 3;
  `:410` 3 + 3; `:425` 2 + 2; `:426` 2 + 2; `:427` 2 + 2; `:428` 2 + 2;
  `:456` 2 + 2; `:463` 2 `$and` + 2 `$not`; `:470` 2 + 2; `:471` 2 + 2;
  `:472` 8 `$and` + 4 `$or`; `:473` 2 `$and`; `:485` 2 `$eq` + 2 `$mux`;
  `:486` 1 `$eq` + 1 `$mux`; `:514` 8 `$eq` + 8 `$mux`; `:660` 1 `$sub`;
  `:666`–`:670` 5 × (1 `$and` + 1 `$eq` + 1 `$or`).
* **All 35 UNCLOSED leaves are roots of this cut**: `md2_mem.p_sel` (1 leaf,
  2 bits); `md2_shifter.sel` (2 instances); `md2_acc.hit` (1 leaf, 6 bits); the
  six counter `op_lo`/`op_hi`; the eight LFSR `op_st`/`op_b0..b2`; the four line
  `sym_op` (8 bits); the twelve stream `cap_en`/`adv`/`rx_we`/`rewind`/`flush`/
  `clr_starved`; and the five debug `d_wr_*` strobes = 35 leaves / 49 bits.
  The orchestrator can add
  `("strobes", strobes_check, strobes_check.check_strobes)` to the inventory's
  checker list to have those cells and leaves credited; the evidence above is
  the count.

### SPEC ambiguities and RTL/SPEC differences (reported, not fixed)

1. **`p_sel` ignores the word's `we` bit.**  `p_sel` decodes `w_p0[13:8]` and
   has no `w_p0[14]` term; with no `P0` winner the word is zero, so `p_sel` is
   the `R` fallback.  That is harmless because `p_we = w_p0[14] = 0` in the
   same cycle, and it is what `md2_mem` expects.  The specification states the
   map on the word's destination (any code outside `AL/AH/W` is `R`), which
   covers the no-winner case.
2. **The line `sop` ignores `ws[14]` (`sym_we`).**  With no `L.SYM` move the
   word is zero and `sop` is the `XOR` default; `md2_line` ignores `sym_op`
   while `sym_we = 0`.  The line cut already documents that the RTL `case`
   default makes an impossible `3` behave like `XOR`; here any destination other
   than `SYM`/`DBIT` is `XOR` (`2`), which is §3.6's default reading.
3. **Stream `CTL` bits from the move.**  `rewind`/`flush` use the *winning
   word's* data bits 0/1 (`PICKG(DG_Sk)`), not the destination code; the
   destination only gates the move (`mctl`).  The host side uses `SRT.CTL` bits
   0/1 and bit 7 for `clr_starved`; §6.3's "requests from both in one cycle
   combine" is the OR the RTL builds, and the specification states exactly that
   OR.
4. **`cap_en = CEN && !RPL`.**  §12.4 defines `cev` from `CEN`, and §13.2 gives
   `RPL` priority; the RTL's capture-enable input also drops `RPL`.  The cut
   proves the gate; `cev`, `FRZ`, `EMASK` and the edge vectors are the debug
   cut's.
5. **DBG strobe merge.**  `d_wr_ectl/em0/em1/rlv0/rlv1` are the OR of the host
   write and a core drain at that byte.  A simultaneous host write and core
   drain to *different* bytes of the same register both take effect; to the
   *same* byte the strobe is one and the converged write-data mux prefers the
   host (`Metronome.Debug`'s byte-split).  The specification claims only the
   strobe, not whole-register supersession.
6. **`HO_DBG_EMASK + 1`, `HO_DBG_RLV + 1`.**  The RTL writes the second byte of
   the two-byte `EMASK`/`RLV` registers with an `offset + 1` comparison; the
   cut proves the offsets are 8/9 and 18/19 and that the five byte strobes are
   distinct.
7. **`HSPAN_SRT = 8`, `HS_SRT = 4`.**  The stream register window spans two
   four-byte slots (`SRT_SH = 2`), so the host decode's stream index is
   `a_srt >>> 2` and the byte offset is `a_srt & 3`.  `hostCtl` states that
   arithmetic.  `w_srt` still carries the window test, which is the host map's.
8. **`DG_*` / `D_*` constants.**  The module transcribes the codes by hand from
   the generated headers; a header change fails the structural check (groups,
   `p_sel`/`sop` comparators, DBG base/offsets) or the Lean equality
   (destinations), so it cannot silently redefine the specification.

### Gaps

* **`mv_en` provenance.**  The dispatch, guards and `md2_core` freeze gate that
  produce `mv_en` are not in this cut, and `mv_en` provenance is not a Lean
  module theorem; "some move is enabled" is not tied to a thread's PC here.  The
  move bus is exactly the input of `Metronome.Moves`.
* **`DG_MAP`.**  `grp_v` is free; `Moves.rtlGrpV_spec` proves the lookup is the
  `machine.json` table.  The strobe is stated against that `grp_v`, so a map
  change is that cut's business.
* **Host decode.**  `w_srt`, `w_dbg`, `a_srt`, `a_dbg` are free; the SRT/DBG
  window tests and the host SPI framing are the host-map/host cuts'.
* **Register state.**  `cen`, `replay`, `cw_drain`, `cw_pending_*` are free
  per-cycle values; their next states are `Metronome.Debug` and
  `Metronome.CoreQueue`.  Composing the two cuts is a rewrite, as in the rest of
  the suite.
* **Word/pick composition.**  `rtlPSel_word`, `rtlRewindS*_word`,
  `rtlFlushS*_word` and `rtlLineSop*_word` substitute `pickWord` (and
  `hitOr`/`symMask`); rewriting them with `Moves.rtlWord*_spec` /
  `Moves.rtlSymWord*_spec` is a one-line rewrite that is documented rather than
  written as a Lean theorem, because those theorems live in the generated Moves
  file, not in a module.
* **`acc_sel6` duplication.**  `units_check.py` already proves the same per-slot
  op-code map from `c_dst`; this cut re-extracts it so the accumulator's whole
  control path is stated in one place.  It covers no new cell.
* **Physical timing.**  The 60 MHz closure, setup/hold, the `hits`/`pick` logic
  depth (the reason for the priority-mask restructure noted in `project.v`) and
  the latch/RAM timing are out of scope, as in every cut.

`verify.py` runs this cut once on the baseline and, with `--mutations`, on its
own mutants (evidence in `<artifacts-dir>/strobes/`).

## Extend the framework

Use [Transition.lean](Metronome/Transition.lean) for state traces and
induction. Keep each block's contract in a Lean module written from its
specification. Add a cut adapter for its elaborated RTL, prove one-step
equality, and test a mutation that changes a covered result. Prove the
assumptions when composing the cuts. For the configuration path, the host
strobe cut connects the chip-top filter to `Config.SpacedHost`, the address
decode cut covers both live-decode leaves and the bank mask, and the queue cut
covers the core-side counter, entry and overflow flag and composes its request
with the arbiter grant. The remaining connections are the SPI pin timing and
byte framing, the freeze register's own next state, payload content, and latch
visibility and physical timing.
