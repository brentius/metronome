# Evidence acceptance report

## Metronome v4 qualification

The selected build is `v4feature45_20261117_central`, with 45% placement
density and a 6 ns post-global-route setup repair target. The physical inputs
were frozen from `metronome-v4.0` over `e8f669f` for this run.

| Evidence | v4 result |
|---|---|
| Extracted OpenSTA at 16.667 ns | Setup slack +6.467 ns fast, +1.463 ns slow, +5.753 ns typical. Hold slack +0.081 ns fast, +0.486 ns slow, +0.228 ns typical. The D24 multicycle exception covered 2,112 latch data pins in each corner. |
| Physical qualification | Zero reported route DRC, LVS, antenna, slew and capacitance violations. Tiny Tapeout precheck and gate smoke passed. Flow: LibreLane 3.1.0.dev4, Tiny Tapeout tools `9d13ff3e`, IHP CMOS5L PDK `89d42ee6`. |
| Routed simulation | 214 selected cases passed: 29 zero-delay lockstep, 45 three-corner SDF lockstep, 80 compiled Score and 60 protocol cases. The initial Score launch missed a spec fixture. The four passing reruns used the same routed netlist and SDF files. |
| Resident UART demo | The 243+233-word program passed full-chip RTL and zero-delay routed gate lockstep at 24 clocks per bit. The [115200 baud board recipe](../code/host2/transcribe/README.md#resident-uart-demonstration) has cycle-model and independent codec evidence. Hardware measurements are pending. |

The basis is the [frozen physical source archive](../data/raw/v4_feature_checked_20261117/central.tgz)
with SHA-256 `07607e3d1d07897a19e85be86e6fcd39a195347d3762f021e57f83bc6935f69d`.
The hardware sources match the current centralized design after line-ending
normalization and the removal of two unused split-bank constants. The
[physical report](../data/processed/v4/phase1/report.md) links the local
compact archives and the native archive on the retained volume. Consult
the [extracted STA samples](../data/raw/v4_layout_closeout_20261118/sta_samples.json)
and [routed regression audit](../data/raw/v4_layout_closeout_20261118/regression_audit.json)
for the corner details and case counts. SDF coverage omits SRAM timing and
interconnect delays. Icarus leaves timing checks unenforced.

### Lean proof of the v4 configuration write port

| Evidence class | Result on RTL revision `b7b4068` | Boundary |
|---|---|---|
| Theorem proving, Lean 4.35.0 with Yosys 0.70+190 extraction | The arbiter and write stage match the specification at every sampled cycle, for arbitrary two-state payloads. Their Lean trace proves write spacing after reset and host-byte delivery within one cycle. Five HDL mutations failed equivalence and one broken connection failed the top-level wiring check. | The cut runs from the arbiter request ports to the latch-bank inputs. Host delivery assumes spaced strobes and reset remains released through delivery. Yosys elaboration and the RTLIL adapter are trusted. |
| Independent RTL induction and RTL/model evidence | The v4 arbiter induction, its three mutation cases, 23 v4 model checks and the full-chip `v4_config_write` lockstep case passed. | The lockstep run used Icarus 14.0 devel and the IHP SRAM behavioral models. |
| Theorem proving, host write-strobe cone, Lean 4.35.0 with Yosys 0.70+190 extraction | The extracted registered `wr`/`bitc` transition matches SPEC Â§9, a write forces the next bit count to zero, and bit count â‰  7 excludes a write. Adjacent strobes in cycles `n+1`/`n+2` are impossible. The chip-top `cfg_host_now` is exactly `u_host.wr & in_cfg & cfg_address_is_live(ha)`, which discharges `Config.SpacedHost` and applies the configuration service theorem. Two host mutations and one top-filter bypass mutation failed the expected layer; the six earlier configuration mutations were retained. Selected rerun: 23 v4 model checks, `v4_config_write` and `spi_target` lockstep, 25 passed. | The host cut starts at sampled `rst_n`, `sck`, `sck_p` and `cs_n` and ends at the next `wr`/`bitc`; `st` and `is_rd` are free inputs. Composition starts in `Host.resetState` so the arbitrary power-up cycle 0 is covered. SPI pin timing, byte framing, payload content, synchroniser analog behaviour and physical timing are outside the cut. Yosys and the RTLIL adapter are trusted. |
| Theorem proving, host and core configuration address decode, Lean 4.35.0 with Yosys 0.70+190 extraction | For all 16-bit addresses the elaborated host `in_cfg & cfg_address_is_live(ha)` and core `cw_is_cfg` equal "in the 0x2000–0x21df window and the elaborated `u_cfg` mask byte at the offset is non-zero". The kernel checks the maximal 284 non-zero bytes of the 480-byte, 2112-bit mask against the `MASK` parameter; the adapter checks each non-zero byte has a `we1`-enabled gate with an `addr1`-only select and exactly its latch set. Boundary facts: 0x2000 and 0x21d7 live, 0x201d a hole, 0x20d0 partial 0x03, 0x21df indexed but mask-zero, 0x21e0 out, 0x1fff wrapped. The host/core arbiter addresses are checked as `a_cfg[8:0]`/`cw_pending_addr[8:0]`; the offset is proved below 512. Four new mutants (permissive line decode, core address-bit swap, non-live mask byte, core address wiring) failed the decode layer; the nine earlier mutants were retained. | The `bv_decide` theorems (two full-address equalities, interval/flag equivalence, offset bound) use Lean's native LRAT certificate checker, the only trust added beyond Yosys and the RTLIL adapter. The window alignment and span are checked preconditions. The cut covers address decode and implemented mask bits, not payload, latch visibility or physical timing. |

See the [Lean proof runner](../lean/README.md), [captured proof input](../data/raw/lean_v4_20261118/proof/baseline.lean),
[host proof input](../data/raw/lean_host_v4_20261118/proof_final3/baseline.host.lean)
and [regression results](../data/raw/lean_v4_20261118/pytest.xml). The host
run console, manifest and JUnit XML are under
[data/raw/lean_host_v4_20261118](../data/raw/lean_host_v4_20261118/README.md).
The address-decode sources, mutation logs and tool versions are under
[data/raw/lean_decode_v4_20261118](../data/raw/lean_decode_v4_20261118/).

## Earlier qualification and methods

Status: 2026-11-16, branch `metronome-v3.0`, uncommitted tree over `refs/v3-baseline/20261116` (7a8bdb9, itself over
HEAD e8f669f). Owner: Track D. This page never lets one kind of evidence stand in for another: every row names its kind,
the exact files, the revision it ran on, and the assumptions that bound the claim. Rows marked **TBD** or **none** are
not claimed.

**Final campaign update, 2026-11-16 22:07 UTC:** v3 physical run `v3r1_20261116T1655` finished21:38:57UTC with all configured stages passed. See [the v3 report](../data/processed/v3/physical_r1_20261116/report.md) and `data/raw/v3_final_20261116T2205/`: native three-corner STA, KLayout DRC/precheck, LVS, TT GL1/1, GL25/25, SDF39/39, Score80/80, protocols60/60. Both frozen438-file source trees and2488 original pipeline output hashes were revalidated. Software retains one documented HDLC G6 xfail; its strict aggregate is failed, not all-pass. The `hazard` UART-TX BMC task (all delays0..11, without SAFE's delay2 exclusion) passes at depth200 on the final v3 source. Earlier F1/F2 results below describe the pre-fix baseline. No hardware or complete SDF signoff claim is added.

## 1. Evidence kinds (strongest to weakest, and what each does not give)

| Kind | Means | Does not mean |
|---|---|---|
| **proved** | k-induction (unbounded) with SymbiYosys/bitwuzla on a unit, properties written from SPEC, non-vacuity by cover tasks and planted mutants | anything about other units, or the full chip |
| **bounded-proved** | BMC of the full chip RTL to a stated depth, symbolic inputs as stated | behaviour beyond the depth or outside the stated input space |
| **exhaustive on model / RTL** | every encoding in a stated enumerated set, RTL and model compared every cycle | encodings outside the set (the 2^64 word space is sampled, not covered) |
| **lockstep RTL** | RTL and Python reference model compared on every pin every cycle for the listed scenarios | completeness; shared misreadings of SPEC (D32 happened) |
| **model** | cycle-level Python model plus independent decoders written from the standards | anything about the RTL |
| **gate-level** | zero-delay simulation of the routed netlist with the IHP cell models | timing |
| **SDF** | gate-level simulation with typ/slow/fast delay back-annotation | complete timing: SRAM and interconnect not annotated, TIMINGCHECKs not enforced, pins sampled 8 ns after the edge |
| **STA** | OpenROAD post-route setup/hold, three corners | the clock as supplied by the board, or anything functional |
| **synthesized / structural** | Yosys area, structural netlist checks | placement, timing, function |
| **hardware** | **none exists.** No silicon, no FPGA, no RP2350 board measurement | |

Revisions used below: **r4b** = `ce37924` RTL (qualified physical run `metronome-v2-b-r4b_20261113T1143`, archive
`data/raw/r4b_only_20261113T1438/`); **v2 working tree** = `refs/v3-baseline/20261116`; **v3** = `metronome-v3.0` working
tree (Track A bundle, uncommitted). r4b physical evidence does **not** cover the v3 RTL or the external timing edits to
`project.v`, `md2_acc.v`, `md2_lfsr.v` made after r4b.

## 2. Standing assumptions (stated once, referenced as A1..A7)

| # | Assumption | Where it matters |
|---|---|---|
| A1 | **Input synchroniser latency.** A level on a raw input in cycle t is `PIN` in t+2 (two flops, `s1`,`s2`); an edge needs `sp` (t+3). Pad, board and RP2350 skew are not modelled. | every input-reacting claim (UART/SPI/I2C receive, listener, live-pin tables) |
| A2 | **Clock.** Nominal 60 MHz, 16.667 ns; r4b slow-corner STA passes at that period (setup +2.284 ns). Tolerance of the supplied clock (RP2350 PLL/jitter) is not measured; protocol-rate claims scale with the real clock. | all rate claims, STA |
| A3 | **Configuration-write spacing (D24).** No two configuration writes in consecutive cycles; SPI gives >= 128 cycles per byte at SCK = clk/16 by construction (`image.min_write_gap_cycles`). `src/project.sdc` has a 2-cycle multicycle path to the latch D pins valid only under this rule. A write in the two cycles after `rst_q` rises is ignored. The host loader contract (section 4, row L1) enforces the rest in software. | latch write path, loader |
| A4 | **SDF limits.** SRAM and interconnect not annotated, TIMINGCHECKs not enforced in Icarus, pins sampled 8 ns after the edge; supplemental, not signoff. | all SDF rows |
| A5 | **Memory power-up.** Lockstep, gate-level and the ISA sweep zero the SRAM arrays at time 0; silicon powers up unknown. The compiled-program BMC does **not** assume zero (program words are written in full; data RAM and unreached program words are unconstrained). | lockstep, GL, sweep |
| A6 | **Preload equivalence (BMC and sweep only).** The formal/sweep builds replace `md2_cfg_bank` by a constant equal to what the image writes (after `rst_q` release) and `md2_host` by a write sequencer that issues the image's non-configuration writes on the same internal bus; reads/SPI framing are not modelled. Latch write path and SPI framing have their own evidence (rows R4, R5). | rows F1-F3, S1 |
| A7 | **Lockstep stimulus.** Programs and configuration load through the real SPI pins at clk/16 in lockstep and GL rows; peer feedback for protocol benches uses the previous cycle's reference outputs. | lockstep, campaign |

## 3. Claim to evidence table

### 3.1 Function of the v2 machine (r4b / v2 tree)

| ID | Claim | Kind | Files and revision | Assumptions and limits |
|---|---|---|---|---|
| R1 | v2 RTL equals the v2 cycle model on every pin every cycle for 9 directed scenarios (smoke, eth_loopback, follower, hold, taps, units, reset_mid, spi_target, shifter_parallel) and seeded random scenarios | lockstep RTL | `code/tests/lockstep_v2/` ; `data/raw/v2_resume_sol_20261112/` ; r4b numbers in `BOTS/PLANS/STATUS.md` (2026-11-13 handoff: GL 25/25 incl. 16 random seeds) ; v3-tree run `data/raw/v3_rtl_20261116/lockstep_full.log` (18 passed, includes all v2 scenarios unchanged) | A1, A5, A7. Agreement on tested cases only |
| R2 | Seven RTL mutants (start commit, FIRST, bit order, hold, round-robin, write-group order, stale-landing) are detected by lockstep | lockstep RTL (mutation) | `code/tests/lockstep_v2/README.md` section "Mutation checks" | three mutants originally survived until `spi_target` was added |
| R3 | Unit contracts of the **v1** units (beat generator, write groups, move bus, pointers/arbiter, engine, LFSR, accumulator, round-robin core) | proved (k-induction), 9 planted mutants rejected | `code/tests/formal/*.sby`, `wiki/VERIFICATION.md` section 3 | **v1 RTL only** (`src/md_*.v` no longer exist; the v2 units `md2_*` are not covered by these proofs). Do not cite for v2 |
| R4 | Latch write path with back-annotated delays: every latch takes exactly what the host wrote, no setup/hold/width violation | SDF (skeleton run r4) | `BOTS/PLANS/DECISIONS.md` D24 addendum ; `data/raw/v2pnr_skeleton_20261112/` | A3, A4; skeleton netlist, full-v2 SDF rerun is in R6 |
| R5 | Host SPI link framing and register read-back | lockstep RTL | every lockstep scenario loads and reads through the SPI pins | not formally proved (`wiki/VERIFICATION.md` section 3 "Not covered formally") |
| R6 | r4b routed netlist equals the model: GL 1/1 (TT template), full GL 25/25, SDF typ/slow/fast 13/13 each | gate-level, SDF | `BOTS/PLANS/STATUS.md` 2026-11-13 handoff ; `data/raw/r4b_only_20261113T1438/` | A4, A5. Covers r4b RTL only |
| R7 | Compiled protocols on the chip: UART, SPI 0-3, I2C 100/400 kHz, USB-LS, Ethernet 10M, JTAG, SWD, PS/2, CAN, HDLC, diff-Manchester; each independently decoded, corrupted-pin control rejected | RTL, gate-level, SDF (75/75 + 13/13) | `data/processed/v2_protocol_campaign_20261115/report.md` ; raw `data/raw/v2_protocols_20261115T1942/` ; `code/tests/protocol_campaign/` | these are transmit waveform demonstrations for most families (no target/arbiter engines, USB no enumeration, Ethernet no full MAC); A1, A4 |
| R8 | Score compiler output on RTL, routed gates and SDF: 20 distinct cases, 105/105 runs; speed points UART TX 10 Mbaud, RX 3 Mbaud, SPI 8.57 MHz, I2C ctrl 3.75 MHz (stress), Ethernet 10M | RTL, gate-level, SDF; rate points on model | `data/processed/score_speed_20261116/report.md` ; `data/raw/score_speed_20261115T2045/` ; `code/tests/score_rtl/`, `code/tests/score_speed/` | 460/460 software tests; highest tested pass is not a proven maximum; qualified on r4b netlist only |
| R9 | STA r4b at 16.667 ns: setup +5.584 (typ) / +2.284 (slow) / +6.328 (fast) ns; hold +0.279 / +0.588 / +0.100 ns; slew and cap violations 0 | STA | `data/processed/v2_protocol_campaign_20261115/report.md` ; STATUS.md 2026-11-13 and 2026-11-15 handoffs ; `code/flow/runpod/protocol_openroad.py` | A2; r4b netlist, not v3 |
| R10 | r4b: route DRC 0, antenna 0, LVS 0, TT precheck passed 2026-11-13 12:42 UTC | physical (DRC/LVS/precheck) | STATUS.md 2026-11-13 handoff ; `data/raw/r4b_only_20261113T1438/` | r4b only; IR drop estimates are typical-activity estimates |

### 3.2 Verification added in v3 (Track D)

Raw logs and traces are in `data/raw/v3_verif_20261116/`. All ran on the frozen baseline snapshot (v2 RTL plus the
compiler as of 2026-11-16 working tree), Windows 11, OSS CAD Suite 2026-10-22 (Yosys 0.70+190, SymbiYosys with
yosys-slang and bitwuzla, Icarus 14.0 devel), Python 3.12. The harnesses take the source root as a parameter so they
re-run unchanged on the v3 tree.

| ID | Claim | Kind | Files | Assumptions and limits |
|---|---|---|---|---|
| F1 | **Compiled UART transmitter (uart_8n1 sender, tx=O8, 10 Mbaud = 6 clk/bit), full-chip RTL:** for every payload byte p (256 values) and every extra HOSTIN delay d in 0..11 except d = 2: O8 is high until the first low cycle t0; O8(t0+k) equals the reference frame {0, p[0..7] LSB first, 1} at 6 clk per bit for k in 0..59; O8 is high from t0+60; t0 is within 24 cycles of the HOSTIN write; line-0 phase is 1 at t0 (edge on the beat grid). | bounded-proved (BMC) | `code/tests/formal_programs/` (`fv_uart_tx.sv`, `gen_fv.py`, `run_proofs.py`, `rtl_fv/`); results `data/raw/v3_verif_20261116/` | **PASS**, depth 200 (BMC covers steps 0..199), 13 min 31 s on one core (`bmc_uart_tx/p_safe/`; the longest frame ends at about step 190). Non-vacuity: the cover task `fell && off == 62` (a complete frame) is reached at step 174 (`bmc_uart_tx/p_cover/`, depth 175, 7 min 31 s), so the proved depth contains complete frames. A5 stronger (no zero memory), A6, input pins unconstrained (free every cycle), reset released at cycle 3, a single HOSTIN write, d in 0..11 after an 18-cycle settle gap (idle loop period 12) |
| F2 | **The same property without the d != 2 exclusion fails** with a counterexample: the HOSTIN-drop hazard (below). | BMC counterexample | `bmc_uart_tx/p_hazard/`: **FAIL** at step 133 (P4, frame never started), counterexample payload 0x8b, delay 2, as predicted by the model and RTL simulation | the exclusion `d != 2` is the documented hazard, not a proof gap |
| F3 | **Mutation teeth:** four mutants each fail the proof: two compiled from a mutated score (stop bit low, start bit high) and two patches of the compiled host writes (beat MOD 7 instead of 6, output LUT stop symbol low); two score mutants (msb first, data:u7) are rejected statically by the compiler's own E-TIME check at 10 Mbaud and so never reach the chip | BMC counterexamples | `bmc_uart_tx/p_mut_*/`: `stop_bit_low` (score mutant) fails at step 166 (frame check), `start_bit_high` (score mutant) at 124, image `img_mod7` at 122, image `img_stop_low` at 118; each with a concrete payload and delay in its `trace.vcd` | the mutant list is small and chosen by hand |
| F4 | Input-reacting program (UART receive, symbolic byte and start offset) | **not done** | BMC depth would be about 350 steps (3 Mbaud = 20 clk/bit, ten bits, load and settle); step cost observed 3 to 6 s at depth 120 to 140 with six jobs in parallel, so well over the 20-minute bound | recorded as infeasible within the bound; reducing it by shrinking the frame would not be the same program |
| S1 | **Single-instruction sweep, RTL vs model, state compared every cycle** (pins, ACC/R0-3, flags, shifters, counters, LFSRs, pointer, stream positions, thread and line state, mailbox, conflict/hazard): every (guard, source, destination) in each of the 3 move slots (3 x 16,128 = 48,384 words; destination T.STOP excluded and swept separately), all 4 guards x 64 sources x 64 cond values with destination ACC.LD (16,384 words), and T.STOP with 4 guards x 64 sources (256 words, 6 threads per batch) | exhaustive on RTL and model for these sets | `code/tests/isa_sweep/` (`sweep.py`, `skeleton.mas`); counts in `data/raw/v3_verif_20261116/isa_sweep_results.json` | encoding space: 2^64 words, 2^14 per move, so it is **not** exhaustive over the word; cross-slot interaction is sampled only. 0 mismatching rows. A5, A6; one thread, 4 cycles per instruction, state evolves across words |
| S2 | Random sample: 12,000 seeded random 64-bit words (T.STOP replaced), jumps and pause included | sample, RTL vs model | same | **824 of 12,000 words executed** (random jumps loop early), so cross-slot coverage is weak; do not read as 12,000 encodings tested |
| S3 | The sweep has teeth: a planted ACC.SUB carry mutant (`>=` to `>`) is caught (118 mismatching rows in 3 batches) | RTL mutation | `data/raw/v3_verif_20261116/isa_mutant_check.txt` | one mutant only |
| C1 | **CDC:** on the r4b post-route netlist every asynchronous input bit (`ui_in[7:0]`, `uio_in[7:0]`) reaches only a stage-1 flop, whose output feeds only a stage-2 flop, both clocked by `clk`; `rst_n` reaches only reset pins of a two-flop release chain (tie-high D); `ena` unused; 0 exceptions, 32 waivers | structural (netlist) | `code/flow/cdc/cdc_check.py`, `test_cdc_check.py` (5 tests); report `data/raw/v3_verif_20261116/cdc_r4b.txt`/`.json`; netlist from the r4b archive `final/nl/tt_um_brentius_metronome.nl.v` | the 32 waivers are the synchronous-reset ANDs (`raw & rst_q` before stage 1 and `s1 & rst_q` before stage 2) that synthesis built; waived because the other input is a flop output. Structural only: no metastability or timing claim. r4b netlist, not v3 |
| L1 | **Host-loader contract:** the loader reads line CTL, thread STAT and CTRL.RUN before every write and refuses writes that would pass a field through mixed values or race a fetch (rules C1-C8) | model (host software against the cycle model) | `code/host2/metronome2_tools/loader_contract.py`; `code/host2/tests/test_loader_contract.py` (19 pass); host2 suite 86 pass | protects only writes issued through it; no RTL change (double buffering rejected for area); model-side flag is Track A's (SPEC_V2 12.5) |

**Finding F-HOSTIN (fixed by Track C; historical repro preserved):** `data/raw/v3_verif_20261116/hostin_drop_repro.md`. The earlier compiled UART sender's
idle loop samples HOST.INV twice per two beats; a HOSTIN write landing between the samples consumes the byte and sends it
with no start bit. Model and RTL agreed; 1 write phase in12 at10Mbaud. The compiler idle loop now samples once, with phase-sweep coverage. Final v3 BMC passes without F1's exclusion; the historical baseline counterexample remains valid for its original image.

### 3.3 v3 RTL bundle (Track A; SPEC_V2 section 12)

| ID | Claim | Kind | Files | Limits |
|---|---|---|---|---|
| V1 | All v2 lockstep scenarios unchanged plus v3 directed and random3 scenarios: 18 passed | lockstep RTL | `data/raw/v3_rtl_20261116/lockstep_full.log`, `code/tests/lockstep_v2/` | A1, A5, A7; RTL vs model only |
| V2 | Freeze/capture properties on `md2_stream` (CAP=1) and `md2_mem`: k-induction proof and cover, 4 planted mutants rejected (6 tests) | proved (unit level) | `data/raw/v3_rtl_20261116/formal_v3_freeze.log`, `code/tests/formal/test_v3_formal.py`, `fv_v3_freeze.sv`, `v3_freeze.sby` | two units only |
| V3 | v3 mutation checks: 6 of 6 RTL mutants killed after adding a burst case (one survived the first two runs) | lockstep RTL (mutation) | `data/raw/v3_rtl_20261116/mutate_v3_run{1,2,3}_*.log` | survivors recorded, not hidden |
| V4 | v3 adds +12,021 um2 synthesized (292,047.6 vs 280,026.4 baseline), 1,004 to 1,096 flops, 2,084 to 2,112 latches | synthesized estimate | `sim/numerics/v3_area/AREA_V3.md`, `data/raw/v3_rtl_20261116/area_v3.log` | typical library, pre-placement; says nothing about fit or 60 MHz |
| V5 | v3 model and block tests, lint | model, RTL lint | `data/raw/v3_rtl_20261116/model_tests.log`, `rtl_v2.log` | |
| V6 | v3 routed netlist, three-corner setup/hold, full precheck/DRC and LVS; TTGL1, GL25, SDF39, Score80, protocol60 cases pass | gate-level, SDF, STA, physical/precheck | `data/processed/v3/physical_r1_20261116/report.md`; raw `data/raw/v3_final_20261116T2205/`, archive and native states |16.667ns, IHP8x4; A3-A5 and documented SDF limits; software HDLC G6 xfail remains; no silicon result |

### 3.4 Listener, autobaud, library and score tooling (Tracks B and C, plus earlier software)

All rows are model only: the v2 cycle model plus independent decoders, with no RTL, gate-level, STA or hardware run
behind them.

| ID | Claim | Kind | Files | Limits |
|---|---|---|---|---|
| T1 | Listener projection (input-only role) logs per-frame status and timestamps for UART, Ethernet receive and SPI | model | `code/scorec/scorec/listener.py`, `spi_listener.py`; `code/tests/scorec/test_listener.py` | no RTL/GL/STA; one-wire/arbitration-loss scope as documented in the module |
| T2 | Autobaud, plan B (chip measures, host sets the divider) | model | `code/scorec/scorec/autobaud.py`; `code/tests/scorec/test_autobaud.py` | plan A impossible: config is write-only latch state |
| T3 | Protocol library (WS2812, DMX512, Wiegand, HDLC, 1-Wire, SWD, JTAG, MDIO, SPI/I2C targets, pattern generator, logic analyser) with a does / does-not table | model (compiled) or codec level, per row | `wiki/PROTOCOL_LIBRARY.md`, `code/score/lib/`, `code/tests/score_lib/` | each row states which of the two kinds it is; HDLC compiled sender ignores stuffing (gap C2) |
| T4 | Score stress, mutation, duet, sweep, coding and transcription tools | model | `code/tests/scorec/test_{stress,mutation,duet,sweep,coding}.py`, `code/tests/transcribe/` | software evidence |
| T5 | Score language, codec and compiler: 460/460 software tests at 2026-11-16 | model | `data/processed/score_speed_20261116/report.md` | |

### 3.5 Hardware

None. No silicon, FPGA prototype or RP2350 board measurement exists for any row.

## 4. Mapping to the judging criteria

Source of criteria: `AGENTS.md` (the blog page, https://blog.janestreet.com/protocol-emulator-asic-competition/, could not
be re-fetched in this session; the FAQ may change, so re-read it before submission).

| Criterion | Evidence in the repository |
|---|---|
| **Flexibility: reprogrammable for protocols it was not designed for** | one machine, many protocols from a score: campaign R7 (11 families, two custom), library T3, compiler R8, listener/autobaud T1/T2, live-pin tables and debug v3 (SPEC_V2 section 12); no fixed UART/SPI/I2C block exists (`wiki/ARCHITECTURE.md`, `wiki/SPEC_V2.md`). A protocol not in the library is shown by the custom HDLC and diff-Manchester cases and by `code/score/examples/` |
| **Novelty** | beat-grid machine with rational divider, hold/stretch and threads over shared units (`wiki/SPEC_V2.md`); one score projected as controller, target and listener (`wiki/SPEC_V2_SCORE.md`); host-side transcription and stress projections (`code/tests/transcribe`, `test_stress.py`); the execution digest and debug freeze (SPEC_V2 section 12) |
| **Verification approach** | independence structure and lockstep (`wiki/VERIFICATION.md` sections 1-2); unit proofs (v1) and v3 freeze proofs (R3, V2); bounded proof of a compiled program (F1-F3); exhaustive single-instruction sweep (S1); mutation at three levels (R2, V3, F3, S3, `test_mutation.py`); CDC check (C1); loader contract (L1); gate-level and SDF on the routed netlist (R6-R8); STA (R9). This page is the acceptance report that keeps the kinds apart |
| **Write-up quality** | `wiki/` (ARCHITECTURE, SPEC_V2, SPEC_V2_SCORE, TOOLCHAIN_V2, VERIFICATION, PROTOCOL_LIBRARY, this file), the does/does-not table, the findings with repros (`data/raw/v3_verif_20261116/hostin_drop_repro.md`), and decision records `BOTS/PLANS/DECISIONS.md` (local, ignored by git) |
| **Physical constraints (IHP 130 nm, 8x4 tiles, 24 pins, 60 MHz)** | r4b: R9,R10; v3: V6 physical/precheck/STA at16.667ns, unchanged pin map; real board clock remains unmeasured |

## 5. What is not claimed

- Silicon, FPGA or RP2350 behaviour; the 60 MHz clock as delivered by the board.
- Complete silicon timing/functionality from the limited physical, GL, SDF and STA evidence in V6.
- Complete formal verification of the v2 RTL: R3 is v1 units; the v2 units are covered by lockstep, the sweep and the
  compiled-program BMC for named programs only.
- Unknown-memory start-up in lockstep, GL and sweep (A5).
- Receive-side compiled-program proof (F4).
- That every compiled sender is free of the HOSTIN hazard; only UART TX at 10 Mbaud is characterised.
