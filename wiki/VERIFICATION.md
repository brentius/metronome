# Verification

How we know Metronome does what its spec says, and how strongly each claim is supported. Every number on this page carries its evidence class: *verified against the reference model* (lockstep), *RTL-simulated*, *formally proven*, *synthesized / precheck-passed*, *calculated*, *estimated*. Nothing here is measured on silicon or on an FPGA yet.

The v2.0 template baseline moves the v1 RTL to `src/` and renames its top level to `tt_um_brentius_metronome`. The template smoke test assembles `blink.mas`, loads it through the host SPI pins, and checks O8 transitions every 60 clocks using the IHP SRAM behavioral models. Local port evidence is in `data/raw/template_port_20261111T2055/`; official Actions results must be checked separately before claiming that this port is hardened. The root SRAM PDN plugin, `odb_stripes.py`, and `src/pdn_cfg.tcl` are unchanged copies of the files documented in `code/flow/tt_project/vendor/PROVENANCE.md`. The simulation-only SRAM model provenance is in `test/sram_model/README.md`.

## 1. The independence structure

A testbench is only as good as the thing it is compared against. The project keeps four artifacts written separately from the same normative text, so a misreading has to be made identically twice to slip through:

| Artifact | Written from | Location |
|---|---|---|
| Machine description (sizes, encodings, port and register maps) | the architecture | `code/md/machine.py`, generated into `src/md_defs.vh`, `code/md/machine.json`, `wiki/ISA_TABLES.md` |
| Normative cycle-level spec | the architecture plus the machine description | `wiki/SPEC.md` (edge cases in section 9a) |
| Reference model (Python, cycle-accurate behind the pins) | SPEC only | `sim/reference/metronome/` |
| RTL | SPEC only | `src/` |
| Protocol checkers (UART, SPI, I2C, 10BASE-T) | the protocol standards, not the chip | `code/tests/checkers/protocols.py` |
| Toolchain (assembler, checker, image/SPI frames) | SPEC and the machine description | `code/host/` |

The model and the RTL were written by different agents in parallel. Whenever they disagreed, the fix went into SPEC first (decisions D11, D12) and then into both implementations, never into just one side to make a test pass.

## 2. Lockstep: RTL against the reference model, every pin, every cycle

`code/tests/lockstep/` drives the RTL (Icarus Verilog via cocotb) and the model with identical per-cycle pin stimulus and compares `uo_out`, `uio_out` and `uio_oe` on every clock. Programs and configuration are loaded through the real host SPI pins, using an SPI encoder in the test that is independent of the model's own helpers, so the host link is always under test. With `LOCKSTEP_PROBE=1` the harness also compares architectural registers each cycle (beat-generator phase and flags, engine PC/READY/RUNNING/ARMED/symbols/sticky flags, accumulator, flags, counters, shifters, LFSRs, and each core's XV/XE/XPC/RR). A mismatch or unavailable/unresolved required probe now fails immediately. Handles are cached for the run. Probes require RTL hierarchy and should be disabled for flattened gate-level netlists. Earlier probe-enabled results below used diagnostic logging only; their pass/fail assertions checked pins.

D17 regressions (`test_round_robin_fairness_core0/core1`) load two recurring ALWAYS engines and a third doorbell engine over SPI. They failed under the old fixed priority and pass under round-robin within the checker's seven-cycle response bound. `test_probe_validation.py` verifies that deliberately mismatched, unavailable, missing-hierarchy and unresolved-value probes produce failing cocotb results with the expected diagnostic.

Scenarios:
- **smoke**: reset, then read the ID register.
- **regs**: register write and read-back.
- **blink**: engine toggling an output cell every beat.
- **random_N**: random configuration of all 4 beat generators, 6 engines and 14 output cells. Random 24-word programs on both cores, with any source, destination, guard, condition and jump mode, including unused encodings. Random pin stimulus for 3000 run cycles, then read-back of engine, sticky and phase state. About 112k cycles each.

| Run | Result | Class |
|---|---|---|
| smoke, regs, blink, random_1..6 (laptop, Icarus 13, behavioural memories, pre-area-pass RTL) | 9/9 identical on all pins, every cycle | RTL-simulated, verified against the reference model |
| smoke, regs, blink, proto_uart_tx/rx, proto_spi_controller, proto_eth_tx, random_1..6 (after the area pass, D14/D15) | 13/13 identical, 18.7 min | RTL-simulated, verified against the reference model |
| smoke, regs, blink, random_1..3 with the PDK's SRAM behavioural models (`USE_IHP_SRAM`, pod, pre-area-pass RTL) | 6/6 identical | RTL-simulated; verifies the SRAM wrappers |
| smoke, regs, blink, UART TX/RX, SPI controller, Ethernet TX, random_1..3 after D17 | 10/10 identical on pins and required internal probes | RTL-simulated, verified against the reference model; `data/raw/codex_rtl_fix_20261111_111615/` |
| smoke and random_1 after D17 with local IHP SRAM models and strict probes | 2/2 identical | RTL-simulated; SRAM wrapper/model integration |
| D17 AREA0 synthesized netlist, IHP standard-cell and SRAM models, smoke/random_1 | 2/2 identical, 54.43 s | zero-delay gate-level simulation, verified against the reference model on all pins; flattened internal probes disabled; `data/raw/physical_resume_20261111_120036/mapped_gl_pytest.log` |
| gate-level netlist after place and route | pending | |

The first random run was not clean: engine 0 failed to accept a `BG1.TAP2` trigger that the model accepted, during configuration. The probe pinned it to cycle 62668, and the RTL owner's next revision fixed it. The stale-landing bug (D12) was found by the RTL author while reading the spec against the pointer pipeline.

## 3. Formal unit contracts

Each unit's port behaviour is written as properties that cite SPEC clauses (`code/tests/formal/`). The properties are bound into the unmodified RTL with the yosys-slang plugin and proven with SymbiYosys (smtbmc + bitwuzla). Run them with `python -m pytest code/tests/formal -v`, which takes about 50 s.

| Unit | SPEC | Properties | Result |
|---|---|---|---|
| beat generator | 3, 9a.6, 9a.10 | 25 | formally proven, k-induction depth 3 |
| write group (3 parameterisations) | 6 | 5 each | formally proven (combinational, complete) |
| move bus, against an independent group-ID function written from the SPEC 6 list | 6 | 26 | formally proven (combinational) |
| pointers and arbiter, including the 9a.3 stale-landing rule | 6.1, 9a.2-9a.4 | 36 | formally proven, k-induction depth 6; RAM abstracted, so control only |
| engine | 4, 9a.1 | 20 | formally proven, k-induction depth 4 |
| LFSR / CRC | 6.1 | 8 | formally proven, k-induction depth 3 |
| accumulator flags | 6.1, 9a.7 | 8 | formally proven, k-induction depth 3 |
| round-robin core dispatch | 5, D17 | circular selection, cursor reset/hold/advance, at most five peer dispatches before a continuously eligible engine | formally proven, k-induction (configured depth 9); covers reached within depth 18 |

Vacuity is guarded in two ways:
- **Cover tasks.** Every proof has a cover task that shows the events it talks about are reachable.
- **Mutations.** Nine deliberate RTL mutations were made: wrong wrap compare, tap boundary, reversed priority, dropped hazard guard and others. The proofs rejected all nine, three of them only as induction failures rather than concrete traces.

Not covered formally: SPI byte framing, watcher dispatch (it moved into the core during the area pass), the cross-cycle claim that each tap fires once per beat, and clock-time liveness without software obligations. The core proof bounds overtaking in dispatches; finite burst lengths and stable RUN/configuration are needed to convert this into the checker's clock bound.

## 4. Protocols, end to end

Example programs (`code/host/examples/*.mas`) go through the full path:
1. The real assembler builds them.
2. They are loaded into the chip through pin-level SPI frames.
3. They run.
4. The protocol pins are decoded by the independent checkers.

The model tests are in `code/tests/protocols/` (11 tests). The RTL runs as `proto_*` lockstep scenarios: the RTL must match the model on every cycle, and the checker also decodes the RTL pins.

| Program | What was checked | Model (verified against reference model) | RTL (lockstep) |
|---|---|---|---|
| `uart_tx` 115200 8N1 | 5 bytes via HOSTIN with HOSTSTAT polling | bytes correct; mean bit 520.778 clk (ideal 520.833); edge error -0.83..+0.50 clk; back-to-back frames | 3 bytes, pass |
| `uart_rx` 115200 8N1 | 0%, +2%, -2% baud error; corrupt stop bit | 4 good bytes; bad frame dropped and flagged | pass |
| `spi_controller` mode 0, 1 MHz | MOSI out, MISO in, against `spi_decode` | 0xA5 0x3C 0xFF out, 0x5A 0xC3 0x81 in | 3 bytes, pass |
| `eth_tx` 10BASE-T | preamble/SFD generated on chip, **FCS computed on chip** (LFSR, reflected CRC-32), Manchester through the output-cell LUT | 15, 60 and 114 byte bodies plus a back-to-back pair decoded bit-exact by `eth_decode`; FCS matches `zlib.crc32`; every edge on the 3-clock half-bit grid (0 jitter); TP_IDL 18 clk | 1 frame, pass (decoded from RTL pins) |

10BASE-T is the tightest case. A burst of n instructions frees its engine at t+n+2 and the next bit's trigger comes at t+6, so each bit gets at most 4 instructions. The bit loops use 3 or 4. The toolchain's static checker reports the worst burst as 4 instructions inside a 6-clock commit window. This bound is *calculated* from SPEC 5 and confirmed in the model.

## 5. Physical (metronome v1.0)

v1.0 is run `metronome_r3_d17__r6_ant_setup`, with artifacts and provenance in `data/raw/metronome_v1.0/`. It was reached in six logged iterations (`BOTS/PLANS/HARDEN_LEDGER.md`):
- **r1, r2:** global-route congestion with only three routing layers.
- **AREA 0 mapping:** cut the mapped area 27%, after which global routing passed.
- **r3, r4:** a VPWR/VGND short, found by Magic/LVS and located with `code/flow/runpod/pwrcheck/pwr_vias.py`. It came from PDN channel-repair straps beside the program SRAMs.
- **r5:** moving the macros fixed the short.
- **r6:** stronger timing repair.

| Check | Result | Class |
|---|---|---|
| TT template smoke harden plus precheck | pass | synthesized, precheck-passed |
| Detailed route | 0 DRC violations | PnR |
| LVS (netgen) | circuits match uniquely | LVS |
| Power grid | all VPWR/VGND shapes connected; worst static IR drop 0.30 mV | estimated (typ, default activity) |
| TT precheck (tt-support-tools 9d13ff3e), including the full KLayout SG13CMOS5L DRC | all checks pass | precheck-passed |
| Gate-level lockstep on the post-route netlist (IHP cell and SRAM models, zero delay) | 11/11 scenarios identical to the reference model (smoke, regs, blink, uart_tx/rx, spi_controller, eth_tx, random_1..4) | RTL-simulated at gate level |
| Setup at 16.667 ns | typ +5.876 ns; fast +9.540 ns; **slow (1.08 V, 125 C) -0.423 ns**, 25 endpoints, about 58.5 MHz worst case | post-route RCX STA; fmax calculated |
| Hold | worst +0.096 ns, 0 violations | post-route RCX STA |
| Antenna | 1 net / 1 pin violation | OpenROAD CheckAntennas |

The slow-corner limit is the program SRAM's slow-corner clock-to-out (about 5.5 ns) followed by the instruction decode in the same cycle. That single-cycle path is what makes the 2-cycle trigger latency possible.

LibreLane's cumulative `final/metrics.json` can keep obsolete pre-PnR values after a checkpoint resume. The flow reporter (`code/flow/runpod/ll_variant.py`, tested in `code/tests/flow`) therefore reads native per-step and per-corner measurements, with their source paths.

## 6. What is not verified

- Silicon, an FPGA prototype and the RP2350 demo board.
- Slow-corner timing closure (v1.0 is -0.42 ns at 1.08 V/125 C) and SDF-annotated gate-level simulation.
- The remaining antenna violation and the max slew/cap violations.
- The IHP SRAM macros' power scheme, which upstream describes as not silicon-proven.
