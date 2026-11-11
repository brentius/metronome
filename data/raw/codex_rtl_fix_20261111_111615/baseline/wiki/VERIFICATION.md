# Verification

How we know Metronome does what its spec says, and how strongly each claim is supported. Every number on this page carries its evidence class: *verified against the reference model* (lockstep), *RTL-simulated*, *formally proven*, *synthesized / precheck-passed*, *calculated*, *estimated*. Nothing here is measured on silicon or on an FPGA yet.

## 1. The independence structure

A testbench is only as good as the thing it is compared against. The project keeps four artifacts written separately from the same normative text, so a misreading has to be made identically twice to slip through:

| Artifact | Written from | Location |
|---|---|---|
| Machine description (sizes, encodings, port and register maps) | the architecture | `code/md/machine.py`, generated into `code/rtl/gen/md_defs.vh`, `code/md/machine.json`, `wiki/ISA_TABLES.md` |
| Normative cycle-level spec | the architecture plus the machine description | `wiki/SPEC.md` (edge cases in section 9a) |
| Reference model (Python, cycle-accurate behind the pins) | SPEC only | `sim/reference/metronome/` |
| RTL | SPEC only | `code/rtl/` |
| Protocol checkers (UART, SPI, I2C, 10BASE-T) | the protocol standards, not the chip | `code/tests/checkers/protocols.py` |
| Toolchain (assembler, checker, image/SPI frames) | SPEC and the machine description | `code/host/` |

The model and the RTL were written by different agents in parallel. Whenever they disagreed, the fix went into SPEC first (decisions D11, D12) and then into both implementations, never into just one side to make a test pass.

## 2. Lockstep: RTL against the reference model, every pin, every cycle

`code/tests/lockstep/` drives the RTL (Icarus Verilog via cocotb) and the model with identical per-cycle pin stimulus and compares `uo_out`, `uio_out` and `uio_oe` on every clock. Programs and configuration are loaded through the real host SPI pins, using an SPI encoder in the test that is independent of the model's own helpers, so the host link is always under test. With `LOCKSTEP_PROBE=1` the harness also compares architectural registers each cycle (beat-generator phase and flags, engine PC/READY/RUNNING/ARMED/symbols/sticky flags, accumulator, flags, counters, shifters, LFSRs) and reports the first divergence, which takes debugging from tens of thousands of cycles down to one.

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

Vacuity is guarded in two ways:
- **Cover tasks.** Every proof has a cover task that shows the events it talks about are reachable.
- **Mutations.** Nine deliberate RTL mutations were made: wrong wrap compare, tap boundary, reversed priority, dropped hazard guard and others. The proofs rejected all nine, three of them only as induction failures rather than concrete traces.

Not covered: SPI byte framing, watcher dispatch (it moved into the core during the area pass), the cross-cycle claim that each tap fires once per beat, and liveness.

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

## 5. Physical

| Check | Result | Class |
|---|---|---|
| TT template, 8x4 tiles, ihp-sg13cmos5l, LibreLane 3.1.0.dev4 (flow smoke test) | harden passed | synthesized |
| Full design with 3 IHP SRAM macros | pending | |
| Precheck (tt-support-tools 9d13ff3e) | pending | |

## 6. What is not verified

- Silicon, an FPGA prototype and the RP2350 demo board.
- Timing closure at 60 MHz until STA results are recorded above. An RTL-simulated pass says nothing about timing.
- The IHP SRAM macros' power scheme, which upstream describes as not silicon-proven.
