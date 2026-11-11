# Metronome: a beat-synchronous protocol engine

Entry for Jane Street's [protocol emulator ASIC competition](https://blog.janestreet.com/protocol-emulator-asic-competition/) (Tiny Tapeout, IHP 130 nm CMOS5L, 8x4 tiles, submission deadline 2027-01-18).

**Idea.** Programs run on the wire's own bit clock, not the chip's. Hardware beat generators produce (or recover) a protocol's bit clock; short loop-free bursts of move instructions run between beats; pin reads and writes are tied to beat taps and boundaries, never to instruction count; a burst that misses its deadline raises a sticky flag instead of silently corrupting the waveform. Rationale: [wiki/ARCHITECTURE.md](wiki/ARCHITECTURE.md). Normative definition: [wiki/SPEC.md](wiki/SPEC.md), with tables generated from the machine description in [wiki/ISA_TABLES.md](wiki/ISA_TABLES.md).

## Layout

| Path | Contents |
|---|---|
| `code/md/` | Machine description (`machine.py`, single source of truth), generator (`gen.py`), instruction encoder (`encode.py`) |
| `code/rtl/` | Verilog for `tt_um_metronome`; `code/rtl/gen/` is generated |
| `code/host/` | Assembler, static timing checks, program images, example programs |
| `code/tests/` | RTL tests, lockstep RTL-vs-model harness, independent protocol checkers |
| `code/flow/` | Tiny Tapeout hardening and precheck scripts for the remote flow machine |
| `sim/reference/` | Cycle-level reference model of the chip (the verification oracle) |
| `wiki/` | Architecture, specification, toolchain and verification write-ups |
| `data/raw/`, `data/processed/` | Original tool outputs and derived results |

## Running things

```bash
source code/tools/env.sh                 # local OSS CAD Suite (Icarus, Yosys, sby, Verilator lint)
python code/md/gen.py --check            # generated files match the machine description
python -m pytest sim/reference -q        # reference model
python -m pytest code/tests -q           # checkers, RTL tests, lockstep
python -m pytest code/host -q            # toolchain
```

Hardening runs the official Tiny Tapeout flow (tt-support-tools + LibreLane 3.1.0.dev4, ihp-sg13cmos5l) on a Linux machine; see `code/flow/runpod/` (`setup_flow.sh`, `tt_harden.sh`, `tt_precheck.sh`).

## Status

**metronome v1.0 (2026-11-11), hardened but not submitted.**
- **Implementation:** RTL, cycle-accurate reference model, assembler/toolchain and protocol examples. UART TX/RX, an SPI controller and 10BASE-T Ethernet TX all pass the independent checkers on the model, the RTL and the post-route gate-level netlist.
- **Layout:** IHP SG13CMOS5L, 8x4 tiles, three SRAM macros. DRC 0, LVS clean and the full Tiny Tapeout precheck passes.
- **Timing:** setup slack at 60 MHz is +5.9 ns at the typical corner and -0.42 ns at the slow corner.
- **Remaining gaps:** 1 antenna violation; no silicon or FPGA testing yet.

Artifacts and provenance: [`data/raw/metronome_v1.0/`](data/raw/metronome_v1.0/README.md). Evidence and limitations: [wiki/VERIFICATION.md](wiki/VERIFICATION.md). The architecture is due for a rewrite after v1.0.
