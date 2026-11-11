![](../../workflows/gds/badge.svg) ![](../../workflows/docs/badge.svg) ![](../../workflows/test/badge.svg) ![](../../workflows/fpga/badge.svg)

# Metronome: a beat-synchronous protocol engine

Entry for Jane Street's [protocol emulator ASIC competition](https://blog.janestreet.com/protocol-emulator-asic-competition/) (Tiny Tapeout, IHP 130 nm CMOS5L, 8x4 tiles, submission deadline 2027-01-18).

**Idea.** Programs run on the wire's own bit clock, not the chip's. Hardware beat generators produce (or recover) a protocol's bit clock; short loop-free bursts of move instructions run between beats; pin reads and writes are tied to beat taps and boundaries, never to instruction count; a burst that misses its deadline raises a sticky flag instead of silently corrupting the waveform. Rationale: [wiki/ARCHITECTURE.md](wiki/ARCHITECTURE.md). Normative definition: [wiki/SPEC.md](wiki/SPEC.md), with tables generated from the machine description in [wiki/ISA_TABLES.md](wiki/ISA_TABLES.md).

## Layout

| Path | Contents |
|---|---|
| `code/md/` | Machine description (`machine.py`, single source of truth), generator (`gen.py`), instruction encoder (`encode.py`) |
| `info.yaml`, `src/`, `test/`, `docs/` | Tiny Tapeout template layout (from [ttihp-verilog-template](https://github.com/TinyTapeout/ttihp-verilog-template)): Verilog for `tt_um_brentius_metronome` and the LibreLane config in `src/` (`src/md_defs.vh` is generated), the template smoke test in `test/`, the datasheet page in `docs/info.md` |
| `code/host/` | Assembler, static timing checks, program images, example programs |
| `code/tests/` | RTL tests, lockstep RTL-vs-model harness, independent protocol checkers |
| `code/flow/` | v1.0 remote hardening scripts (RunPod). v2.0 hardens through the template's GitHub Actions |
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

Hardening runs through the template's GitHub Actions (`gds`: LibreLane GDS, TT precheck and gate-level test; `test`: the cocotb smoke test in `test/`). The SRAM macros use the power-stripe step at the repository root (`librelane_plugin_sram_pdn.py`, `odb_stripes.py`, from ttcodebot/ttihp-cmos5l-sram-example). v1.0 was hardened on RunPod with `code/flow/`.

## Status

**metronome v1.0 (2026-11-11), hardened but not submitted.**
- **Implementation:** RTL, cycle-accurate reference model, assembler/toolchain and protocol examples. UART TX/RX, an SPI controller and 10BASE-T Ethernet TX all pass the independent checkers on the model, the RTL and the post-route gate-level netlist.
- **Layout:** IHP SG13CMOS5L, 8x4 tiles, three SRAM macros. DRC 0, LVS clean and the full Tiny Tapeout precheck passes.
- **Timing:** setup slack at 60 MHz is +5.9 ns at the typical corner and -0.42 ns at the slow corner.
- **Remaining gaps:** 1 antenna violation; no silicon or FPGA testing yet.

Artifacts and provenance: [`data/raw/metronome_v1.0/`](data/raw/metronome_v1.0/README.md). Evidence and limitations: [wiki/VERIFICATION.md](wiki/VERIFICATION.md). The architecture is due for a rewrite after v1.0.
