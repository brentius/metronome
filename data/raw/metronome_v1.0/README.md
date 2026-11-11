# Metronome v1.0: hardened layout (2026-11-11)

`tt_um_metronome`: IHP SG13CMOS5L, Tiny Tapeout 8x4 tiles (die 1724.16 x 710.64 um), 60 MHz target (16.667 ns), with three IHP SRAM macros (2 x 256x64 program memory, 1 x 512x32 data memory). Source run: `metronome_r3_d17__r6_ant_setup` (see `BOTS/PLANS/HARDEN_LEDGER.md`). Not submitted to any shuttle.

## Provenance

- **RTL.** D17 source (round-robin dispatch). The 31-file manifest is `data/raw/codex_rtl_fix_20261111_111615/verified_source_hashes.json`, and the RTL in `code/rtl` at this commit is the same.
- **Flow.**
  - LibreLane 3.1.0.dev4 (image `ghcr.io/librelane/librelane:3.1.0.dev4`), tt-support-tools `9d13ff3e`, PDK ihp-sg13cmos5l `89d42ee6` (ciel).
  - SRAM power-stripe step vendored from ttcodebot/ttihp-cmos5l-sram-example @15ac9bc (`code/flow/tt_project/vendor/`).
- **Config.** Variant overrides are in `evidence/config_r6_ant_setup.json`, on top of the `make_project.py` project:
  - SYNTH_STRATEGY "AREA 0"
  - FP_PDN_VOFFSET 17.39
  - program SRAMs at x = 891.32 um
  - GRT_ADJUSTMENT 0.15, with no congestion allowed
  - post-GRT design repair and timing repair, setup margins 3.0 ns, TNS repair 100%, buffer budget 80%, gate cloning
  - antenna repair iterations 10, margin 15%
- **Hashes.** GDS sha256 `35c29ee33cc30fbf20d9d0f3e74e7a99b2c75dd693e41456564797665918d747`, uncompressed, before gzip. Bundle sha256 `07c2ccbfd91ea7a38d84d04ec2eaf262fd56b937af1e55d239b2f283b18f53f2`.

## Results (evidence class in brackets)

| Gate | Result |
|---|---|
| Global route | 0 overflow, no congestion allowance [synthesized/PnR] |
| Detailed route | 0 DRC violations [PnR, OpenROAD DRT] |
| LVS (netgen) | Circuits match uniquely [LVS] |
| Power grid | All shapes on VPWR and VGND connected. Worst static IR drop is 0.30 mV (VPWR) and 0.18 mV (VGND) at the typ corner with default activity [estimated] |
| TT precheck | All pass: KLayout pin labels, **full SG13CMOS5L DRC**, zero area, pin, boundary, layer, cell name, analog pin, Verilog syntax [precheck-passed] |
| Gate-level sim | 11/11 lockstep scenarios identical to the reference model on every cycle. The netlist is the post-route `final/nl` with IHP cell and SRAM models, simulated with zero delay. Scenarios: smoke, regs, blink, uart_tx, uart_rx, spi_controller, eth_tx, random_1..4 [RTL-simulated at gate level] |
| Setup, typ 1.20 V 25 C | **+5.876 ns** worst slack at 16.667 ns [post-route RCX STA] |
| Setup, slow 1.08 V 125 C | **-0.423 ns** worst slack, 25 violating endpoints, TNS -4.756 ns. Worst case about 58.5 MHz [post-route RCX STA; fmax calculated] |
| Setup, fast 1.32 V -40 C | +9.540 ns |
| Hold, all corners | worst +0.096 ns (fast), 0 violations |
| Max cap / max slew | 22 / 237 violations at the slow corner (19 / 81 at typ) [STA] |
| Antenna | **1 net / 1 pin violation** (CheckAntennas), not cleared by repair |

## Known gaps

- **Slow-corner setup is negative.** The limit is the program SRAM's slow-corner clock-to-out (about 5.5 ns), followed by the instruction decode in the same cycle. The typical corner closes 60 MHz with 5.9 ns of margin.
- **One antenna violation** and slew/cap violations remain.
- **Not yet verified:** gate-level sim with SDF timing, silicon, an FPGA prototype and the demo board.
- The SRAM power scheme (vendored stripe step) is not silicon-proven upstream.

## Files

- `gds/`: `tt_um_metronome.gds.gz`, `.lef`, the powered netlist `tt_um_metronome.v` (submission view) and the unpowered `tt_um_metronome.nl.v` (gate-level sim view), plus `info.yaml`.
- `metrics.json` and `summary.json`: LibreLane final metrics and the variant gate summary.
- `precheck/`: precheck log and reports.
- `gl_lockstep/`: pytest log and junit XML.
- `reports/`: STA summary, IR-drop log, LVS report and manufacturability report. The full per-corner path reports (`reports/nom_*`) and `r6_run_text.tgz` (all step logs) are kept locally and on the RunPod volume, not in git.
- `evidence/`: the r4, r5 and route_repaired12 summaries, r5's precheck, `runs.log` (every run on the pod) and the r6 config.
