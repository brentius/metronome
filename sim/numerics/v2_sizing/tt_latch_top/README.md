# Latch-bank Tiny Tapeout top (physical-flow sizing run)

Minimal `tt_um_brentius_metronome` wrapping a 256-byte (2,048-bit) `cfg_latch_bank`. Not the Metronome design; see
`../LATCH_SIZING.md`. Pin protocol is in the header of `tt_um_brentius_metronome.v`.

Source files for a Tiny Tapeout `info.yaml` `source_files` list (copy, do not edit `src/` of the template here):
- `tt_um_brentius_metronome.v` (this folder)
- `../rtl/cfg_latch_bank.v`
- `../rtl/cells_behav.v` (simulation models only; the flow must NOT need it, see below)

Required Tiny Tapeout/LibreLane config: define `USE_IHP_CELLS` (e.g. `VERILOG_DEFINES: ["-DUSE_IHP_CELLS"]` or
`-DUSE_IHP_CELLS` in the flow's define list) so the wrapper instantiates `sg13cmos5l_dlhrq_1` and `sg13cmos5l_lgcp_1`.
With the define set, drop `cells_behav.v` from the source list (the library cells are the cells). Without it the
behavioural latches are used and the flow would see inferred latches.

Smoke test (behavioural cells): `python -m pytest sim/numerics/v2_sizing/tt_latch_top/test_tt_latch_top.py -q`.
Note: the 256:1 byte readback mux in this top is itself about 50k um2; it is test scaffolding, not part of the bank.
