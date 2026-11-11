# Power-grid checks around the IHP SRAM stripe step

Added after `metronome_r3_d17__route_repaired12`, where netgen LVS failed and Magic reported `Ports "VPWR" and "VGND" are electrically shorted`.

| Script | Run with | Checks |
|---|---|---|
| `pwr_vias.py ODB` | `openroad -python -exit` | Expands every VPWR/VGND special via into its layer shapes, then reports overlaps with opposite-net special wires and vias. **This is the one that found the r3 short.** |
| `stripes_json.py ODB OUT.json`, then `stripe_vs_gds.py` | openroad, then `klayout -b -r ... -rd js= -rd gdsdir= -rd lefdir=` | Tests every Metal4 stripe over a macro against the macro's real GDS Metal4, with each polygon classed by LEF power pin. Flags wrong-polarity contacts. |
| `pwr_macro.py ODB` | openroad | Stripes over macros against LEF pins and OBS, with a per-macro summary. OBS hits on VPWR columns are expected: they are the VDD!/VDDARRAY! column gaps. |

r3 finding: 113 overlaps at x≈1720 µm. The stripe step replaced partial-height stripes at the core's right edge with a full-height stripe plus 57 `via3_4` rail stacks (2.1 µm wide), and those landed on the clipped 0.26 µm VGND stripe sliver. The cause was `FP_PDN_VOFFSET` 6.15 / pitch 44.96: the last pair (VPWR at 1714.63) put its VGND past the core edge at 1721.28. The fix is offset 17.39, which is 6.15 + 11.24, one SRAM power-column pitch, so stripes stay aligned to the macro columns. The last pair then ends at about 1688.6 µm.
