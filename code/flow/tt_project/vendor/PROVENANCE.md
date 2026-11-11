# Vendored files

From https://github.com/ttcodebot/ttihp-cmos5l-sram-example at commit `15ac9bc8560384d1ca7b24e5df0b7b82357d98db`
(2026-11-05), Apache-2.0, Copyright Tiny Tapeout B.V. Unmodified.

| File | Purpose |
|---|---|
| `librelane_plugin_sram_pdn.py` | LibreLane step `Project.ExtendPowerStripes` (loaded from the project root) |
| `odb_stripes.py` | The step's OpenDB script: moves the tile's Metal4 stripes onto the IHP SRAM power columns |
| `pdn_cfg.tcl` | PDN config without a per-macro grid |

The upstream README notes the SRAM power scheme has not been proven in silicon yet.
