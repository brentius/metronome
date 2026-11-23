<!-- Tracked copy of build/vendor/MANIFEST.md, which is the file the download script writes next to the
     vendor models.  build/ is Git-ignored by this project, so this copy is the one that survives a checkout;
     keep the two identical when the pins change. -->

# Third-party device models (build/vendor)

Downloaded by `python -I code/tests/vendor_models/fetch_vendor.py`, which writes each file byte for byte and
checks its SHA-256. `build/` is Git-ignored: the repository ships the fetch script and these pins, not the
vendored sources.

Security: only Verilog and data files are fetched; nothing from a download is executed. The models are
compiled with Icarus (`iverilog -g2012`) and run under the project's own testbenches. No upstream makefile,
script or Python is run.

All hashes below were re-verified on 2026-11-19; each line is the SHA-256 of the file as stored.

## 1. Winbond W25Q128JV SPI NOR flash - Winbond copyright, all rights reserved (re-hosted under an Unlicense file)

| | |
|---|---|
| Upstream | https://github.com/lijiaxun-sgms/w25q128jvxim_v_sim |
| Commit | `6cfed424e0426bb1156f718259d3ce2667b98a65` |
| License | **Not public domain.** The model header reads "Copyright (c) 2001-2016 Winbond Electronics Corporation. All Rights Reserved." The re-hosting repository adds an Unlicense `LICENSE` file, but a third party cannot relicense Winbond's model. Treat it as Winbond's vendor model: used locally for simulation, not redistributed (review S1, 2026-11-19) |
| Used by | `code/tests/vendor_models/tb_spi_flash.v`, `flash_test.py` |

| File | SHA-256 | Note |
|---|---|---|
| `w25q128jv/W25Q128JVxIM.v` | `625495dcd898c6042b3adfb8ed1de3c77a8d58acda532a15a67b1dc9ba02efcd` | the device model (unmodified) |
| `w25q128jv/LICENSE` | `6b0382b16279f26ff69014300541967a356a666eb0b91b422f6862f6b7dad17e` | |
| `w25q128jv/SFDP.TXT` | `73d55352d9a73285d9d441cc5a9635fb9cfb2266f646f85023c7dbde9f9ecbe5` | SFDP table the model loads |
| `w25q128jv/SECSI.TXT` | `83bf735a69c5f3c279a577e6c2a99e6de60d897a79ba4708e56790dd6b80489a` | security-register preload |
| `w25q128jv/SREG.TXT` | `3fd2178f2da76bee4b5c6ca7e03ef0ed59e67d7fe112905bc99fd246be458ed8` | status-register preload |

Upstream also ships `MEM.TXT` (the 128 Mbit array preload, 52 MB) and `W25Q128JVxIM_test.v` (its own
testbench). Neither is fetched: the bench writes its own 64 KiB erased `MEM.TXT` (the model's user preload
mechanism) and the upstream testbench is not needed.

Bench settings (all in `tb_spi_flash.v`, none edited in the model): `NUM_PAGES=256` (64 KiB) and
`tPP=100000` (100 us instead of the part's 0.7-3 ms), documented in the README.

## 2. Microchip 24LC256 I2C EEPROM - restrictive vendor notice, not open source

| | |
|---|---|
| Upstream | https://github.com/azonenberg/antikernel |
| Commit | `6c2915428b897b596694419b428202e9b5273b80` |
| Path | `legacy-trunk/3rdparty/models/i2c_eeprom/24LC256.v` (Git blob `bed3d67fbf4cfae48d05a20a9897b2e04dc69894`) |
| License | File header: "This information is distributed under license from Young Engineering. COPYRIGHT (c) 2006 YOUNG ENGINEERING ... This information is provided to you for your convenience and use with Microchip products only." |
| Used by | `code/tests/vendor_models/tb_i2c_eeprom.v`, `eeprom_test.py` |

| File | SHA-256 |
|---|---|
| `antikernel/models/i2c_eeprom/24LC256.v` | `d403d5325b5625c4de8517881ad0ceff60fd80a42131c894beda871d470ad0a9` |

Provenance checked on 2026-11-19: the commit, path and blob are the ones recorded above, and the file is
unmodified. **The licence is not an open-source licence**: it permits use with Microchip products only, which
is what a 24LC256 simulation model is, and it forbids redistribution outside that scope. It is therefore not
redistributed here (`build/` is Git-ignored; only the pin is in the repository). If a fully permissive model
is required, the OpenCores `i2c_slave_model.v` (see below) is the alternative; it was rejected because it
models a 16-byte device with no write cycle, so it cannot exercise acknowledge polling.

Bench settings (`tb_i2c_eeprom.v`, none edited in the model): `MemoryBlock` preloaded with 0xFF, and
`tWC=200000` (200 us instead of 5 ms) so the busy window is affordable in a full-chip simulation.

## Alternatives examined and not used

| Candidate | Outcome |
|---|---|
| `freecores/i2c` → `bench/verilog/i2c_slave_model.v` (Richard Herveille, "may be used and distributed without restriction provided this copyright statement is not removed") | Permissive, but a 16-byte register file with no write-cycle busy state, so acknowledge polling cannot be tested. Kept as the fallback if the 24LC256 licence is unacceptable. |
| GitHub student projects containing 24LC/AT24C models | Most have no licence file at all; not usable. |

## First-party files that are not vendor models

`code/tests/vendor_models/ps2_keyboard_peer.v` is a PS/2 device peer written for this project from the IBM
PS/2 interface specification (see the file header and the README). It is not a third-party model and is not
covered by this manifest.
