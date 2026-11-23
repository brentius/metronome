# Vendor-model co-simulation and the PS/2 blind challenge

Full-chip Metronome RTL driven against third-party device models on its pins, plus one protocol the emulator
was never designed for, written from its public specification only.

```sh
source code/tools/env.sh                                       # OSS CAD Suite on PATH (iverilog)
python -I code/tests/vendor_models/fetch_vendor.py             # download + verify the pinned models
python -m pytest code/tests/vendor_models -q                   # ~3 min from a clean build (177-181 s in two runs)
```

`fetch_vendor.py` is the only network step; it writes each file byte for byte and checks SHA-256 (see
`build/vendor/MANIFEST.md`). `build/` is Git-ignored, so the models themselves are not in the repository.

## What is under test

Each test builds the **full chip** (`code/tests/lockstep_v2/rtl_sources.py` source list: all of `src/`, the
IHP SRAM behavioural arrays unless `VENDOR_IHP_SRAM=1`) with one device wired to the `uio` pins, then drives
the chip over its SPI host link exactly as `code/tests/lockstep_v2` does. Every byte the host checks crossed
real pins to/from the model. Nothing is backdoored into either side: the device only sees wires.

| Test | Device (pin map) | Controller program | Third-party? |
|---|---|---|---|
| `test_spi_flash_read_id_program_read` | Winbond W25Q128JV, SCK=O0, CS_N=O1, MOSI=O2, MISO=P3 | Score: `code/score/lib/spi_mode0.score`, controller role | yes; Winbond copyright, not redistributed (see manifest) |
| `test_i2c_eeprom_write_poll_read` | Microchip 24LC256, SCL=P0/O0, SDA=P1/O1 (open drain) | Score: `code/score/lib/i2c.score`, controller role | yes, vendor notice |
| `test_ps2_keyboard_receive` | PS/2 keyboard, CLK=P0, DATA=P1 (open drain) | assembly `code/host2/examples/vendor/ps2_keyboard_rx.mas` **and** Score `ps2_keyboard.score` | peer written here from the spec |
| `test_24lc256_ack_poll_quirk_reproduced` | 24LC256 alone (no chip) | - | yes |

Licences, upstream commits and per-file SHA-256: `build/vendor/MANIFEST.md`, with a tracked copy in
`code/tests/vendor_models/MANIFEST.md` (`build/` is Git-ignored). The 24LC256 model carries a restrictive
Microchip/Young Engineering notice (use with Microchip products only); it is *downloaded, not
redistributed*, and the manifest records the permissive OpenCores fallback and why it was rejected.

## Results (actual run, 2026-11-19)

Icarus Verilog 14.0 (devel, s20260301-638-ge072b3334-dirty), cocotb 2.1.0, Python 3.12.10, pytest 9.2.0,
Windows 10.0.26200. Raw log: `evidence/pytest_vendor_models_2026-11-19.log`; per-run numbers in
`evidence/summary_2026-11-19.json`. Evidence class for all of the following: **RTL-simulated against a
third-party device model** (or, for the PS/2 rows, against a first-party spec-derived peer). Nothing here is
a silicon measurement.

| Check | Result | Simulated |
|---|---|---|
| Flash JEDEC ID (9Fh) read over the pins | `EF 70 18` | 64,062 chip cycles, 65 bytes on the wire, 1.068 ms |
| Flash WREN-gated page program | program without WREN is ignored; with WREN the 4 bytes read back `DE AD BE EF` | same run |
| Flash `tPP` busy model | WIP set during the program, clear after; WEL self-clears | same run |
| EEPROM page write (0x50, word 0x0040, 4 bytes) | all six acknowledges received | 126,570 cycles, 2.1 ms of bus time |
| EEPROM acknowledge polling | first probe NACKed while busy, later probe ACKed | same run |
| EEPROM read-back (dummy write + repeated start, 6 bytes from 0x003E) | `FF FF DE AD BE EF` | same run |
| EEPROM wrong device address 0x51 | NACKed, transaction stopped | same run |
| PS/2 assembly receiver, 3 frames (0x1C, 0x5A, 0xE0 with a bad parity bit) | bytes exact; start/stop exact; the raw log equals the wire bit for bit (33 captured bits, then zero flush padding) | 156,924 cycles |
| PS/2 Score receiver, same 3 frames | bytes exact; status byte 0 for every frame; captured parity matches, bad-parity frame flagged by the host | 159,882 cycles |

Negative controls, all inside the tests: flash program-without-WREN must not change memory; EEPROM
unprogrammed word address must read `FF`; a deliberately wrong expected page must make the same comparison
raise; an unaddressed device must not acknowledge; PS/2 wrong-byte expectation must raise and the injected
parity error must be caught. Each "checker has teeth" control asserts that the comparison *does* fail, so a
vacuous pass is impossible.

## The PS/2 blind challenge (protocol not in `wiki/PROTOCOL_LIBRARY.md`)

Specification: IBM Personal System/2 Hardware Interface Technical Reference (1988), "Keyboard-to-System
Communication" (scanned copy: <https://archive.org/details/bitsavers_ibm>), mirrored as "The PS/2
Mouse/Keyboard Protocol" (A. Chapweske, 1999), sections "Communication: General Description" and
"Communication: Device-to-Host", <https://www.burtonsys.com/ps2_chapweske.htm> - 11 bits per frame (start 0,
8 data bits LSB first, odd parity, stop 1), device-generated clock 10-16.7 kHz, data read on the falling
edge, data changing while the clock is high (5-25 us before the next fall), open-collector lines.

* Independence caveat (review S6): the same delegate wrote the peer and both receivers, so this is a datasheet-built challenge with a self-written peer, not a blind test by an independent party.
* Peer (`ps2_keyboard_peer.v`): written here from that description, not from the program. 16.7 kHz, odd
  parity, optional injected parity error. The testbench records the data level at every falling edge, so the
  chip's receive log is compared with the wire bit for bit.
* Program 1 (assembly): follows the device's clock, snapshots DATA at each falling edge, frames 11 bits with
  its own counter, logs the raw frame and reports the byte on `HOST.OUT`.
* Program 2 (Score): `ps2_keyboard.score`, compiled by `scorec` to a 10-instruction fixed-rate receiver.
  This was not planned: the campaign assumed Score could not express a self-clocked 11-bit frame, and the
  compiler proved otherwise (see `FINDINGS.md` F5). Its limit is that it samples at a fixed 60 us beat, so it
  covers roughly 15.9-17.5 kHz rather than the whole 10-16.7 kHz device range (calculated, not swept) - which
  is why the assembly program is kept.
* Neither program checks parity in logic; both capture it and the host checks it, which is what the parity
  negative control exercises.

## What this does and does not establish

* It does establish: the RTL, the host link and the compiled controllers work against unmodified
  third-party protocol models at the pins, including timing-dependent device behaviour (flash `tPP`, EEPROM
  `tWC` and acknowledge polling), and that a protocol outside the library can be received both in assembly
  and in Score.
* It does not establish: anything about silicon, the SRAM macros (`VENDOR_IHP_SRAM=1` switches to them),
  real device corners (both models are shortened in *time* only: `tPP` 100 us vs 0.7-3 ms, `tWC` 200 us vs
  5 ms; the protocol behaviour at those shortened times is what is checked), bus rise times, or pin loading.
  Model simplifications are the models' own.
* The 24LC256 licence is restrictive (manifest); the flash model is Winbond-copyrighted (all rights reserved) despite the re-host's Unlicense file; the PS/2 peer is ours.

## Files

| File | Role |
|---|---|
| `vendor_common.py` | cocotb bench helpers: pins, SPI host link, image load, free-running waits |
| `tb_spi_flash.v`, `flash_test.py` | flash co-simulation |
| `tb_i2c_eeprom.v`, `eeprom_test.py` | EEPROM co-simulation |
| `tb_ps2.v`, `ps2_test.py`, `ps2_keyboard_peer.v` | PS/2 blind challenge (assembly + Score) |
| `ps2_keyboard.score` | the PS/2 receiver in Score |
| `repro_24lc256.v` | F1 reproduction, run by its own test |
| `fetch_vendor.py`, `.gitignore` | pinned download; generated preload/build files |
| `FINDINGS.md` | F1 model bug, F2-F4 notes, F5 Score fit |
| `evidence/` | run log and the summary JSON with dates, versions and hashes |

## Gaps

* Two third-party models (the task allows 2-3). A third was considered - OpenCores `i2c_slave_model.v` - and
  rejected as a duplicate protocol without a write cycle; see the manifest.
* The EEPROM test pays one extra write cycle of simulated time because of F1.
* Bus rates: 4 MHz SCK (flash), 300 kHz I2C (inside the part's 400 kHz rating and above the model's own
  `tLO = 1.3 us` timing check), 16.7 kHz PS/2.
* No formal, mutation or gate-level run here; those live in the rest of the tree.
