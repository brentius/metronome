# Protocol library: what each score does and does not do

Status: **2026-11-16, Metronome v3.0 Track B.** Scores are in `code/score/lib/`; tests are in `code/tests/score_lib/`
(independent decoders in `indep.py` and `indep_more.py`). Every claim below is **software only**: the v2 cycle-level
model (`sim/reference/metronome2`) and Python decoders written from each standard. There is **no RTL run, no gate-level
run and no hardware measurement** behind any row, and a model pass does not prove timing closure at 60 MHz on silicon.

## How to read the evidence column

| Kind | Meaning |
|---|---|
| **compiled on cycle model, checked by independent decoder** | `scorec` compiled the role, the image ran on the cycle-level model, and the pins were decoded by a checker written from the standard (not from the score codec). |
| **codec level, checked by independent decoder** | The reference codec (`code/score`) produced the waveform; an independent decoder written from the standard read it back. `scorec` does not compile the score; the refusal is pinned in `test_library.py`. |
| **parse and check only** | Valid score language; no waveform check. (None in the table.) |

"All 256 byte values" means every value 0 to 255 occurs in every byte-wide field, with the independent decoder agreeing
on each. Where a test samples a subset by default, the full run is behind `SCORE_LIB_SLOW=1` and is stated in the row.

## Protocol table

| Score (`lib/`) | Does | Does not | Evidence | Tests |
|---|---|---|---|---|
| `uart_8n1` (existing) | 8N1 at any rate; sender and receiver | parity, 2 stop bits, break | compiled on cycle model, checked by independent decoder (existing `protocols.uart_decode`) | `code/tests/scorec/test_uart.py` |
| `ws2812` | 24-bit GRB frames, 8 LEDs, 800 kHz; high 0.40 us / 0.80 us, beat 1.25 us (75 chip cycles), latch gap 60 us; pulse widths checked within the datasheet's +-150 ns | read-back; strips of other lengths without editing the score; a receiver role (scorec refuses it) | compiled on cycle model, checked by independent decoder; also all 256 byte values (11 frames) and codec level | `test_ws2812.py` |
| `dmx512` | break 100 us, MAB 12 us, null start code, four 8N2 slots at 250 kbit/s (break >= 92 us, MAB >= 12 us checked) | receiver role (scorec refuses it), more than four slots without editing, alternate start codes | compiled on cycle model, checked by independent decoder (two packets, edge values); codec level over all 256 slot values | `test_dmx512.py` |
| `wiegand26` | 26-bit H10301 frame on D0/D1, trailing odd parity computed, 50 us pulse / 2 ms interval at the nominal clock | the leading even parity (host supplies it: gap G5); panel/receiver role; longer formats | compiled on cycle model at 20 kHz, checked by independent decoder (bits and both parities, 10 % pulse fraction); the standard's absolute pulse/interval windows are checked at the codec level at the nominal clock, and on the cycle model at 4 kHz with `SCORE_LIB_SLOW=1` (about 75 s). All 256 facility codes and card bytes at the codec level | `test_wiegand26.py` |
| `hdlc` | Flag, address, control, 4 info bytes, CRC-16/X-25, LSB first, zero insertion after five ones, separate bit clock | the closing-flag zero when the data ends in five ones (gap G6); abort; NRZI; variable length; sender and receiver roles: scorec refuses `stuff` with `E-UNSUPPORTED` (C2, fixed 2026-11-16; previously a silent miscompile) | codec level, checked by independent decoder and independent encoder (all 256 values; frames whose data ends in five ones are non-conforming, and the test pins that exactly). Not compiled | `test_hdlc.py` |
| `onewire` | Reset (560 us), presence (starts at 60 us, 80 us long), Skip ROM, Read Scratchpad, 8 data bytes read by the device and the Maxim CRC-8; 80 us slots, write-0 low 60 us, write-1 low 6 us, 15 us read point | search-ROM, overdrive, parasite power, a no-device branch; presence starts at the far edge (60 us) of the 15 to 60 us window because the language allows three split points | codec level, checked by independent decoder (nominal timing windows; all 256 scratchpad values at 8x speed). Compiler refuses (`E-UNSUPPORTED`, bus template is MSB-first only) | `test_onewire.py` |
| `swd` | ARM SWD request with parity, both turnaround clocks, 3-bit ACK (OK, WAIT, FAULT), 32-bit data with parity, read and write | line reset and JTAG-to-SWD switch, WDATAERR sticky handling, multi-drop; SWDIO is modelled open-drain (the codec resolves every shared wire as wired-AND) | codec level, checked by independent ADIv5 packet decoder (all 16 header combinations x 3 ACKs; all 256 values in each of the 4 data bytes of reads and writes). Compiler refuses (`E-UNSUPPORTED`, parity) | `test_swd.py` |
| `jtag` | TAP navigation by TMS, one data-register scan: 8 TDI/TDO bits plus the exit clock | TMS=1 on the last data bit (gap G1; the register is effectively 9 bits wide, ninth bit sent as 0); IR scans; variable length. **Partial** | codec level, checked by an independent 1149.1 TAP-controller model (256 scans, all TDI and TDO byte values, state path asserted). Compiler refuses (`E-UNSUPPORTED`, `||` outside a `*` loop; follower shape) | `test_jtag.py` |
| `mdio` | IEEE 802.3 clause 22 read and write frames, 32-bit preamble, read turnaround (released, then PHY drives 0) | clause 45, preamble suppression | codec level, checked by independent frame decoder (512 frames, every value in both data bytes). Compiler refuses (`E-UNSUPPORTED`, bus template shape) | `test_mdio.py` |
| `spi_mode0` ("SPI target" is the `peripheral` role) | Mode 0, CS_N framed, whole bytes, MSB first, full duplex; both roles | modes 1 to 3, LSB first, quad lanes | compiled on cycle model (peripheral role), driven by an independent mode-0 controller waveform; MOSI stored and MISO read back. All 256 values in both directions with `SCORE_LIB_SLOW=1` (about 40 s); default run uses 64 values | `test_spi_target.py` (and `code/tests/scorec/test_spi.py`) |
| `i2c` (target role is "I2C target") | START, repeated START, STOP, 7-bit address match by parameter, write and read, per-byte ACK | 10-bit address, clock stretching by the target, arbitration | compiled on cycle model (target role) against an independent UM10204 controller waveform and bus decoder; address ACK and NACK at 100 and 400 kHz; all 256 values written in one transaction with `SCORE_LIB_SLOW=1` (about 65 s), default run uses 48 values. The controller role is covered by `code/tests/scorec/test_i2c.py` | `test_i2c_target.py` |
| `pattern_gen` (personality) | One output pin plays 512 host-written bits at a load-time rate (tested 1, 2.5 and 5 MHz), LSB first, then idles low; host script `code/score/examples/pattern_gen_host.py` writes a VCD | more than one pin per pattern (gap G2), loops, triggers | compiled on cycle model, checked against the packed bit list and the beat grid (edges within one chip cycle); all 256 byte values; VCD round trip | `test_personalities.py` |
| `logic_analyser` (personality) | One pin sampled at the middle of every beat after a rising-edge trigger; 128 samples stored in RAM; host script `code/score/examples/logic_analyser_host.py` writes a VCD (tested 0.5, 1 and 2 MHz; a UART byte captured at 4x baud and decoded by hand) | more than one channel, other triggers, pre-trigger history | compiled on cycle model, checked against the stimulus; VCD round trip | `test_personalities.py` |

## Protocols not written, and why

A protocol is listed here only when the score language cannot say it (so there is nothing valid to keep) or when it was not
attempted. Gaps G1 to G5 are properties of the language as written in `SPEC_V2_SCORE.md`; two are reproduced as tests.

| Protocol | Status | Reason |
|---|---|---|
| SpaceWire (data-strobe) | not expressible | D is the data and S toggles whenever D does not: the second wire depends on history, and a line has one coder and one remembered bit (gap G4). The score language would need a per-beat parity or a two-wire coder. |
| QSPI (4 lanes) | not expressible | A quad beat carries four data bits from one owner; `||` needs different owners (gap G2, reproduced: `E-DUPLEX`). |
| NEC infrared | not expressible | Bit 0 and bit 1 have different durations (pulse-distance coding) and the mark is a 38 kHz carrier; the beat length is constant (gap G3). |
| I2S | not expressible | WS changes one clock before the MSB, which needs a different symbol for one bit position of a field (gap G1). |
| CAN with stuffing | not attempted | The CRC-15 covers a bit stream that is not a whole number of bytes (the compiler and the CRC rule need whole bytes, spec 9 and NOTES 13). |
| LIN, PWM / servo | not attempted | PID parity and the classic checksum are computed fields (not compiled); servo pulse width is a data-dependent duration (gap G3). |

## Language gaps found (for the spec owner)

| # | Gap | Hit by | Evidence |
|---|---|---|---|
| G1 | Every bit of a field uses the one `bit` symbol, so a symbol cannot differ by bit position (no TMS=1 on a last bit, no I2S word-select lead) | JTAG, I2S | design reading of 5.3 and 7.3; JTAG score is the partial workaround |
| G2 | One owner cannot place two independent data bits (or four lanes) in one beat | QSPI, JTAG TMS+TDI, parallel pattern output | `test_library.py::test_gap_two_data_bits_per_beat_from_one_owner_is_rejected` |
| G3 | The beat length is constant, so a bit cannot be longer than another | NEC, servo PWM | design reading of 5.2 |
| G4 | A line has one differential coder and one remembered bit | SpaceWire | design reading of 6 |
| G5 | Fields are L-attributed: a parity or check cannot cover later fields | Wiegand leading parity | `test_library.py::test_gap_leading_parity_over_later_fields_is_rejected` |
| G6 | Stuffing is lazy: no zero is inserted before a bypass symbol that follows five ones, but HDLC requires it; a bypass flag also skips differential coding, so an NRZI HDLC flag cannot be written | HDLC | `test_hdlc.py::test_every_byte_value_codec_vs_independent_decoder` pins which frames are affected; `test_data_ending_in_five_ones_is_stuffed_before_the_closing_flag` (strict xfail) |
| G7 | `turnaround N beats` takes time but produces no clock edges, so a clocked turnaround (SWD, MDIO) is written as an explicit released-line symbol | SWD, MDIO | the scores use `ta` and `tz` |
| G8 | The codec resolves every `shared` wire as wired-AND even when `push-pull` is written | SWD | modelling note in `swd.score` |
| G9 | On a shared wire only the terminal's owner drives the beat, so a 1-Wire read slot's initial low pulse is attributed to the device | 1-Wire | comment in `onewire.score` |

## Compiler gaps found (for Track C)

Each is reproduced by a test in `code/tests/score_lib/`; the strict xfails flip to failures when the gap is fixed, which is the cue to remove the marker.

| # | Gap | Reproduction |
|---|---|---|
| C1 | `X x N` repeats one list of `Step` objects in `flatten.py`; `merge_syms` mutates their counts in place, so `mab x 3` stages 4 beats and `slot x 4` (a slot that ends in two stop bits) over-merges them (5 beats); with `brk x 25` the count becomes 2^24 and the assembler fails (`E-ASM`, immediate does not fit). Silent wrong timing for N = 3. **Fixed 2026-11-16** (each repeat is a copy) | `test_dmx512.py::test_compiler_symbol_repeat_count_x3` now passes (regression). The DMX512 score still writes the repeats out |
| C2 | The sender template ignores `bits ..., stuff BIT after N ...` and `bits ..., differential on 0`: both compile with no diagnostic and the wire carries plain NRZ without inserted zeros **Fixed 2026-11-16 by refusal:** both now raise `E-UNSUPPORTED` (implementation still open) | `test_hdlc.py::test_compiled_sender_refuses_stuffing`, `test_library.py::test_compiled_sender_refuses_differential_coding` |
| C3 | A frame that starts with `bytes[N]` is rejected by the static check (`E-AMBIG`, "can match nothing") even for a constant N, so the score needs a leading symbol (`lead` in `pattern_gen.score`) | try `frame = pat:bytes[64]` as the first item of a `*` production |
| C4 | Shared-wire scores compile only through the I2C-shaped bus template: MSB first, no parity, `START REQUEST (RSTART REQUEST)* STOP`. That blocks 1-Wire (LSB first), SWD (parity) and MDIO (shape). A generated-clock sender for shared wires where one role drives each beat would cover all three | `test_library.py::test_compile_status_is_pinned` |
| C5 | A single `{ a \|\| b }` outside a `*` loop is `E-UNSUPPORTED` ("step 'dup' in a sender frame"), which blocks the JTAG scan; follower and receiver templates accept only the SPI `select ... deselect` shape, which refuses HDLC and JTAG device roles | same test |
| C6 | Receiving `brk` (a symbol terminal that repeats) and an edge-recovered receiver with a multi-segment symbol (WS2812 LED) are refused | same test |

## What this table does not claim

- No row is RTL-simulated, gate-level simulated, synthesised or measured on silicon.
- The independent decoders check standards' waveforms at chip-cycle resolution (16.7 ns); they are not electrical (no
  rise times, thresholds or pull-up values).
- "Compiled on cycle model" means the scorec image ran on `sim/reference/metronome2` with the `LATE`, `OVR` and `CONFLICT`
  witnesses at zero in the tests that check them (`model_clean`).
- Pulse-width tolerances (WS2812 +-150 ns) are met at the 16.7 ns chip-cycle grid: the compiled pulses are 24 and 48
  cycles, exactly 0.40 and 0.80 us.
