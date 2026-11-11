# Example programs

Assemble with `python -m metronome_tools.asm examples/NAME.mas -o NAME.json -v` (run from `code/host`). All five pass the static checks and are exercised in `code/host/tests/test_examples.py` with a beat-level functional model (`tests/funcsim.py`). That model is a sanity check only. It is not the reference model and it is not cycle-accurate. The programs have since been run on the cycle reference model and the RTL: see `code/tests/protocols/` (pytest, pin-level SPI load, independent checkers) and `code/tests/lockstep/proto_scenarios.py`. Not run on hardware.

| File | Behaviour | Pins | Rate |
|---|---|---|---|
| `blink.mas` | Toggles a pin on every beat. | O8 = `uo_out[2]` | BG0 at 1 kHz (inc/mod = 1/60000), so a 500 Hz square wave. Calculated. |
| `uart_tx.mas` | 115200 8N1 transmitter. Bytes are written by the host to `HOSTIN` (0x2404) when `HOSTSTAT` bit 0 is clear. | O8 = `uo_out[2]`, idle high from reset | inc/mod = 6/3125 (exact at 60 MHz). Back-to-back frames. |
| `uart_rx.mas` | 115200 8N1 receiver. Each good frame gives one byte in `HOSTOUT` (0x2405) and `IRQ` on `uo_out[1]` (`.irqen outv`). A bad stop bit drops the byte and sets F2. | P8 = `ui_in[3]` | Same rate. Samples at 25, 50 and 75% of the bit with a 2-of-3 vote. |
| `spi_controller.mas` | SPI mode 0 master, MSB first, one byte per `HOSTIN` write; the MISO byte comes back in `HOSTOUT`. | SCK=O8 `uo_out[2]`, MOSI=O9 `uo_out[3]`, CS_N=O10 `uo_out[4]`, MISO=P8 `ui_in[3]` | 60 clocks per bit (1 MHz). |
| `eth_tx.mas` | 10BASE-T frame transmitter: preamble, SFD, body from data RAM (RAM[0..1] = body length, body from RAM[2]), on-chip CRC-32 FCS (LFSR unit), Manchester at 6 clocks/bit, TP_IDL. Started by any `HOSTIN` write. | O8 = `uo_out[2]`, single-ended, idle low | 4 instructions per 6-clock beat, the maximum. No link pulses, no differential pair. |

Design notes are in the comments of each file. Three points recur.

- The 8-bit `imm` field is shared by the jump target and immediates. States that need both use two instructions. The `pause goto L` goes in the second one.
- State lives in the engine PC. `pause` ends the burst and the next trigger resumes at the following instruction.
- Symbols staged in a burst commit at the next beat. `uart_tx` uses symbol 0 = high so that the line is high from reset.

Not written: an I2C example and a data-RAM message sender.
