# Findings

Overview: this campaign looked for defects in the *models* and in the *emulator*. No RTL or Score-compiler
defect was found. One third-party model has a real behavioural bug (F1), one has a documentation caveat
(F2), and two of the issues met while writing the benches were in my own testbench or in the way the host
must use a documented RTL feature (F3, F4). Each item says what was observed, how to reproduce it, and what
the campaign does about it.

Evidence class for everything here: RTL-simulated (Icarus 14.0, full-chip RTL, 2026-11-19) plus the
stand-alone model runs below. No silicon.

---

## F1 - 24LC256 model starts a spurious write cycle after an acknowledge-poll transaction (model bug)

**What happens.** After a page write completes, the standard acknowledge-polling probe - a START, the device
address with R/W = 0, and a STOP, with no data byte - is acknowledged correctly (as on silicon). But the
model then starts a *second* write cycle at that STOP and refuses its address for another `tWC` (5 ms by
default). A real 24LC256 performs no write for that transaction and answers its address immediately
(datasheet "Acknowledge Polling": the device responds as soon as the internal write cycle is complete; a
write needs at least one data byte).

**Why.** `24LC256.v` clears the byte-address flags on STOP, but `WrCounter` is only cleared by the byte-address
register block,

```
always @(negedge SCL) if (CTRL_Rcvd & (BitCounter == 8) ...) WrCounter <= 0;      // section 1.06
```

and `CTRL_Rcvd` is set by the control-byte block *at the same negedge* (section 1.05, non-blocking). For a
control byte followed by a STOP there is no later byte, so `WrCounter` keeps the previous transaction's
count. The write-cycle timer then sees `WrCycle & (WrCounter > 0)` at the STOP and runs a cycle that writes
the stale buffer again:

```
always @(posedge STOP_Rcvd) if (WrCycle & (WP == 0) & (WrCounter > 0)) begin WriteActive = 1; #(tWC); ... end
```

**Reproduction.** `code/tests/vendor_models/repro_24lc256.v` runs on the model alone (~1 s) and prints:

```
PAGE WrCounter=1 WriteActive=1
IDLE WriteActive=0
POLL ack=0
AFTER_POLL WriteActive=1 WrCounter=1     <- should be 0
POLL2 ack=1                              <- should be 0
```

`test_24lc256_ack_poll_quirk_reproduced` in `test_vendor_models.py` pins exactly these lines, so the finding
cannot silently change.

**Consequences and what this campaign does.** Memory content is not corrupted (the stale buffer is the data
just written), but a driver that polls and immediately reads gets an address NACK. `eeprom_test.py` waits one
write cycle after the successful poll and says so in a comment. It also means the *first* poll of a driver
must not be trusted blindly: the co-simulation observes the NACK on the busy poll, then the ACK, which is
what the test asserts.

**Not worked around in the model.** The model is compiled unmodified; only `MemoryBlock` (preload) and `tWC`
(simulation time) are set from the testbench.

---

## F2 - 24LC256 model: `RESET` only gates the timing checks (documentation caveat)

The `RESET` pin of `M24LC256` is used by exactly one expression, `TimingCheckEnable = (RESET == 0) & ...`, so
the model's `$width`/`$setup` checks are only active while `RESET` is low. It is not a functional reset: the
memory array and the state machine are not cleared. The bench drives `RESET = 0` (checks enabled) and does
not rely on the pin for anything else. Recorded because a reader may otherwise expect a reset.

---

## F3 - Receive streams hold a partial byte until a flush (RTL behaviour, usage rule)

A receive stream commits a byte to data RAM when the byte completes; a bit count that ends mid-byte (here
33 bits over three PS/2 frames, and 27 bits over three Score frames) stays in the stream's shift register.
`SRT.CTL` bit 1 (flush) commits it, padding with zeros. Reading data RAM before the flush silently returns
the last complete byte plus whatever was in RAM, which looked exactly like a dropped last bit in the first
PS/2 run. Confirmed against `src/md2_stream.v` (`done = (bitin & last) | (fl & ...)`).

This is documented behaviour, not a defect; the PS/2 assembly bench flushes before reading and asserts that
the padding bits are zero, and the EEPROM bench reads whole bytes only.

---

## F4 - W25Q128JV model preloads from the working directory (bench note)

The flash model `$readmemh`s `MEM.TXT`, `SFDP.TXT`, `SECSI.TXT` and `SREG.TXT` from the *run* directory, so
the cocotb run happens in `code/tests/vendor_models/` and the generated files are Git-ignored there. The
upstream 128 Mbit `MEM.TXT` (52 MB) is not fetched: the bench runs the model with `NUM_PAGES=256` and writes
its own 64 KiB all-0xFF (erased) preload. Not a defect; recorded so the test cannot be mistaken for an
unmodified-array run.

---

## F5 - Score fit for PS/2: it compiles, but only as a fixed-rate receiver (limitation)

The blind-challenge protocol was first written as assembly
(`code/host2/examples/vendor/ps2_keyboard_rx.mas`) on the assumption that Score had no template for it. The
specification used for both is IBM's "Keyboard-to-System Communication" (scanned:
<https://archive.org/details/bitsavers_ibm>; mirrored text: <https://www.burtonsys.com/ps2_chapweske.htm>,
"Communication: General Description" and "Communication: Device-to-Host"). That assumption was wrong: the
compiler accepts

```
clock 16667 Hz
  device: generated
  host:   started by clk fall
symbols  bit(d) clk "10" data "d" sample data at 50%
grammar  line = frame*
         frame = bit(0) data:u8 parity:bit bit(1)
```

and emits a 10-instruction receiver plus a per-frame status byte
(`code/tests/vendor_models/ps2_keyboard.score`). Both programs are co-simulated against the same peer in
`ps2_test.py`.

The limitation is the receive template, not the protocol: like the UART receiver it samples at a fixed beat
derived from the declared clock (3600 cycles = 60 us at 60 MHz), it does not track the device's clock. With
a 50% sample point and 10 coded bits, the last sample stays inside its bit while the bit period is within
about +-5% (calculated, UART-style argument; not swept here), i.e. roughly 15.9-17.5 kHz. A PS/2 device at
10-12 kHz would therefore *not* be received by the Score program, whereas the assembly program follows every
falling edge and is designed to accept the whole 10-16.7 kHz range in the specification (simulated only at 16.7 kHz; the rest of the range is calculated, not swept - review S6) (its static check bounds the
period at 3000-40000 cycles, i.e. 20 kHz down to 1.5 kHz).

Also, neither program checks the parity bit in logic: both capture it (the Score program as a `parity:bit`
field, the assembly program in its raw 11-bit log) and the host checks it. The negative control in the test
injects a wrong parity bit and shows the host decode catching it while the captured byte stays correct.

**Diagnostic quality note.** A first attempt with `frame = ...` as the top-level production failed with
`E-UNSUPPORTED: 18:11: grammar: 'top-level sym outside the frame loop' is not compiled yet`. That message
does not say that wrapping the frame in `line = frame*` makes it compile; the wrapper is only visible in the
library scores. Not a defect, but the first thing to try when porting a new frame protocol.
