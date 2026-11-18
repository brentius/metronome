# transcribe: record a wire, emit a score

Host-side "play by ear": capture one wire (one 0/1 level per sample, default 60 MHz), infer the protocol, and emit a
`.score` (spec `wiki/SPEC_V2_SCORE.md`) that the compiler can run as the sender. Zero chip area.

    python -m transcribe trace TRACE.txt --fs 60e6 -o out.score     # TRACE.txt: string of 0/1 characters
    python -m transcribe crc FRAMES.txt [--len W]                   # one hex frame per line; last W bytes = CRC
    python -m transcribe demo-image resident-uart.json              # Metronome v4 resident firmware

Run from `code/host2` (or put it on `sys.path`). The host trace workflow uses `code/score` for Score checking.

## Inferred
- NRZ/UART: idle level (trace start/end level), start polarity, bit time (run lengths clustered to a base, then
  least squares over all runs), baud (rounded to a standard baud only if within 1%, otherwise the measured value is
  used; the score comment says which), data bits 5..9, parity none/even/odd (score `parity ... over data`), stop bits.
  Frame format is the shortest valid framing (all frames must pass stop-bit and parity checks).
- Idle-low lines are emitted as `idle low` + `bits lsb first, invert` + inverted start/stop symbols.
- Manchester vs NRZ classification from the run-length pattern (runs of 1 or 2 half-bits only) with bit rate.
  Manchester score emission is not implemented (classification only).
- CRC: `search_crc` tries catalogue polynomials (8/16/32 bit) x init x xorout x refin x refout x byte order and
  returns every match, with a `crc NAME width W poly .. init .. [refin] [refout] xorout ..` declaration (spec 9).

## Assumed / limits
- Bit order is assumed LSB first. It cannot be inferred from the wire; check it against a known frame.
- Stop bits: only a lower bound if the sender always idles between frames. Start-to-start spacing gives the count when
  frames are back-to-back. 7N2 and 8N1-with-constant-1 MSB are indistinguishable; the shorter data field is chosen.
- Minimum 4 samples per bit. Needs a handful of frames (the tool warns below 4). Data patterns using only 1- and
  2-bit runs (e.g. all 0xAA) on a UART can be misclassified as Manchester.
- CRC search is catalogue-based, not a general polynomial solver; needs >= 2 distinct frames.
- Garbage, constant, or unframeable traces raise `InferenceError`; no score is produced.

## Resident UART demonstration

`fw_stage1.source(framing=True, transmit=True)` builds a resident Metronome v4 image at
243 and 233 words on the two 256-word cores. It captures 64 edges, learns polarity,
bit time, data width, parity and a lower bound on stop bits, then transmits the
complete validated prefix on O8 at the learned rate. The host loads the image and
can read the result bytes after `HOST.OUT` reports completion. The chip performs the inference
and transmission autonomously. The firmware supports 5–9 data bits, no/even/odd
parity, and 1–15 bits per interior run. The transmit image needs a bit period of
at least 16 and less than 2048 chip clocks. It assumes LSB-first data and can
choose the shortest of several plausible framings.

### Load and drive the demo

1. Select the project, supply the 60 MHz chip clock, and connect the SPI host
   and a UART source with a common ground. Drive idle-high 3.3 V UART into P5
   (`uio[5]`). Connect a logic analyzer to P5 and O8 (`uo[2]`) to compare
   input and replay. Keep the UART source idle until the image is loaded.
2. Configure the SPI host for mode 0, MSB first, at 1 MHz. Wire SCK to
   `ui[0]`, CS_N to `ui[1]`, MOSI to `ui[2]` and MISO to `uo[0]`.
   Hold CS_N high and SCK low. Pulse `rst_n` low, release it, and leave at
   least a few chip clocks before the first transaction.
3. Send one SPI transaction per entry in the JSON image's `writes` array, in
   order. Each transaction is `02 ADDR_HI ADDR_LO` followed by the decoded
   hex bytes in `data`. Keep CS_N low throughout that transaction and high
   for at least a few chip clocks between transactions. The image includes
   the write that enables execution.
4. Leave P5 idle for 1 ms after loading. Send a contiguous 115200 baud 8N1
   burst with no extra inter-byte gaps. Repeat the byte sequence
   `A5 5C 38 E7 13 F4 89 27` four times within that burst, then return
   to idle. The firmware uses the first 64 edges and transmits only complete
   validated frames. In the cycle model this stimulus yields an 11-byte replay
   of `A5 5C 38 E7 13 F4 89 27 A5 5C 38` on O8. Decode the replay after
   O8 reaches the learned idle level. O8 can start low before transmission.
5. Poll `HOSTSTAT` at `0x2406` for bit 1 with a bounded timeout after sending
   the burst. On completion, read `HOSTOUT` at `0x2405` and `ERRSUM` at
   `0x2408`. Expect `HOSTOUT = 1` and `ERRSUM = 0` for a clean replay.
   Read the result block using the SPI addresses below. Reset and reload to
   repeat the demonstration.

An SPI read sends `03 ADDR_HI ADDR_LO` followed by one dummy byte per requested
byte, all under one CS_N assertion. Discard the first three received bytes.
For example, use the following with an initialized SPI peripheral and CS_N
output in MicroPython. The board-specific pin setup and reset precede the load.

```python
import binascii
import json
from time import sleep_us


def exchange(spi, cs_n, request):
    reply = bytearray(len(request))
    cs_n.value(0)
    try:
        sleep_us(1)
        spi.write_readinto(request, reply)
        sleep_us(1)
    finally:
        cs_n.value(1)
    sleep_us(1)
    return reply[3:]


def load_demo(spi, cs_n, path="resident-uart.json"):
    with open(path) as image_file:
        image = json.load(image_file)
    for write in image["writes"]:
        address = write["addr"]
        request = bytes((0x02, address >> 8, address & 0xff))
        exchange(spi, cs_n, request + binascii.unhexlify(write["data"]))


def read_bytes(spi, cs_n, address, count):
    request = bytes((0x03, address >> 8, address & 0xff))
    return exchange(spi, cs_n, request + bytes(count))
```

| SPI address | Data RAM offset | Result bytes in order |
|---|---|---|
| `0x1710` | `0x710` | Rate status, idle level, bit period low byte, bit period high byte, runs accepted, divisor candidate. The bit period is in 1/32 clock units. |
| `0x1716` | `0x716` | Framing status, data width, parity (0 none, 1 even, 2 odd), validated frame count, minimum observed stop interval. |

Rate status 1 means learned, 2 means the bit period was too long, and 3 means
no rate passed. After a successful rate calculation, framing status 1 means
learned, 2 means a run could not be quantised, and 3 means no framing passed.
If framing succeeds below 16 clocks per bit, `HOST.OUT` reports 4 and the transmitter stays off.
Read the rate details only after rate status 1 and the framing details only
after framing status 1. The framing status itself is valid after rate status 1.
Convert a successful bit period to baud as `60_000_000 * 32 / (low | high << 8)`.

### Evidence

The cycle-model test independently
decodes 8N1, 7E2 and idle-low 8O1 with clock error and edge jitter. The separate
`replay_capture=True` mode reproduces the recorded edge timing and has full-chip
RTL lockstep coverage. The resident image passes full-chip RTL lockstep and
routed zero-delay gate simulation for 8N1 at 24 clocks per bit. The 115200 baud
recipe above has cycle-model and independent codec evidence. Board bring-up
remains pending.

The host transcription tool supports wider input conditions and CRC search. It was verified in simulation against the reference codec (hidden score -> Codec waveform with +-1.5% clock error and +-2
sample edge jitter -> transcribe -> compile emitted sender -> v2 cycle-level model -> decode with the hidden score's
Codec). Model level only; nothing here is measured on hardware. Tests: `python -m pytest code/tests/transcribe -q`.
Known compiler gap (scorec, not this tool): a score with a `parity` field, or idle-low with `invert`, already
misbehaves when compiled directly, so those round trips are checked for equivalence with the hidden score compiled
directly rather than for exact bytes.
