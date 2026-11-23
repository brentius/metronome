# `scorec` compiler

`scorec` compiles a v2 score into one role's v2 assembly, checked program, host image, and fit report. It uses the score parser and semantic checks in `code/score`, then assembles and statically checks output with `code/host2`.

```python
from scorec import compile_score

compiled = compile_score("path/to/protocol.score", "sender", "tx=O8", rate_hz=115200)
print(compiled.mas)       # generated, readable v2 assembly
print(compiled.report)    # resource allocation and calculated timing
image = compiled.image    # v2 host-write image
```

The role binding syntax maps input/output-capable wires to pins, for example `sck=P1/O1 cs_n=P2/O2 mosi=P0/O0 miso=P3/O3`; unidirectional outputs need only an output pin and inputs only an input pin. `rate_hz` overrides a generated/started/recovered clock's score rate. A follower score needs `follow_period` in chip cycles as its accepted maximum clock period. `compile_score` raises `CompileError` with a stable diagnostic code for parse, binding, fit, assembly, or static timing failures. Set `raise_on_check=False` to inspect generated output and diagnostics when only the machine static check fails.

## Accepted milestone subset

The first compiler milestone is exercised against the v2 cycle-level model and the independent `score.Codec` oracle:

- UART 8N1 sender and receiver, including bad stop-bit reporting and receiver clock error.
- SPI mode 0 controller as a full-duplex sender/receiver (the controller's physical trace is checked by the independent peer codec). The peripheral regression checks two external-controller transactions at 60- and 120-cycle periods, with frame decode, receive RAM, and stream/error flags.
- Ethernet 10BASE-T frame sender and receiver, including CRC-32, back-to-back receive, and rate-error checks.
- I2C controller and target (spec 16.2) on an open-drain wired-AND bus (`scorec/bus.py`, D35). The controller is checked against a behavioural target written in the test, including address NACK and three beats of clock stretching; the target against the codec's controller waveform at 25, 100 and 400 kHz, unaddressed requests, repeated starts, an abort on STOP inside the address, and a host-written address parameter. Bus traces are decoded by the independent `i2c_decode` checker and the reference codec.

### I2C host interface

```python
from scorec.bus import controller_tx, controller_rx, target_rx
c = compile_score(src, "controller", "scl=P0/O0 sda=P1/O1")
tx = controller_tx([(0x42, "w", b" "), (0x42, "r", 2)])   # stream 0 bytes; then a go byte in HOST.IN
t = compile_score(src, "target", "scl=P0 sda=P1/O1", follow_period=2400, params={"my_addr": 0x42})
t.host["params"]   # {'my_addr': {'data_addr': ..., ...}}: a data RAM byte, re-read after every START
```

Open-drain wires bind to the same `uio` index for input and output (R5). The controller's transmit stream carries the score's fields plus its choice bits (another write byte; repeated start or stop); HOST.OUT reports 0 (done) or 1 (address not acknowledged, stopped). Its receive stream holds the target's bits and is flushed at the stop. The target's receive stream adds record markers so the host can see the controller's choices; `target_rx` parses it. Each template docstring states the exact layout.

The compiler derives projections and waveforms from the parsed score AST; it does not import or read the reference codec. Tests may use that codec as a black-box waveform oracle. Generated timing and fit figures are static calculations at the assumed 60 MHz machine clock, not silicon measurements or timing-closure results. The reported burst-only upper rate bound is a necessary scheduling bound, not a validated maximum: trigger phase, tap quantization, snapshots and external input timing can impose lower limits. Interior taps that quantize to a disabled/boundary phase or collapse together are rejected.

Mailbox fields configure the shifter before loading each changed width/order, including frame-loop entry. Runtime CFG and LD use adjacent instructions (a simultaneous LD would use the old configuration); homogeneous eight-bit LSB frames retain their fast path. The one-byte mailbox has no FIFO or automatic frame stall. A host must supply each field before its scheduled read; high wire rates measured with an ideal producer do not establish sustainable host SPI throughput. The image loader enables dispatch before generated lines to avoid startup LATE/OVR and assumes a reset/stopped chip.

For generated-clock inputs sampled at an explicitly named local output edge, `E-TIME-IO` now rejects a boundary-to-sample budget below four cycles (registered output, two input synchronizers, capture of the previous synchronized value). This is a minimum pipeline check, not a proof of arbitrary interior transitions or external peer timing. Fractional/duration samples remain explicit choices. `code/score/examples/spi_mode0_late_sample.score` chooses a later return-data observation while preserving the wire clock; its75% request quantizes to phase4/6 at10MHz. Timing reports expose the quantization error. A peripheral must hold the returned data through the observation window; the original edge-sampled Score is not silently changed.

## Language extensions (part A 18)

- **Timing certificate** (`scorec.certify`, 18.1). `certify.written(src, events)` measures a score's `constrain` section on the reference codec's bus; `certify.compiled(src, trace)` measures a pin trace of a compiled image (one sample per chip cycle); `certify.report(...)` prints both tables and a verdict. Measurements over the frames supplied, not proofs; `UNTESTED` when no pair was seen. Checked in `code/tests/scorec/test_lang_ext_compiled.py` on the compiled UART sender (PASS, 520-521 cycle bit edges), I2C controller (tHD;STA 5.0 us and tSU;STA 10 us PASS, with a repeated START; O7 closed) and I2C target. Target output-enable staging now preserves at least the18-cycle/300ns internal hold; focused raw-pin model traces at25/100/400kHz measure22cycles/366.7ns, including paused-clock/restart/NACK cases. No external pull-up rise-time or hardware guarantee follows.
- **Layered scores** (`scorec.compile_layered`, 18.2). Compiles the lower protocol for the chip in the mapped role and returns the upper grammar's host codec (`host_runs(events)` gives byte runs and the silence after each; `host_decode(frames)` parses received frames). Modbus RTU requests over the compiled UART sender decode correctly with `score.layer.LayeredCodec` (3 random seeds). `compile_score` refuses a layered score with `E-LAYER`.
- **Enums and state** (18.3). Enum-typed fields compile exactly like their integer type (identical assembly). State updates (`NAME <- EXPR`) are refused with `E-UNSUPPORTED`; not yet lowered to data RAM and the accumulator.
- **Open crc range** `crc NAME over F1..*` is handled by `flatten.crc_range`.

## Current exclusions

Periodic productions such as Ethernet normal link pulses (`every ...`) are explicitly unsupported; `skip_periodic=True` is a test/helper escape hatch that compiles only the non-periodic frame path. Multiple independent score groups and general follower protocols are not implemented. Shared/open-drain wires compile only through the bus template, which accepts the spec 16.2 transaction shape (a repeated START may be several controller symbols, 16.2 uses `rstart start`) and rejects others with `E-UNSUPPORTED`; arbitration (`arbitrate`) and target clock stretching are not provided. The follower backend emits a constrained SPI mode-0 peripheral template for `select { own || peer }* deselect`, with recognised clock edges, one sampled peer wire, whole-byte fields, and a caller-provided `follow_period`. The SPI peripheral now passes full-duplex model checks over two external-controller transactions at 60- and 120-cycle periods, including no stream starvation. A focused abort-while-SCK-high regression checks return to idle low after CS_N rises. The transmit task is gated by the live select level so queued trailing edges cannot consume a rewound stream; deselection stops both lines before pulsing the output line to commit idle. Other score features may parse and validate but are not necessarily compilable; unsupported constructs fail with `E-UNSUPPORTED`.

Run the milestone checks from the repository root:

```sh
python -m pytest code/tests/scorec -q
```

## Stress, duet, mutation and coding additions (2026-11-14, V3 rival-ideas thread)

- **Stress projection** (`scorec/stress.py`). `compile_stressed(src, role, bind, [("tempo", ppm) | ("crc_init", bit) | ("const", byte, bit) | ("terminal", k, args)])` transforms the parsed score and compiles it unchanged, so each fault lands on the beat. The report starts `STRESSED:`. Each stress is checked by two codecs: the original score's codec must reject the waveform, and the stressed score's codec must accept it. A receiver compiled from the nominal score must also flag the fault (`test_stress.py`). `crc_init` corrupts the CRC by flipping an init bit rather than a CRC output bit, because the LFSR path only takes xorout 0 or all ones.
- **Coding in the sender** (`test_coding.py`):
  - `parity even|odd over F` is computed on LF0 as a width-1 CRC (poly 1; odd is xorout 1).
  - `bits ..., invert` complements every coded bit (fields, constants, CRC and parity), as the codec does.
  - MSB-first fields narrower than 8 bits are pre-shifted inside the load burst. Before this fix the sender sent them shifted one bit (the shifter's MSB mode starts at bit 7).
  - All three gaps were found by the transcription round trip.
  - Receivers, full-duplex senders and the bus template refuse parity and `invert` with `E-UNSUPPORTED`.
  - A frame may hold at most one crc or parity field.
- **Duet** (`test_duet.py`): controller and target, or sender and receiver, compiled from one score and wired back to back on two model chips, for UART, SPI mode 0, I2C (wired-AND, including an address NACK) and 10BASE-T. The wire is also decoded by the reference codec, and for I2C by `i2c_decode`.
- **Mutation** (`test_mutation.py`): every score mutant is killed. Mutants that compile are killed by the codec; two Ethernet mutants are rejected by the compiler (`E-UNSUPPORTED`, `E-TIME`). In 80 sampled single-bit image flips, 18 were killed and 62 were equivalent at the pins (identical `uo/uio/oe` on every cycle). None changed the pins without being caught. Results are in `data/processed/v3_rival/image_mutants_uart.json`.
- **Sweep** (`code/host2/sweep/uart_shmoo.py`, spot-checked by `test_sweep.py`): a shmoo of receiver sample point against sender rate error, written to `data/processed/v3_rival/uart_shmoo.{json,png}`.

The evidence is model-level only: v2 cycle model plus the reference codec. These additions have no RTL lockstep and no hardware results.

## Listener and autobaud (V3 plan, track C)

- **Listener projection** (`scorec/listener.py`, `spi_listener.py`; `compile_listener(src, "tx=P5")`). An input-only role projected from the same score: it binds input pins only (output pins are refused with `E-BIND`), has no `.out` block, and drives nothing (tests check every output-enable is 0 and the dedicated outputs never move). Frame protocols (UART, Ethernet receive) reuse the receive template with per-terminal violation flags; SPI mode 0 is a chip-select framed observer of both data wires. Each frame or transaction appends one record to a log in data RAM (record layout, ruler timestamp and status bits are in the `listener.py` docstring and in `compiled.host["listener"]`); `ListenerDecoder` decodes it into violations with the grammar terminal, its beat in the frame and a ruler tick timestamp (+-1 tick). Violations: framing (last terminal, or an SPI transaction ending inside a byte), grammar (earlier terminal), CRC, constant mismatch. Gaps: I2C bus monitor (refused with `E-UNSUPPORTED`), `arbitrate`/lost-arbitration fall-back (the compiler has no `arbitrate`), a timing-window violation code (edges outside the re-alignment window are ignored, not flagged), SPI clock activity while deselected, log holds 341 (UART) or 204 (SPI) records and then stops logging.
- **Autobaud, plan B** (`scorec/autobaud.py`, `code/host2/autobaud/lin_autobaud.py`; `compile_score(..., autobaud={})`). SPEC_V2 gives no move destination for a line's INC/MOD/taps/PRE, so a program cannot retime itself. The chip logs the six falling-edge intervals of a LIN break and 0x55 sync field; the host computes the bit time and rewrites line 0's divider and ARM bit. Tests: `code/tests/scorec/test_autobaud.py`; sweep record `data/processed/v3_autobaud/lin_sweep_115200.json`.

### Fixed-rate 8N1 receive envelope

`scorec.envelope.uart8n1_envelope(compiled)` computes the receive sample
cycles and a sender rate-error interval from the compiled line divider,
preset, sample tap, and static scheduler latency bound. The calculation
includes a one-cycle quantization and synchronization margin. Supply
`jitter_cycles` for additional edge displacement and `idle_bits` for a
guaranteed additional gap. Use `envelope.require(Fraction(4, 100))` to
check a required symmetric rate tolerance.

For the 1 Mbaud, 60 MHz test receiver with a 50% sample tap and contiguous
frames, the calculated interval is −4.594% to +4.348%, with open endpoints.
Every archived model sweep point inside the calculated intervals passed at
each of the seven tested tap positions. The calculation covers the fixed-rate
single-thread 8N1 template under the model's digital pin assumptions.
