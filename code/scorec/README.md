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

The compiler derives projections and waveforms from the parsed score AST; it does not import or read the reference codec. Tests may use that codec as a black-box waveform oracle. Generated timing and fit figures are static calculations at the assumed 60 MHz machine clock, not silicon measurements or timing-closure results.

## Current exclusions

Periodic productions such as Ethernet normal link pulses (`every ...`) are explicitly unsupported; `skip_periodic=True` is a test/helper escape hatch that compiles only the non-periodic frame path. Multiple independent score groups and general follower protocols are not implemented. Shared/open-drain wires compile only through the bus template, which accepts the spec 16.2 transaction shape and rejects others with `E-UNSUPPORTED`; arbitration (`arbitrate`), target clock stretching and the I2C 300 ns internal SDA hold are not provided (the target changes SDA about 4 cycles after SCL falls, estimated). The follower backend emits a constrained SPI mode-0 peripheral template for `select { own || peer }* deselect`, with recognised clock edges, one sampled peer wire, whole-byte fields, and a caller-provided `follow_period`. The SPI peripheral now passes full-duplex model checks over two external-controller transactions at 60- and 120-cycle periods, including no stream starvation. A focused abort-while-SCK-high regression checks return to idle low after CS_N rises. The transmit task is gated by the live select level so queued trailing edges cannot consume a rewound stream; deselection stops both lines before pulsing the output line to commit idle. Other score features may parse and validate but are not necessarily compilable; unsupported constructs fail with `E-UNSUPPORTED`.

Run the milestone checks from the repository root:

```sh
python -m pytest code/tests/scorec -q
```
