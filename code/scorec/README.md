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

The compiler derives projections and waveforms from the parsed score AST; it does not import or read the reference codec. Tests may use that codec as a black-box waveform oracle. Generated timing and fit figures are static calculations at the assumed 60 MHz machine clock, not silicon measurements or timing-closure results.

## Current exclusions

Periodic productions such as Ethernet normal link pulses (`every ...`) are explicitly unsupported; `skip_periodic=True` is a test/helper escape hatch that compiles only the non-periodic frame path. Multiple independent score groups, shared/open-drain wires, and general follower protocols are not implemented. The follower backend emits a constrained SPI mode-0 peripheral template for `select { own || peer }* deselect`, with recognised clock edges, one sampled peer wire, whole-byte fields, and a caller-provided `follow_period`. The SPI peripheral now passes full-duplex model checks over two external-controller transactions at 60- and 120-cycle periods, including no stream starvation. A focused abort-while-SCK-high regression checks return to idle low after CS_N rises. The transmit task is gated by the live select level so queued trailing edges cannot consume a rewound stream; deselection stops both lines before pulsing the output line to commit idle. Other score features may parse and validate but are not necessarily compilable; unsupported constructs fail with `E-UNSUPPORTED`.

Run the milestone checks from the repository root:

```sh
python -m pytest code/tests/scorec -q
```
