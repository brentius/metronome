# Score reference implementation: notes and spec readings

Package: `code/score/score/` (parser, checks, projection, reference codec). Tests: `code/tests/score/`
(`python -m pytest code/tests/score` from the repository root; 137 tests).
Written from `wiki/SPEC_V2_SCORE.md` part A only (draft 2, 2026-11-12). The earlier partial files for the superseded
format were deleted, not reused. Status of every claim here: **RTL-independent, verified in Python against the
spec examples and the independent decoders in `code/tests/checkers/protocols.py`**; nothing here is compiled,
synthesised or measured.

## Layout

| Module | Role |
|---|---|
| `lexer.py`, `parser.py`, `ast.py` | Tokens with line:column, recursive descent, AST. Syntax errors carry `line:col`. |
| `model.py` | Wave strings, symbol instances, expressions, beat/segment arithmetic |
| `analysis.py` | One-symbol-lookahead FIRST sets (E-AMBIG), bit lengths (E-DUPLEX) |
| `checks.py` | Names, ownership, decidability, duplex, fit R1-R5, `check_binding` |
| `project.py` | Role projection (10.1) as an annotated tree plus host stream layouts |
| `codec.py` | `Codec.encode / encode_all / decode` at chip-cycle (60 MHz) resolution |
| `crc.py` | Rocksoft CRC and the `use std` table |

## Codec interface (a compiler author needs this)

* Time is chip cycles at 60 MHz. Beat length is `60e6 / rate` cycles, exact (a `Fraction`), so 115200 Hz gives 520.83.
  Beat k starts at `T0 + k*P`; segment j starts at `ceil(T + boundary_j * P)`. A level at cycle c is the level of the
  segment containing cycle c.
* Events (input of encode, output of decode) are tuples: `("addr", 0x50)` for a named field (bytes for `bytes`
  fields), `("start",)` for a named symbol terminal with no parameter, `("abort", "stop_c")` for an abort trigger.
  Parameterised framing symbols (UART `bit(0)`, `bit(1)`) and `const` bytes are not events.
  A symbol event may be omitted when only one path is possible (it is then generated); it must be present at a
  decision (`(rstart request)*`, `transaction*`). A field with `= EXPR` or a `crc` may be omitted (computed) or given
  (fault injection).
* `encode(role, events)` returns that role's drive waveform (0, 1, or `None` = released). `encode_all` returns every
  role's drive plus the resolved bus (open-drain and `shared` wires are wired-AND with a pull-up; push-pull conflicts
  raise). `decode(role, bus)` takes the resolved bus and returns `DecodeResult(events, ok, notes)`.
* Frames must be followed by idle, and a frame's first beat must leave the idle level (decode needs an edge to align
  to). `ok=False` carries violations and mismatches (`notes`), decode continues where it can.

## Readings chosen where the spec is silent or inconsistent

Items 1-8 are inconsistencies or gaps a compiler author must be told about; the rest are interpretations.

1. **Derived sample points make tether violate R3 (and would make I2C).** 5.3 says that with no `sample` clause the
   point is the middle of the latest differing segment. Tether (split 25/50/75, no `sample`) then needs a 4th tap at
   87.5 % (R3 allows 3). Reading kept so the example stays valid: derive sample points **only when the score has no
   explicit `sample` clause at all** (I2C's `start/rstart/stop` are seen through `recognise`), and when the derived
   point would need a 4th tap, **place it at the start of that segment**, which is a split point and shares its tap
   (75 % for tether; irrelevant for the codec, which compares whole symbols).
2. **R4 "wire B only at tap 1" versus SPI.** SPI has one tap (50 %) and samples two wires there. Read as: tap 1 is a
   hardware register index, not "the second tap in time"; the check is "the second sampled wire is sampled at one point".
3. **Differential coding on the open-drain tether wire, acknowledge slot.** `ack:bit by node = 0` is sent as a *level
   change* (differential on 0). If the previous line level were 0 the change is to 1 = release, so the acknowledge
   would be invisible and an absent node would read as an ACK. Reading kept: `turnaround` releases the wire, so the
   differential reference becomes the idle level (1) at a turnaround. Then ACK = node pulls low, absent node = no change
   = NACK. The spec does not say what happens to the remembered bit across a turnaround.
4. **Tether `stuff 1 after 5 equal`.** Meaning of BIT and of "equal" is not defined. Implemented: stuffing works on the
   data bits (before differential coding), counts N equal data bits, then inserts BIT (the complement if BIT is omitted).
   The stuffed bit starts a new run. Consequence: after five 1s a stuffed 1 sends "no change" on a `differential on 0`
   line, so it does not create an edge; the example's stuffing never breaks a run of ones on the wire. A designer
   probably meant `stuff 0` or a line-level reading. Round trips are still correct.
5. **Which symbol carries a coded bit.** 5.3, 6 and 7.3 never say how `name:u8` maps to a symbol. Required: a symbol
   named `bit` (all five examples have one); its parameters are the coded line bit (differential/stuffing/invert are
   applied to produce it). E-NAMES if a field is used and there is no `bit`.
6. **`||` parameter order.** `bit(m, s)` takes the first parameter from the left side of `||` and the second from the
   right (positional). Lengths must be known and equal; a `||` side that contains a symbol terminal is rejected (a
   beat is not a bit). Differential and stuffing are rejected with `||` (side lengths would diverge).
7. **Who drives what in a beat.** Not defined for beats owned by one role on wires owned by the other. Reading: an
   `out`/`in` wire is always driven by the wire's owner; a `shared` wire is driven by the owner of the beat's terminal(s)
   only. So in I2C the target's acknowledge beat has the target drive both `sda` and `scl` (`scl "0110"`), and the
   controller releases both; wired-AND makes the bus identical to the real one. A role's own `encode()` waveform is
   therefore incomplete for the beats it does not own; always compare the resolved bus.
8. **`body:bytes until eof` and the FCS (16.4).** The comment says the receiver takes the last 4 bytes as the FCS, but
   `until eof` has already consumed them. Implemented for the pattern `F:bytes until X` immediately followed by a crc
   field whose range ends at `F`: decode captures the bytes, splits the trailing crc-width bytes off, reports `F` without
   them and checks the crc. `eof` ("no edge on td for 1 beats") fires when no edge arrives within N beats x (1 + tolerance)
   + 1 cycle of the last edge; the extra cycle absorbs chip-clock quantisation of edge times.
9. **Role of `follow` and `recovered` in the codec.** The codec decodes on a beat grid derived from the clock `RATE`.
   `recovered`: each beat is re-aligned on the first edge of the wire inside the window (to the window centre); edges
   outside the window are ignored. `follow`: after each beat the next one is re-timed from the capture (or follow) edge
   within +-30 % of the beat. `started by`: re-armed at the previous beat's sample point after every `gap`. Acquisition
   of the first beat aligns the first departure from idle to the first departure of the candidate next symbol.
10. **Abort.** "Matched before the next beat is interpreted" is implemented as: an abort rule applies to a beat that no
    expected symbol matches and that fires the event (or a `violation`). An expected symbol that raises the same event
    (`stop` for `on stop_c -> bus`) is consumed by the grammar, so decode output equals the encode input. Resumption
    unwinds to the innermost active call of the target production (`-> request` restarts the request, the loop
    after it continues); `-> idle` stops decoding, `-> report` also records a `report` event. The beat that carries
    the event is consumed.
11. **Precedence of `||`/`|` inside expressions.** `|` and `||` are grammar operators, so inside field values and
    conditions they are bitwise/logical operators only in parentheses.
12. **`every`, `retry`, `within`, `arbitrate`, `asm`, `model`.** Parsed and checked (`retry N { } on EVENT`, top-level
    `arbitrate WIRE`, `asm { }` with `beats/reads/writes` header and `model { }` captured raw). Codec: `every` is skipped
    (link pulses are background), `retry` runs the block once, `within` is ignored, `asm` raises NotImplementedError.
    `every QTY: ITEM` binds one item, so `link = every 16 ms: nlp  frame*` means the pulse runs periodically and
    `frame*` follows.
13. **CRC input.** Covered fields are serialised to bytes in transmit order (a `u16 lsb first` field contributes little-endian
    bytes; `bytes[N]` its bytes) and processed per Rocksoft (`refin` = each byte LSB first), so `crc32_ethernet`
    equals `zlib.crc32`. Covered widths must be multiples of 8. The crc value is sent as a field of its width in the
    `bits` order (`lsb first` gives little-endian bytes, as Ethernet requires). The range `F1..F2` is the latest
    occurrence of F2 and the nearest F1 before it.
14. **Coder state.** The stuffing run resets at a bypass symbol and at `gap`; the differential reference is the data
    wire's idle level at stream start and `gap`, its final-segment level after a bypass symbol that drives it (so after
    tether's `mark "0010"` it is 0), and the idle level after `turnaround`. Stuffing is lazy: the stuffed bit is sent
    only when another coded bit follows. Order: stuff, differential, invert.
15. **Diagnostics added.** Codes beyond 12.3: `E-FIT-SYM` (R1), `E-FIT-SMP` (R4), `E-FIT-PIN` (R5, more than 8 released
    wires), `E-FIT-GROUP`, `E-BIND`, `E-NAMES`. `E-FIT-ENC` is a real search for a 4-bit symbol encoding in which each
    wire's waveform depends on at most 3 bits (`checks.find_encoding`).
16. **Defaults.** No `bits` line means `msb first`; a push-pull wire without `idle` idles low, an open-drain or `shared`
    wire released (high through the pull-up). Parameters in wave strings are single letters (`x` and `z` reserved).
    The wave character `x` holds the previous level in the codec. `use std` is the only library.

## Not implemented

`asm` execution, `every` timing, `retry` re-runs, `within` timeouts and the `timeout` and `lost` events, `arbitrate`
read-back, `sample` clauses as such in decode (symbols are matched by their whole waveform at segment midpoints, a
stricter test than the chip's sampled classes), multi-group codec (parse and check only), `level_for` recognise
events, and the cost report for expressions beyond `model.expr_cost`.

## Update for spec decision D29 (2026-11-12)

Items 1-8, 10 and 14 above are now normative in the spec (samples per line with comma lists, R3 per role, who-drives,
`bit` symbol, `||` rules, bytes-until split generalised, abort, coding resets). The code follows D29:
E-OWNER now means "a terminal's value (symbol parameter, not a constant) is in the wave of an `out`/`in` wire its owner
cannot drive"; `||` rejects symbol terminals, differential and stuffing (E-DUPLEX); the differential reference
resets to idle at owner change, `turnaround` and `gap`/frame start; `bytes until X` splits any run of fixed-width
fields that follows it (not only a CRC) off the end.

New ambiguities found while applying D29:
* **Tether fails R3 per role.** Host transmits `mark` (3 split points) and receives the ACK `bit`, sampled at 37.5 % and
  62.5 %: 5 taps (4 even if the unused 25 % split is merged away). The checker reports E-FIT-TAP for the tether example;
  the test asserts exactly that, and `Codec(score, strict=False)` skips E-FIT-* so the codec tests still run on it.
  No reading of D29 keeps it valid (it would need transmit and receive taps to be counted separately).
* **"A role never drives its clock-source wire" (5.1) contradicts tether**, where the node is `recovered from d edges`
  and drives `d` in the ACK slot. Implemented only through the other rules (out wire: owner; shared: terminal owner), so
  the sentence has no effect; the node does drive `d`.
* R3 "transmitted splits": a role needs the split taps if it drives a multi-character wave on a wire (its out wire,
  or a shared wire in a beat it owns); a received sample shares a split tap only if no symbol it receives changes level
  on that wire at that boundary.
* Derived points (no `sample` anywhere): middle of the latest differing segment; else a split where no symbol changes
  that wire's level; else E-FIT-TAP (checked against every role).

## Update for part A 18, language extensions (2026-11-14)

New modules: `constrain.py` (timing constraints measured on a waveform, 18.1) and `layer.py` (library scores in
`code/score/lib/`, layered-score checks, `ByteCodec` and `LayeredCodec`, 18.2). New AST nodes: `Constraint`,
`TEvent`, `EnumDecl`, `StateDecl`, `Assign`; `Score` gained `constraints`, `enums`, `states`, `imports`, `over`
(all defaulted). Lexer: `<-` and a single `.` are now operators. Parser: enum members are pre-scanned so `NAME:`
ends a sequence inside a switch (a field may not share a member's name); an unknown type name is an enum, resolved
after the whole file is read (E-NAMES if none). Checks: `check_extensions` (names of the new declarations) and the
role-consistency rule `role_expr` (E-ROLE, 18.4). Codec: enum members and state in the environment; state kept per
(direction, role) on the `Codec` across calls (`reset_state()`); enum names accepted on encode; a received non-member
raises `mismatch`. Tests: `code/tests/score/test_lang_ext.py` (34).

Readings chosen:
* **Constraint pairing.** Each A pairs with the first B strictly after it. `when W L` requires W at L on both cycles of
  the edge, so an edge coincident with a W change is not counted. A released drive reads as the pull-up.
* **Frame split in `LayeredCodec.decode`.** An idle run of at least 2/3 of the smallest upper `gap`; each split frame is
  decoded with 8 cycles of lead and at least one character of tail.
* **`<-` lexing.** `a<-1` lexes as a state update; write `a < -1` for a comparison with a negative number.
* **Role mapping in layering** is positional; every upper field must be owned by the role that drives the lower payload.

## Update for spec decision D30 (2026-11-12)

The two D29 findings above are resolved in the spec: tether (`split 50%`, `mark d "01"`, node window `80%..20%`) now passes all
static checks in strict mode (`strict=False` is no longer used by the tests), and 5.1 narrows the clock-wire rule.
Code: the parser accepts a wrapping recovery window (A > B; only A = B is rejected); `recovered` decode re-aligns on edges
in `[0, B]` (to the beat start) or `[A, 100%]` (to the next boundary), ignoring mid-beat edges; a role never drives a wire it
`follow`s (no effect on the five examples). Tether decodes with ±1.5 % sender clock error. 140 tests pass.
