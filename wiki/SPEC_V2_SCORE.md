# Metronome v2 specification, part A: the score language

Status: **draft 2, 2026-11-12. Design only.** No parser, compiler or reference codec implements this text yet. Every resource limit below is **calculated** from the v2 design (`BOTS/PLANS/V2_DESIGN.md` sections 4 and 8), not simulated.

Part B, the machine, is [SPEC_V2.md](SPEC_V2.md). Section 13 below states the resource-level contract the language needs from it. Where the two parts disagree, part B wins for machine behaviour and the difference is recorded in `BOTS/PLANS/DECISIONS.md`.

## 1. Purpose

A **score** is one text file that describes one protocol completely: wires, timing, waveforms, coding, framing and the exchange between the two ends. From one score the toolchain produces:

| Output | Used for |
|---|---|
| Chip image (configuration and thread programs) | Running either role on Metronome v2 |
| Reference codec (Python) | The definition of correctness: frame values to waveforms and back |
| Peer model | The opposite role, as testbench stimulus and checker |
| Host library | Sending and receiving frames by field name |
| Fit and timing report | Resources used, cycles per beat, fastest rate that fits |
| Timing diagrams | Documentation and the write-up |

Design goals, in priority order:

1. **Any protocol inside the envelope (section 14) can be written as a score**, including protocols nobody has designed yet. Odd behaviour drops to inline assembly (section 11); it is never unreachable because the language lacks a word.
2. **One score serves both ends.** Each role's behaviour is a *projection* of the one description (section 10).
3. **Every construct has both an encode and a decode meaning.** There are no send-only or receive-only fields.
4. **The compiler fails clearly.** A score that does not fit is rejected with a reason stated in protocol terms (section 12.3), never compiled into something that silently misbehaves.

Non-goal: general computation. The language is not Turing-complete.

### 1.1 Lineage

| Layer | Borrowed from | What we take |
|---|---|---|
| Grammar | Seawright and Brewer, *Clairvoyant* / production-based specification (DAC 1992, IEEE TVLSI 1994) | Hierarchical productions, compiled to a controller without enumerating states |
| Data-dependent fields | Knuth's attribute grammars; Kaitai Struct; Construct | Fields named and used later (`bytes[len]`); one definition both parses and builds |
| Branching | P4 parser graphs | Choose a production on a value already received |
| Roles | Multiparty session types (Scribble) | One global description, projected to each participant |
| Waveforms | WaveDrom wave strings | Symbols written as compact per-wire strings |
| CRC | Rocksoft ("Painless guide") CRC model | Any CRC from five parameters |

The difference from Clairvoyant is the claim: Clairvoyant synthesised a fixed controller per protocol, while a score compiles onto a fixed, reprogrammable chip. Because of that, resource fit, roles and the physical layer are part of the language.

## 2. Meaning

A score denotes, for each role R:

- a set of **frames**: records of named field values;
- a relation between frames and **waveforms**: the levels on each wire, beat by beat, that R drives and expects.

The relation has four layers, each defined by its own section:

```
 frame values      grammar (7), exchange (8)      which fields, in what order, driven by whom
      |
 bit sequence      coding (6)                     bit order, differential coding, stuffing
      |
 symbol sequence   symbols (5.3), recognise (5.4) which waveform each beat carries
      |
 wire levels       wires (5.1), clock (5.2)       pins, drive type, timing
```

The **reference codec** implements this relation directly in Python, and it is the definition of correctness for the compiler. For a standard protocol, the score is checked against the standard by independent decoders (section 15). For an invented protocol, the score *is* the specification.

## 3. Lexical rules

- `#` starts a comment, which runs to the end of the line.
- Keywords are lower case. Identifiers are `[A-Za-z_][A-Za-z0-9_]*` and case-sensitive.
- Numbers: decimal `42`, hex `0x2A`, binary `0b101010`, and two-digit bare hex inside `const` lists (`55 D5`).
- Quantities with units:
  - frequency: `Hz kHz MHz`
  - time: `ns us ms s`, `cycles`, `beats`
  - fraction of a beat: `%`
- A block is introduced by a keyword at the start of a line, and its contents are indented. Indentation is significant only to end a block.
- Strings appear only as wave strings (section 5.3), in double quotes.

## 4. File structure

```
protocol NAME [version N]
roles    ROLE, ROLE             # exactly two
use      LIBRARY                # optional: shared definitions (crc names, common symbols)

wire ...                        # 5.1, one or more
clock ...                       # 5.2, exactly one per line group
symbols ...                     # 5.3
recognise ...                   # 5.4, optional
bits ...                        # 6
crc ...                         # 9, optional
grammar ...                     # 7
abort ...                       # 8.3, optional
param ...                       # 10.3, optional
```

Sections may appear in any order; names are resolved over the whole file. A score with wires on more than one clock declares a `group` per clock (section 5.5).

## 5. Physical layer

### 5.1 Wires

```
wire NAME  DIRECTION [DRIVE] [idle LEVEL] [by ROLE]
```

- `DIRECTION` is one of:
  - `out`: driven only by the owning role.
  - `in`: driven only by the other role.
  - `shared`: either role may drive it (open-drain buses, half duplex).
  - `out`/`in` are written from the point of view of the role named in `by`; with no `by`, the first role in `roles`.
- `DRIVE`: `push-pull` (default for `out`) or `open-drain` (default for `shared`). For an open-drain wire, writing `1` means *release* (output enable off) and the level is set by an external pull-up.
- `idle`: `low`, `high` or `released`. This is the level held outside frames and after reset.
- `mirror NAME = !OTHER` declares a wire that always carries the complement of another (a differential pair driven from two pins).
- **Who drives a beat (D29).** An `out` wire is driven by its owner in every beat, whoever owns the beat's terminal, and an `in` wire is never driven. A `shared` wire is driven only by the owner of the beat's terminal; the other role releases it. A role never drives a wire it `follow`s. It may drive a wire it recovers from, or is started by, in beats it owns (tether's node drives `d` in its ACK slot) (D30). Comparisons are made on the resolved bus (wired-AND for open-drain), not on one role's drive.

Pins are **not** named in the score. A separate binding, given at load time, maps wire names to chip pins:

```
bind scl=P3/O3 sda=P4/O4      # input pin / output pin of the chip
```

So one score runs on any free pins, and the pin map stays a board decision.

### 5.2 Clock

```
clock RATE | free
  ROLE: MODE
  ROLE: MODE
  [split S1 [S2 [S3]]]
  [tolerance T]
```

The clock defines the **beat**: one bit time, or one time slot. Each role states how it obtains the beat:

| Mode | Meaning | Maps to (machine contract, section 13) |
|---|---|---|
| `generated` | The role makes the beat from the chip clock at `RATE` | Beat generator, free-running |
| `started by WIRE rise\|fall` | Generated, but the first beat starts at an edge (UART receive) | Beat generator, edge-started |
| `recovered from WIRE edges, window A..B` | Generated, re-aligned by edges that fall inside the window, given as fractions of the beat where edges are expected. The window may wrap through the boundary: `80%..20%` covers edges near the beat start, as with NRZ or NRZI data. The compiler maps it to a non-wrapping hardware window through `PRE` (part B 10.4) (D30). Used for Manchester and for NRZ/NRZI with transitions | Beat generator with edge re-alignment |
| `follow WIRE rise\|fall [, capture on WIRE rise\|fall]` | The other side's clock wire defines the beat; there is no rate | Follower mode, optional edge-sourced tap |
| `stretch on WIRE` (with `generated`) | After releasing WIRE, the beat stalls until it reads high | Beat-generator hold (part B 3.2a) |

`RATE` may be `free` when every role follows. `split` gives up to three fractions of the beat that divide it into **segments** (default `split 50%`). `tolerance` is the clock error the receiver must accept (default 2%), and it is used to check `window` and sample points.

Time references in the rest of the score are written in one of three ways:
- as a fraction of the beat (`at 62%`);
- as an edge (`at scl rise`);
- as a duration (`after 2 us`).

A role in `follow` mode may use only edge references and durations, because it has no beat length.

### 5.3 Symbols

A symbol is what one beat carries. Each symbol gives one wave string per wire that changes during it, and optionally a receive rule:

```
symbols
  NAME[(PARAM)]   WIRE "WAVE"  [WIRE "WAVE" ...]   [sample WIRE at TIME]
```

A wave string has one character per segment, or a single character for the whole beat.

| Char | Meaning |
|---|---|
| `0` `1` | Drive low or high. On an open-drain wire `1` means release |
| `z` | Release (output enable off) |
| `.` | Hold the level of the previous segment |
| `x` | Don't care (the compiler may choose) |
| a parameter name | The value of that 1-bit parameter |
| `!`param | Its complement |

A parameterised symbol such as `bit(d)` defines one symbol per parameter value, so `bit(0)` and `bit(1)` here. `bit(d)` with `sda "dddd"` is "SDA holds the data bit for the whole beat".

**Receive rule.** `sample WIRE at TIME[, TIME...]` names sample points for that wire. Sample points belong to the line, not the symbol: every beat is sampled at the union of the points named in any symbol, and the symbol a receiver reports is the one whose expected samples match. Samples that match no symbol report `violation`.

With no `sample` clause anywhere, the compiler derives the points. It prefers the middle of the latest segment that differs between symbols. If that would exceed R3, it may use a split point at which no candidate symbol changes level. Otherwise the score is rejected (E-FIT-TAP). The fit report says where the points landed (D29).

**Coded bits** use the parameterised symbol named `bit`, which every line that carries fields must define. Its parameters are, in order, the bit values of the `||` sides (7.8), or the single coded bit otherwise (D29).

**Fit rules per line.** These are checked against part B: section 8 for the pin tables, 3.4–3.5 for taps and capture, and `code/md2/machine.py`. They are derived from the tables, not simulated.

- **R1.** At most 16 transmitted symbols per line, counting each parameter expansion. The output symbol is 4 bits (`OSYM_BITS`).
- **R2.** Each wire's waveform may depend on at most 3 bits of the symbol, so a wire has at most 8 distinct waveforms. Each pin table takes 3 selected symbol bits plus `SEG` (`PIN_LUT_IN_BITS = 5`). The compiler chooses the symbol encoding so that every wire's waveform depends on at most 3 bits. If no such encoding exists, the score is rejected (E-FIT-ENC).
- **R3.** At most 4 segments per beat. R3 is counted **per role** on each line (D29). The split points of the symbols that role transmits, plus its sample points, use at most 3 taps. A sample point that coincides with a split point shares its tap; this is only valid if no symbol received there changes level at that point. `SEG` counts fired taps (0..3).
- **R4.** A line samples at most **two wires**:
  - wire A at up to three points;
  - wire B at exactly one point. In hardware, wire B is captured by tap 1, and the compiler assigns tap 1 to that point (D29).

  From those 4 samples and one remembered bit, the receiver gets 2 bits of class for free (two 32-entry input tables). That means at most 4 symbol classes, such as `0`, `1`, `idle` and `violation`, with differential codes decoded through the remembered bit. More classes need the raw capture (`L.CAP`) and cost instructions on every beat; the fit report says how many. Further wires can be watched through edge triggers and live pin guards (`recognise`, 5.4), not per-beat samples.
- **R5 (pins).** A wire the role ever releases needs an output-enable table. That covers `open-drain`, `shared` and `z` in a wave string. Output-enable tables exist only on output pins O0..O7, which are the bidirectional `uio` pins, so at most 8 such wires per loaded image. A `shared` wire that is both driven and read binds to `uio[k]` for both its input P_k and its output O_k. Push-pull outputs may use any of O0..O13; inputs any of P0..P12. The binding is rejected otherwise (E-BIND).

**O6 outcome (2026-11-12).** The 16-per-line and 8-per-wire limits are confirmed against the tables. D26's "at most 8 symbols" was the per-wire limit stated as a per-score one. The check added R4's two-wire sampling limit and R5.

### 5.4 Recognise

`recognise` defines events that are not beats: conditions a receiver must notice between or across beats.

```
recognise
  NAME[, NAME]   WIRE rises|falls while WIRE high|low
  NAME           no edge on WIRE for N beats | DURATION
  NAME           WIRE low|high for > DURATION
  NAME           WIRE rises|falls
```

Uses:
- I2C START and STOP: an SDA edge while SCL is high.
- End of frame on a self-clocked line: no edge for one beat.
- UART break, or a bus reset: a wire low for longer than a frame.

A recognised event can appear in the grammar as a terminal and in `abort` as a trigger. It maps to edge-triggered threads and watchers (section 13).

### 5.5 Groups

Wires that share one clock form a **group**, and a group compiles to one line. A score with independent clocks, such as UART with separate TX and RX, declares one group per clock:

```
group tx_side:  wire tx ...   clock ...
group rx_side:  wire rx ...   clock ...
```

At most 4 groups per loaded image, shared with any other loaded score.

## 6. Coding layer

```
bits ORDER [, differential [on 0|on 1]] [, stuff BIT after N equal|ones|zeros] [, invert]
```

- `ORDER` is `msb first` or `lsb first`. It applies to every multi-bit field unless the field overrides it (`u16 lsb first`).
- `differential`: NRZI-style. A data value of the named bit (default `on 0`) is sent as a change of level, and the other value as no change. Decoding uses the remembered bit of R4.
- `stuff`: counted on data bits **before** differential coding. After N equal bits (or N ones, or N zeros), insert BIT, or the complement of the run's value if BIT is omitted. Insertion is lazy: the stuffed bit is sent only if another coded bit follows. The receiver removes the bit, and the stuffed bit is not part of any field. A missing stuffed bit is a `violation`. With `differential on 0`, write `stuff 0 after N ones`, which guarantees a transition, as USB does (D29).
- **Differential reference.** Differential coding continues across terminals of one owner. At a change of owner (including after a `turnaround`), and at the start of each frame, the reference level resets to the wire's idle level (D29).
- `invert`: complement every bit.

Coding applies to fields only. Symbols written by name in the grammar (`start`, `mark`) bypass it, which is how framing marks can break the stuffing rule on purpose.

## 7. Grammar layer

### 7.1 Productions

```
grammar
  NAME[(PARAMS)] = EXPR
```

The first production is the **start production**. Productions may call each other but may not recurse; the compiler expands them, so nesting depth is bounded.

### 7.2 Expressions

| Form | Meaning |
|---|---|
| `A B` or `A` on one line, `B` on the next | sequence |
| `A \| B` | choice; must be decidable (7.6) |
| `A \|\| B` | full duplex: A and B occupy the same beats, with different owners (7.8) |
| `A*` `A+` `A?` | zero or more, one or more, optional |
| `A x N` | exactly N times; N is a constant or an earlier field |
| `{ ... } until COND` | repeat, testing COND after each pass |
| `{ ... } while COND` | repeat, testing COND before each pass |
| `A if COND` | A when COND is true, nothing otherwise |
| `switch EXPR { V1: A  V2: B  else: C }` | choose on a value |
| `NAME(ARGS)` | call a production; arguments are constants or fields |

### 7.3 Terminals

| Terminal | Meaning |
|---|---|
| `SYMBOL` or `SYMBOL(V)` | one beat carrying that symbol, bypassing coding |
| `name:bit` | one coded bit |
| `name:uN`, `name:sN` | an N-bit unsigned or signed integer, N ≤ 32 |
| `name:bytes[N]` | N bytes; N is a constant or an earlier field |
| `name:bytes until SYMBOL\|EVENT` | bytes until a symbol or recognised event (receive length = what arrived). If fixed-width fields follow it before the terminator, such as a CRC, the receiver splits their bytes off the end (D29) |
| `const B B B ...` | constant bytes (bare hex) |
| `const bits "0110"` | constant bits |
| `[name:] crc NAME over F1..F2` | a CRC field computed over a range of fields (9) |
| `[name:] parity even\|odd over F1..F2` | one parity bit |
| `gap DURATION\|N beats` | the line holds idle |
| `EVENT` | wait for a recognised event (5.4) |

### 7.4 Ownership and values

Each terminal has an owner, the role that drives it:

- `by ROLE` sets the owner. Without it, a terminal inherits the owner of the enclosing production, and the start production's owner is the first role.
- `name:TYPE by ROLE = EXPR` gives the value the owner drives: a constant, a parameter or an expression over earlier fields. Without `= EXPR`, the value comes from the host.
- `name:TYPE expect EXPR` checks a received value. A mismatch raises the `mismatch` event, which `abort` can catch; without a handler, the frame is reported to the host as failed.

### 7.5 Fields and expressions

A named field is in scope from its own end to the end of the enclosing transaction. Fields are L-attributed: a value can depend only on fields before it, so both roles can compute it in order.

Expressions use integers with `+ - * & | ^ ~ << >>`, comparisons, `&& || !`, `c ? a : b`, field names, parameters and constants. **Each expression must compile to a bounded number of instructions**; the fit report prints the cost of each one.

### 7.6 Decidability

Every choice must be decidable by the receiver, using:
- fields already received; or
- the next symbol or recognised event (one-symbol lookahead).

`body(0)` in the I2C example ends because the next symbol is `stop` or `rstart` rather than `bit`. That is decidable. A choice that needs two symbols of lookahead is rejected (E-AMBIG), with the two paths printed.

### 7.7 Data to and from the host

By projection (section 10):
- a field the executing role owns and has no `= EXPR` is read from the **host transmit stream**;
- a field the other role owns is written to the **host receive stream**.

The compiler lays both streams out in the order fields occur, and the host library names them. `hidden` on a field keeps it out of the receive stream; `notify` raises a host interrupt when it completes.

### 7.8 Full duplex

`A || B` places two field sequences on the same beats. It is how SPI, and any protocol where both ends send at once, is written.

- A and B must have different owners and drive different wires.
- Both sides must have the same length in bits, and that length must be known before the pair starts (from constants or earlier fields). Otherwise the score is rejected (E-DUPLEX).
- Bit i of A and bit i of B travel in the same beat. A symbol that carries both sides takes its parameters from both, in operand order (`bit(m, s)` in 16.3: m from the left side, s from the right).
- Neither side may contain a symbol terminal. Only bit order and `invert` apply under `||`; differential coding or stuffing on a duplex line is rejected (E-DUPLEX) (D29).
- **Projection.** Each role transmits its own side from its host transmit stream. In the same beat, it captures the other side into its receive stream. On the chip this is one burst per beat, moving one stream bit out and one sampled bit in (part B 6.3: two streams, one transmit and one receive).
- **Precedence.** `||` binds tighter than `|` and looser than sequence, so `a b || c d` pairs `a b` with `c d`.

## 8. Exchange

### 8.1 Time constraints

| Form | Meaning |
|---|---|
| `A within DURATION` | A must start within DURATION, or the `timeout` event is raised |
| `gap DURATION` | minimum idle between frames (inter-frame gap) |
| `turnaround N beats` | idle beats where wire ownership changes on a `shared` wire |
| `every DURATION: A` | run A periodically while the bus is idle (Ethernet link pulses) |

### 8.2 Retries

```
retry N { ... } on EVENT
```

Re-runs the block up to N times when EVENT occurs inside it. The transmit stream rewinds to the block's start.

### 8.3 Abort

```
abort
  on EVENT [in PRODUCTION] -> PRODUCTION | idle | report
```

`abort` is how a score says "this can interrupt anything". When the event fires inside the named production (or anywhere), the current production is abandoned and control resumes at the target. It is matched before the next beat is interpreted.

An expected symbol that would also raise an abort event is consumed by the grammar, not treated as an abort. Resumption unwinds to the innermost active call of the target production (D29).

Events:
- recognised events (5.4);
- `violation`, `mismatch` (7.4) and `timeout` (8.1);
- `lost`, raised by `arbitrate` (8.4).

### 8.4 Arbitration

```
arbitrate WIRE
```

On a `shared` wire, every beat the owner drives is read back. If the wire reads `0` while the owner released it, the owner raises `lost`, stops driving and continues as a receiver. This is CAN and multi-controller I2C arbitration. It requires a reaction within the beat (section 14).

## 9. CRC

```
crc NAME width W poly P init I [refin] [refout] xorout X
```

These are the five Rocksoft parameters, so any CRC up to 32 bits can be described. `use std` provides named ones: `crc32_ethernet`, `crc16_ccitt`, `crc16_usb`, `crc5_usb`, `crc8_smbus`, `crc15_can`.

A `crc` field is driven by its owner and checked by the receiver. A failed check raises `mismatch`. It maps to an LFSR unit.

## 10. Roles, projection and parameters

### 10.1 Projection

For each role R, the compiler derives R's local behaviour from the global grammar with these rules:

| Global construct | R owns it | The other role owns it |
|---|---|---|
| symbol terminal | transmit the waveform | expect it; report `violation` otherwise |
| field, no `= EXPR` | take the value from the host stream | capture to the host stream |
| field `= EXPR` | compute and transmit | capture; optionally `expect` |
| `crc`, `parity` | compute and transmit | check |
| choice / repeat on a value | decide | follow the received value |
| recognised event | (generate it, if it is a symbol) | detect it |

The chip runs one projection. The peer model runs the other.

### 10.2 Ownership rules

- Every terminal has exactly one owner.
- An `out` or `in` wire is driven only by its owner, in every beat (5.1). A symbol's wave string for such a wire describes the owner's drive, whichever role owns the terminal that selects the symbol. That is how the controller keeps clocking `scl` during the target's ACK beat (D29). The error case: a terminal's value (a symbol parameter) appears in the wave of a wire its owner cannot drive, because the wire's owner cannot know that value (E-OWNER).
- On a `shared` wire, consecutive terminals with different owners need a `turnaround` unless the drive is `open-drain`, where releasing is always safe.

These are checked statically (E-OWNER).

### 10.3 Parameters

```
param
  NAME : TYPE [= DEFAULT] [for ROLE]
```

A parameter is a runtime value that the host sets through the host link without recompiling: an address, a rate divisor, a timeout. Parameters may appear in any expression. The compiler emits a name-to-host-write map.

## 11. Escape hatch

```
name:u8 by ROLE asm {
  ; v2 assembly
}
```

A field, an event handler or a whole production may be written in assembly. The block states its contract in a header:
- `beats N` or `beats dynamic`
- `reads F, G`
- `writes stream|host`

The compiler places the block, checks the contract's beat count against the static timing check, and treats the block as opaque. The reference codec needs a matching Python function, given in a `model { }` block. Without it, the score is valid on the chip but marked **unverified**.

## 12. Compilation

### 12.1 Pipeline

```
score --parse--> AST --check--> projected per-role beat programs --allocate--> assembly + configuration --assemble--> image
```

The compiler emits readable v2 assembly, so its output can be checked by hand and diffed against hand-written programs.

### 12.2 Checks

Static, in order:
1. syntax;
2. names;
3. ownership (10.2);
4. decidability (7.6);
5. fit (R1-R4, units, groups);
6. timing: each beat's worst-case instruction path against the beat length, using the static timing check.

### 12.3 Diagnostics

Every rejection names the score construct, the limit and the number:

```
E-FIT-SEG   symbols: 'mark' needs 5 segments; a line has 4 (split points + 1)
E-FIT-TAP   clock: 3 split points + sample 'sda at 62%' need 4 taps; a line has 3
E-TIME      grammar: 'body' worst case 9 cycles per beat; beat is 6 cycles at 10 MHz
            fastest rate that fits: 6.67 MHz
E-AMBIG     grammar: choice in 'frame' needs 2 symbols of lookahead: 'idle idle' vs 'idle bit'
E-DUPLEX    grammar: '||' in 'transfer': 'out' is 8 bits, 'in' is 16 bits; both sides must be equal
E-OWNER     grammar: 'ack' owned by target puts its value on 'scl', which only controller drives
```

## 13. Machine contract (what part B must provide)

The language assumes the following resources (V2_DESIGN section 4). Exact behaviour is part B's to define.

| Language construct | Machine resource |
|---|---|
| group | line: beat generator (generated, edge-started, recovered, follower) with 3 taps |
| symbol | 4-bit staged and committed output symbol per line |
| wave string | per-pin tables over 3 symbol bits and the segment; output-enable tables |
| sample / receive | 2-bit input symbol from tables over 4 samples plus one remembered bit; raw capture readable |
| per-beat behaviour | threads (6) on 2 cores, triggered by beat, tap, pin edge, flag or host |
| `recognise`, `abort` | pin-edge triggers and per-thread watchers |
| fields, host streams | 2 stream units over 2 KB data RAM |
| `crc`, `parity` | 2 LFSRs |
| expressions | accumulator, counters, flags |
| `param` | host-written configuration and registers |

## 14. Envelope

These limits are calculated from the design, not simulated (V2_DESIGN section 8):

- **Rate:** up to about 10 Mbit at 60 MHz for one instruction per bit, alone on a core. Stuffing and per-beat expressions lower it, and the fit report gives the actual figure.
- **Reaction within a beat** (`arbitrate`, an acknowledge in the same bit): at least 4 cycles plus the wait to the next boundary. CAN at 1 Mbit has 60 cycles per bit.
- **Follower roles:** about 5 cycles from the other side's edge to our output, so target roles reach a few MHz (estimated).
- **Line code:** R1-R4 above.
- **Concurrency:** 4 groups, 6 threads.
- **Frames:** up to 2 KB of RAM shared by all streams. The host link (about 3.75 Mbit per second raw) is slower than Ethernet, so frames are buffered, not streamed.
- **Outside the envelope:**
  - multi-level or analog signalling;
  - more than 4 wires changing per beat in one group;
  - per-byte table lookups, such as 8b/10b;
  - frames larger than RAM.

## 15. Verification

| Link | Checked by |
|---|---|
| standard → score | independent decoders (the existing protocol checkers, sigrok decoders) read reference-codec waveforms |
| score → image | the image runs on the cycle-level model; its pins are decoded by the reference codec; frames are random |
| image timing | static check; sticky `LATE`, `OVR`, `CONFLICT`, `TAPMISS` as runtime witnesses |
| model → RTL → gates | lockstep on every pin, every cycle |
| both roles | the chip against the peer model, and the chip against itself in loopback (one role per group) |

Two rules:
- **Independence.** The reference codec and the compiler are two implementations of this document. They are written by different authors from this text, not from each other's code.
- **Random protocols.** A generator samples valid scores at random (symbols, coding, field layouts, CRC parameters, role splits) and pushes each through the score → image link in both roles. The result is reported as compiled, passed, or rejected by fit rule. This measures flexibility instead of asserting it.

## 16. Examples

These examples are written to this draft. None has been compiled.

### 16.1 UART 8N1

```
protocol uart_8n1
roles    sender, receiver

wire tx out push-pull idle high by sender

clock 115200 Hz
  sender:   generated
  receiver: started by tx fall
  tolerance 3%

symbols
  bit(d)   tx "d"          sample tx at 50%

bits lsb first

grammar
  line   = char*
  char   = bit(0)                     # start bit
           data:u8
           bit(1)                     # stop bit
           gap 0 beats
```

One wire, one segment, one sample point. The receiver's clock is restarted by every start bit, so drift does not accumulate. A full-duplex UART is two scores, or one score with two groups.

### 16.2 I2C, both roles

```
protocol i2c
roles    controller, target

wire scl out open-drain idle high by controller     # only the controller drives scl; the target reads it
wire sda shared open-drain idle high

clock 100 kHz
  controller: generated, stretch on scl          # hold, part B 3.2a
  target:     follow scl fall, capture on scl rise
  split 25% 50% 75%

symbols                                   # quarters of the controller's beat
  bit(d)   scl "0110"  sda "dddd"   sample sda at scl rise
  start    scl "1110"  sda "1100"
  rstart   scl "0110"  sda "1100"
  stop     scl "0111"  sda "0001"

recognise
  start_c   sda falls while scl high      # START or repeated START
  stop_c    sda rises while scl high

bits msb first

grammar
  bus          = transaction*
  transaction  = start request (rstart request)* stop

  request      = addr:u7  by controller
                 rw:bit   by controller
                 ack:bit  by target = (addr == my_addr) ? 0 : 1
                 body(rw) if ack == 0

  body(0)      = { data:u8 by controller
                   dack:bit by target = 0 }*                 # ends at stop or rstart

  body(1)      = { data:u8 by target
                   more:bit by controller } until more == 1  # NACK ends a read

abort
  on stop_c  -> bus
  on start_c -> request

param
  my_addr : u7 for target
```

Notes:
- **Target timing.** The target follows the *falling* SCL edge and captures on the rising one. It therefore changes SDA only while SCL is low, as I2C requires, at whatever rate the controller runs. This corrects the walkthrough version, which followed the rising edge.
- **ACK needs no special syntax.** It falls out of open drain plus ownership. The target pulls SDA low only on an address match. If no target matches, SDA floats high and the controller reads a NACK.
- **`scl` is `out` with open drain.** Only the controller drives it, including in the target's ACK and data beats, which keeps the clock from depending on beat ownership (D29). Clock stretching by a target, holding `scl` low, is visible to the controller through its hold. The target role in this score does not stretch.
- **The two `body` productions end differently.** `body(0)` ends by one-symbol lookahead (7.6). `body(1)` ends on a value the *other* role drives.

### 16.3 SPI mode 0, both roles

```
protocol spi_mode0
roles    controller, peripheral

wire sck  out idle low  by controller
wire cs_n out idle high by controller
wire mosi out idle low  by controller
wire miso out idle low  by peripheral

clock 1 MHz
  controller: generated
  peripheral: follow sck fall, capture on sck rise
  split 50%

symbols
  bit(m, s)  sck "01"  cs_n "0"  mosi "m"  miso "s"  sample mosi at sck rise  sample miso at sck rise
  select     sck "0"   cs_n "0"
  deselect   sck "0"   cs_n "1"

recognise
  cs_on   cs_n falls
  cs_off  cs_n rises

bits msb first

grammar
  bus      = transfer*
  transfer = select
             { out:u8 by controller  ||  in:u8 by peripheral }*
             deselect

abort
  on cs_off -> bus
```

`||` (7.8) pairs the controller's and the peripheral's bytes on the same beats. The `select` and `deselect` symbols bracket the transfer, and a peripheral sees `select` as the `cs_on` event.

### 16.4 10BASE-T Ethernet, one direction

```
protocol ethernet_10baset
roles    sender, receiver
use      std

wire   td out push-pull idle low by sender
mirror tdn = !td                    # the other half of the differential pair

clock 10 MHz
  sender:   generated
  receiver: recovered from td edges, window 33%..67%
  split 50%

symbols                             # Manchester: the edge in mid-beat carries the bit
  bit(d)   td "!dd"     sample td at 75%
  tpidl    td "1"                   # end-of-frame high
  nlp      td "1"                   # one beat high = 100 ns normal link pulse

recognise
  eof      no edge on td for 1 beats

bits lsb first

grammar
  link   = every 16 ms: nlp
           frame*
  frame  = const 55 55 55 55 55 55 55 D5
           body:bytes until eof
           fcs: crc crc32_ethernet over body     # sender: appended; receiver: last 4 bytes, checked
           tpidl x 2
           gap 9.6 us
```

The score describes one direction. A full-duplex station loads it twice, once in each role, bound to different pins: `sender` on the transmit pair, `receiver` on the receive pair. That is the general pattern for any link with independent directions, UART included.

### 16.5 An invented protocol: tether

This is a protocol designed for this document. It combines features no standard demo has together: one shared wire, a self-clocked differential code, bit stuffing with a start mark that data cannot produce, a length field, a CRC-8, and an acknowledge slot driven by the other role.

```
protocol tether
roles    host, node

wire d shared open-drain idle high

clock 500 kHz
  host: generated
  node: recovered from d edges, window 80%..20%     # data edges come at the beat boundary
  split 50%

symbols
  bit(v)   d "v"                           sample d at 37.5%, 62.5%
  mark     d "01"                          # 0 then 1 within a beat: never produced by data, which holds for the beat;
                                           # its mid-beat edge lies outside the window, so it does not re-align the clock

bits msb first, differential on 0, stuff 0 after 5 ones     # a stuffed 0 forces a transition

crc c8 width 8 poly 0x07 init 0x00 xorout 0x00

grammar
  bus      = request*
  request  = mark x 2
             addr:u8
             len:u8
             payload:bytes[len]
             check:crc c8 over addr..payload
             turnaround 1 beats
             ack:bit by node = 0  within 2 beats
             gap 4 beats

abort
  on violation -> bus
  on timeout   -> report
```

## 17. Open questions for the owner

| # | Question | Draft position |
|---|---|---|
| O1 | ~~Can `stretch` map to the beat generator?~~ | **Decided (owner, 2026-11-12):** yes, the beat-generator hold (part B 3.2a) |
| O2 | ~~Time written as fractions of the beat, or cycles?~~ | **Decided (owner, 2026-11-12):** fractions; the fit report prints the quantised cycle and the error |
| O3 | ~~Full-duplex fields for SPI~~ | **Decided (owner, 2026-11-12):** `\|\|`, section 7.8 |
| O4 | ~~Received control bits (ACK, `rw`) in the host stream by default?~~ | **Decided (owner, 2026-11-12):** yes, unless `hidden` |
| O5 | ~~One score per protocol, or allow several clocks per score?~~ | **Decided (owner, 2026-11-12):** groups (5.5); this supersedes D26's one-clock-per-file choice. Compiler support for more than one group is not yet implemented |
| O6 | ~~Symbol limit~~ | **Checked 2026-11-12** against part B 8 and `machine.py`: R1–R5 in 5.3 |

## Appendix A. Grammar of the score language (EBNF, informal)

```
score      = header { section } ;
header     = "protocol" ID [ "version" INT ] NL "roles" ID "," ID NL { "use" ID NL } ;
section    = wire | mirror | clock | symbols | recognise | bits | crc | grammar | abort | param | group ;
group      = "group" ID ":" NL INDENT { wire | mirror | clock } DEDENT ;
wire       = "wire" ID dir [ drive ] [ "idle" level ] [ "by" ID ] NL ;
dir        = "out" | "in" | "shared" ;
drive      = "push-pull" | "open-drain" ;
mirror     = "mirror" ID "=" "!" ID NL ;
clock      = "clock" ( QTY | "free" ) NL INDENT { ID ":" mode NL | "split" PCT { PCT } NL | "tolerance" PCT NL } DEDENT ;
mode       = "generated" [ "," "stretch" "on" ID ]
           | "started" "by" ID edge
           | "recovered" "from" ID "edges" "," "window" PCT ".." PCT
           | "follow" ID edge [ "," "capture" "on" ID edge ] ;
symbols    = "symbols" NL INDENT { ID [ "(" ID { "," ID } ")" ] { ID WAVE } [ sample ] NL } DEDENT ;
sample     = "sample" [ ID ] "at" time { "," time } { "sample" ID "at" time { "," time } } ;
recognise  = "recognise" NL INDENT { ID { "," ID } cond NL } DEDENT ;
bits       = "bits" ( "msb" | "lsb" ) "first" { "," coding } NL ;
grammar    = "grammar" NL INDENT { prod } DEDENT ;
prod       = ID [ "(" params ")" ] "=" expr ;
expr       = par { "|" par } ;
par        = seq { "||" seq } ;
seq        = item { item } ;
item       = atom [ "*" | "+" | "?" | "x" value ] [ "if" cond ] [ "within" QTY ] ;
atom       = terminal | ID [ "(" args ")" ] | "{" expr "}" ( "until" | "while" ) cond
           | "switch" value "{" { value ":" expr } [ "else" ":" expr ] "}" | "every" QTY ":" expr ;
terminal   = ID ":" type [ "by" ID ] [ "=" value | "expect" value ] [ "hidden" ] [ "notify" ]
           | "const" { HEX } | "const" "bits" WAVE | "gap" QTY | "turnaround" INT "beats" ;
```

The appendix is informative. Section text wins over it.
