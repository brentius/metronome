# Architecture: a beat-synchronous protocol engine

Working name: Metronome (placeholder). Status: proposal, 2026-11-10. Nothing here is implemented, synthesized or simulated yet. Every number carries its evidence class, as `AGENTS.md` requires.

This document is the hand-off for planning. It fixes the shape of the machine and the reasons for it. It deliberately leaves the instruction encoding, unit counts and pin map to the builder, and section 13 lists what is fixed and what is open.

## 1. What we are building and why

The competition asks for a chip that can be reprogrammed after fabrication to speak protocols it was not designed for. The usual answer is a tiny processor that toggles pins and counts clock cycles, in the style of the RP2040 PIO. That style has four weaknesses:

1. Timing depends on instruction count, so every code path has to be balanced by hand.
2. There is no first-class way to lock onto the other side's clock.
3. There is no arithmetic for CRC or bit stuffing.
4. A timing mistake is silent: the waveform is simply wrong.

This design removes all four with one idea: **the program runs on the wire's own bit clock, not on the chip's clock.** Hardware recovers or generates a bit clock (the *beat*). Code runs in short bursts between beats. Pin reads and writes are tied to the beat, never to the instruction that issued them. A burst that does not fit its beat raises a flag.

Primary demonstration target: 10 Mbit Ethernet (10BASE-T), transmit and receive, with the CRC computed on-chip. UART, SPI and I2C come first as the baseline. Low-speed USB is a stretch.

## 2. Goals, non-goals, anti-goals

**Goals**

- Run 10 Mbit Ethernet transmit and receive concurrently at a 60 MHz clock, with preamble, framing and the 32-bit frame check done on-chip.
- Run UART, SPI (modes 0 to 3) and I2C (100 and 400 kHz) from the same hardware by loading a different program.
- Make pin timing independent of which branch the code took.
- Make every timing violation visible as a sticky flag, never a silently wrong waveform.
- Keep the machine modular: each datapath unit sits behind one uniform port interface and can be added, removed or resized without touching the instruction decoder.
- Give verification a clean split: programs are checked at beat level, the hardware is checked once against the beat-level contract.

**Non-goals**

- Speeds above about 10 Mbit. The clock is 60 MHz and the pads allow roughly 66 MHz output (Tiny Tapeout estimate).
- Analog front ends. Ethernet receive needs a line receiver on a Pmod; that is board work, not chip work.
- A general-purpose CPU. The demo board's RP2350 is the host for anything above frame level.
- Real-time streaming of Ethernet payload to the host. Frames are stored in on-chip RAM and moved to the host afterwards.

**Anti-goals** (the entry fails if it becomes one of these, even if it works)

- A UART block, an SPI block and an I2C block behind a mux. The post rejects this explicitly.
- Datapath units that only make sense for one protocol. Every unit must be justified by at least three unrelated protocols.
- A pile of unrelated clever features. The write-up has to be explainable from the single idea in section 1.

## 3. Constraints and the numbers this design rests on

| Fact | Value | Evidence |
|---|---|---|
| Process and flow | IHP 130nm CMOS5L, Tiny Tapeout IHP Verilog template, 8x4 tiles | Competition post |
| Die for an 8x4 design | 1724.16 x 710.64 µm, about 1.22 mm² | Literature: PRISM SRAM walkthrough (another entrant's 8x4 layout), not re-measured |
| Pins | 8 in, 8 out, 8 bidirectional, plus clock and reset. No analog pads | Competition post |
| Clock | 60 MHz from the demo board is confirmed acceptable. Whether our logic closes timing there is unknown | Competition post; closure assumed |
| Pad round trip | About 10 ns; output up to about 66 MHz | Tiny Tapeout estimate quoted in the post. No silicon yet |
| One flip-flop | About 52 µm² | Literature: PRISM SRAM walkthrough |
| One SRAM macro bit | Under 5 µm² | Literature: same |
| `RM_IHPSG13_1P_512x32_c2_bm_bist` | 416.64 x 191.34 µm, about 0.08 mm², 6.5% of the die | Literature: same |
| SRAM read | Synchronous, data valid one clock after the address | Literature: same. Access time not stated |
| Routing over an SRAM macro | Blocked on Metal2 to Metal4; signal pins on one long edge | Literature: same |
| Cycles per bit at 60 MHz | UART 115200: about 520. I2C 400 kHz: 150. Low-speed USB: 40. Ethernet: 6, which is 3 per Manchester half-bit | Calculated |
| Clock drift over a maximum Ethernet frame | About 2.4 bits at ±100 ppm per end (12,144 bits x 200 ppm) | Calculated; the tolerance figure is from memory of IEEE 802.3 |

Two consequences drive the whole architecture.

- **Configuration held in flip-flops costs about ten times the area of configuration held in SRAM.** An SRAM delivers one word per clock. So the area-efficient reprogrammable machine in this flow consumes its configuration as a stream of words, which is an instruction stream. Spatial fabric (lookup tables with configuration in flops) is affordable only in small amounts, so it is placed only where a reaction within one 60 MHz cycle is needed.
- **Ethernet leaves 6 cycles per bit.** Per-bit work must fit in one or two instructions, so each instruction must do several things at once.

SRAM macros available in the PDK (file listing of `IHP-Open-PDK/ihp-sg13g2/libs.ref/sg13g2_sram/lef`, read 2026-11-10): single-port 64x16, 64x64, 256x8/16/32/48/64, 512x8/16/32/64, 1024x8/16/32/64, 2048x32/64, 4096x8/16, 8192x32; dual-port 64x22, 64x32, 256x8/16/32, 512x8/16/32, 1024x16/32. Only the 512x32 footprint is known to us. Read the other footprints from the LEF files before fixing the memory plan.

## 4. Vocabulary

| Term | Meaning |
|---|---|
| Beat | One period of a protocol's bit clock, produced by a beat generator |
| Tap | A programmable point inside a beat, used to sample inputs or change output segment |
| Segment | The part of a beat between two taps. A beat has up to four |
| Symbol | A 2-bit value an engine emits or receives once per beat. The pin cells turn symbols into waveforms and back |
| Engine | One thread of control: a program counter, a binding to a trigger, and a little state. Engines own no datapath |
| Burst | The instructions an engine runs from one trigger until it pauses. A burst never loops |
| Core | Fetch and execute hardware. A core runs one burst at a time, for whichever of its engines is ready |
| Unit | A datapath block (shifter, counter, LFSR and so on) reached through ports |
| Commons | The pool of units, shared by all engines. The toolchain allocates units to engines |
| Move | The only operation: copy a source port to a destination port, under a guard |

## 5. Block diagram

```
 pins (8 in, 8 bidir)                                pins (8 out, 8 bidir)
        |                                                    ^
   synchronisers, edge detect                           pin cells: lookup
        |                                               tables turning
        +---------> beat generators (x4) ---segment---> (symbol, segment)
        |             rational divider,                 into pin level and
        |             windowed edge re-alignment        output enable
        |                  | trigger, commit                 ^
        v                  v                                 | staged symbols,
   input capture ----> engines (x6): PC, trigger binding,    | committed on
   at taps, lookup     watchers, staged symbol               | the beat
   table to symbol          |                                |
                            v                                |
                 core A              core B                  |
                 program SRAM        program SRAM            |
                 3 move buses        3 move buses -----------+
                        \              /
                         unit commons
        shifters, counters, LFSRs, accumulator, flags, RAM pointers
                              |
                 data SRAM (frame buffer, tables)
                              |
                 host link (SPI target) <----> RP2350 on the demo board
```

## 6. The blocks

Counts and widths below are starting values and my call. They are parameters, to be set after the sizing run in section 12.

### 6.1 Pin front end

Two-flop synchronisers on all 16 inputs, then rising and falling edge detectors. All outputs are registered. The path from pad to engine and from engine to pad is therefore a fixed number of cycles, and "cycle-exact" in this document means exact up to that constant.

### 6.2 Beat generators (x4)

Each generator is a rational divider: every clock, `phase += inc`; when `phase >= mod`, subtract `mod` and start a new beat. The beat rate is `clock x inc / mod`, exact in the long run with at most one cycle of jitter. Ethernet is `inc = 1, mod = 6`. 115200 baud is `inc = 6, mod = 3125` (calculated: both exact at 60 MHz). Width: 20 bits, enough for the 16 ms Ethernet link pulse interval (960,000 cycles, calculated).

Each generator also has:

- **Three taps**, as phase thresholds. They split the beat into up to four segments and mark when inputs are sampled.
- **Edge re-alignment.** On a chosen edge of a chosen pin, the phase is set to a preset value. The edge is accepted only if the phase is inside a programmable window. This one mechanism covers UART start-bit alignment (window open, preset to mid-bit), Manchester recovery (window around the expected mid-bit edge, so bit-boundary edges are ignored), and CAN and USB resynchronisation.
- **A `sync_seen` status bit**, set when an edge was accepted during the current beat. A missing edge is how Manchester idle, a line-code violation or carrier loss shows up.

### 6.3 Pin cells: the fabric

Everything faster than a beat lives here, in lookup tables that run at the full clock rate. This is the only spatial fabric in the design, for the area reason in section 3.

- **Output cell**, one per output pin and one per bidirectional pin: a 4-input lookup table over `{symbol[1:0], segment[1:0]}` of a selected engine, giving the pin level. Bidirectional pins get a second table for output enable. Manchester is "symbol 0: high then low; symbol 1: low then high; symbol 2: low throughout". An SPI clock, an I2C clock with data changing while the clock is low, an open-drain line and a WS2812 pulse are all just different tables.
- **Input cell**, two per engine: the engine selects two pins. Pin A is captured at each of the three taps and pin B at the middle tap. Two 4-input lookup tables over those four captured bits give the engine's 2-bit input symbol. A majority vote for UART, a Manchester bit, or the J, K and single-ended-zero states of USB are each one table.
- **Optional fifth input** on output cells, selecting any synchronised input pin. This gives pass-through with modification: the engine's symbol chooses pass, invert, force low or force high, with a fixed two-to-three-cycle latency. Include it only if the sizing run shows room.

Cost of the baseline: 24 output tables of 16 bits plus selects, about 430 flops, about 2% of the die (estimated from the 52 µm² flop figure).

### 6.4 Engines (x6) and bursts

An engine is a program counter plus:

- a **trigger binding**: a tap of one beat generator, a pin edge, a flag raised by another engine, or a host doorbell;
- a **staged output symbol**, written by moves and committed to the pin cells at the next beat boundary;
- two **watchers**, each a condition and a handler address. At a trigger, if a watcher's condition holds, the program counter is replaced by the handler address before the burst starts. This is how timeouts, line idle, bus reset and aborts from another engine are handled without polling.

On a trigger the engine becomes ready. Its core runs instructions from the engine's program counter until an instruction marked `pause`. The program counter persists across the pause, so a protocol's sequence of phases is written as straight-line code.

**The burst rule:** every cycle in a program's control-flow graph must pass through a `pause`. The assembler enforces this. It follows that each burst is loop-free and its worst-case length is known statically.

### 6.5 Cores (x2)

Each core has its own program SRAM (256 words of 64 bits, one `RM_IHPSG13_1P_256x64_c2_bm_bist`), an instruction register, and three move buses into the commons. Engines are assigned to a core statically. A core runs bursts to completion and dispatches ready engines in round-robin order when free (SPEC 5, D17). A three-bit cursor advances only on dispatch, preventing recurring engines from starving a ready peer.

Two cores exist for one reason: Ethernet transmit and receive each need most of a 6-cycle budget, and a single SRAM yields one instruction per cycle. With one core each, a per-bit burst of two instructions takes three cycles including the one-cycle fetch latency (calculated from the synchronous SRAM read), leaving half the budget spare.

Because engines own no registers, switching a core between engines saves and restores nothing. Running many slow protocols at once is therefore limited by the unit pool and the beat generators, not by context-switch cost.

### 6.6 Instructions

One 64-bit word holds three guarded moves, a guarded jump and a `pause` flag. All sources are read at the start of the cycle and all destinations written at the end, so the moves in one word are simultaneous.

- A **move** is `[guard] source -> destination`. Units act when a port is written: writing a shifter's `shift` port shifts it, writing an LFSR's `step` port clocks one bit in.
- A **guard** selects one condition bit, optionally inverted: a flag, a unit status bit (counter zero, shifter done, accumulator zero or carry), an input symbol bit, `sync_seen`, or a pin level.
- Ports prefixed `e.` refer to the executing engine's own symbol registers and beat generator, so code can be moved between engines unchanged.

Rough field budget (my sketch, to be settled in the instruction set document): three moves at about 17 bits each (5 guard, 6 source, 6 destination), a jump of about 13 bits (5 guard, 8 target, the target doubling as an 8-bit literal when there is no jump). The hard requirement is that the Ethernet per-bit path fits in two instructions.

**One machine description file is the single source of truth.** It lists every unit, port, width and guard bit. The RTL decoder, the assembler, the reference model, the port documentation and the per-unit formal properties are all generated from it. This is how the instruction encoding stays consistent across RTL, toolchain and docs.

### 6.7 The unit commons

| Unit | Starting count | What it is | Protocols that need it |
|---|---|---|---|
| Shifter | 4 | 8-bit shift register, either direction, with a bit counter and a `done` status | All of them |
| Counter | 4 | 16-bit down counter with reload and a `zero` status | Byte counts, timeouts, run lengths for bit stuffing, inter-frame gaps |
| LFSR | 2 | Up to 32 bits, programmable polynomial, one bit per step, readable by byte | CRC-5, CRC-15, CRC-16, CRC-32, parity (a 1-bit LFSR), scrambling, test patterns |
| Accumulator | 1 | 8-bit add, subtract, and, or, xor, compare, with 8 scratch registers | Address matching, checksums, byte-level decisions |
| Flags | 16 | 1-bit registers, usable as guards | State bits, signals between engines |
| RAM pointers | 4 | Auto-incrementing addresses into the data SRAM | Frame buffers, lookup tables, FIFOs to the host |
| Engine ports | per engine | Staged output symbol, input symbol, direct pin read and write | All of them |
| Beat ports | per generator | `inc`, `mod`, taps, re-alignment settings | All of them |

One LFSR direction is enough. A CRC defined most-significant-bit first is the same computation as a least-significant-bit-first one with the polynomial and state bit-reversed, and the assembler handles the reversal.

If two engines write the same port in the same cycle, core A wins and a sticky `conflict` flag is set. The toolchain's allocator is expected to make this impossible; the flag exists to catch allocator bugs.

### 6.8 Memory

| Memory | Macro | Purpose |
|---|---|---|
| Program A, program B | 2 x `1P_256x64` | 256 instructions per core |
| Data | 1 x `1P_4096x8`, or `1P_1024x8` if area is short | Frame buffers and tables. 4096 bytes holds one maximum transmit frame and one maximum receive frame (1518 bytes each) |

Assumed total: under a quarter of the die. This is unverified, because only the 512x32 footprint is known. Fallback if the macros do not fit: one core, with Ethernet transmit and receive demonstrated separately.

### 6.9 Host link

An SPI target, sampled in the system clock domain, driven by the RP2350. The host loads both program SRAMs, reads and writes the data SRAM, and reads and writes any unit port. Host port access uses the same port address space as moves, so there is no separate register map to maintain. The host also reads the sticky flags and starts or stops each engine.

The design loses all state when Tiny Tapeout deselects it, so the host reloads everything after selection. Pin assignment is open. A starting proposal is three inputs and two outputs for the host link (clock, select, data in; data out, interrupt), leaving 5 inputs, 6 outputs and 8 bidirectional pins for protocols.

## 7. The timing contract

This section is the core of the design and the part the verification is built around.

1. **Inputs** are captured at the taps of the engine's beat generator. They do not change until the same tap in the next beat.
2. **A burst** starts at the engine's trigger and sees those captured inputs.
3. **Outputs** written by the burst are staged. They take effect at the first beat boundary after the trigger, in the same cycle regardless of which instructions ran.
4. **Late write:** if a burst writes a staged output after that boundary has passed, the engine's sticky `late` flag is set.
5. **Overrun:** if an engine is triggered while its previous burst has not finished, its sticky `overrun` flag is set.
6. **Static check:** the assembler computes each burst's worst-case length and, per core, the worst-case response time of each engine given the other engines on that core. It rejects a program whose response times exceed the trigger-to-boundary or trigger-to-trigger distance.

The static check proves the flags will stay clear. The flags are the runtime witness that the check was sound. A waveform is either exactly what the beat-level program says, or a flag is set.

## 8. Worked examples

These are paper sketches, not simulated.

**UART receive.** Beat rate equals the baud rate. Re-alignment is on the falling edge with the window fully open and the preset at mid-bit, so the start bit aligns the beat. Taps sit close to the centre of the bit, the input table is a majority vote, and the burst shifts the symbol into a shifter. After the stop bit the engine widens the window again. The budget is about 520 cycles per bit against a burst of one or two instructions.

**I2C controller.** The beat boundary is placed where the data line may change, in the middle of the clock-low period. The clock pin's table is low, high, high, low across the four segments. The data pin's table is open-drain: drive low for symbol 0, release otherwise. Clock stretching is a watcher on the clock pin's level that holds the engine.

**Ethernet transmit.** Beat rate 10 MHz, exact. One instruction per bit: move the shifter's output bit to the staged symbol, move the same bit to the LFSR's `step` port, shift, and jump out when the shifter is done. A second burst once per byte loads the next byte from the data SRAM. Preamble, start delimiter and frame check are the same loop with a different source. A separate engine on a 16 ms beat emits link pulses while idle.

**Ethernet receive.** Re-alignment on every mid-bit edge, with the window excluding bit-boundary edges. The bit is the level sampled three-quarters of the way through the beat. One instruction per bit shifts it in and steps the LFSR. A beat with no accepted edge ends the frame. The margin is thin: a half-bit is 3 samples, so the sampling point has about one sample (16.7 ns, calculated) of slack either side. Section 12 lists this as the main technical risk.

## 9. Verification approach

The architecture was chosen partly for what it makes checkable.

1. **Two-level reference model** in `sim/reference/`. The beat-level model defines what a program means: a function from state and input symbols to state and output symbols, once per beat. The cycle-level model adds the front end, beat generators and core scheduling, and is compared against the RTL in lockstep.
2. **Programs are finite Mealy machines.** Because bursts never loop, the toolchain can symbolically execute each burst into a combinational function and extract the whole program as a state machine over beats. That machine is checked against an independent protocol specification, by exhaustive exploration where the state space allows and by constrained-random testing otherwise.
3. **Per-unit formal contracts.** Each unit's port behaviour is a small set of properties generated from the machine description and proved with an open-source formal tool.
4. **Differential testing of the cores.** A generator produces random legal programs and random pin stimulus. Pin waveforms and all sticky flags must match the cycle-level model exactly. A second generator produces programs that deliberately break the timing budget, and the test is that the flags fire on exactly the predicted cycle.
5. **Independent protocol checkers** in cocotb. For Ethernet, the transmitted waveform is decoded by test code that shares nothing with the chip's program, and the frame check is compared with a library CRC-32.
6. **Gate-level simulation and an FPGA prototype** before submission, as the post recommends.

## 10. Alternatives considered

| Alternative | Why not |
|---|---|
| Cycle-counted state machines in the PIO style | The most common entry. Keeps all four weaknesses listed in section 1 |
| Spatial eFPGA | Configuration in flops costs about ten times SRAM area. An estimated 100 to 200 lookup tables fit, against an estimated 300 to 400 for an Ethernet MAC with clock recovery. Both figures are estimates |
| Wire-clocked folded fabric: the program is a circuit, evaluated a few operators per cycle between beats | The most novel option and the closest rival. It needs about 15 operator evaluations per Ethernet bit (estimated) and a multi-port state store, against roughly 12 evaluations available from two 64-bit SRAMs. It is strong for slow protocols and fails the primary target. Its key property survives here: loop-free bursts are circuits, which is what makes item 2 of section 9 possible |
| Array of PSoC-style blocks (programmable logic plus an 8-bit datapath slice each) | Runs at the full clock rate, but an estimated 6 to 8 blocks fit and an Ethernet MAC needs an estimated 8 to 10. Also needs a place-and-route tool instead of an assembler |
| Programmable state machine in SRAM plus fixed datapath | Dense and fast, but the lane of at least one strong existing entry (PRISM, section 11), and it has no timing model |
| Timestamped event queues with a relaxed processor | Clean semantics, but one event per edge cannot keep up above about 1 Mbit. The staged-output rule in section 7 keeps its benefit without the queue |
| Stream pipeline of fixed operators | Ruled out by the project owner. Also the closest to the fixed-function design the post rejects |
| Virtual engines with saved and restored register contexts | Replaced by the commons. Engines that own no registers need no context switch |

## 11. Prior art and positioning

- **RP2040 PIO** and **TI Sitara PRU**: the inspirations the post names. Both tie timing to instruction count.
- **XMOS timed ports** and **precision-timed processors**: the source of "outputs happen at a stated time, not when the code gets there".
- **Synchronous languages (Esterel, Lustre)** and reactive processors built for them: the source of the burst model, `pause` and watchers.
- **Transport-triggered architectures**: the source of the move-only instruction format and the uniform unit interface.
- **Cypress PSoC universal digital blocks**: evidence that a small set of generic datapath units covers UART, SPI, I2C and CRC.
- **PRISM** (another entrant, public at `kdp1965.github.io/ihp-um-janestreet-prism`): two 16-state programmable state machines with datapaths beside a RISC-V core, with packet FIFOs in SRAM. Its site lists Ethernet, CAN, USB and nine other protocols. Working Ethernet will therefore not distinguish this entry by itself.

What this entry claims as its own: a wire-clocked execution model in which timing violations cannot be silent, programs that are extractable state machines and so can be checked against a protocol specification, and engines that are threads over a shared pool of units. Each piece has precedent. The combination, applied to protocol emulation and carried through to a verification method, is the claim.

## 12. Risks and first measurements

Do these before anything else. Each can change the design.

| Risk | First measurement | If it goes badly |
|---|---|---|
| Three SRAM macros do not fit beside the logic | Read the LEF footprints for `1P_256x64`, `1P_4096x8` and `1P_1024x8`. Floorplan them in the 8x4 template | Drop to one core, or to a `1P_1024x8` data RAM |
| The move buses do not close timing at 60 MHz | Synthesize and place one core with a stub commons. Read the critical path | Lower the clock to 40 MHz (Ethernet transmit still works at 2 cycles per half-bit; receive margin halves), or pipeline the guard evaluation |
| Logic area | Synthesize a beat generator, a pin cell and each unit. Record flop and cell counts in `sim/numerics/` | Cut unit counts. Rough estimate today: about 2,100 flops, about 9% of the die, plus combinational logic |
| Ethernet receive margin at 6 samples per bit | Simulate the receive path against jittered and duty-cycle-distorted waveforms in the cycle-level model | Sample once per bit only, or add a second sampling phase on the falling clock edge for receive |
| Ethernet receive hardware | Confirm a line receiver or comparator Pmod exists or can be built, and that two CMOS pins through a transformer are an acceptable transmitter | Demonstrate transmit on real hardware and receive in loopback |
| Toolchain scope | Count the lines needed for the assembler, allocator and static timing check | Ship the assembler and timing check first. State-machine extraction is the stretch |

## 13. Decisions

**Decided by the project owner**

- Primary target is 10 Mbit Ethernet. Low-speed USB is a stretch.
- No stream pipeline.
- Fabric is wanted. It appears here as the pin cells. The area argument in section 3 is why it is not larger, and the sizing run can overturn that.

**My calls, open to challenge**

- Verilog on the Tiny Tapeout template, with a Python reference model and assembler.
- Two cores, each with its own program SRAM.
- Six engines, four beat generators, and the unit counts in section 6.7.
- 64-bit instructions with three moves, a jump and a pause flag.
- 2-bit symbols and three taps per beat.
- Store-and-forward frames in a data SRAM, with an SPI host link.
- The file location: `ARCHITECTURE.md` at the repository root, as requested. Detailed instruction set and verification notes belong in `wiki/`.

**Left to the builder**

- Exact instruction encoding, port numbering and guard list, captured in the machine description file.
- Final unit counts and widths after the sizing run.
- Pin map, checked against the Tiny Tapeout pinout recommendations and the Pmods chosen.
- The host link's command format.
- Whether to add the fifth pin-cell input.
- The clock frequency to target after place and route.

## 14. Build order

The order is chosen so that the riskiest facts arrive first and something demonstrable exists at every step.

1. Sizing run: macro footprints, one core synthesized, a flop count. Outcome: confirmed or revised counts in section 6.
2. Machine description file and the generators for decoder, assembler and beat-level model.
3. One beat generator, one engine, one core, pin cells: a UART transmitter out of a pin, loaded over the host link. This is the first step the post itself suggests.
4. UART receive, SPI and I2C, each with an independent checker. The timing contract and its flags are tested here.
5. Second core, data SRAM, LFSR: Ethernet transmit, then receive, in simulation against a modelled line.
6. Full flow: GDS, precheck, gate-level simulation, FPGA prototype.
7. Stretch, in this order: state-machine extraction and checking, low-speed USB, the fifth pin-cell input.
