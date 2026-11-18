# Metronome v2 specification, part B: the machine

Status: **v2.0 draft 2, 2026-11-12.** Part B is **normative** for the v2 machine: the v2 RTL, the v2 cycle-level reference model and the v2 assembler implement exactly this. Part A, the score language that compiles onto this machine, is [SPEC_V2_SCORE.md](SPEC_V2_SCORE.md); its section 13 lists what the language needs from part B.

Names and numbers (field positions, port, guard and trigger indices, write groups, configuration fields, host addresses) come from `code/md2/machine.py` and its generated tables ([ISA_TABLES_V2.md](ISA_TABLES_V2.md), `code/md2/md2_defs.vh`). `BOTS/PLANS/V2_DESIGN.md` explains *why*; this file says *what*. Where they disagree, this file wins and the difference is recorded in `BOTS/PLANS/DECISIONS.md`. v1 semantics stay in [SPEC.md](SPEC.md); section 11 lists what changed.

**Changes from draft 1 (commit f945c29):** the beat-generator **hold** (3.2a, D27), start commit and first-beat edge-tap exemption (D28), and priority fixes implementing the existing cycle-state rules (D31-D32). The hold is in the machine tables, model and full v2 RTL. Configuration is 2,084 bits; `HOLD` is at line offset 0x1C and `HELD` is CTL bit 7.

Evidence (2026-11-12, uncommitted working tree over f945c29): the cycle-level model has 43 passing tests; v2 block tests, three Verilator lint configurations and generated-table checks total 9 passing pytest checks, and the Tiny Tapeout RTL template smoke test passes. Pin-level lockstep evidence, source hashes, red/green regressions and exact tool/library provenance are recorded in `data/raw/v2_resume_sol_20261112/` and the current `BOTS/PLANS/STATUS.md` handoff. The model and RTL had a shared host-stop/start-edge error caught by an independently asserted test (D32); lockstep establishes agreement on tested cases, not completeness. Full-v2 synthesis estimates 274,908.2868 um? of standard cells excluding SRAM macros. Physical fit, DRC/LVS, gate-level simulation and 60 MHz timing for this full RTL remain unverified. The earlier sizing skeleton's flow results (D24/U10) apply only to that skeleton.

## 1. Conventions

- One clock, `clk`, nominally 60 MHz. "Cycle t" is the interval between clock edges t and t+1. A value "at cycle t" is the register value during cycle t. `X'` is the value X takes at the end of cycle t (visible in cycle t+1).
- All combinational quantities in cycle t are functions of register values in cycle t, configuration values in cycle t and the raw input pins.
- Unsigned arithmetic unless stated. `{a,b}` is concatenation with `a` most significant. `popcount` counts set bits.
- **Reset.** `rst_n` is asserted asynchronously and released synchronously through two flops; the internal reset `rst_q` is `rst_n` delayed by two rising edges. While `rst_q` is low every register in this document is 0. Configuration (below) clears to 0 while `rst_n` is low.
- **Configuration** is the host-written, program-invisible state listed per unit as "Configuration" (`machine.CONFIG_BLOCKS`; 2,052 bits in draft 1, 2,084 with the hold fields of 3.2a). It is held in resettable latches (V2_DESIGN 4.7). A configuration byte written by the host in cycle W (section 9) is seen by all logic from cycle W+2; logic sees the old value through W+1. Multi-byte fields change one byte at a time, so a field written while it is in use passes through mixed values.
- **Configuration write spacing (D24).** Two configuration writes must not occur in consecutive cycles. The host link (section 9) gives at most one write per completed SPI byte, so it holds by construction. A configuration write in the two cycles after `rst_q` rises is ignored.

## 2. Pins

- Raw inputs are synchronised: `s1' = raw`, `s2' = s1`, `sp' = s2`. The **synchronised level** of input pin k is `PIN[k] = s2[k]`. `RISE[k] = s2 & !sp`, `FALL[k] = !s2 & sp`.
- Input pins P0..P12 are `uio_in[0..7]`, `ui_in[3..7]`. A pin select of 13..15 reads constant 0 and has no edges.
- The host link uses `ui_in[0..2]` (SCK, CS_N, MOSI) through the same synchronisers and drives `uo_out[0]` (MISO) and `uo_out[1]` (IRQ) from registers.
- Output pins O0..O13 are `uio_out[0..7]`, `uo_out[2..7]`. `uio_oe[i]` is O_i's output-enable register (section 8).

## 3. Lines (l = 0..3)

A line is a beat generator plus the pins it samples, its input symbol and its output symbol. Threads (section 4) are bound to one line; ports named `L.*` refer to the executing thread's line.

### 3.1 Configuration and state

Configuration: `INC, MOD, T0, T1, T2, PRE, WLO, WHI` (16 bits each); `EDGE` (pin 4 bits, polarity 2 bits: 0 none, 1 rise, 2 fall, 3 both), `WEN`, `FOLLOW`; `T0EDGE` (pin, polarity), `T0SRC`; `SNAP` (2 bits); `PINA, PINB` (4 bits); `LUT0, LUT1` (32 bits); hold `HEN` (1), `HPIN` (4), `HLVL` (1), `HTAP` (2).

State: `PH` (16); `RUN, ARM, REN`; `HELD`; `FIRST`; `SC, SP`; `FIRED[2:0]`; working samples `W = {B1, A2, A1, A0}`; snapshot `SN` (4); remembered bit `REM`; `STAGED, COMMITTED` (4 bits each); sticky `TAPMISS`.

### 3.2 Beat generator

In cycle t:

```
edge   = polarity-selected RISE/FALL of PIN[EDGE.pin]        (0 if pin >= 13 or polarity 0)
e0     = polarity-selected RISE/FALL of PIN[T0EDGE.pin]      (same rule)
inwin  = (WLO <= WHI) ? (WLO <= PH && PH <= WHI) : (PH >= WLO || PH <= WHI)
start  = edge && ARM && !RUN
accept = edge && RUN && REN && (!WEN || inwin)
adv    = RUN && !accept && !hold                      (hold: section 3.2a)
n      = PH + INC  (17-bit);   nx = (n >= MOD) ? n - MOD : n
wrap   = adv && (n >= MOD)
BEAT   = FOLLOW ? accept : wrap
PH'    = (start || accept) ? PRE : (adv ? nx : PH)
RUN'   = RUN || start;   ARM' = ARM && !start
```

`BEAT` is the line's **boundary**. An accepted edge never advances the phase in its cycle; it re-aligns it.

`SYNC`, read by guard `L.SYNC`, is `SP`:

```
FOLLOW = 0:  SC' = accept ? 1 : (BEAT ? 0 : SC);   SP' = BEAT ? SC : SP
FOLLOW = 1:  SC' = 0;                               SP' = BEAT ? 1 : (wrap ? 0 : SP)
```

A move to `Lk.CTL` in cycle t sets `RUN' = bus[0], ARM' = bus[1], REN' = bus[2]`, overriding the lines above; `PH'` is unaffected. Host writes to `PHASE` or `CTL` behave the same way and take priority over moves and over the generator.

### 3.2a Hold (clock stretching)

A line can stall its phase until a pin reaches a level. This lets a generated clock wait for a wire it has released, as in I2C clock stretching, without a thread polling the pin.

```
k      = HTAP                                   (a phase tap: k = 1, 2, or 0 with T0SRC = 0)
want   = RUN && !accept && (cross_k of 3.4, evaluated with adv = 1)
hold   = HEN && want && (PIN[HPIN] != HLVL)
HELD'  = hold
```

While `hold` is true, the phase does not advance. Tap k does not fire, and neither does any later tap or boundary of the beat. The phase advances again in the first cycle in which the pin reads `HLVL`, and tap k fires in that cycle.

An accepted edge takes priority, because `want` is 0 in an accept cycle. The hold is disabled when `HEN = 0`, when `HTAP = 3`, when tap k is disabled, or when `HTAP = 0` while `T0SRC = 1`.

Consequences (calculated from the rules above, not simulated):

- **A hold only lengthens beats.** Every bound in section 10 that is stated relative to a line's boundaries still holds. A bound stated in cycles grows by the time spent held.
- **Read-back latency stretches every beat.** The pin is read through the synchronisers (section 2). A wire released at tap j is therefore read back about 4 to 5 cycles later: output register, pad and two synchroniser stages (estimated). If tap k is fewer cycles than that after tap j, the beat stretches by the difference even when no other device holds the wire.
- **`HPIN >= 13` reads 0.** With `HLVL = 1` the line would hold forever, so the toolchain rejects that combination.
- **There is no built-in timeout.** A stuck wire leaves the line held, and the host can read `HELD` (section 9). A score's `within` (part A 8.1) compiles to a thread on another line, or to a counter.

Score mapping (part A 5.2): `stretch on WIRE` sets `HEN = 1`, `HPIN` = the wire's input pin, `HLVL = 1`, and `HTAP` = the first tap after the segment in which the role releases the wire.

Cost: 8 configuration bits per line, 32 in total, about 1.0k µm² at the measured 32.4 µm² per latch bit, plus one tap comparator per line (estimated). The comparator can share the tap-crossing logic of 3.4.

### 3.3 Follower mode

With `FOLLOW = 1` the boundary is an accepted edge, not a phase wrap. The phase restarts at `PRE` on every boundary, so taps 1 and 2 count cycles from the edge. A wrap with no edge is a missing clock: no boundary, and `SYNC` clears. Choose `MOD` as the longest allowed clock period and `INC = 1`.

**Edge-sourced tap 0.** With `T0SRC = 1`, tap 0 fires on `e0` instead of at phase `T0`. Typical use: the boundary on one clock polarity (commit) and tap 0 on the other (capture), so a target works at whatever rate the controller runs. `T0SRC` is also legal with `FOLLOW = 0`.

A follower line is started by setting `RUN` and `REN` (move or host). The start edge of section 3.2 is not a boundary in either mode.

### 3.4 Taps, fired bits and `TAPMISS`

Tap k is **enabled** if `Tk < MOD`, or, for tap 0 with `T0SRC = 1`, if `T0EDGE.polarity != 0`. In cycle t, for each enabled tap k:

```
phase taps (k = 1, 2; k = 0 when T0SRC = 0):
  cross_k = adv && ((n >= MOD) ? (Tk > PH || Tk <= nx) : (PH < Tk && Tk <= nx))
  next_k  = cross_k && BEAT && (n >= MOD) && (Tk <= nx)
edge tap 0 (T0SRC = 1):
  cross_0 = RUN && e0
  next_0  = cross_0 && BEAT
cur_k  = cross_k && !next_k
TAPk   = (cur_k && !FIRED[k]) || next_k
```

`next_k` marks a tap event that belongs to the beat starting at this boundary; `cur_k` one that belongs to the current beat. A tap fires at most once per beat: a current-beat event with its fired bit already set is dropped. Disabled taps never fire.

```
if RUN' && !RUN:  FIRED'[k] = (k is an enabled phase tap) && (Tk <= PH');  FIRST' = 1   (taps behind the starting phase count as fired)
elif BEAT:        FIRED'[k] = next_k;  FIRST' = 0
else:             FIRED'[k] = FIRED[k] || cur_k
TAPMISS' = TAPMISS || (BEAT && some enabled k has !FIRED[k] && !cur_k && !(k == 0 && T0SRC && FIRST))
SEG = popcount(FIRED)                                                            (2 bits)
```

`FIRST` (one bit per line, state) marks the starting beat, which is partial: its edge-sourced tap 0 may legitimately not occur (an SPI mode-1 target sees its first boundary before any capture edge), so it does not raise `TAPMISS` there (D28). `TAPMISS` is sticky until the host clears it. `SEG` is the number of taps fired so far in the beat; for phase taps in ascending order with no re-alignment it equals the v1 segment (calculated).

### 3.5 Capture, snapshot and input symbol

Let `pa = PIN[PINA]`, `pb = PIN[PINB]` (0 for selects >= 13).

- **Capture.** `TAP0: A0' = pa`. `TAP1: A1' = pa, B1' = pb`. `TAP2: A2' = pa`.
- **Snapshot.** `snap = (SNAP == 3) ? BEAT : TAP[SNAP]`. If `snap`: `SN' = W'` (the working bits including any capture in the same cycle) and `REM' = IN[1]`.
- **Input symbol.** `IN = {LUT1[{REM, SN}], LUT0[{REM, SN}]}`, combinational from the `REM` and `SN` registers. Source `L.CAP` reads `{REM, SN} = {REM, B1, A2, A1, A0}`.

`IN`, `L.CAP` and guards `L.IN0, L.IN1` therefore change only at the end of a snapshot cycle. `REM` is table output 1 of the previous snapshot, which lets a table decode differential codes.

### 3.6 Output symbol and commit

The three symbol ports form one write group per line (section 6). The winning write in cycle t sets `STAGED'`:

```
L.SYM:   STAGED' = bus[3:0]
L.DBIT:  STAGED' = {STAGED[3:1], bus[0]}
L.XOR:   STAGED' = STAGED ^ bus[3:0]
```

If `BEAT` in cycle t, or `RUN' && !RUN` (the line starts, by an edge, a move or a host write): `COMMITTED' = STAGED'` (a write in the same cycle is committed). The start commit lets a follower present its first bit before the first clock edge, as an SPI mode-0 target must: a thread stages the bit and starts the line, for example on the chip-select edge (D28).

## 4. Threads (t = 0..5)

Configuration: `CORE` (bit), `LINE` (2), `TRIG` (5, codes in ISA_TABLES_V2), watchers `W0C, W1C` (6-bit guard index, 0 disables) and `W0H, W1H` (8-bit handler address). State: `PC` (8), `EN`, `READY`, `RUNNING`, `ARMED`, sticky `LATE`, `OVR`.

- **Trigger event** `trig` in cycle t: `EN && (event(TRIG) || DB[t])`, where `DB[t]` is the doorbell pulse (section 9). Events: `Lg.BEAT`, `Lg.TAPk` of line g in cycle t; `FLAGk.RISE` = `F[k] && !FP[k]`; `PINA.RISE/FALL/EDGE` = `RISE`/`FALL`/either of `PIN[PINA]` of the thread's line; `HOST.INV` = `INV && !INVP`; `ALWAYS` = `!READY && !RUNNING`; `NONE` never.
- On `trig`: if `READY || RUNNING` then `OVR' = 1` and the trigger is dropped; otherwise `READY' = 1, ARMED' = 1`.
- **Disarm.** If its line has `BEAT` in cycle t: `ARMED' = 0`, unless an accepted trigger in the same cycle sets it to 1.
- **Late write.** Every enabled move to `L.SYM`, `L.DBIT` or `L.XOR` by a thread whose `ARMED` is 0 sets that thread's `LATE' = 1`, whether or not it wins the write group.
- **Stop.** An enabled move to `T.STOP`: `EN' = 0`. The current burst continues to its pause. A host write of `EN` in the same cycle wins.
- Dispatch and pause (section 5) set `READY' = 0, RUNNING' = 1` and `RUNNING' = 0, PC' = npc`. A host write of `PC` in the same cycle as a pause wins.

## 5. Cores (c = 0..1)

Each core has a 256 x 64 program memory with a synchronous read: an address presented in cycle t is registered at the end of t, and its word is at the memory output during t+1. A core is a three-stage pipeline: present an address (F), word at the output (R), execute from the instruction register (X). Fetch runs one word ahead on the next sequential address.

State: `XV` (IR holds an instruction to execute), `IR` (64), `RV` (the memory output holds a word of the current burst), `FPC` (8, address of that word), `XT` (3, executing thread), `XL` (2, its line), `RR` (3, round-robin cursor). While `XV`, `FPC = PC(IR) + 1 mod 256`.

In cycle t, with guards `G` evaluated on cycle-t state with line-relative guards taken from line `XL`:

```
if XV:
    C  = G[IR.cond];   JC = G[JUMP_GUARDS[IR.jcond]]
    for each move m: en_m = guard_m==always || (guard_m==if && C) || (guard_m==ifnot && !C)
                     if en_m: write SRC[IR.src_m] (read in cycle t) to DST[IR.dst_m] at end of cycle
    taken = jmode==always || (jmode==if && JC) || (jmode==ifnot && !JC)
    npc   = taken ? IR.imm : FPC
jmp  = XV && !IR.pause && taken
pse  = XV && IR.pause
load = RV && !jmp && !pse
free = pse || (!XV && !RV)
if pse:  PC[XT]' = npc;  RUNNING[XT]' = 0
disp = free && RUN_global && some thread e has CORE == c and READY
if disp:
    e = first ready thread bound to c in circular order RR, RR+1, ... (mod 6)
    d = (W0C[e] != 0 && G_e[W0C[e]]) ? W0H[e] : (W1C[e] != 0 && G_e[W1C[e]]) ? W1H[e] : PC[e]
    READY[e]' = 0;  RUNNING[e]' = 1;  XT' = e;  XL' = LINE[e];  RR' = (e + 1) mod 6
fetch address = jmp ? IR.imm : load ? FPC + 1 : disp ? d : none
if a fetch address:  FPC' = address
RV' = jmp || load || disp
XV' = load;   if load: IR' = word at the memory output
```

`G_e` evaluates guards relative to thread e's line; watchers are sampled in the dispatch cycle, on the state before that cycle's moves are written (v1 meaning). `RR` changes only on dispatch.

Consequences (calculated from the rules above):

| Event | Timing |
|---|---|
| Trigger in cycle t, core idle | `READY` in t+1, dispatch in t+1, first instruction executes in **t+3** |
| Sequential instructions | one per cycle |
| Taken jump on a non-pausing instruction | the fetched-ahead word is discarded and never executes; the target executes two cycles after the jump (one idle cycle) |
| `pause` | `PC` takes `npc`, including a jump target, at no cost; the fetched-ahead word is discarded |
| Dispatch after a pause | in the pause cycle; the next thread's first instruction executes two cycles later (one idle cycle) |

**Burst length** is counted in cycles: instructions executed plus one for each taken jump on a non-pausing instruction. **Response bound:** from a trigger in cycle t, a thread's last instruction executes no later than `t + n + 2 + Σ_p (L_p + 1)`, where n is its own burst length and the sum runs over the other threads bound to the same core with longest burst `L_p`. This assumes finite bursts, `RUN_global = 1` and unchanged program and configuration during the interval. Alone on its core, a one-instruction burst executes at t+3. (Checked on the model by randomized trigger timing for two threads on one core.)

Host writes to a core's program memory take the memory port in that cycle; a fetch in the same cycle returns an undefined word (9a.8).

## 6. Moves, write groups and conflicts

All moves of both cores in cycle t read their sources from cycle-t state and write at the end of cycle t. The move bus is 8 bits; single-bit sources occupy bit 0, and unused high bits read 0. Destination ports are partitioned into **write groups** (`machine.WRITE_GROUPS`): `L.SYM` (the three symbol ports of one line, resolved to the executing thread's line), `T.STOP` (per thread), `FLAGS`, `ACC`, each `Rk`, `SHk`, `SHk.CFG`, `CNTk`, `LFk`, `P0`, `Sk`, `Lk.CTL`, `HOST.OUT`. `NULL` has no group. If two or more enabled moves target one group in a cycle, sticky `CONFLICT' = 1` and only the write with the lowest (core, move index) takes effect.

Source side effects happen only for enabled moves: reading `HOST.IN` clears `INV`; reading `P0.D` while `P0.RDY == 0` sets sticky `MEMHAZ` (the stale byte is returned).

### 6.1 Units

- **Flags** `F[15:0]`. `SET n: F[n]' = 1`. `CLR n: F[n]' = 0`. `FP' = F` every cycle.
- **Accumulator** `A` (8), `Z, C, N`, scratch `R0..R3`: as SPEC v1 6.1.
- **Shifters** `SH0, SH1`: as SPEC v1 6.1 (`LEN`, `MSB` are state set by `SHk.CFG`).
- **Counters** `CNT0..CNT2`: as SPEC v1 6.1.
- **LFSR/CRC** `LF0, LF1`: as SPEC v1 6.1, `POLY` is configuration. Source `LFk.O` and guard `LFk.OUT` read `S[0]`.
- **Pointer** `P0`: as SPEC v1 6.1 for one pointer, with the data RAM arbiter below.
- **Host mailbox**: as SPEC v1 6.1. Guard `HOST.OUTE` is `!OUTV`.

### 6.2 Data RAM and arbiter

The data RAM is 512 x 32 bits (2,048 bytes; byte address a is lane `a[1:0]` of word `a[10:2]`, little-endian). One access per cycle. Requesters, in priority order: stream S0, stream S1, pointer P0, host. Each holds at most one request, visible to the arbiter in the cycle after it is set. A write is performed at the end of the cycle it is served. A read served in cycle s has its word at the RAM output during s+1, and the requester loads it at the end of s+1 (P0: `RDY` visible from s+2, as v1). Addresses wrap at 2,048 bytes.

### 6.3 Streams (k = 0..1)

Configuration: `MODE` (0 transmit, 1 receive), `MSB` (1 = most significant bit first), `START` (11), `LEN` (12, 0..2048 bytes), `MARK` (12). State: `POS` (12), `BIDX` (3), `BA` (11), `CUR` (8), `CV`, `WB` (32), `WV`, `RQ`, `LD`, `PEND` (8), `PV`, sticky `STARVED`.

Common definitions in cycle t: `END = (POS == LEN)`; `b = MSB ? 7 - BIDX : BIDX`; `LB` = lane `BA[1:0]` of `WB`; `g` = the arbiter serves this stream in cycle t. The stream requests a read of word `BA[10:2]` while `RQ` (transmit), or a one-byte write of `PEND` to byte `BA` while `PV` (receive).

**Transmit** (`MODE = 0`). `adv` = an enabled move to `Sk.ADV` and `!END`.

```
if LD:   WB' = word read in t-1;  WV' = 1;  LD' = 0
if RQ && g:   RQ' = 0;  LD' = 1
elif !WV && !RQ && !LD:   RQ' = 1
if adv && !CV:   STARVED' = 1                                   (the advance is ignored)
if !CV && WV:    CUR' = LB;  CV' = 1;  BA' = BA + 1;  if BA[1:0] == 3: WV' = 0
elif adv && CV:
    if BIDX != 7:  BIDX' = BIDX + 1
    else:          POS' = POS + 1;  BIDX' = 0
                   if WV:  CUR' = LB;  BA' = BA + 1;  if BA[1:0] == 3: WV' = 0
                   else:   CV' = 0;  STARVED' = 1
```

`Sk.BIT` (source and guard) is `CV && !END && CUR[b]`. Source `Sk.BYTE` reads `CUR`. A stream may read up to one word past its region; it never writes in transmit mode.

**Receive** (`MODE = 1`). `bitin` = an enabled move to `Sk.RX` and `!END`, with bit `bus[0]`; `flush` = a flush request (below) and `!END`.

```
NSH  = CUR | ((bitin && bus[0]) << b)                           (CUR is the assembly register)
done = (bitin && BIDX == 7) || (flush && (BIDX != 0 || bitin))
if PV && g:   PV' = 0;  BA' = BA + 1                             (PEND is written to byte BA this cycle)
if bitin && !done:   CUR' = NSH;  BIDX' = BIDX + 1
if done:   CUR' = 0;  BIDX' = 0;  POS' = POS + 1
           if PV && !g:  STARVED' = 1                            (the byte is dropped)
           else:         PEND' = NSH;  PV' = 1
```

`Sk.BIT` is 0 in receive mode. Source `Sk.BYTE` reads `PEND`, the last completed byte. Unfilled bits of a flushed byte are 0. The host reads `POS` and `BIDX` for the frame length; read `BIDX` before a flush, which clears it.

**Guards.** `Sk.END = END`; `Sk.MARK = (POS == MARK) && (BIDX == 0)`; `Sk.BYTE = (BIDX == 0)`; `Sk.BIT` as above.

**Control.** A move to `Sk.CTL` or a host write of the stream's `CTL` register makes a request; requests from both in one cycle combine. Bit 0 **rewinds** at the end of the cycle: `POS' = 0, BIDX' = 0, BA' = START, CUR' = 0, CV' = WV' = RQ' = LD' = PV' = 0`, overriding every other update of these. A request served in a rewind cycle still accesses the RAM; read data is discarded. `PEND` and `STARVED` are unchanged. Bit 1 **flushes** (receive only). Host `CTL` bit 7 clears `STARVED`, unless a starve event occurs in the same cycle. Reset leaves each stream rewound at address 0. `MODE`, `MSB` and `START` changes take effect at the next rewind; `LEN` and `MARK` are used live.

## 7. Guard conditions and jump conditions

Indices are in [ISA_TABLES_V2.md](ISA_TABLES_V2.md). Guard 0 is constant true. Line-relative guards use the executing thread's line, or for watchers the line of the thread being dispatched: `L.IN0, L.IN1` are the bits of `IN`, `L.SYNC` is `SP`, `L.PINA, L.PINB` are `PIN[PINA]`, `PIN[PINB]`. `Lk.RUN` is line k's `RUN`. `PINk` is `PIN[k]`. Move guards use the 6-bit `cond`. Jumps use the 5-bit `jcond`, which selects guard `JUMP_GUARDS[jcond]`; all 32 entries are defined.

## 8. Output pins (o = 0..13)

Configuration: `LINE` (2), `BOUND`, `SEL0, SEL1, SEL2` (2 bits each), `LUT` (32), and for o < 8 `OE` (32). Each cycle:

```
idx = BOUND ? {SEG(LINE), COMMITTED(LINE)[SEL2], COMMITTED(LINE)[SEL1], COMMITTED(LINE)[SEL0]} : 0
OUT[o]' = LUT[idx];   OEN[o]' = OE[idx]   (o < 8)
```

The pin outputs are these registers. After reset every pin drives 0 with its output enable off.

**v3 note:** on `metronome-v3.0`, `LIVE` (BIND bits 4:3) may replace b2 and b1 by live pins, and the registers hold in a frozen cycle (12.1, 12.3).

## 9. Host link and host map

**SPI target, mode 0, MSB first.** Let `SR` be the synchronised rising edge of SCK (section 2) in a cycle where the synchronised CS_N is low. While CS_N is high: the byte state returns to the command byte, the bit count clears and `TX' = 0`. `MISO = TX[7]`.

- On each `SR`: `RX' = {RX[6:0], MOSI}` and the bit count increments. On the 1st..7th `SR` of a byte, `TX' = {TX[6:0], 0}`. The 8th `SR` in cycle c **completes** the byte, value `{RX[6:0], MOSI}`, and leaves `TX` unchanged.
  - Byte 0: command. `0x02` write, `0x03` read; any other value ignores the rest of the transaction.
  - Byte 1: `ADDR[15:8]`. Byte 2: `ADDR[7:0]`; for a read, a read request at `ADDR` is issued in cycle c+1.
  - Write, bytes 3 onward: a **host write** of the byte to `ADDR` in cycle **W = c+1**; `ADDR' = ADDR + 1` at the end of W. Register and configuration writes take effect at the end of W (configuration is seen from W+2, section 1). Program-memory bytes are written in W. Data RAM writes become a host request.
  - Read, bytes 3 onward: completing a data byte issues a read request at `ADDR` in cycle c+1.
- **Read response.** A register read issued in cycle R loads `TX` at the end of R+1 with the register's value in cycle R. A data RAM read issued in R becomes a host request; served in s, its byte loads `TX` at the end of s+1. `ADDR' = ADDR + 1` with each load. The loaded byte must arrive before the next `SR`; with SCK at clk/16 a data RAM read must be served within 12 cycles of its request (calculated), so a program must not keep the RAM busy that long while the host reads it. A load in the same cycle as a shifting `SR` is lost.
- **No host read has a side effect.** Reads prefetch one address past the last byte the host clocks out.
- Keep SCK at or below clk/16 (3.75 MHz at 60 MHz).
- `IRQ' = (IRQEN[0] && OUTV) || (IRQEN[1] && ERR)`, where `ERR` is any of `CONFLICT`, `MEMHAZ`, every thread's `LATE` and `OVR`, every line's `TAPMISS` and every stream's `STARVED`.

**Host map.** Addresses, register layouts and access types are generated from `machine.HOST_MAP` and `HOST_BLOCKS` into [ISA_TABLES_V2.md](ISA_TABLES_V2.md#host-address-map). Configuration registers (access W) are write-only and read 0 (D14). Program memory is written by byte lane (byte k of word w of core c at `c*0x800 + 8w + k`, holding word bits `8k+7..8k`, so little-endian) and reads 0. Unmapped addresses read 0 and ignore writes. Multi-byte registers are little-endian; each byte is written independently. Host writes take priority over moves and hardware updates of the same state, except where a section above says otherwise; a sticky flag set in the same cycle as a host clear stays set.

Runtime registers (flops):

- `CTRL.RUN` bit 0 is `RUN_global`. `STICKY` reads `{MEMHAZ, CONFLICT}` in bits 1, 0, write 1 to clear. `IRQEN` bits 0, 1. `DOORBELL` reads 0; writing bit t in cycle W makes `DB[t] = 1` in cycle W+1 only. `HOSTIN` writes `INB` and sets `INV`, reads `INB`. `HOSTOUT` reads `OUTB`. `HOSTSTAT` reads `{OUTV, INV}` in bits 1, 0; writing 1 to bit 1 clears `OUTV`. `ID` reads `0xA2`. `ERRSUM` reads `{MEMHAZ, CONFLICT, any STARVED, any TAPMISS, any OVR, any LATE}` in bits 5..0.
- Line runtime: `PHASE` reads and writes `PH`. `CTL` bits 0..2 read and write `RUN, ARM, REN` (section 3.2); reads also give `SYNC` in bit 3, `FIRED` in bits 6:4 and `HELD` in bit 7. `SYM` reads `{COMMITTED, STAGED}`. `INS` reads `{IN, REM, SN}` in bits 6:0. `STAT` bit 0 reads `TAPMISS`, write 1 to clear.
- Thread runtime: `PC` reads and writes. `STAT` reads `{OVR, LATE, EN, ARMED, RUNNING, READY}` in bits 5..0; a write sets `EN` from bit 3 and clears `LATE` or `OVR` where bit 4 or 5 is 1. A host clearing `LATE` writes `EN` as well, so it must write the current `EN`.
- Stream runtime: `POSL`, `POSH` (`{STARVED, BIDX, POS[11:8]}`), `CTL` (write-only; section 6.3).
- **v3 (section 12):** block `DBG` at `0x2460`: `DBG` (freeze, step), `MCTL`/`MISR` (execution digest), `ECTL`/`EMASK` (edge capture), and read-only `ACC`, `AFLG`, `FLAGS`, `CST`, `FPC`. All are 0 after reset, which leaves the v2 behaviour unchanged.

## 9a. Resolutions of edge cases

1. **Unused encodings.** Source indices beyond the table read 0; destination indices beyond the table are `NULL`; guard indices beyond the table evaluate false, in instructions and watchers; trigger codes beyond the table never fire.
2. **Request overwrite** (P0 and host): as SPEC v1 9a.2. A stream never overwrites its own request.
3. **RDY precedence and stale landings**: as SPEC v1 9a.3.
4. **Host request slot**: one data RAM request; a new one overwrites an unserved one (no flag).
5. **Mailbox precedence**: as SPEC v1 9a.5.
6. **Beat generator range.** `INC < MOD` is required (the toolchain checks). The 17-bit sum is reduced once and stored in 16 bits.
7. **Flags.** `Z` for ADD, SUB and CMP is computed on the 8-bit result.
8. **Program loading.** A fetch in a cycle with a host program-memory write to the same core returns an undefined word, and a word fetched while only some bytes are rewritten executes the mix. Load programs with `RUN_global = 0` and no burst in flight.
9. **Host read address.** The first read of a transaction uses `{byte 1, byte 2}`.
10. **Taps.** Disabled taps never fire and never count in `SEG`. `T0 = T1 = T2 = 0` on a running generated line gives `SEG = 3` after every boundary; to use fewer segments, put unused taps at or above `MOD`.
11. **Configuration changes in use.** Changing a running line's, a bound pin's or a ready thread's configuration is legal, but intermediate byte combinations are visible from W+2 of each byte. Stop the line or thread first.
12. **Line with `RUN = 0`.** No boundary, no taps, no snapshot; symbol writes only stage. `ARMED` threads stay armed and later writes are not late.
13. **Stream mode change.** Changing `MODE`, `MSB` or `START` without a rewind leaves the stream in an unspecified state until the next rewind.

## 10. The timing contract (what a program may rely on)

1. **Inputs.** `L.IN`, `L.CAP`, `L.IN0` and `L.IN1` change only at the end of a snapshot cycle, so they are stable from one snapshot to the next. A burst triggered by the snapshot tap in cycle t executes from t+3 and reads the snapshot taken in t, provided it finishes before the next snapshot cycle.
2. **Outputs.** A symbol written by a thread is committed at the first boundary of its line after the thread's trigger, provided the write executes no later than that boundary cycle. The pin registers change one cycle after the commit.
3. **Flags.** A late symbol write sets `LATE`; a trigger during a burst or before dispatch sets `OVR`; a contested write group sets `CONFLICT`; a data RAM hazard sets `MEMHAZ`; a boundary with an enabled tap unfired sets `TAPMISS`; a stream advanced or completed without its byte sets `STARVED`. All are sticky until the host clears them.
4. **Toolchain obligations.** The static check accepts a program only if:
   - every burst is loop-free and its length, in cycles as section 5 counts them, is known;
   - for every thread triggered by a line event, the response bound of section 5, counted from the trigger cycle, places its last symbol write no later than its line's next boundary and its last input read before the line's next snapshot cycle;
   - every generated line has `INC < MOD`;
   - every line that re-aligns (`REN` used, `WEN = 1`, `FOLLOW = 0`) has a non-wrapping window (`WLO <= WHI`), and every enabled phase tap T used for capture, snapshot or a trigger satisfies either `T < WLO` and `T <= PRE`, or `T > WHI + INC` and `T > PRE`. Such a program cannot raise `TAPMISS` while edges arrive inside the window (calculated from 3.2 and 3.4; checked on the model with ±1-cycle jitter, not proven).
5. **Streams (calculated; checked on the model with one advance per cycle, not proven for every arbiter load).** A transmit stream requests the next word as soon as it moves the last byte of a word into `CUR`, so it has eight advances to receive it. With streams first in the arbiter, each stream waits at most one cycle for the other. A transmit stream advanced at most once per cycle, or a receive stream given at most one bit per cycle, therefore does not set `STARVED`.

## 11. Differences from SPEC v1

| Area | v1 | v2 |
|---|---|---|
| Structure | 4 beat generators, 6 engines with their own pins and tables | 4 lines (beat generator, pins, tables, symbols), 6 threads bound to a line |
| Taps | suppressed in an accept cycle without a flag; `SEG` from the phase | fired bits: at most once per beat, `TAPMISS` on a skipped tap; `SEG` = taps fired |
| Clock modes | generated, edge-started, recovered | adds follower mode, an edge-sourced tap 0 and the hold (3.2a) |
| Input | 2-bit symbol from 16-entry tables over `CAP`, visible per tap | 2-bit symbol from 32-entry tables over an atomic snapshot and a remembered bit |
| Output | 2-bit symbol, one write port | 4-bit symbol; whole, data-bit and exclusive-or ports, one write group per line |
| Pin tables | 4 inputs | 5 inputs: three chosen symbol bits and `SEG` |
| Core | first instruction at t+2; bursts back to back | registered instruction, first at t+3; one idle cycle per taken jump and per dispatch |
| Jumps | on the move condition | on a separate 5-bit condition over 32 guards |
| Units | 4 shifters, 4 counters, 2 pointers | 2 shifters, 3 counters, 1 pointer, 2 streams; LFSR output bit as a source |
| Configuration | flops, cleared by synchronous reset | latches, cleared by reset, seen two cycles after a write; no consecutive writes |
| Host map | `machine.HOST_MAP` (v1) | regenerated; ID `0xA2`; per-line `TAPMISS`, per-stream `STARVED`, `ERRSUM` |

## 12. v3 additions (draft 2026-11-16, branch `metronome-v3.0`)

**Status: normative for the v3 RTL and the v3 cycle model on `metronome-v3.0`; r4b (`metronome-v2.0`) does not have them.** Every addition is off after reset: with every v3 register at its reset value the machine is cycle-identical to sections 1 to 10 (all v2 lockstep scenarios pass unchanged). Names and addresses come from `machine.OUT_REGS` (`LIVE`) and `machine.DBG_REGS` (block `DBG` at `0x2460`, runtime flops with the section 9 access rules). Decisions D38 to D42.

### 12.1 Live-pin inputs on the pin tables (`OUT.BIND` bits 4:3, `LIVE`)

Section 8 becomes, with `ln = LINE`, `cm = COMMITTED(ln)` and `PINA(ln)`, `PINB(ln)` the bound line's pin selects (section 3.1; a select >= 13 reads 0):

```
b0  = cm[SEL0]
b1  = LIVE[1] ? PIN[PINB(ln)] : cm[SEL1]
b2  = LIVE[0] ? PIN[PINA(ln)] : cm[SEL2]
idx = BOUND ? {SEG(ln), b2, b1, b0} : 0
OUT[o]' = LUT[idx];   OEN[o]' = OE[idx]   (o < 8; both hold in a frozen cycle, 12.3)
```

`LIVE = 0` is v2. Latency (calculated): a level on a raw input in cycle t is `PIN` in t+2 (two synchronisers) and in the output register in t+3, so a table reacts three cycles after the wire changes (plus pad delays) instead of at the line's next boundary. The table still sees `SEG` and the other symbol bits, so one table can say "drive data bit b0, and from segment 2 release the wire if PINA reads back low": wired-AND read-back, I2C acknowledge, CAN or I2C arbitration loss, and pin-to-pin pass-through (a `LUT` that copies b2). Taking the pins from the bound line keeps the selection at two bits per output pin (28 latch bits in all, estimated about 1.3k µm² with the multiplexers); an output can follow any input pin by binding it to a line whose `PINA` or `PINB` selects that pin (an otherwise idle line works). The path is synchroniser to output register only; no guard, move or core path gains logic.

### 12.2 Execution digest (`MCTL`, `MISR`)

A 32-bit multiple-input signature register `M`. With `D = {OEN[7:0], OUT[13:0]}` (22 bits: `OUT[o]` in bit o, `OEN[o]` in bit 14+o), the pin registers' values in cycle t (the levels on the pads during t):

```
if the host writes MCTL with bit 1 set in cycle t:   M' = 0
elif MEN && !FRZ:   M' = ((M << 1) mod 2^32) ^ (M[31] ? 0x04C11DB7 : 0) ^ D
else:               M' = M
```

`MEN` is `MCTL` bit 0. The host reads `M` as `MISR` bytes 0..3 (little-endian, no side effect). The polynomial is the CRC-32 generator (`machine.MISR_POLY`) in Galois form, shifting left. The model computes the same value, so one read after millions of cycles checks every output and output-enable register against the model over the whole interval, for the same input stimulus. `MISO` and `IRQ` are excluded because they depend on host timing. A random error escapes with probability about 2^-32 (literature-derived property of a 32-bit MISR; not proven here for this input width).

### 12.3 Debug: freeze, single-cycle step and readback (`DBG`, `ACC`, `AFLG`, `FLAGS`, `CST`, `FPC`)

State: `FREEZE` (host bit, `DBG` bit 0), `FRZ` (this cycle is frozen) and `FRZD` (`FRZ` of the previous cycle). A host write of `DBG` in cycle W with byte d sets `FREEZE' = d[0]` and `FRZ' = d[0] && !d[1]`; without a `DBG` write, `FRZ' = FREEZE`. Always `FRZD' = FRZ`. Writing `0x01` freezes from W+1. With `FREEZE = 1`, writing `0x03` (STEP) runs exactly cycle W+1 and freezes again from W+2. Single-**cycle** stepping was chosen over single-beat stepping: it costs nothing beyond the freeze and is defined for every line at once; a beat step is a host loop of cycle steps that reads `LRT.CTL`.

A cycle with `FRZ = 1` is **frozen**. In a frozen cycle:

- No core executes, jumps, pauses, fetches or dispatches. `XV, RV, IR, FPC, XT, XL, RR` hold and there are no moves, so no unit, flag, pointer, stream, symbol, `T.STOP`, `CONFLICT`, `LATE` or `MEMHAZ` update comes from a move.
- No line sees a pin edge and no line advances: as if `edge = e0 = 0` and `adv = 0` (no start, accept, boundary, tap, capture, snapshot or `TAPMISS` event). `HELD` holds.
- No trigger is accepted (no `READY`, `ARMED` or `OVR` change). `FP` and `INVP` hold, so a flag or mailbox rise during the freeze triggers in the first unfrozen cycle. A doorbell pulse in a frozen cycle is held (`DB' = written bits | DB`) and delivered in the first unfrozen cycle.
- Streams and the pointer make no autonomous update and are not served; the arbiter serves only the host request, so host data RAM reads and writes work while frozen. **Landing exception:** a stream or pointer read served in the last unfrozen cycle s has its word captured from the RAM output at the end of s+1 even if s+1 is frozen (into the stream's `WB` or the pointer's `D`), because a host read during the freeze would replace the RAM output. `LD`, `WV` and `RDY` update in the first unfrozen cycle as usual. `WB` is not visible while `LD = 1`; the pointer's `D` reads as the landed byte, not the stale byte of 9a.3, if a move reads `P0.D` in that first unfrozen cycle (the landing cycle, already a `MEMHAZ` hazard).
- Output pin registers (`OUT`, `OEN`), `M` (12.2) and the edge-capture counter `DC` (12.4) hold, so the pads keep their levels.
- Still running: the input synchronisers (an input edge that occurs and ends inside a freeze is not seen), the host link, configuration latches (W+2 rule), `IRQ`, and every host write with its section 9 effect: line `PHASE`, `CTL`, `STAT` (a host start still commits and sets `FIRED` and `FIRST`), thread `PC` and `STAT`, `CTRL` registers, stream `CTL` rewind and STARVED clear. A host stream **flush** is ignored while frozen.

`RUN_global` and `FREEZE` are independent: `RUN_global = 0` stops dispatch only (bursts in flight finish and lines run), a freeze stops everything above. Program memory may be written while frozen only on a core with `XV = RV = 0` (read `CST`); otherwise 9a.8 applies. Readback, frozen or running (value in cycle R, no side effect): thread `PC` and `STAT` (section 9), `ACC` (A), `AFLG` (`{N, C, Z}` in bits 2..0), `FLAGS` (F15..F0), and per core `CST` (`{RV, XV, XT}` in bits 4, 3, 2..0) and `FPC` (while `XV`, the executing instruction is at `FPC - 1` and belongs to thread `XT`). Apart from the input and landing exceptions above, a freeze is **transparent**: deleting the frozen cycles from a run, with the same inputs in the remaining cycles, gives the same state sequence (checked by lockstep against the model, and the freeze hold of the stream and memory units is proved by k-induction in `code/tests/formal/v3_freeze.sby`; not proven for the whole chip).

### 12.4 Edge capture into stream S0 (`ECTL`, `EMASK`)

With `CEN` (`ECTL` bit 0) set, stream S0 becomes a capture stream. Its transmit and receive bit paths are disabled: moves to `S0.ADV` and `S0.RX` and flushes have no effect and raise no `STARVED`, `S0.BIT` reads 0 and `S0.BYTE` reads as 6.3 says for its `MODE`. Change `CEN` only together with a rewind of S0 (as 9a.13). State: `DC` (19 bits). In an unfrozen cycle t:

```
cev  = CEN && ((RISE | FALL)[12:0] & EMASK) != 0
rec  = {DC[18:0], PIN[12:0]}                     (bits 31:13 DC; bits 12:0 the synchronised levels in t)
DC'  = !CEN ? 0 : (cev ? 1 : min(DC + 1, 2^19 - 1))        (a host ECTL write sets DC' = 0, also while frozen)
push = cev && !END
if PV && g:  PV' = 0;  BA' = BA + 4              (the pending record is written to word BA[10:2], all four lanes)
if push:     if PV && !g:  STARVED' = 1          (record dropped; POS unchanged)
             else:         WB' = rec;  PV' = 1;  POS' = POS + 4
```

While `PV`, S0 requests a one-word write of `WB` at word `BA[10:2]`. `DC` counts cycles since the previous edge event (pushed or dropped); every `ECTL` write clears it (host priority, also in a frozen cycle), so it is 0 in the first cycle with `CEN = 1` after an `ECTL` write, and it saturates at 524,287 cycles (8.7 ms at 60 MHz). **Resolution:** one clock cycle. Records are little-endian words from `START`; use a word-aligned `START` and a `LEN` that is a multiple of 4 (`END` is `POS == LEN`, and `POS` counts bytes). Rewind, `END`, `MARK`, `POS` readback and the STARVED clear work as in 6.3.

**Write width and back-to-back edges (calculated from 6.2 and the rules above).** A record is one RAM access. S0 has the highest arbiter priority, so a record pushed in cycle t is written in t+1 and a push in t+1 is accepted: an edge event every cycle is sustained without `STARVED` until `END`. While edges arrive every cycle, S1, P0 and the host get no RAM cycle; a host data RAM read must be served within 12 cycles (section 9), so the host should not read data RAM during a burst of more than about 11 consecutive edge cycles. Edges of several masked pins in one cycle make one record. This suits captures, not continuous full-rate streaming: a 2 KB region holds 512 records.

### 12.5 Program-load contract (model diagnostic only)

Configuration is not double-buffered (rejected for area, V3_RIVAL_IDEAS 7.6), so a field written while in use passes through mixed values (section 1, 9a.11). **Contract:** the host writes a configuration byte of a line only while that line has `RUN = 0` and `ARM = 0`; of an output pin only while it is unbound or its line has `RUN = 0` and `ARM = 0`; of a thread only while that thread has `EN = 0`, `READY = 0` and `RUNNING = 0`; of an LFSR polynomial only while `RUN_global = 0`; and writes program memory of a core only while `RUN_global = 0` and that core has `XV = RV = 0`. (Stream configuration is already defined by 6.3 and 9a.13: `MODE`, `MSB`, `START` act at the next rewind.) The hardware does not enforce the contract; writes take effect as sections 1 and 9 say. The cycle model records every host write that breaks it, in the cycle the write is issued (W), in `Chip.contract_violations` as `(cycle, address, reason)`. Strict harnesses assert that the list is empty; the v3 host loader refuses such writes (Track D).

## 13. v4 additions (draft 2026-11-17, branch `metronome-v4.0`)

**Status.** Sections 13.1–13.2 are implemented in the cycle model and RTL. Core writes and S0 replay have directed RTL lockstep checks, and the shared bank arbiter has an induction proof covering host priority and write spacing. The centralized A1/A2 build at 45% placement density passed extracted timing and Tiny Tapeout precheck at 16.667 ns. Every addition is off after reset. With `ECTL.RPL = 0` and no `CW.D` move, the machine follows sections 1 to 12. Destination codes 58..60 were `NULL` in v3 (9a.1). The encodings are in `machine.DST` (`CW.*`), `machine.DBG_REGS` (`RLV`, `ECTL` bit 1), `CTRL.STICKY` bit 2 and `ERRSUM` bit 6 (`CWOVR`).

### 13.1 Configuration written by the cores (`CW.AL`, `CW.AH`, `CW.D`)

State: `CWA` (16), `CWV`, `CWQ = (address, byte)`, sticky `CWOVR`; `BWP` (the configuration latch bank was written in the previous cycle) and `HH` (one held host configuration write). One write group `CW`.

- `CW.AL`, `CW.AH`: `CWA[7:0]` or `CWA[15:8] := bus`.
- `CW.D` in cycle t: if `CWV` and the pending write does not drain in t, `CWOVR' = 1` and the new write is dropped. Otherwise `CWQ' = (CWA, bus)`, `CWV' = 1`, `CWA' = CWA + 1`.
- **Bank port.** The latch bank has one write port and is never written in two consecutive cycles (the `md2_cfg_bank` write spacing rule, which the 2-cycle latch timing exception of `project.sdc` relies on). In cycle t, from cycle-t state: a held host write `HH` is performed. Otherwise a host configuration write issued in t is performed, unless `BWP`, in which case it is held to t+1 (`HH`). If neither is performed and `CWV` holds a configuration address and `!BWP`, the core write is performed and drains. `BWP' = 1` if and only if a write was performed. A performed write is seen by the logic from t+2 (section 1). So a host configuration write normally keeps W+2, and it becomes W+3 only when a core write used the bank in W-1. Host writes are at least one SPI byte apart, so `HH` never holds two writes.
- **Other targets.** A pending write to `DBG.ECTL`, `EMASK` or `RLV` drains in the next cycle as a runtime write (end of that cycle, before a host write in the same cycle, which wins). A pending write to any other address drains with no effect.
- **Timing (calculated, checked in `code/tests/md2/test_v4_model.py`).** A `CW.D` executed in cycle t reaches the logic from t+3 when the bank is free. One write per two cycles is sustained. Three `CW.D` in consecutive cycles lose the third (`CWOVR`).
- **Contract.** The section 12.5 contract applies to core writes. The model checks it when the write reaches the bank and records violations prefixed `core:`. Programs write a line's configuration only while it has `RUN = ARM = 0`.

### 13.2 Edge replay from S0 (`ECTL.RPL`, `RLV`)

`ECTL` bit 1 `RPL` turns S0 into a replay stream; it takes priority over `CEN` (capture is off while `RPL`). Change it only together with a rewind of S0. `RLV` (13 bits, read/write, `DBG` offset 0x12) holds the replay levels. While `RPL`, the synchronised level of every pin in `EMASK` is `RLV`, its previous level is `RLV` of the previous cycle, and the pad is ignored. Lines, triggers, guards and `PINS.*` all see the replayed waveform.

S0 reads whole words, records of 12.4, from `START` in order, into a two-deep buffer (`WB`, then `NB`). A read is requested when the stream is not at `END`, no read is in flight and the buffer is not full; `POS` advances by 4 per word read. With `DC` reused as the replay timer (0 after an `ECTL` write):

```
apply = RPL && WV && DC + 1 >= WB.DC                     (WB.DC = WB[31:13])
apply:  RLV' = (RLV & ~EMASK) | (WB[12:0] & EMASK);  DC' = 0;  WB' = NB, WV' = NV, NV' = 0
else:   DC' = min(DC + 1, 2^19 - 1)
late:   apply && DC + 1 > WB.DC   ->  STARVED' = 1
```

**Mirror property (checked by test):** if a capture starts with an `ECTL` write in cycle W and a replay with an `ECTL` write in W', with `RLV` = the pre-capture level of the masked pin, then the synchronised level in replay cycle W'+1+i equals the captured level in cycle W+1+i, for every i up to the last record. Edge intervals of at least 3 cycles never starve (measured on the model; 1-cycle intervals do starve). The initial level is `RLV`, not inferred from the records; a single masked pin is the supported case.
