# Metronome v2: normative machine specification

Status: v2.0 draft 1, 2026-11-12 (build step 2). This document is **normative** for v2: the v2 RTL, the v2 cycle-level reference model and the v2 assembler implement exactly this. Names and numbers (field positions, port, guard and trigger indices, write groups, configuration fields, host addresses) come from `code/md2/machine.py` and its generated tables ([ISA_TABLES_V2.md](ISA_TABLES_V2.md), `code/md2/md2_defs.vh`). `BOTS/PLANS/V2_DESIGN.md` explains *why*; this file says *what*. Where they disagree, this file wins and the difference is recorded in `BOTS/PLANS/DECISIONS.md`. v1 semantics stay in [SPEC.md](SPEC.md); section 11 lists what changed.

Evidence: the v2 cycle-level model `sim/reference/metronome2/` implements this document; its tests (`sim/reference/tests_v2/`, 28 pass) exercise each section, including Ethernet-rate transmit and receive in loopback on two cores. Model and spec are by the same author, so the model checks consistency and the calculated claims, not independent correctness; that comes from lockstep against the RTL. The v2 sizing blocks in `sim/numerics/v2_sizing/` (core, stream, latch bank, host link) are RTL-simulated and the skeleton passed the Tiny Tapeout flow (D24, U10); where this specification differs from them, this specification wins.

## 1. Conventions

- One clock, `clk`, nominally 60 MHz. "Cycle t" is the interval between clock edges t and t+1. A value "at cycle t" is the register value during cycle t. `X'` is the value X takes at the end of cycle t (visible in cycle t+1).
- All combinational quantities in cycle t are functions of register values in cycle t, configuration values in cycle t and the raw input pins.
- Unsigned arithmetic unless stated. `{a,b}` is concatenation with `a` most significant. `popcount` counts set bits.
- **Reset.** `rst_n` is asserted asynchronously and released synchronously through two flops; the internal reset `rst_q` is `rst_n` delayed by two rising edges. While `rst_q` is low every register in this document is 0. Configuration (below) clears to 0 while `rst_n` is low.
- **Configuration** is the host-written, program-invisible state listed per unit as "Configuration" (`machine.CONFIG_BLOCKS`; 2,052 bits). It is held in resettable latches (V2_DESIGN 4.7). A configuration byte written by the host in cycle W (section 9) is seen by all logic from cycle W+2; logic sees the old value through W+1. Multi-byte fields change one byte at a time, so a field written while it is in use passes through mixed values.
- **Configuration write spacing (D24).** Two configuration writes must not occur in consecutive cycles. The host link (section 9) gives at most one write per completed SPI byte, so it holds by construction. A configuration write in the two cycles after `rst_q` rises is ignored.

## 2. Pins

- Raw inputs are synchronised: `s1' = raw`, `s2' = s1`, `sp' = s2`. The **synchronised level** of input pin k is `PIN[k] = s2[k]`. `RISE[k] = s2 & !sp`, `FALL[k] = !s2 & sp`.
- Input pins P0..P12 are `uio_in[0..7]`, `ui_in[3..7]`. A pin select of 13..15 reads constant 0 and has no edges.
- The host link uses `ui_in[0..2]` (SCK, CS_N, MOSI) through the same synchronisers and drives `uo_out[0]` (MISO) and `uo_out[1]` (IRQ) from registers.
- Output pins O0..O13 are `uio_out[0..7]`, `uo_out[2..7]`. `uio_oe[i]` is O_i's output-enable register (section 8).

## 3. Lines (l = 0..3)

A line is a beat generator plus the pins it samples, its input symbol and its output symbol. Threads (section 4) are bound to one line; ports named `L.*` refer to the executing thread's line.

### 3.1 Configuration and state

Configuration: `INC, MOD, T0, T1, T2, PRE, WLO, WHI` (16 bits each); `EDGE` (pin 4 bits, polarity 2 bits: 0 none, 1 rise, 2 fall, 3 both), `WEN`, `FOLLOW`; `T0EDGE` (pin, polarity), `T0SRC`; `SNAP` (2 bits); `PINA, PINB` (4 bits); `LUT0, LUT1` (32 bits).

State: `PH` (16); `RUN, ARM, REN`; `SC, SP`; `FIRED[2:0]`; working samples `W = {B1, A2, A1, A0}`; snapshot `SN` (4); remembered bit `REM`; `STAGED, COMMITTED` (4 bits each); sticky `TAPMISS`.

### 3.2 Beat generator

In cycle t:

```
edge   = polarity-selected RISE/FALL of PIN[EDGE.pin]        (0 if pin >= 13 or polarity 0)
e0     = polarity-selected RISE/FALL of PIN[T0EDGE.pin]      (same rule)
inwin  = (WLO <= WHI) ? (WLO <= PH && PH <= WHI) : (PH >= WLO || PH <= WHI)
start  = edge && ARM && !RUN
accept = edge && RUN && REN && (!WEN || inwin)
adv    = RUN && !accept
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
if RUN' && !RUN:  FIRED'[k] = (k is an enabled phase tap) && (Tk <= PH')       (taps behind the starting phase count as fired)
elif BEAT:        FIRED'[k] = next_k
else:             FIRED'[k] = FIRED[k] || cur_k
TAPMISS' = TAPMISS || (BEAT && some enabled k has !FIRED[k] && !cur_k)
SEG = popcount(FIRED)                                                            (2 bits)
```

`TAPMISS` is sticky until the host clears it. `SEG` is the number of taps fired so far in the beat; for phase taps in ascending order with no re-alignment it equals the v1 segment (calculated).

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

If `BEAT` in cycle t: `COMMITTED' = STAGED'` (a write in the boundary cycle is committed).

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

**Host map.** Addresses, register layouts and access types are generated from `machine.HOST_MAP` and `HOST_BLOCKS` into [ISA_TABLES_V2.md](ISA_TABLES_V2.md#host-address-map). Configuration registers (access W) are write-only and read 0 (D14). Program memory is written by byte lane (byte k of word w of core c at `c*0x800 + 8w + k`) and reads 0. Unmapped addresses read 0 and ignore writes. Multi-byte registers are little-endian; each byte is written independently. Host writes take priority over moves and hardware updates of the same state, except where a section above says otherwise; a sticky flag set in the same cycle as a host clear stays set.

Runtime registers (flops):

- `CTRL.RUN` bit 0 is `RUN_global`. `STICKY` reads `{MEMHAZ, CONFLICT}` in bits 1, 0, write 1 to clear. `IRQEN` bits 0, 1. `DOORBELL` reads 0; writing bit t in cycle W makes `DB[t] = 1` in cycle W+1 only. `HOSTIN` writes `INB` and sets `INV`, reads `INB`. `HOSTOUT` reads `OUTB`. `HOSTSTAT` reads `{OUTV, INV}` in bits 1, 0; writing 1 to bit 1 clears `OUTV`. `ID` reads `0xA2`. `ERRSUM` reads `{MEMHAZ, CONFLICT, any STARVED, any TAPMISS, any OVR, any LATE}` in bits 5..0.
- Line runtime: `PHASE` reads and writes `PH`. `CTL` bits 0..2 read and write `RUN, ARM, REN` (section 3.2); reads also give `SYNC` in bit 3 and `FIRED` in bits 6:4. `SYM` reads `{COMMITTED, STAGED}`. `INS` reads `{IN, REM, SN}` in bits 6:0. `STAT` bit 0 reads `TAPMISS`, write 1 to clear.
- Thread runtime: `PC` reads and writes. `STAT` reads `{OVR, LATE, EN, ARMED, RUNNING, READY}` in bits 5..0; a write sets `EN` from bit 3 and clears `LATE` or `OVR` where bit 4 or 5 is 1. A host clearing `LATE` writes `EN` as well, so it must write the current `EN`.
- Stream runtime: `POSL`, `POSH` (`{STARVED, BIDX, POS[11:8]}`), `CTL` (write-only; section 6.3).

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
| Clock modes | generated, edge-started, recovered | adds follower mode and an edge-sourced tap 0 |
| Input | 2-bit symbol from 16-entry tables over `CAP`, visible per tap | 2-bit symbol from 32-entry tables over an atomic snapshot and a remembered bit |
| Output | 2-bit symbol, one write port | 4-bit symbol; whole, data-bit and exclusive-or ports, one write group per line |
| Pin tables | 4 inputs | 5 inputs: three chosen symbol bits and `SEG` |
| Core | first instruction at t+2; bursts back to back | registered instruction, first at t+3; one idle cycle per taken jump and per dispatch |
| Jumps | on the move condition | on a separate 5-bit condition over 32 guards |
| Units | 4 shifters, 4 counters, 2 pointers | 2 shifters, 3 counters, 1 pointer, 2 streams; LFSR output bit as a source |
| Configuration | flops, cleared by synchronous reset | latches, cleared by reset, seen two cycles after a write; no consecutive writes |
| Host map | `machine.HOST_MAP` (v1) | regenerated; ID `0xA2`; per-line `TAPMISS`, per-stream `STARVED`, `ERRSUM` |
