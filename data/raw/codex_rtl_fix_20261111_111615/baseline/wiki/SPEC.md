# Metronome v1: normative machine specification

Status: v1, 2026-11-11. This document is **normative**: the RTL (`code/rtl/`), the cycle-level reference model (`sim/reference/`) and the assembler (`code/host/`) implement exactly this. Names and numbers (field positions, port and guard indices, trigger codes, host addresses) come from `code/md/machine.py` and its generated tables (`wiki/ISA_TABLES.md`, `code/rtl/gen/md_defs.vh`). wiki/ARCHITECTURE.md explains *why*; this file says *what*. Where they disagree, this file wins and the difference is recorded in `BOTS/PLANS/DECISIONS.md`.

## 1. Conventions

- One clock, `clk`, nominally 60 MHz. "Cycle t" is the interval between clock edges t and t+1. All state is registers. A value "at cycle t" is the register value during cycle t. "X' " means the value X takes at the end of cycle t (visible in cycle t+1).
- All combinational quantities in cycle t are functions of register values in cycle t and of the raw input pins.
- Reset (`rst_n` low, synchronous) clears every register in this document to 0, including configuration.
- Unsigned arithmetic unless stated. `{a,b}` is concatenation with `a` most significant.

## 2. Pins

- Raw inputs are synchronised: `s1' = raw`, `s2' = s1`, `sp' = s2`. The **synchronised level** of input pin k is `PIN[k] = s2[k]`. `RISE[k] = s2 & !sp`, `FALL[k] = !s2 & sp`.
- Input-capable protocol pins P0..P12 are `uio_in[0..7]`, `ui_in[3..7]`. A pin select of 13..15 reads constant 0 (no edges).
- The host link uses `ui_in[0..2]` (SCK, CS_N, MOSI) through the same synchronisers, and drives `uo_out[0]` (MISO) and `uo_out[1]` (IRQ) from registers.
- Output pins O0..O13 are `uio_out[0..7]`, `uo_out[2..7]`. `uio_oe[i]` comes from O0..O7's output-enable table.

## 3. Beat generators (g = 0..3)

Configuration: `INC, MOD, T0, T1, T2, PRE, WLO, WHI` (16 bits), `WEN` (bit), `EDGE` (pin select 4 bits, polarity 2 bits: 0 none, 1 rise, 2 fall, 3 both). State: `PH` (16 bits), `RUN, ARM, REN, SC, SP` (bits). `SC` = an edge was accepted in the current beat, `SP` = in the previous beat.

In cycle t:

```
edge   = polarity-selected RISE/FALL of PIN[EDGE.pin]          (0 if pin >= 13 or polarity 0)
inwin  = (WLO <= WHI) ? (WLO <= PH && PH <= WHI) : (PH >= WLO || PH <= WHI)
start  = edge && ARM && !RUN
accept = edge && RUN && REN && (!WEN || inwin)
if RUN && !accept:
    n = PH + INC                     (17-bit)
    wrap = (n >= MOD);  nx = wrap ? n - MOD : n
    BEAT = wrap
    TAPk = (Tk < MOD) && (wrap ? (Tk > PH || Tk <= nx) : (PH < Tk && Tk <= nx))
else:
    BEAT = TAPk = 0
PH'  = (start || accept) ? PRE : (RUN ? nx : PH)
RUN' = RUN || start;   ARM' = ARM && !start
SC'  = accept ? 1 : (BEAT ? 0 : SC);   SP' = BEAT ? SC : SP
SEG  = (PH >= T0 && T0 < MOD) + (PH >= T1 && T1 < MOD) + (PH >= T2 && T2 < MOD)     (2-bit segment)
```

A move to `BGg.CTL` in cycle t sets `RUN' = bus[0], ARM' = bus[1], REN' = bus[2]`, overriding the lines above; `PH'` is unaffected. Host writes to `PHASE` or `CTL` behave the same way and take priority over moves. `SEG` assumes `T0 <= T1 <= T2`.

## 4. Engines (e = 0..5)

Configuration: `EN` (bit), `CORE` (bit), `BG` (2 bits), `TRIG` (5 bits, codes in ISA_TABLES), `PINA, PINB` (4 bits), `LUT0, LUT1` (16 bits), watchers `W0C, W1C` (6-bit guard index, 0 disables) and `W0H, W1H` (8-bit handler address). State: `PC` (8), `READY, RUNNING, ARMED` (bits), `STAGED, COMMITTED` (2 bits), `CAP = {B1,A2,A1,A0}` (4 bits), sticky `LATE, OVR`.

Let `B` be the engine's beat generator and `pa = PIN[PINA]`, `pb = PIN[PINB]` (0 for selects >= 13).

- **Capture.** `B.TAP0: A0' = pa`. `B.TAP1: A1' = pa, B1' = pb`. `B.TAP2: A2' = pa`.
- **Input symbol.** `IN = {LUT1[CAP], LUT0[CAP]}` (combinational from the `CAP` register).
- **Trigger event** `trig` in cycle t: `EN && event(TRIG)`, or a host doorbell write for this engine in cycle t (also requires `EN`). Events: `BGg.BEAT/TAPk` of cycle t; `FLAGk.RISE` = `F[k] && !FP[k]` (FP is last cycle's flags, see 6.1); `PINA.RISE/FALL/EDGE` from the synchroniser of `PINA`; `HOST.INV` = `INV && !INVP` (rising); `ALWAYS` = `!READY && !RUNNING`.
- On `trig`: if `READY || RUNNING` then `OVR' = 1` and the trigger is dropped; otherwise `READY' = 1, ARMED' = 1`.
- **Commit.** If `B.BEAT` in cycle t: `COMMITTED' = (E.SYM written for e in cycle t) ? bus[1:0] : STAGED`, and `ARMED' = 0` unless a trigger in the same cycle sets it to 1 (the trigger wins).
- **Symbol write.** An enabled move to `E.SYM` by the core executing e: `STAGED' = bus[1:0]`; if `ARMED == 0` then `LATE' = 1` (written after its beat boundary already committed).
- **Stop.** An enabled move to `E.STOP`: `EN' = 0`. The current burst continues to its pause; no new triggers are accepted.

## 5. Cores (c = 0..1)

Each core has a 256 x 64 program memory with a synchronous read: the address registered at the end of cycle t selects the word `I` visible during cycle t+1. State: `XV` (executing), `XE` (engine, 3 bits), `XPC` (8 bits).

In cycle t, with `G[i]` the guard conditions (section 7) evaluated on cycle-t state, `E.*` referring to engine `XE`:

```
free = !XV
if XV:
    C = G[I.cond]
    for each move m: en_m = guard_m==always || (guard_m==if && C) || (guard_m==ifnot && !C)
                     if en_m: write SRC[I.src_m] (read in cycle t) to DST[I.dst_m] at end of cycle
    taken = jmode==always || (jmode==if && C) || (jmode==ifnot && !C)
    npc = taken ? I.imm : (XPC + 1) mod 256
    if I.pause: PC[XE]' = npc; RUNNING[XE]' = 0; free = 1
    else:       addr = npc; XPC' = npc; XV' = 1
if free:
    if RUN_global and some engine e has CORE==c and READY (lowest e wins):
        d = (W0C[e] != 0 && G_e[W0C[e]]) ? W0H[e] : (W1C[e] != 0 && G_e[W1C[e]]) ? W1H[e] : PC[e]
        addr = d; XPC' = d; XE' = e; XV' = 1; READY[e]' = 0; RUNNING[e]' = 1
    else:
        XV' = 0
```

`G_e` evaluates engine-relative guards for engine e. A trigger in cycle t makes `READY` visible in t+1, so the earliest dispatch is t+1 and the first instruction executes in t+2. A burst of n instructions on an otherwise idle core occupies cycles t+2 .. t+n+1. A core finishing a burst can dispatch another ready engine in the same cycle, so back-to-back bursts have no gap. Host writes to a core's program memory take priority over fetches; load programs with `RUN_global = 0` and no burst in flight.

## 6. Moves, write groups and conflicts

All moves of all cores in cycle t read their sources from cycle-t state and write at the end of cycle t. Destination ports are partitioned into **write groups** (per unit instance): `ACC.*` (all seven ops); each `Rk`; `SHk.{LD,SH}`; `SHk.CFG`; `CNTk.{LO,HI,DEC}`; `LFk.{ST,B0..B3}`; `Pk.{AL,AH,W,R}`; `FLAGS.{SET,CLR}`; each `BGk.CTL`; `HOST.OUT`; and per engine `E.SYM`, `E.STOP`. `NULL` has no group. If two or more enabled moves target the same group in one cycle, the sticky `CONFLICT' = 1` and only the write with the lowest (core, move index) takes effect.

Source side effects happen only for enabled moves: reading `HOST.IN` clears `INV`; reading `Pk.D` while `Pk.RDY == 0` sets sticky `MEMHAZ` (the stale byte is returned).

### 6.1 Units

- **Flags** `F[15:0]`. `SET n: F[n]' = 1`. `CLR n: F[n]' = 0`. `FP' = F` every cycle (for rise triggers).
- **Accumulator** `A` (8), `Z, C, N`. `LD: A'=v`. `ADD: r=A+v, A'=r[7:0], C'=r[8]`. `SUB: r=A-v, A'=r[7:0], C'=(A>=v)`. `AND/OR/XOR: A'=A op v`. `CMP: r=A-v, C'=(A>=v)`, A unchanged. Every op sets `Z'=(result==0)`, `N'=result[7]` (result = r or the new A). Scratch `Rk' = v`.
- **Shifter** `D` (8), `CNT` (4), `LEN` (4, 0 means 8), `MSB`. `LD: D'=v, CNT'=LEN?LEN:8`. `SH: D' = MSB ? {D[6:0],v[0]} : {v[0],D[7:1]}, CNT' = CNT ? CNT-1 : 0`. `CFG: LEN'=v[3:0], MSB'=v[4]`. Out bit `O = MSB ? D[7] : D[0]`. `DONE = (CNT == 0)`.
- **Counter** `V` (16). `LO: V[7:0]'=v`. `HI: V[15:8]'=v`. `DEC: V' = V ? V-1 : 0`. `Z = (V == 0)`.
- **LFSR/CRC** `S` (32), `POLY` (32, host-set). `ST: fb = S[0]^v[0]; S' = (S >> 1) ^ (fb ? POLY : 0)`. `Bk: S[8k+7:8k]' = v`. `OUT = S[0]`. This is the reflected (LSB-first) Galois form; MSB-first CRCs use the bit-reversed polynomial and state (the assembler converts).
- **Pointers and data RAM** (2048 bytes, one access per cycle). Pointer state `PTR` (11), `D` (8), `RDY`, and one pending request `REQ` (none, fetch, write+addr+data).
  - `AL: PTR[7:0]'=v`; `AH: PTR[10:8]'=v[2:0]`; both clear `RDY` and set `REQ = fetch`.
  - `W: REQ = write(PTR, v); PTR' = PTR+1; RDY' = 0`. `R: PTR' = PTR+1; RDY' = 0; REQ = fetch`.
  - Setting `REQ` while one is pending overwrites it and sets sticky `MEMHAZ`.
  - The memory arbiter serves one request per cycle in priority P0, P1, host. A write request writes in the cycle it is served. A fetch served in cycle t reads `mem[PTR]` (PTR as of cycle t) and loads `D' ` at the end of cycle t+1 with `RDY' = 1`, so `RDY` is visible from t+2.
- **Host mailbox.** `HOST.OUT: OUTB'=v, OUTV'=1`. Host write of `HOSTIN`: `INB'=v, INV'=1`. Host write of 1 to `HOSTSTAT` bit 1 clears `OUTV` (section 9; host reads have no side effects). `INVP' = INV` every cycle.

## 7. Guard conditions

Indices are in `wiki/ISA_TABLES.md`. Guard 0 is constant true. Engine-relative guards (`E.IN0, E.IN1, E.SYNC, E.PINA, E.PINB`) use the executing engine (or, for watchers, the engine being dispatched): `E.IN*` are the bits of `IN`, `E.SYNC` is `SP` of the engine's beat generator, `E.PINA/B` are `PIN[PINA/B]`.

## 8. Output cells (o = 0..13)

Configuration: `ENG` (3 bits; 6 and 7 mean unbound), `LUT` (16), `OE` (16, o < 8). Each cycle: `idx = {SEG of ENG's beat generator, COMMITTED of ENG}` (0 when unbound); `OUT[o]' = LUT[idx]`, `OEN[o]' = OE[idx]`. The pin outputs are these registers.

## 9. Host link (SPI target, mode 0)

Let `SR` (rise) and `SF` (fall) be the synchronised edge events of `SCK` (section 2) and `CS = !PIN(CS_N)` the synchronised select. When `CS` is 0: bit count, byte count and transmit register are cleared, the command is cleared and `MISO' = 0`. When `CS` is 1:

- In a cycle with `SR`: `RX' = {RX[6:0], MOSI}` (synchronised MOSI of the same cycle) and the bit count increments. The cycle with the 8th `SR` of a byte **completes** the byte (value `{RX[6:0], MOSI}`) and processes it in that cycle:
  - Byte 0: command. `0x02` write, `0x03` read; any other value makes the link ignore the rest of the transaction.
  - Byte 1: address high. Byte 2: address low. For a read command, completing byte 2 issues a read of `ADDR` and sets `ADDR' = ADDR + 1`.
  - Write command, bytes 3 onward: the byte is written to `ADDR` (effect at the end of this cycle; data-RAM writes are queued to the arbiter as a host request) and `ADDR' = ADDR + 1`.
- Read data path: an issued read loads the holding register `HRD`: register-mapped addresses at the end of the issuing cycle; data-RAM addresses when the arbiter serves the host request (the byte lands at the end of the cycle after service). In a cycle with `SF`: if the previous completed byte was byte 2 or later of a read command and its byte has not been loaded yet, `TX' = HRD` and a read of `ADDR` is issued with `ADDR' = ADDR + 1`; otherwise `TX' = {TX[6:0], 0}`. `MISO' = TX[7]` every cycle (registered output).

Each program-memory byte is written directly into its byte lane of the addressed word (little-endian: byte k of word w is host address `PROG_BASE + core*0x800 + 8w + k`), using the SRAM's bit mask; there is no staging register. Program memory reads return 0. Keep SCK at or below clk/16 (3.75 MHz at 60 MHz). `IRQ' = (IRQEN[0] && OUTV) || (IRQEN[1] && any sticky error)`, where the sticky errors are CONFLICT, MEMHAZ and every engine's LATE and OVR.

**Registers.** The host map (`code/md/machine.py`: `HOST_MAP` and the `*_REGS` tables) lists every host register; multi-byte registers are little-endian and each byte is written independently. Only the registers in `HOST_READABLE` (beat generator `PHASE`, `CTL`; engine `PC`, `SYM`, `STAT`) and the `CTRL` block are readable; all other configuration registers (beat generator `INC`..`WHI`, `EDGE`; engine `CFG`..`W1H`; output cells; LFSR `POLY`) are **write-only and read 0** (D14, to save the read-back multiplexer area). Readable registers read back their state (undefined bits read 0). Beat generator `PHASE` reads `PH`, writing sets `PH`; `CTL` bits are RUN, ARM, REN, WEN. Engine `PC` is read/write; `SYM` is read-only (`{COMMITTED, STAGED}`); `STAT` reads `{OVR, LATE, 0, ARMED, RUNNING, READY}` in bits 5,4,3,2,1,0, and writing 1 to bit 4 or 5 clears `LATE` or `OVR`. `CTRL.RUN` bit 0 is `RUN_global`. `STICKY` reads `{MEMHAZ, CONFLICT}` in bits 1,0 and is write-1-to-clear. `DOORBELL` reads 0; writing bit e triggers engine e in the cycle the byte completes. `HOSTIN` writes `INB` and sets `INV` (reads return `INB`). `HOSTOUT` reads `OUTB` (no side effect). `HOSTSTAT` reads `{OUTV, INV}` in bits 1,0; writing 1 to bit 1 clears `OUTV` (the host acknowledges the outgoing byte). **No host read has a side effect** (reads prefetch one address ahead, see above). `ID` reads `0xA0 | VERSION`. LFSR `POLY` is write-only (D14). Unmapped addresses read 0 and ignore writes. Host writes take effect at the end of the completing cycle and take priority over moves to the same state.

## 9a. Resolutions of edge cases (normative, 2026-11-11, D11)

1. **Unused encodings.** Source indices beyond the table read 0; destination indices beyond the table are `NULL`; guard indices beyond the table evaluate **false** everywhere (instruction condition and watchers); trigger codes beyond the table never fire.
2. **Request overwrite.** `MEMHAZ` is set only when a pointer (or the host) replaces a request that is still unserved at the end of the cycle. A request served in cycle t may be followed by a new one set in cycle t without a hazard.
3. **RDY precedence and stale landings.** If a pointer move that sets a request (`AL`, `AH`, `W`, `R`) happens in the cycle a fetch is served or in the cycle it lands, `D` loads the landing byte but `RDY'` is 0; only the newer request's landing sets `RDY`. (Without this, `P0.AL` at t then `P0.AH` at t+1 would show `RDY` with a byte read from the old high address.)
4. **Host request slot.** The host has one data-RAM request slot; a new host request overwrites an unserved one (no flag).
5. **Mailbox precedence.** A `HOST.OUT` move and a host clear of `OUTV` in the same cycle: the move wins (`OUTV' = 1`). A host `HOSTIN` write and a `HOST.IN` read in the same cycle: the write wins (`INV' = 1`).
6. **Beat generator range.** Programs must keep `INC < MOD` (the toolchain checks). The 17-bit sum is reduced once and stored in 16 bits.
7. **Flags.** `Z` for ADD, SUB and CMP is computed on the 8-bit result.
8. **Program loading.** A fetch in a cycle with a host program-memory write to the same core is undefined, and a word fetched while only some of its bytes have been rewritten executes the mix; load programs while the core is idle (`RUN_global = 0` and no burst in flight).
9. **Host read address.** The first read of a transaction uses the address completed by byte 2, i.e. `{byte 1, byte 2}`.
10. **Segments.** Taps with `Tk >= MOD` neither fire nor count in `SEG`. With `T0 = T1 = T2 = 0` a running generator has `SEG = 3`; to use fewer segments put unused taps at or above `MOD`.

## 10. The timing contract (what a program may rely on)

1. Inputs used by a burst are the `CAP` values captured at the engine's taps; they are stable from a tap until the same tap in the next beat.
2. Outputs written by a burst take effect at the first `BEAT` of the engine's beat generator after the trigger, independent of which instructions ran, provided the write happens no later than that cycle.
3. A late write sets `LATE`; a trigger during a burst (or before dispatch) sets `OVR`; a contested write group sets `CONFLICT`; a data-RAM hazard sets `MEMHAZ`. Flags are sticky until the host clears them.
4. The assembler's static check (wiki/TOOLCHAIN.md) bounds every burst and every engine's worst-case dispatch delay so that 2 and 3 hold for accepted programs.
