# Metronome v2 stream unit: sizing run

Evidence class: **synthesized estimate** (yosys synth + abc, pre-placement, flat module, no routing) plus **RTL-simulated** behaviour. Not timing-closed, not placed.

- Date 2026-11-12. Tool: Yosys 0.70+190 (git 485b63564), OSS CAD Suite 2026-10-22. Library `build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib` (IHP sg13cmos5l, typical 1.20 V 25 C).
- RTL `rtl/md2_stream.v` (Verilog-2005, Verilator `-Wall` clean). Flow `area_stream.py` / `area_stream.ys`; log `stream_area.log`.
- Tests: `python -m pytest code/tests/v2_sizing/test_stream.py -q` (Icarus + cocotb 2.1): 7 cocotb tests + Verilator lint, 8 passed.

## Result

| Item | Value |
|---|---|
| Area, one stream | 7787 um2 (445 cells) |
| Sequential | 3968 um2 (81 `dfrbpq_1`, 51%) |
| Two streams | about 15.6k um2 |
| V2_DESIGN 4.8 ledger | +10k um2 for two streams |

The ledger is low by about 5.6k um2 (56%) for two streams. Flop budget: ba 11, pos 12, wbuf 32, sh 8, pend 8, bitidx 3, flags 7. The 32-bit lookahead word is 40% of the flops, and each flop sits behind an enable mux. Possible reductions (not tried): hold `wbuf` in the resettable latch cell the design already prices for latch banks; share the 12-bit `pos == LEN` and `pos == MARK` comparators with the program counters; drop `byte_out`/`pend` replication. The area is dominated by flops and the two 12-bit equality comparators, not by the request FSM.

## Contract decisions

Where the brief left a rule open, these were chosen (simplest first):

1. Port `bit` is named `bit_out` (`bit` is a SystemVerilog keyword).
2. Config (`cfg_*`) is sampled live. Changing mode, MSB or START needs a rewind. LEN and MARK may change any time.
3. Reset clears all state. A one-bit `inited` flag makes the first cycle after reset act as an implicit rewind, so START is loaded without a host action.
4. **Transmit.** `sh` holds the current byte and `wbuf` the word of lookahead. Bit order is applied by indexing `sh`. A refill is requested when `wbuf` is exhausted (the lane-3 byte moved to `sh`), so the next word has one whole byte time to arrive (48 cycles at Ethernet rate; in simulation with prompt grants it arrives in 4 cycles). Bytes are always taken from lane `ba[1:0]` so START may be unaligned.
5. After rewind (and the implicit one) the first byte is available about 4 cycles later with prompt grants. An ADV earlier than that is **ignored and sets `starved`**; the stream does not move.
6. `bit_out` is 0 when `sh` is not valid, at END, and in receive mode. `byte_out` is the raw `sh` register (the current byte in memory order; stale or 0 when invalid; the assembling byte in receive mode).
7. Advancing at a byte boundary into a byte not yet in `wbuf`: `pos` and `bitidx` advance, `sh` becomes invalid, `starved` sets, and `bit_out` is 0 until the word arrives. The following ADVs, while `sh` is still invalid, are ignored (and keep `starved` set). The stream therefore never loses its place; the program's bits during the stall are wrong and the frame must be treated as failed.
8. ADV at END (pos == LEN) does nothing. The unit may prefetch up to one word beyond the region (read only; the address wraps at 2 KB).
9. `MARK` = `pos == cfg_mark && bitidx == 0`; `BYTE` = `bitidx == 0`; `END` = `pos == LEN`.
10. **Receive.** A bit is placed at its bit-order position in an 8-bit assembly register that is cleared at every byte start, so unfilled bits are 0 after a flush. A completed byte moves to the single `pend` buffer and is written with a one-lane write mask at address `ba` (`START + bytes written`). `ba` increments when the write is granted. The assembly register keeps accepting bits while `pend` waits.
11. Overflow: a byte completing while `pend` is occupied and not granted that same cycle is **dropped**, `starved` sets, `pos` still advances, and `ba` does not. Later bytes land one position early. The frame is failed until rewind.
12. Receive ignores bits at END (pos == LEN): no write, no pos change.
13. Flush (`ctl[1]`) completes a partial byte and advances `pos`. Flush with an empty assembly register (`bitidx == 0` and no bit this cycle) does nothing. A bit arriving in the same cycle as a flush is included. Flush in transmit mode is ignored. `pos` after a flush counts the partial byte (the host derives the bit count as `8*pos - (8 - bitidx_before_flush)`; the bit index is lost after flush, so software wanting the exact bit length must read `bitidx` first).
14. Rewind (`ctl[0]`) resets `pos`, `bitidx`, the lookahead and any outstanding or in-flight read, and **drops a pending receive write**. Rewind has priority over a simultaneous ADV, `rx_bit_we` or flush. A grant that arrives in the same cycle as a rewind is discarded (a stale read result is never used).
15. `starved` is sticky and cleared only by `clr_starved` (or reset). It is not cleared by rewind. If `clr_starved` and a new starve event coincide, the event wins.
16. RAM interface: `req` is a level held until `gnt` (tx read request, rx pending write). Receive write data is the byte replicated in all four lanes with only the target lane's mask bit set. `gnt` without `req` is ignored in transmit; in receive `gnt` is assumed to come only with `req`.

## Evidence of behaviour

Bench `code/tests/v2_sizing/tb_stream.py` runs a behavioural 512 x 32 synchronous RAM and an arbiter that can withhold grants. Verified in simulation (RTL, not against a separate reference model): transmit of 5 bytes at START 5 in both bit orders with ADV every cycle and every 6 cycles (each bit, BYTE, MARK, END, pos, bitidx, byte_out); 16 bytes at START 0, 1, 2, 3 and at the top of the RAM; receive of 2 bytes plus a 3-bit flushed tail with unwritten neighbour bytes preserved (both bit orders); receive stopping at END; flush with nothing pending; receive overflow setting `starved`; transmit with prompt grants at 6-cycle pacing never starving and with the second fetch withheld starving exactly on entering byte 4; `clr_starved`; rewind mid-frame replaying from START.

## Open issues

- Area is above the ledger; see the reductions above. The 12-bit magnitude of the comparators is a design choice (LEN 0..2048 needs 12 bits).
- Grant latency is the only timing assumption: a grant within about 40 cycles per byte at Ethernet rate. Under the stream-first arbiter this should hold, but arbiter latency with the pointer and host contending is not modelled.
- Not checked: timing at 60 MHz, gate-level simulation, behaviour with the real SRAM macro (the model assumes data valid the cycle after the grant).
