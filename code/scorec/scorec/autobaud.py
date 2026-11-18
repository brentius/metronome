"""Autobaud, plan B (V3 plan C item 2, rival-ideas section 2.6): the chip measures, the host sets the divider.

SPEC_V2 decides plan A is not available: line configuration (`INC`, `MOD`, taps, `PRE`) is host-written, write-only
latch state; no move destination reaches it (3.1, 9: "program-invisible state").  A follower line with a window can
re-align a *phase* to edges (`accept`), but the beat length stays `MOD/INC`, so it tolerates only a few percent.

Plan B adds three resources to a `started by` UART receiver (LIN slave style) and leaves its own line disarmed:

* line 1   free-running ruler, one tick every `tick_cycles` chip cycles (default 12); thread 1 decrements the 16-bit
           CNT1 on each tick.
* line 2   pin A = the receive pin; its falling edges trigger thread 2.
* thread 2 on each of the first `frames` (6) falling edges: snapshot CNT1, append the 16-bit raw down-count to the
           data RAM log at address 0, post the remaining-record count (6..1) to the host mailbox, and raise flag 5, on
           which the ruler thread reloads CNT1 to 0xFFFF at its next tick (the reload is in the ruler's own thread so
           that the two never write CNT1 in one cycle).  A record is therefore the interval since the previous fall,
           in ticks, up to one tick short.

LIN header: break (>= 13 bit times low), delimiter, sync char 0x55 (falls at t = 0, 2, 4, 6, 8 bit times).  The six
logged falls are: break start (interval since power-up, ignore), break end + delimiter start (the break and
delimiter, many bit times), then four intervals of 2 bit times each.  The host reads the log after mailbox byte 1,
computes the bit time from the four 2-bit intervals, and rewrites line 0's `INC/MOD/taps/PRE` and arms it (a handful of
host config bytes, `host2/autobaud`) before the first data character starts (>= 2 bit times after the last
logged fall).  Everything else of the receiver is unchanged.
"""
from __future__ import annotations

from .ctx import emit_threads  # noqa: F401
from .emit import imm

FRAMES = 6
LOG_BASE = 0


def add_measurement(x, rx_pin):
    opts = x.opts["autobaud"]
    tick = int(opts.get("tick_cycles", 12))
    n = int(opts.get("frames", FRAMES))
    x.b.block(".line 1", ["inc 1", f"mod {tick}", "taps - - -", "ctl run"])
    x.b.block(".line 2", ["inc 1", f"mod {tick}", "taps - - -", f"pins A=P{rx_pin}"])
    k = x.b.cores[1]                  # the ruler has core 1 to itself, so its burst bound stays under one tick
    k.label("tick")
    k.i([], goto="reload", jmode="if", jcond="F5", note="a fall asked for an interval restart: decided once per burst")
    k.i(["ZERO -> CNT1.DEC"], goto="tick", pause=True, note="ruler tick")
    k.label("reload")
    k.i([imm(255, "CNT1.LO")], note="restart the interval counter")
    k.i([imm(255, "CNT1.HI")])
    k.i([imm(5, "FLAGS.CLR")])
    k.i([], goto="tick", pause=True)
    c = x.b.cores[0]
    c.label("fall")
    c.i(["CNT1.LO -> R0", "CNT1.HI -> R1"], note="falling edge: snapshot the interval counter")
    c.i(["! R0 -> P0.W"], when="CNT2.Z", note="log the raw down-count of this interval (first N falls only)")
    c.i(["! R1 -> P0.W"], when="CNT2.Z")
    c.i(["! CNT2.LO -> HOST.OUT"], when="CNT2.Z", note="progress to the host: records still to come, 1 = last one logged")
    c.i(["! " + imm(5, "FLAGS.SET")], when="CNT2.Z", note="ask the ruler to restart the interval counter (first N falls only)")
    c.i(["! ZERO -> CNT2.DEC"], when="CNT2.Z")
    c.i([], goto="fall", pause=True)
    x.init_moves += [imm(255, "CNT1.LO"), imm(255, "CNT1.HI"), imm(n, "CNT2.LO"), "ZERO -> P0.AL", "ZERO -> P0.AH"]
    x.host["autobaud"] = {"plan": "B", "tick_cycles": tick, "records": n, "log_base": LOG_BASE,
                          "log_layout": "n x uint16 little-endian raw down-counts; interval ticks = 0xFFFF - raw",
                          "mailbox": "records remaining after the one just logged is NOT posted; value = records still "
                                     "to come including this one (n..1); 1 means the last record is in the log",
                          "armed_by_host": True}
    x.host["mailbox_out"].append("autobaud progress (n..1), then frame status bytes once the host arms line 0")
    return [(1, 1, 1, "L1.BEAT", "tick"), (2, 0, 2, "PINA.FALL", "fall")]
