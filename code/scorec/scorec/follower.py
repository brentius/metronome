"""Follower template: a role that has no clock of its own and follows another role's clock wire (SPEC A 5.2 `follow`,
SPEC B 3.3).  Compiled shape: a chip-select framed full-duplex byte exchange (SPI mode 0 peripheral, spec 16.3).

Resources (SPEC B 3.3, 3.6, D28):

* line 0   follower: boundary = the clock's accepted fall (the output bit changes), tap 0 = the clock's rise (the
           input bit is captured, an edge-sourced tap), pin A = the data-in wire; running only inside a frame.
* line 1   follower on the same fall; it owns the output pin table (so that threads bound to it stage the output bit)
           and watches the chip-select wire with pin A for the pin-edge triggers.
* thread 0 (L1.BEAT)       stages the next output bit from transmit stream 0 at every boundary.
* thread 1 (L0.TAP0)       appends the captured bit to receive stream 1.
* thread 2 (L1 PINA.FALL)  chip select asserted: stage output bit 0 and bit 1, start both lines (the start commits the
                           staged bit before the first clock edge, D28), rewind the receive stream.
* thread 3 (L1 PINA.RISE)  chip select released: stop line 0, return the output to idle (a start-then-stop pulse
                           commits the idle symbol), rewind the transmit stream so its first byte is prefetched.
"""
from __future__ import annotations

from .ctx import RX_BASE, TX_BASE, Ctx, emit_out_pins, emit_threads
from .emit import imm
from .flatten import field_bits
from .plan import CompileError, driven_wires, plan_rx, plan_tx


def compile_follower(x: Ctx, follow_period):
    score, role, clk = x.score, x.role, x.clk
    clock = score.clock_for()
    rc = clock.roles[role]
    if not rc.cap_wire:
        raise CompileError("E-UNSUPPORTED", f"role {role}: a follower needs 'capture on WIRE rise|fall' (the input tap)")
    clkw = rc.wire
    pins = {w: x.bind.get(w, (None, None)) for w in x.bind}
    for w in (clkw, rc.cap_wire):
        if pins[w][0] is None:
            raise CompileError("E-BIND", f"wire '{w}' needs an input pin P<k>")
    # ---- frame shape: select { own || peer }* deselect, framed by the edges of one wire
    frame = x.frame
    kinds = [s.kind for s in frame]
    if kinds != ["sym", "star", "sym"] or len(frame[1].body) != 1 or frame[1].body[0].kind != "dup":
        raise CompileError("E-UNSUPPORTED", "follower template: only 'select { a || b }* deselect' frames are compiled")
    edges = [r for r in score.recognise if r.kind == "edge" and r.edge in ("falls", "rises")]
    fall = [r for r in edges if r.edge == "falls"]
    rise = [r for r in edges if r.edge == "rises"]
    if len(fall) != 1 or len(rise) != 1 or fall[0].wire != rise[0].wire:
        raise CompileError("E-UNSUPPORTED", "follower template: needs recognised events 'W falls' and 'W rises' for the "
                                            "frame start and end")
    csw = fall[0].wire
    if pins[csw][0] is None:
        raise CompileError("E-BIND", f"wire '{csw}' needs an input pin P<k>")
    own = [t for t in frame[1].body[0].sides if len(t) == 1 and t[0].kind == "field" and t[0].owner == role]
    peer = [t for t in frame[1].body[0].sides if len(t) == 1 and t[0].kind == "field" and t[0].owner != role]
    if not own or not peer or (field_bits(own[0][0]) or 0) % 8:
        raise CompileError("E-UNSUPPORTED", "follower template: '||' sides must be one whole-byte field each")
    f_own, f_peer = own[0][0], peer[0][0]
    # ---- the data input: the wire the capture rises on is the wire sampled
    nominal = None
    if clock.rate:
        nominal = float(60e6 / float(clock.rate))
    mod = int(follow_period or (4 * nominal if nominal else 0))
    if not mod:
        raise CompileError("E-RATE", "follower: pass follow_period=<longest clock period in cycles> (the score gives no rate)")
    minper = max(4, int(nominal / 2)) if nominal else 8
    minhalf = max(2, minper // 2)
    driven = driven_wires(score, role)
    x.txp = plan_tx(score, role, driven, [])
    # input table: one A capture (slot 0) from the edge-sourced tap 0
    from .plan import explicit_samples
    pts = explicit_samples(score, clock, role, None)
    dw = [w for w in pts if w != clkw]
    if len(dw) != 1:
        raise CompileError("E-UNSUPPORTED", "follower template: exactly one sampled wire")
    wire_in = dw[0]
    frac = next(iter(pts[wire_in]))
    slots = {(wire_in, frac): 0, "A": wire_in, "B": None}
    x.rxp = plan_rx(score, role, [], slots, x.bind, "tap0")
    r = x.rxp
    t = x.txp
    c0, c1 = t.family_codes[(0,)], t.family_codes[(1,)]
    if (c0 ^ c1) != 1 or (c0 & 1):
        raise CompileError("E-UNSUPPORTED", "follower template: data codes must differ in symbol bit 0 alone")
    x.host["tx_stream"] = {"stream": 0, "base": TX_BASE, "fields": [f_own.f.name]}
    x.host["rx_stream"] = {"stream": 1, "base": RX_BASE, "fields": [f_peer.f.name], "capacity_bytes": 0x3E0}
    pk, pm, pc = pins[clkw][0], pins[wire_in][0], pins[csw][0]
    edge_of = {"rise": "rise", "fall": "fall"}
    b = x.b
    # ---- lines
    b.block(".line 0", [f"inc 1", f"mod {mod}", "follow", f"edge P{pk} {rc.edge}", f"t0edge P{pk} {rc.cap_edge}",
                        f"pins A=P{pm}", f"lut0 0x{r.lut0:08X}", f"lut1 0x{r.lut1:08X}", "snap tap0",
                        f"minperiod {minper}", f"minhalf {minhalf}"])
    b.block(".line 1", [f"inc 1", f"mod {mod}", "follow", f"edge P{pk} {rc.edge}", f"pins A=P{pc}",
                        f"minperiod {minper}", f"minhalf {minhalf}"])
    clk.mod = mod
    emit_out_pins(x, 1)
    b.block(".stream 0", ["mode tx", f"order {'msb' if x.msb else 'lsb'}", f"start {TX_BASE}", "len 0"])
    b.block(".stream 1", ["mode rx", f"order {'msb' if x.msb else 'lsb'}", f"start {RX_BASE}", f"len {0x3E0}"])
    emit_threads(x, [(0, 0, 1, "L1.BEAT", "tx"), (1, 1, 0, "L0.TAP0", "rx"),
                     (2, 1, 1, "PINA.FALL", "cs_on"), (3, 0, 1, "PINA.RISE", "cs_off")])
    # ---- code
    c = x.b.cores[0]
    c.label("tx")
    c.i(["! S0.BIT -> L.DBIT", "! ZERO -> S0.ADV"], when="L.PINA", goto="tx", pause=True,
        note="stage while selected; a queued trailing edge must not consume the rewound stream")
    c.label("cs_off")
    c.i(["ZERO -> L.SYM", "ZERO -> L0.CTL", "ZERO -> L1.CTL"],
        note="stage idle and stop both lines before the idle start-commit")
    c.i([imm(5, "L1.CTL")], note="start the output line: the start commits the idle symbol")
    c.i(["ZERO -> L1.CTL", "#1 -> S0.CTL"], note="stop it again; rewind the transmit stream (prefetch next byte)")
    c.i([], goto="cs_off", pause=True)
    k = x.b.cores[1]
    k.label("rx")
    k.i(["L.IN -> S1.RX"], goto="rx", pause=True, note="capture the input bit")
    k.label("cs_on")
    k.i([imm(c0, "L.SYM"), "#1 -> S1.CTL"] if False else [imm(c0, "L.SYM")], note="chip select asserted: kind of the data symbol")
    k.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV", imm(5, "L1.CTL")], note="output bit 0; start the output line (commit)")
    k.i(["ZERO -> L.XOR"] if False else ["S0.BIT -> L.DBIT", "ZERO -> S0.ADV", imm(5, "L0.CTL")],
        note="output bit 1; start the input line")
    k.i(["#1 -> S1.CTL"], note="rewind the receive stream")
    k.i([], goto="cs_on", pause=True)
    x.host["mailbox_out"].append("none (the receive stream's POS tells the length)")
    x.notes.append(f"follower: line period up to {mod} cycles (MOD); assumes the clock is no faster than "
                   f"{minper} cycles per period, {minhalf} per half (check minperiod/minhalf)")
