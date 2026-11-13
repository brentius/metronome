"""Open-drain addressed-bus template: both roles of a score with the shape of SPEC A 16.2 (I2C).

The template is chosen when a score has a `shared` open-drain wire.  Its control structure is fixed; everything else
(symbol codes, pin and output-enable tables, taps, the hold, sample points, recognised events, field widths, the
acknowledge expression and the parameter) is derived from the score.  A score that does not match the shape is
rejected with E-UNSUPPORTED naming the construct.

Shape (names are the score's own):

    TOP     = TRANS*
    TRANS   = START REQ (RSTART REQ)* STOP             START, RSTART, STOP: symbols owned by the controller
    REQ     = h1 .. hn                                 controller fields, 8 bits in all, the last one 1 bit (rw)
              ack:bit by target = (a == p) ? 0 : 1     a: a header field, p: a target parameter (or a constant)
              BODY(rw) if ack == 0
    BODY(w) = { d:u8 by controller  k:bit by target = K }*                  write variant
    BODY(r) = { d:u8 by target      m:bit by controller } until m == 1      read variant
    abort   on E1 -> TOP;  on E2 -> REQ                 E1, E2: 'W rises|falls while V high|low' events

Controller (generated clock, `stretch on V`): line 0 with three phase taps at the split points, the hold on the
stretched wire at the first tap after its release, one thread triggered by the last tap (75 % for 16.2).  The burst
in beat k stages beat k+1, so a value received in beat k (the acknowledge) already decides beat k+1.  The sample
point `at V rise` maps to the hold tap: the tap fires at the observed rise, so a target that stretches the clock is
sampled after it lets go (D35).

Target (`follow V fall, capture on V rise`): line 0 follows the clock wire, its edge-sourced tap 0 captures the data
wire and triggers the protocol thread; the burst at a rise stages the next beat, committed at the next fall.  Two
threads on pin-A edges of the same line implement the recognised events: each sets a flag that a watcher of the
protocol thread turns into the abort target at its next dispatch, and stages idle so that a frame abandoned mid-way
never drives the bus at the next fall.

Host interface (both roles: streams in field order, SPEC A 7.7, with the controller's decisions as choice bits):

* controller transmit stream 0, bits, most significant first: per request the header bits; for a write body
  `1 d7..d0` per byte then `0`; for a read body one `m` bit per byte (1 on the last); then `1` (repeated start,
  another request follows) or `0` (stop).  A go byte in HOST.IN starts one transaction.  A not-acknowledged
  address ends the transaction with a stop at once (the controller chooses `stop`, which the grammar allows).
  HOST.OUT gets 0 after a completed transaction, 1 after an address that was not acknowledged.
* controller receive stream 1: the target's bits in order: `ack`, then per written byte `k`, per read byte `d`;
  flushed to a byte boundary at the stop.  `controller_tx` and `controller_rx` pack and parse both streams.
* target receive stream 1: the controller's fields in order, with record markers because the controller's choices
  (how many bytes, repeated start or stop) are not otherwise visible in a bit stream: `0 1` and the header bits per
  START or repeated START, `1` and 8 data bits per written byte, the `m` bit per read byte, `0 0` per STOP followed
  by a flush to the byte boundary.  `target_rx` parses it.  The first bit of a possible write byte is held back
  until the next rise shows it is data, not a repeated START or STOP.  A transaction aborted inside the header
  leaves a partial record; the flush at the STOP resynchronises the parser.
* target transmit stream 0: the bytes returned by reads, consumed in order across transactions.
* target parameter: one data RAM byte (`host['params']`), read through pointer 0 after each START.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from score.ast import Bin, Cond, Field, If, Name, Num, Ref, Rep, Seq

from .ctx import CONST_BASE, RX_BASE, TX_BASE, Ctx, emit_init_thread, emit_out_pins, emit_threads
from .emit import imm
from .plan import CompileError, Tap, plan_tx, seg_levels

RX_CAP = 0x3E0
PARAM_BASE = CONST_BASE          # target parameters, one byte each


def _unsup(msg, node=None):
    pos = getattr(node, "pos", None)
    where = f"{pos[0]}:{pos[1]}: " if pos else ""
    raise CompileError("E-UNSUPPORTED", f"{where}bus template: {msg}")


def _width(f: Field) -> int:
    t = f.type
    if t.kind == "bit":
        return 1
    if t.kind == "u":
        return t.width
    _unsup(f"field '{f.name}': only bit and uN fields are compiled here", f)


def _items(n):
    return n.items if isinstance(n, Seq) else [n]


@dataclass
class BusShape:
    ctl: str
    tgt: str
    top: str
    req: str
    start: str
    rstart: str
    stop: str
    header: list
    rw: str
    ack: Field
    ack_field: str | None        # field compared with the parameter
    ack_param: str | None
    ack_const: int | None
    write: tuple                  # (data field, ack field, value, rw literal)
    read: tuple                   # (data field, more field, stop value, rw literal)
    events: dict                  # event name -> Recog
    aborts: dict                  # event name -> 'top' | 'req'


def match_shape(score) -> BusShape:
    S = score
    roles = list(S.roles)
    clock = S.clock_for()
    gen = [r for r in roles if clock.roles[r].mode == "generated"]
    fol = [r for r in roles if clock.roles[r].mode == "follow"]
    if len(gen) != 1 or len(fol) != 1:
        _unsup("one role must generate the clock and the other follow it")
    ctl, tgt = gen[0], fol[0]
    top = S.prods[0]
    if not (isinstance(top.body, Rep) and top.body.kind == "star" and isinstance(top.body.node, Ref)):
        _unsup(f"start production '{top.name}' must be 'TRANSACTION*'", top.body)
    tr = S.prods_named(top.body.node.name)
    if len(tr) != 1:
        _unsup(f"production '{top.body.node.name}' must have one variant")
    it = _items(tr[0].body)
    kinds = ["sym" if isinstance(x, Ref) and S.symbol(x.name) else "ref" if isinstance(x, Ref) else type(x).__name__
             for x in it]
    if kinds != ["sym", "ref", "Rep", "sym"] or it[2].kind != "star":
        _unsup(f"transaction '{tr[0].name}' must be 'START REQUEST (RSTART REQUEST)* STOP'", tr[0].body)
    rep = _items(it[2].node)
    if len(rep) != 2 or not (isinstance(rep[0], Ref) and S.symbol(rep[0].name)) or \
            not (isinstance(rep[1], Ref) and rep[1].name == it[1].name):
        _unsup("the repeated part must be 'RSTART REQUEST'", it[2])
    start, req, rstart, stop = it[0].name, it[1].name, rep[0].name, it[3].name
    rq = S.prods_named(req)
    if len(rq) != 1:
        _unsup(f"production '{req}' must have one variant")
    ri = _items(rq[0].body)
    if not ri or not isinstance(ri[-1], If):
        _unsup(f"request '{req}' must end with 'BODY(rw) if ack == 0'", rq[0].body)
    fields = ri[:-1]
    if not all(isinstance(f, Field) for f in fields) or len(fields) < 2:
        _unsup(f"request '{req}' must be fields then the body choice", rq[0].body)
    own = lambda f: f.by or ctl
    header, ack = fields[:-1], fields[-1]
    if any(own(f) != ctl or f.value is not None or f.expect is not None for f in header):
        _unsup("request header fields must be the controller's host fields", header[0])
    if sum(_width(f) for f in header) != 8 or _width(header[-1]) != 1:
        _unsup("the request header must be 8 bits and end with the 1-bit direction field", header[0])
    if own(ack) != tgt or _width(ack) != 1 or ack.value is None:
        _unsup(f"'{ack.name}' must be a 1-bit field by {tgt} with '= EXPR'", ack)
    ack_field = ack_param = ack_const = None
    v = ack.value
    if isinstance(v, Num):
        ack_const = v.value & 1
    elif isinstance(v, Cond) and isinstance(v.c, Bin) and v.c.op == "==" and isinstance(v.a, Num) and \
            isinstance(v.b, Num) and (v.a.value, v.b.value) == (0, 1) and isinstance(v.c.a, Name) and \
            isinstance(v.c.b, Name) and S.param(v.c.b.name) is not None and \
            v.c.a.name in [f.name for f in header]:
        ack_field, ack_param = v.c.a.name, v.c.b.name
    else:
        _unsup(f"'{ack.name}': the acknowledge must be a constant or '(FIELD == PARAM) ? 0 : 1'", ack)
    if ack_field and ack_field != header[0].name or (ack_field and _width(header[0]) != 7):
        _unsup("the compared field must be the first header field, 7 bits", ack)
    body = ri[-1]
    c = body.cond
    if not (isinstance(body.node, Ref) and len(body.node.args) == 1 and isinstance(body.node.args[0], Name)
            and body.node.args[0].name == header[-1].name and isinstance(c, Bin) and c.op == "=="
            and isinstance(c.a, Name) and c.a.name == ack.name and isinstance(c.b, Num) and c.b.value == 0):
        _unsup(f"the body must be 'BODY({header[-1].name}) if {ack.name} == 0'", body)
    write = read = None
    for p in S.prods_named(body.node.name):
        if len(p.params) != 1 or p.params[0][0] != "lit":
            _unsup(f"'{p.name}' variants must be selected by a literal", p.body)
        lit = p.params[0][1]
        b = p.body
        if not isinstance(b, Rep):
            _unsup(f"'{p.name}({lit})' must be a repeat", b)
        bi = _items(b.node)
        if len(bi) != 2 or not all(isinstance(f, Field) for f in bi):
            _unsup(f"'{p.name}({lit})' must repeat a byte field and a 1-bit field", b)
        d, k = bi
        if _width(d) != 8 or _width(k) != 1:
            _unsup(f"'{p.name}({lit})' must repeat a byte field and a 1-bit field", b)
        if b.kind == "star" and own(d) == ctl and own(k) == tgt and isinstance(k.value, Num) and d.value is None:
            write = (d, k, k.value.value & 1, lit)
        elif b.kind == "until" and own(d) == tgt and own(k) == ctl and d.value is None and k.value is None and \
                isinstance(b.arg, Bin) and b.arg.op == "==" and isinstance(b.arg.a, Name) and \
                b.arg.a.name == k.name and isinstance(b.arg.b, Num):
            read = (d, k, b.arg.b.value & 1, lit)
        else:
            _unsup(f"'{p.name}({lit})': expected '{{ data by {ctl}; ack:bit by {tgt} = K }}*' or "
                   f"'{{ data by {tgt}; more:bit by {ctl} }} until more == V'", b)
    if write is None or read is None or write[3] == read[3]:
        _unsup(f"'{body.node.name}' needs one write and one read variant")
    events = {}
    for r in S.recognise:
        for nm in r.names:
            events[nm] = r
    aborts = {}
    for a in S.aborts:
        if a.in_prod is not None:
            _unsup(f"abort 'on {a.event} in {a.in_prod}' is not compiled")
        r = events.get(a.event)
        if r is None or r.kind != "edge_while":
            _unsup(f"abort on '{a.event}': only 'W rises|falls while V high|low' events are compiled")
        if a.target == top.name:
            aborts[a.event] = "top"
        elif a.target == req:
            aborts[a.event] = "req"
        else:
            _unsup(f"abort target '{a.target}': only '{top.name}' or '{req}'")
    return BusShape(ctl, tgt, top.name, req, start, rstart, stop, header, header[-1].name, ack, ack_field, ack_param,
                    ack_const, write, read, events, aborts)


# ---- shared helpers -------------------------------------------------------------------------------------------
def _recode(txp, wires):
    """Re-encode so the data symbol is `base | d` (L.DBIT stages the data bit) with idle 0, keeping R2: every wire's
    waveform depends on at most 3 symbol bits.  The searched space is small (at most 16 codes)."""
    import itertools
    from .plan import _select_bits
    fam = [c for c in txp.classes if isinstance(c.key, tuple) and c.key and c.key[0] == "bit"]
    oth = [c for c in txp.classes if c not in fam]
    if len(fam) != 2 or oth[0].key != "idle":
        return
    if txp.family_codes and (txp.family_codes[(0,)] ^ txp.family_codes[(1,)]) == 1 and \
            not txp.family_codes[(0,)] & 1:
        return
    f0 = next(c for c in fam if c.key == ("bit", 0))
    f1 = next(c for c in fam if c.key == ("bit", 1))
    for base in range(2, 16, 2):
        free = [v for v in range(1, 16) if v not in (base, base | 1)]
        for codes in itertools.permutations(free, len(oth) - 1):
            for c, v in zip(oth[1:], codes):
                c.code = v
            oth[0].code, f0.code, f1.code = 0, base, base | 1
            sel, ok = _select_bits(txp.classes, wires)
            if ok:
                txp.sel = sel
                txp.code_of = {m: c.code for c in txp.classes for m in c.members}
                txp.family_codes = {(0,): base, (1,): base | 1}
                txp.idle_code = 0
                txp.encoding = "search: data symbol = base | d, idle = 0"
                return
    raise CompileError("E-FIT-ENC", "symbols: no 4-bit encoding keeps the data bit in symbol bit 0 and every wire's "
                                    "waveform on at most 3 symbol bits (R2)")


def _codes(x: Ctx):
    t = x.txp
    c0, c1 = t.family_codes[(0,)], t.family_codes[(1,)]
    if (c0 ^ c1) != 1 or (c0 & 1):
        raise CompileError("E-UNSUPPORTED", "bus template: the data symbol's two codes must differ in symbol bit 0 "
                                            "alone, with bit 0 = the data bit")
    return c0, c1


def _lut_slot(slot: int) -> int:
    """Input table 0 that reports the capture slot `slot` (A0, A1 or A2) as the data bit (index {REM,B1,A2,A1,A0})."""
    return sum(((i >> slot) & 1) << i for i in range(32))


def _pin(x: Ctx, wire, which):
    k = x.bind.get(wire, (None, None))[0 if which == "in" else 1]
    if k is None:
        raise CompileError("E-BIND", f"wire '{wire}' needs an {'input pin P<k>' if which == 'in' else 'output pin O<k>'}"
                                     f" for role {x.role}")
    return k


def _data_wire(score):
    sd = score.symbol("bit")
    for w, wave, _ in sd.waves:
        if sd.params and sd.params[0] in wave:
            return w
    raise CompileError("E-UNSUPPORTED", "bus template: no wire carries the data bit")


# ---- controller -----------------------------------------------------------------------------------------------
def compile_controller(x: Ctx, sh: BusShape):
    score, clk = x.score, x.clk
    clock = score.clock_for()
    rc = clock.roles[x.role]
    sda = _data_wire(score)
    sclw = rc.stretch
    if not sclw:
        _unsup(f"the controller ({x.role}) needs 'stretch on WIRE' (the hold)")
    splits = list(clock.split)
    if len(splits) != 3:
        _unsup("the controller needs three split points (four segments)")
    taps = [Tap(i, f, int(round(f * clk.mod)), "split") for i, f in enumerate(splits)]
    # the hold tap: the first tap after the segment in which the controller releases the stretched wire
    rel = None
    for sd in score.symbols:
        if sd.name not in (sh.start, sh.rstart, sh.stop, "bit"):
            continue
        args = (0,) if sd.params else ()
        lv = seg_levels(score, clock, sd, args, sclw)
        for j in range(1, len(lv)):
            if lv[j] == "z" and lv[j - 1] != "z":
                rel = j if rel is None else min(rel, j)
    if rel is None or rel >= 3:
        _unsup(f"the controller never releases '{sclw}' before the last segment")
    htap = rel                   # segment j starts at tap j-1; the first tap after segment j is tap j
    # sample point: the score says `at scl rise`; that is the hold tap (it fires at the observed rise)
    taps[htap].why = f"split+hold {sclw}+sample {sda}"
    x.taps = taps
    x.txp = plan_tx(score, x.role, [sclw, sda], taps)
    _recode(x.txp, [sclw, sda])
    c0, c1 = _codes(x)
    code = x.txp.code_of
    START, RSTART, STOP = code[sh.start], code[sh.rstart], code[sh.stop]
    trig_tap = 2
    if trig_tap <= htap:
        _unsup("the hold tap must precede the last tap")
    psda, osda, pscl, oscl = _pin(x, sda, "in"), _pin(x, sda, "out"), _pin(x, sclw, "in"), _pin(x, sclw, "out")
    if osda >= 8 or oscl >= 8:
        raise CompileError("E-BIND", "open-drain wires need output-enable tables: bind them to O0..O7 (R5)")
    rd_lit = sh.read[3]
    x.host["tx_stream"] = {"stream": 0, "base": TX_BASE,
                           "layout": "per request: header bits; write: (1, 8 data bits)* 0; read: one 'more' bit per "
                                     "byte; then 1 = repeated start, 0 = stop"}
    x.host["rx_stream"] = {"stream": 1, "base": RX_BASE, "capacity_bytes": RX_CAP,
                           "layout": "ack bit; per written byte its ack bit; per read byte 8 data bits; flushed at the stop "
                                     "(controller_rx parses it)"}
    x.host["mailbox_in"].append("go: any byte starts one transaction")
    x.host["mailbox_out"].append("0 = transaction completed, 1 = address not acknowledged (stopped)")
    c = x.b.cores[0]
    hb = sum(_width(f) for f in sh.header)          # 8
    c.label("idle")
    c.i([f"? {imm(START, 'L.SYM')}"], when="HOST.INV", note=f"go byte: stage {sh.start}")
    c.i(["? HOST.IN -> NULL"], when="HOST.INV", goto="req", jmode="if", jcond="HOST.INV", pause=True,
        note="consume the go byte")
    c.i([], goto="idle", pause=True, note="idle, second beat (no go)")
    # header: hb-1 address bits, then the direction bit (remembered in flag 1)
    c.label("req")
    c.i([imm(c0, "L.SYM")], note=f"{sh.req}: first header bit")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV"])
    c.i([imm(hb - 3, "CNT0.LO")], pause=True)
    c.label("hdr")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV", "ZERO -> CNT0.DEC"], goto="hdr", jmode="ifnot", jcond="CNT0.Z",
        pause=True, note="header bits")
    c.i(["? #1 -> FLAGS.SET", "! #1 -> FLAGS.CLR"], when="S0.BIT", note=f"'{sh.rw}' -> flag 1")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV"], pause=True, note=f"stage '{sh.rw}'")
    c.i([imm(c1, "L.SYM")], pause=True, note=f"'{sh.ack.name}' beat: release {sda}")
    c.label("ack")
    c.i(["L.IN -> S1.RX"], goto="nack", jmode="if", jcond="L.IN0", note=f"capture '{sh.ack.name}'")
    c.i([], goto="rd0", jmode="if" if rd_lit else "ifnot", jcond="F1", note="read body?")
    # write body decision bit: 1 = another byte, 0 = end of body
    c.label("wdec")
    c.i(["ZERO -> S0.ADV"], goto="wd0", jmode="if", jcond="S0.BIT", note="choice bit: another data byte?")
    c.label("rdec")
    c.i(["ZERO -> S0.ADV"], goto="rst", jmode="if", jcond="S0.BIT", note=f"choice bit: {sh.rstart} or {sh.stop}")
    c.i([imm(STOP, "L.SYM")], note=f"stage {sh.stop}")
    c.i(["#2 -> S1.CTL"], note="flush the received bits")
    c.i(["ZERO -> HOST.OUT"], goto="aftstop", pause=True, note="report: completed")
    c.label("rst")
    c.i([imm(RSTART, "L.SYM")], note=f"stage {sh.rstart}")
    c.i([], goto="req", pause=True)
    c.label("nack")
    c.i([imm(STOP, "L.SYM")], note=f"not acknowledged: stage {sh.stop}")
    c.i(["#2 -> S1.CTL"], note="flush the received bits")
    c.i(["#1 -> HOST.OUT"], pause=True, note="report: address not acknowledged")
    c.label("aftstop")
    c.i(["ZERO -> L.SYM"], goto="idle", pause=True, note="idle after stop")
    # write data byte
    c.label("wd0")
    c.i([imm(c0, "L.SYM")], note=f"'{sh.write[0].name}' bit 7")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV"])
    c.i([imm(6, "CNT0.LO")], pause=True)
    c.label("wdl")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV", "ZERO -> CNT0.DEC"], goto="wdl", jmode="ifnot", jcond="CNT0.Z",
        pause=True, note="data bits 6..0")
    c.i([imm(c1, "L.SYM")], pause=True, note=f"'{sh.write[1].name}' beat: release {sda}")
    c.i(["L.IN -> S1.RX"], goto="wdec", note=f"capture '{sh.write[1].name}'")
    # read data byte: release the data wire for 8 beats, capture each
    c.label("rd0")
    c.i([imm(c1, "L.SYM")], note=f"'{sh.read[0].name}': release {sda}")
    c.i([imm(6, "CNT0.LO")], pause=True)
    c.label("rdl")
    c.i(["L.IN -> S1.RX", "ZERO -> CNT0.DEC"], goto="rdl", jmode="ifnot", jcond="CNT0.Z", pause=True,
        note="capture data bits 7..1")
    c.i(["L.IN -> S1.RX"], note="capture data bit 0")
    c.i([imm(c0, "L.SYM")], note=f"stage '{sh.read[1].name}' from the host stream")
    stop_v = sh.read[2]
    c.i(["? #2 -> FLAGS.SET", "! #2 -> FLAGS.CLR"], when="S0.BIT", note=f"'{sh.read[1].name}' -> flag 2")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV"], pause=True)
    c.i([], goto="rdec", jmode="if" if stop_v else "ifnot", jcond="F2", note=f"{sh.read[1].name} == {stop_v}: end")
    c.i([], goto="rd0", note="another byte")
    # configuration
    t = " ".join(str(tp.T) for tp in taps)
    x.b.block(".line 0", [f"inc {clk.inc}", f"mod {clk.mod}", f"taps {t}", f"pins A=P{psda}",
                          f"lut0 0x{_lut_slot(htap):08X}", "lut1 0x00000000", f"snap tap{htap}",
                          f"hold P{pscl} high tap{htap}", "ctl run"])
    emit_out_pins(x, 0)
    x.b.block(".stream 0", ["mode tx", "order msb", f"start {TX_BASE}", "len 0"])
    x.b.block(".stream 1", ["mode rx", "order msb", f"start {RX_BASE}", f"len {RX_CAP}"])
    x.b.cfg.append("")
    emit_threads(x, [(0, 0, 0, f"L0.TAP{trig_tap}", "idle")])
    x.notes.append(f"controller: thread 0 runs at tap {trig_tap} and stages the next beat; hold on {sclw} at tap "
                   f"{htap} (P{pscl} high); {sda} sampled at the hold tap (D35)")


# ---- target ---------------------------------------------------------------------------------------------------
def compile_target(x: Ctx, sh: BusShape, follow_period, params):
    score, clk = x.score, x.clk
    clock = score.clock_for()
    rc = clock.roles[x.role]
    if not (rc.cap_wire == rc.wire and rc.edge and rc.cap_edge and rc.edge != rc.cap_edge):
        _unsup(f"the target ({x.role}) must 'follow W fall|rise, capture on W rise|fall' on one wire")
    sclw, sda = rc.wire, _data_wire(score)
    x.txp = plan_tx(score, x.role, [sda], [])
    _recode(x.txp, [sda])
    c0, c1 = _codes(x)
    psda, osda, pscl = _pin(x, sda, "in"), _pin(x, sda, "out"), _pin(x, sclw, "in")
    if osda >= 8:
        raise CompileError("E-BIND", "open-drain wires need output-enable tables: bind them to O0..O7 (R5)")
    rate = x.opts.get("rate_hz") or clock.rate
    nominal = float(Fraction(60_000_000) / Fraction(rate)) if rate else None
    mod = int(follow_period or (4 * nominal if nominal else 0))
    if not mod:
        raise CompileError("E-RATE", "follower: pass follow_period=<longest clock period in cycles>")
    minper = max(16, int(nominal / 2)) if nominal else 32
    minhalf = max(8, minper // 2)
    clk.mod = mod
    # the parameter the acknowledge compares with: one data RAM byte, read through pointer 0
    params = dict(params or {})
    pval = 0
    if sh.ack_param:
        pd = score.param(sh.ack_param)
        if sh.ack_param in params:
            pval = int(params[sh.ack_param])
        elif pd.default is not None:
            from score.model import eval_expr
            pval = int(eval_expr(pd.default, {}))
        x.host["params"][sh.ack_param] = {"data_addr": PARAM_BASE, "initial": pval & 0x7F,
                                          "takes_effect": "at the next START"}
        x.b.cfg.append(f".data {PARAM_BASE} 0x{pval & 0x7F:02X}")
        x.init_moves += [imm(PARAM_BASE & 0xFF, "P0.AL"), imm(PARAM_BASE >> 8, "P0.AH")]
    x.host["tx_stream"] = {"stream": 0, "base": TX_BASE, "fields": [sh.read[0].name],
                           "layout": "bytes returned to read requests, in order"}
    x.host["rx_stream"] = {"stream": 1, "base": RX_BASE, "capacity_bytes": RX_CAP,
                           "layout": "per START or repeated START: 0 1, the header bits; per written byte: 1, 8 data bits; per "
                                     "read byte: the 'more' bit; per STOP: 0 0, then a flush to the byte boundary "
                                     "(target_rx parses it)"}
    x.host["mailbox_out"].append("a byte after every STOP")
    # recognised events -> edge threads
    edge_thr = []
    for ev, tgt in sh.aborts.items():
        r = sh.events[ev]
        if r.wire != sda or r.while_wire != sclw:
            _unsup(f"event '{ev}': only edges of '{sda}' while '{sclw}' is at a level are compiled")
        edge_thr.append((ev, tgt, "PINA.FALL" if r.edge == "falls" else "PINA.RISE", r.while_level == "high"))
    if sorted(t for _, t, _, _ in edge_thr) != ["req", "top"]:
        _unsup("abort rules must send one event to the start production and one to the request")
    F_REQ, F_TOP, F_RW, F_HELD = 3, 4, 1, 2
    rd_lit = sh.read[3]
    c = x.b.cores[0]
    # ---- protocol thread: one burst per rise of the clock wire, stages the beat that starts at the next fall
    c.label("ign")
    c.i([], goto="ign", pause=True, note="not addressed / waiting for a START or STOP")
    c.label("on_top")
    c.i([imm(F_TOP, "FLAGS.CLR")], note="after a STOP")
    c.i([], goto="ign", pause=True)
    c.label("on_req")
    c.i([imm(F_REQ, "FLAGS.CLR")], note=f"after a START: header bit 7")
    c.i([imm(F_TOP, "FLAGS.CLR")])
    c.i(["L.IN -> ACC.LD", "L.IN -> S1.RX"])
    c.i([imm(5, "CNT0.LO")], pause=True)
    c.label("hdr")
    c.i(["ACC -> ACC.ADD"], note="header bits 6..1")
    c.i(["L.IN -> ACC.OR", "L.IN -> S1.RX", "ZERO -> CNT0.DEC"], goto="hdr", jmode="ifnot", jcond="CNT0.Z",
        pause=True)
    c.i(["L.IN -> S1.RX"], note=f"'{sh.rw}'")
    c.i(["? #1 -> FLAGS.SET", "! #1 -> FLAGS.CLR"], when="L.IN0")
    if sh.ack_param:
        c.i(["P0.D -> ACC.CMP"], note=f"{sh.ack_field} == {sh.ack_param}?")
        c.i([imm(c1, "L.SYM")], note=f"'{sh.ack.name}' = 1 unless matched")
        c.i(["? ZERO -> L.DBIT"], when="ACC.Z", goto="acked", jmode="if", jcond="ACC.Z", pause=True)
        c.i([], goto="ign", pause=True, note="not addressed")
    else:
        c.i([imm(c0 | sh.ack_const, "L.SYM")], note=f"'{sh.ack.name}' = {sh.ack_const}")
        c.i([], goto="acked", pause=True)
    c.label("acked")
    c.i([], goto="r0", jmode="if" if rd_lit else "ifnot", jcond="F1", note="read body?")
    # write body: release after the acknowledge; hold the first bit of each possible byte
    c.i(["ZERO -> L.SYM"], goto="w0", pause=True, note="release the data wire")
    c.label("w0")
    c.i(["? #2 -> FLAGS.SET", "! #2 -> FLAGS.CLR"], when="L.IN0", pause=True,
        note="first bit of a byte, or of a repeated START / STOP: hold it")
    c.i(["#1 -> S1.RX"], note="it was data: marker 1")
    c.i(["? #1 -> S1.RX", "! ZERO -> S1.RX"], when="F2", note="append the held bit")
    c.i(["L.IN -> S1.RX"])
    c.i([imm(4, "CNT0.LO")], pause=True)
    c.label("wl")
    c.i(["L.IN -> S1.RX", "ZERO -> CNT0.DEC"], goto="wl", jmode="ifnot", jcond="CNT0.Z", pause=True,
        note="data bits 5..1")
    c.i(["L.IN -> S1.RX"], note="data bit 0")
    c.i([imm(c0 | sh.write[2], "L.SYM")], pause=True, note=f"'{sh.write[1].name}' = {sh.write[2]}")
    c.i(["ZERO -> L.SYM"], goto="w0", pause=True, note="release after the acknowledge")
    # read body: data bits from transmit stream 0, then the controller's 'more' bit
    c.label("r0")
    c.i([imm(c0, "L.SYM")], note=f"'{sh.read[0].name}' bit 7")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV"])
    c.i([imm(6, "CNT0.LO")], pause=True)
    c.label("rl")
    c.i(["S0.BIT -> L.DBIT", "ZERO -> S0.ADV", "ZERO -> CNT0.DEC"], goto="rl", jmode="ifnot", jcond="CNT0.Z",
        pause=True, note="data bits 6..0")
    c.i(["ZERO -> L.SYM"], pause=True, note=f"'{sh.read[1].name}' beat: release")
    c.i(["L.IN -> S1.RX"], goto="ign", jmode="if" if sh.read[2] else "ifnot", jcond="L.IN0",
        note=f"capture '{sh.read[1].name}'; == {sh.read[2]}: end")
    c.i([], goto="r0", note="another byte")
    # ---- edge threads (recognised events)
    for ev, tgt, trig, hi in edge_thr:
        lab = f"ev_{ev}"
        c.label(lab)
        g = f"PIN{pscl}"
        q = "?" if hi else "!"
        c.i([f"{q} ZERO -> L.SYM"], when=g, note=f"'{ev}': {sda} edge while {sclw} {'high' if hi else 'low'}; idle")
        if tgt == "top":
            c.i([f"{q} {imm(F_TOP, 'FLAGS.SET')}"], when=g)
            c.i([f"{q} ZERO -> S1.RX"], when=g, note="record marker 00, then flush")
            c.i([f"{q} ZERO -> S1.RX"], when=g)
            c.i([f"{q} #2 -> S1.CTL"], when=g)
            c.i([f"{q} ZERO -> HOST.OUT"], when=g, goto=lab, pause=True, note="report the end of a transaction")
        else:
            c.i([f"{q} {imm(F_REQ, 'FLAGS.SET')}"], when=g)
            c.i([f"{q} ZERO -> S1.RX"], when=g, note="record marker 01: a request follows")
            c.i([f"{q} #1 -> S1.RX"], when=g)
            if sh.ack_param:
                c.i([f"{q} {imm(PARAM_BASE >> 8, 'P0.AH')}"], when=g, note="refresh the parameter byte")
            c.i([], goto=lab, pause=True)
    # ---- configuration
    x.b.block(".line 0", ["inc 1", f"mod {mod}", "follow", f"edge P{pscl} {rc.edge}", f"t0edge P{pscl} {rc.cap_edge}",
                          f"pins A=P{psda}", f"lut0 0x{_lut_slot(0):08X}", "lut1 0x00000000", "snap tap0",
                          f"minperiod {minper}", f"minhalf {minhalf}", "ctl run ren"])
    emit_out_pins(x, 0)
    x.b.block(".stream 0", ["mode tx", "order msb", f"start {TX_BASE}", "len 0"])
    x.b.block(".stream 1", ["mode rx", "order msb", f"start {RX_BASE}", f"len {RX_CAP}"])
    x.b.cfg.append("")
    req_ev = next(e for e, t, _, _ in edge_thr if t == "req")
    top_ev = next(e for e, t, _, _ in edge_thr if t == "top")
    thr = [(0, 0, 0, "L0.TAP0", "ign")]
    n = 1
    for ev, tgt, trig, _ in edge_thr:
        thr.append((n, 0, 0, trig, f"ev_{ev}"))
        n += 1
    emit_threads(x, thr)
    # watchers on the protocol thread: abort targets
    i = x.b.cfg.index(".thread 0")
    x.b.cfg.insert(i + 1, f"    watch0 F{F_REQ} -> on_req")
    x.b.cfg.insert(i + 2, f"    watch1 F{F_TOP} -> on_top")
    emit_init_thread(x, 5, core=0)
    x.notes.append(f"target: line 0 follows {sclw} {rc.edge}, captures {sda} on {sclw} {rc.cap_edge} (tap 0); "
                   f"'{req_ev}' and '{top_ev}' are pin-A edge threads with watchers on the protocol thread; assumes "
                   f"a clock no faster than {minper} cycles per period, {minhalf} per half (minperiod/minhalf)")


def compile_bus(x: Ctx, follow_period=None, params=None):
    sh = match_shape(x.score)
    if x.role == sh.ctl:
        compile_controller(x, sh)
    else:
        compile_target(x, sh, follow_period, params)
    x.shape_bus = sh
    return sh


# ---- host helpers ---------------------------------------------------------------------------------------------
def _bits(v, n):
    return [(v >> (n - 1 - i)) & 1 for i in range(n)]


def _pack(bits):
    out = bytearray()
    for i in range(0, len(bits), 8):
        chunk = bits[i:i + 8] + [0] * (8 - len(bits[i:i + 8]))
        out.append(sum(b << (7 - j) for j, b in enumerate(chunk)))
    return bytes(out)


def controller_tx(requests) -> bytes:
    """Host transmit stream for one controller transaction.  requests: [(addr, 'w', bytes) | (addr, 'r', n)]."""
    bits = []
    for i, (addr, kind, arg) in enumerate(requests):
        bits += _bits(addr, 7) + [0 if kind == "w" else 1]
        if kind == "w":
            for d in arg:
                bits += [1] + _bits(d, 8)
            bits += [0]
        else:
            bits += [0] * (arg - 1) + [1]
        bits += [1 if i + 1 < len(requests) else 0]
    return _pack(bits)


def controller_rx(requests, data: bytes, nbits: int):
    """Unpack the controller's receive stream: [(ack, [write acks] | [read bytes])] per request reached."""
    bits = [(data[i // 8] >> (7 - i % 8)) & 1 for i in range(nbits)]
    out, k = [], 0
    for addr, kind, arg in requests:
        if k >= len(bits):
            break
        ack = bits[k]
        k += 1
        if ack:
            out.append((ack, []))
            break
        if kind == "w":
            acks = bits[k:k + len(arg)]
            k += len(arg)
            out.append((0, acks))
        else:
            got = []
            for _ in range(arg):
                got.append(sum(b << (7 - j) for j, b in enumerate(bits[k:k + 8])))
                k += 8
            out.append((0, got))
    return out


def target_rx(data: bytes, my_addr: int, rd_lit=1, stop_v=1):
    """Parse the target's receive stream into transactions: [[(addr, rw, payload)]], payload = written bytes,
    read 'more' bits, or None when the request was not for `my_addr`."""
    bits = [(b >> (7 - j)) & 1 for b in data for j in range(8)]
    out, cur, i = [], None, 0

    def take(n):
        nonlocal i
        v = 0
        for b in bits[i:i + n]:
            v = (v << 1) | b
        i += n
        return v

    while i + 2 <= len(bits):
        m = take(2)
        if m == 0b01:
            cur = [] if cur is None else cur
            h = take(8)
            a, rw = h >> 1, h & 1
            if a != my_addr:
                cur.append((a, rw, None))
            elif rw != rd_lit:
                ds = []
                while i < len(bits) and bits[i] == 1:
                    i += 1
                    ds.append(take(8))
                cur.append((a, rw, ds))
            else:
                ms = []
                while i < len(bits):
                    ms.append(take(1))
                    if ms[-1] == stop_v:
                        break
                cur.append((a, rw, ms))
        elif m == 0b00:
            if cur is not None:
                out.append(cur)
            cur = None
            i = (i + 7) // 8 * 8
        else:
            break
    return out
