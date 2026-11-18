"""Reference codec: frame events <-> per-wire waveforms at chip-cycle resolution (60 MHz).

This is the definition of correctness for the compiler (spec section 2, 15). It implements the relation of
SPEC_V2_SCORE.md part A directly. Conventions the spec leaves open are listed in code/score/NOTES.md.

Event stream (input of encode, output of decode): a list of tuples
    ("field", value)      a named field (int, or bytes for bytes fields), in grammar order
    ("symbol",)           a named symbol terminal that takes no parameter (start, stop, mark, tpidl ...)
    ("abort", "event")    an abort trigger (encode: generates it; decode: reports it)
Parameterised framing symbols (UART's bit(0)/bit(1)) and const bytes are not events.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

from .analysis import END, Analyzer, bitlen, kind_of
from .ast import *  # noqa: F403
from .checks import assert_ok
from .crc import STD, crc_bytes
from .model import (DATA_SYMBOL, EvalError, beat_cycles, boundaries, eval_expr, expand_wave, idle_level, nseg,
                    pulled_level, qty_cycles, symbol_instances, inst_name)

Z = None   # high impedance in a drive waveform


class EncodeError(Exception):
    pass


class FrameError(Exception):
    """Decode could not continue the frame (violation, truncation); carries the message."""


class Abort(Exception):
    def __init__(self, target, event):
        self.target, self.event = target, event


# ---- waveforms -----------------------------------------------------------------------------------------------
@dataclass
class Waveform:
    """Per-wire level per chip cycle. Drive waveforms hold 0, 1 or None (released); a bus holds 0/1."""
    wires: dict
    n: int

    def __getitem__(self, w):
        return self.wires[w]

    def table(self, names=None, start=0, stop=None):
        names = names or list(self.wires)
        stop = stop if stop is not None else self.n
        return {w: "".join("z" if v is None else str(v) for v in self.wires[w][start:stop]) for w in names}


def resolve(score: Score, drives: list[Waveform]) -> Waveform:
    """Combine the drives of several roles into the bus: open-drain / shared wires are wired-AND with an external
    pull-up; push-pull wires must not be driven to different levels."""
    n = max(d.n for d in drives)
    out = {}
    for w in score.all_wires():
        if w.mirror_of:
            continue
        pull = pulled_level(w)
        wired_and = w.drive == "open-drain" or w.dir == "shared"
        lv = []
        for t in range(n):
            vals = [d.wires[w.name][t] for d in drives if w.name in d.wires and t < d.n]
            vals = [v for v in vals if v is not None]
            if wired_and:
                lv.append(0 if 0 in vals else 1)
            else:
                if len(set(vals)) > 1:
                    raise EncodeError(f"bus conflict on push-pull wire '{w.name}' at cycle {t}")
                lv.append(vals[0] if vals else pull)
        out[w.name] = lv
    for w in score.all_wires():
        if w.mirror_of:
            out[w.name] = [1 - v for v in out[w.mirror_of]]
    return Waveform(out, n)


@dataclass
class Beat:
    inst: tuple          # (symbol name, args)
    owners: frozenset
    kind: str = "beat"


@dataclass
class Idle:
    cycles: Fraction
    kind: str = "idle"


@dataclass
class Encoded:
    plan: list
    drives: dict         # role -> Waveform
    bus: Waveform
    period: Fraction
    events: list


@dataclass
class DecodeResult:
    events: list
    ok: bool
    notes: list
    end: int = 0         # cycle index just after the last consumed beat


# ---- coder (spec 6) ------------------------------------------------------------------------------------------
class Coder:
    """Bit coding state: stuffing (data domain, lazy), differential, invert. One per bit stream."""

    def __init__(self, bits: Bits, idle_line: int):
        self.b, self.idle_line = bits, idle_line
        self.reset()

    def reset(self):
        self.prev = self.idle_line ^ int(self.b.invert)       # last line level in the pre-invert domain
        self.run_val, self.run_n = None, 0

    def bypass(self, line_level=None):
        """A symbol written by name: breaks the stuffing run, and sets the differential reference."""
        self.run_val, self.run_n = None, 0
        if line_level is not None:
            self.prev = line_level ^ int(self.b.invert)

    # -- stuffing helpers --
    def _counts(self, bit):
        k = self.b.stuff[2]
        return k == "equal" or (k == "ones" and bit == 1) or (k == "zeros" and bit == 0)

    def _stuff_pending(self):
        return self.b.stuff is not None and self.run_n >= self.b.stuff[1] and self.run_val is not None

    def _stuff_value(self):
        bit = self.b.stuff[0]
        return (1 - self.run_val) if bit is None else bit

    def _note(self, bit):
        if self.b.stuff is None:
            return
        if not self._counts(bit):
            self.run_val, self.run_n = None, 0
        elif bit == self.run_val:
            self.run_n += 1
        else:
            self.run_val, self.run_n = bit, 1

    def _line(self, data):
        """data bit -> line bit (pre-invert domain tracked in self.prev)."""
        if self.b.differential is not None:
            line = self.prev ^ (1 if data == self.b.differential else 0)
        else:
            line = data
        self.prev = line
        return line ^ int(self.b.invert)

    def encode(self, data):
        """Data bit -> list of line bits (a stuffed bit first, when due)."""
        out = []
        if self._stuff_pending():
            s = self._stuff_value()
            out.append(self._line(s))
            self.run_val, self.run_n = None, 0
        out.append(self._line(data))
        self._note(data)
        return out

    def decode(self, get_line):
        """Read line bits via get_line() until one data bit emerges. Returns (bit, violation_text|None)."""
        viol = None
        while True:
            lb = get_line() ^ int(self.b.invert)
            if self.b.differential is not None:
                data = self.b.differential if lb != self.prev else 1 - self.b.differential
            else:
                data = lb
            self.prev = lb
            if self._stuff_pending():
                want = self._stuff_value()
                if data != want:
                    viol = f"missing stuffed bit (expected {want}, got {data})"
                self.run_val, self.run_n = None, 0
                if viol:
                    return data, viol
                continue
            self._note(data)
            return data, viol


def to_bits(value: int, width: int, order: str) -> list[int]:
    value &= (1 << width) - 1
    return [(value >> (width - 1 - i)) & 1 for i in range(width)] if order == "msb" else \
        [(value >> i) & 1 for i in range(width)]


def from_bits(bits: list[int], order: str) -> int:
    v = 0
    if order == "msb":
        for b in bits:
            v = (v << 1) | b
    else:
        for i, b in enumerate(bits):
            v |= b << i
    return v


class _RawCoder:
    """Pass-through coder: the bits were already decoded (bytes captured by 'bytes until')."""

    def encode(self, bit):
        return [bit]

    def decode(self, get_line):
        return get_line(), None


# ---- instances -----------------------------------------------------------------------------------------------
@dataclass
class Inst:
    name: str
    args: tuple
    sdef: SymbolDef
    segs: dict           # wire -> per-segment drive: '0','1','z','x' ('h' = hold previous beat's level)
    exp: dict            # wire -> per-segment expected resolved level (0/1/None)

    @property
    def key(self):
        return (self.name, self.args)

    def __str__(self):
        return inst_name(self.sdef, self.args)


class Codec:
    def __init__(self, score: Score, params: dict | None = None, rate=None, fclk: int | None = None,
                 strict: bool = True):
        if strict:
            assert_ok(score)
        else:       # ignore resource-fit rejections (E-FIT-*), keep every semantic error
            from .checks import errors
            es = [e for e in errors(score) if not e.code.startswith("E-FIT")]
            if es:
                raise ScoreError("; ".join(map(str, es)), es[0].pos, es[0].code)
        if len(score.groups) > 1 or (score.groups and score.wires):
            raise NotImplementedError("the reference codec handles one clock group; split multi-group scores")
        self.score = score
        self.clock = score.clock_for()
        self.rate = rate
        self.P = beat_cycles(self.clock, rate)
        self.bounds = boundaries(self.clock)
        self.n = nseg(self.clock)
        self.tol = self.clock.tolerance
        self.params = dict(params or {})
        for p in score.params:
            if p.name not in self.params and p.default is not None:
                self.params[p.name] = eval_expr(p.default, {})
        self.insts: dict = {}
        for sd, args in symbol_instances(score):
            self.insts[(sd.name, args)] = self._mk_inst(sd, args)
        self.wires = [w for w in score.all_wires() if not w.mirror_of]
        self.q = {w.name: pulled_level(w) if w.idle is None and w.drive == "push-pull" else
                  {"high": 1, "low": 0, "released": 1}.get(w.idle, pulled_level(w)) for w in self.wires}
        self.bitsym = score.symbol(DATA_SYMBOL)
        self.roleclk = {r: self.clock.roles[r] for r in score.roles}
        self.last_stuff_note = None
        self.consts = score.consts()
        self.state: dict = {}           # (encode|decode, role) -> {state name: value}; persists across calls (18.3)

    def state_for(self, key) -> dict:
        if key not in self.state:
            self.state[key] = {s.name: s.init for s in self.score.states}
        return self.state[key]

    def reset_state(self):
        self.state.clear()

    # -- helpers --
    def _mk_inst(self, sd, args):
        segs, exp = {}, {}
        for w, wave, pos in sd.waves:
            raw = expand_wave(wave, sd.params, args, self.n, pos)
            wire = self.score.wire(w)
            held = []
            for j, c in enumerate(raw):
                if c == ".":
                    c = held[-1] if j else "h"
                held.append(c)
            segs[w] = held
            wa = wire.drive == "open-drain" or wire.dir == "shared"
            exp[w] = [{"0": 0, "1": 1, "z": (1 if wa else None), "x": None, "h": None}[c] for c in held]
        return Inst(sd.name, args, sd, segs, exp)

    def data_wire(self):
        """Wire whose wave uses the data symbol's first parameter (differential reference)."""
        sd = self.bitsym
        if sd is None or not sd.params:
            return None
        p = sd.params[0]
        for w, wave, _ in sd.waves:
            if p in wave:
                return w
        return None

    def idle_line_level(self):
        w = self.data_wire()
        return self.q[w] if w else 1

    def insts_for(self, token):
        _, name, args = token
        return [i for i in self.insts.values() if i.name == name and (args is None or i.args == tuple(args))]

    def final_level(self, inst: Inst):
        w = self.data_wire()
        if w is None or w not in inst.segs:
            return None
        v = inst.segs[w][-1]
        return {"0": 0, "1": 1, "z": 1}.get(v)

    # ====================================================================================================
    # public API
    # ====================================================================================================
    def encode_all(self, events, lead: int = 8, tail: int = 8) -> Encoded:
        run = _Run(self, enc=True, events=list(events))
        plan = run.run_top()
        drives = self._synth(plan, lead, tail)
        bus = resolve(self.score, list(drives.values()))
        return Encoded(plan, drives, bus, self.P, list(events))

    def encode(self, role: str, events, lead: int = 8, tail: int = 8) -> Waveform:
        """Waveform that `role` drives for the whole transaction in `events` (all fields, both roles)."""
        if role not in self.score.roles:
            raise EncodeError(f"unknown role {role!r}")
        return self.encode_all(events, lead, tail).drives[role]

    def decode(self, role: str, bus, **kw) -> DecodeResult:
        """Decode a resolved bus (Waveform or {wire: [levels]}) as seen by `role`."""
        if isinstance(bus, Waveform):
            bus = bus.wires
        run = _Run(self, enc=False, bus=bus, role=role)
        return run.run_decode()

    # ====================================================================================================
    # waveform synthesis
    # ====================================================================================================
    def _synth(self, plan, lead, tail):
        P, b = self.P, self.bounds
        t = Fraction(lead)
        spans = []
        for it in plan:
            if isinstance(it, Beat):
                spans.append((t, it))
                t += P
            else:
                t += it.cycles
        total = math.ceil(t) + tail
        drives = {}
        for r in self.score.roles:
            d = {}
            for w in self.score.all_wires():
                if w.mirror_of:
                    continue
                owners = self.score.wire_owners(w)
                lvl = idle_level(w)
                d[w.name] = [lvl if r in owners else Z] * total
            drives[r] = d
        for t0, bt in spans:
            inst = self.insts[bt.inst]
            for w, segs in inst.segs.items():
                wire = self.score.wire(w)
                if wire.mirror_of:
                    continue
                owners = self.score.wire_owners(wire)
                drivers = (set(bt.owners) if wire.dir == "shared" else owners)
                for r in drivers:
                    arr = drives[r].get(w)
                    if arr is None:
                        continue
                    prev = None
                    c0 = math.ceil(t0)
                    prev = arr[c0 - 1] if c0 >= 1 else None
                    wa = wire.drive == "open-drain" or wire.dir == "shared"
                    for j, c in enumerate(segs):
                        a = math.ceil(t0 + b[j] * P)
                        e = math.ceil(t0 + b[j + 1] * P)
                        if c == "0":
                            v = 0
                        elif c == "1":
                            v = Z if wa else 1
                        elif c == "z":
                            v = Z
                        else:      # x, h: hold the previous level
                            v = prev
                        for k in range(a, e):
                            arr[k] = v
                        prev = v
        out = {}
        for r in self.score.roles:
            d = drives[r]
            for w in self.score.all_wires():
                if w.mirror_of:
                    d[w.name] = [None if v is None else 1 - v for v in d[w.mirror_of]]
            out[r] = Waveform(d, total)
        return out

    # ====================================================================================================
    # event predicates on a bus
    # ====================================================================================================
    def sym_fires(self, inst: Inst, ev: Recog) -> bool:
        """Does this symbol, on its own waveform, produce recognised event `ev`?"""
        def lv(w, j):
            c = inst.exp.get(w, [None] * self.n)[j]
            return c
        if ev.kind not in ("edge", "edge_while"):
            return False
        want = (0, 1) if ev.edge == "rises" else (1, 0)
        w = ev.wire
        if w not in inst.segs:
            return False
        for j in range(self.n):
            if j == 0 and ev.kind == "edge_while":
                continue                       # needs a real previous level
            prev = lv(w, j - 1) if j else want[0]
            cur = lv(w, j)
            if prev == want[0] and cur == want[1]:
                if ev.kind == "edge":
                    return True
                lvl = 1 if ev.while_level == "high" else 0
                if lv(ev.while_wire, j) == lvl and (j == 0 or lv(ev.while_wire, j - 1) == lvl):
                    return True
        return False

    def trigger_symbol(self, event_name):
        r = self.score.event(event_name)
        for key, inst in self.insts.items():
            if r and self.sym_fires(inst, r):
                return key
        return None


# ====================================================================================================
# the walker (encode and decode share it)
# ====================================================================================================
class _Run:
    def __init__(self, c: Codec, enc: bool, events=None, bus=None, role=None):
        self.c, self.s, self.enc, self.role = c, c.score, enc, role
        self.st = c.state_for(("encode" if enc else "decode", role))
        self.env: dict = {**c.consts, **c.params, **self.st}
        self.flog: list = []                    # (name, value, kind, width, order) of fields in this frame
        self.stack: list[str] = []
        self.bits = c.score.bits
        self.coder = Coder(self.bits, c.idle_line_level())
        self.chan = None                        # duplex side channel override
        self.last_owner = None
        self.out_events: list = []
        self.notes: list = []
        self.ok = True
        # encode
        self.plan: list = []
        self.ev = events or []
        self.ei = 0
        # decode
        self.bus = bus
        self.pos = Fraction(0)                  # search position when unanchored
        self.anchored = False
        self.start = Fraction(0)
        self.last_end = Fraction(0)
        self.nbus = max((len(v) for v in bus.values()), default=0) if bus else 0

    # ---- top level ----------------------------------------------------------------------------------
    def run_top(self):
        s0 = self.s.prods[0]
        try:
            self._call_top(s0)
        except Abort as a:
            self._after_abort_top(a)
        if self.ei < len(self.ev):
            raise EncodeError(f"event #{self.ei} {self.ev[self.ei]!r} was not consumed by the grammar")
        return self.plan

    def _call_top(self, s0):
        self.stack.append(s0.name)
        while True:
            try:
                self.walk(s0.body, self.s.roles[0])
                break
            except Abort as a:
                if a.target == s0.name:
                    continue
                raise
        self.stack.pop()

    def _after_abort_top(self, a):
        if a.target in ("idle", "report"):
            if a.target == "report":
                self.out_events.append(("report", a.event))
            return
        ps = self.s.prods_named(a.target)
        if ps:
            self.stack = []
            self._call_top(ps[0])

    def run_decode(self):
        s0 = self.s.prods[0]
        try:
            self._call_top(s0)
        except Abort as a:
            try:
                self._after_abort_top(a)
            except FrameError as e:
                self._fail(str(e))
        except FrameError as e:
            self._fail(str(e))
        return DecodeResult(self.out_events, self.ok, self.notes, math.floor(self.last_end))

    def _fail(self, msg):
        self.ok = False
        self.notes.append(msg)
        self.out_events.append(("violation", msg))

    # ---- encode: event access -------------------------------------------------------------------------
    def peek_ev(self):
        if self.ei >= len(self.ev):
            return None
        e = self.ev[self.ei]
        if e[0] == "abort":
            self._do_abort(e[1])
        return e

    def _do_abort(self, evname):
        self.ei += 1
        key = self.c.trigger_symbol(evname)
        if key is None:
            raise EncodeError(f"no symbol generates event '{evname}'")
        self.plan.append(Beat(key, frozenset(self.s.roles)))
        rule = next((a for a in self.s.aborts if a.event == evname and (a.in_prod is None or a.in_prod in self.stack)),
                    None)
        if rule is None:
            raise EncodeError(f"no abort rule for event '{evname}' here")
        raise Abort(rule.target, evname)

    def take_ev(self, name, optional=False):
        e = self.peek_ev()
        if e is not None and e[0] == name:
            self.ei += 1
            return e
        if optional:
            return None
        got = "end of events" if e is None else repr(e)
        raise EncodeError(f"expected event {name!r}, got {got} (event #{self.ei})")

    # first-event analysis ------------------------------------------------------------------------------
    def fev(self, n, seen=()):
        S = self.s
        if isinstance(n, Seq):
            names = set()
            for it in n.items:
                nm, nl = self.fev(it, seen)
                names |= nm
                if not nl:
                    return names, False
            return names, True
        if isinstance(n, Choice):
            names, nul = set(), False
            for a in n.alts:
                nm, nl = self.fev(a, seen)
                names |= nm
                nul = nul or nl
            return names, nul
        if isinstance(n, Dup):
            return self.fev(n.a, seen)
        if isinstance(n, Rep):
            nm, nl = self.fev(n.node, seen)
            if n.kind in ("star", "opt", "while"):
                return nm, True
            return nm, nl
        if isinstance(n, If):
            return self.fev(n.node, seen)[0], True
        if isinstance(n, (Within, Retry)):
            return self.fev(n.node, seen)
        if isinstance(n, Every):
            return set(), True
        if isinstance(n, Switch):
            names, nul = set(), n.other is None
            for _, a in n.arms:
                nm, nl = self.fev(a, seen)
                names |= nm
                nul = nul or nl
            if n.other is not None:
                nm, nl = self.fev(n.other, seen)
                names |= nm
                nul = nul or nl
            return names, nul
        if isinstance(n, Field):
            return ({n.name}, False) if n.name else (set(), True)
        if isinstance(n, (ConstBytes, ConstBits, Gap, Turnaround)):
            return set(), True
        if isinstance(n, Ref):
            k = kind_of(S, n.name)
            if k == "sym":
                return ({n.name}, False) if not S.symbol(n.name).params else (set(), True)
            if k == "prod" and n.name not in seen:
                names, nul = set(), False
                for p in S.prods_named(n.name):
                    nm, nl = self.fev(p.body, seen + (n.name,))
                    names |= nm
                    nul = nul or nl
                return names, nul
            return set(), True
        return set(), True

    def starts(self, node):
        """Encode: does the next event begin `node`?"""
        e = self.peek_ev()
        if e is None:
            return False
        return e[0] in self.fev(node)[0]

    # ---- value conversion ----------------------------------------------------------------------------
    def order_of(self, t: Type):
        return t.order or self.bits.order

    def type_bits(self, f: Field, env=None):
        t = f.type
        if t.kind == "bit":
            return 1
        if t.kind in ("u", "s"):
            return t.width
        if t.kind == "parity":
            return 1
        if t.kind == "crc":
            c = self.s.crcs.get(t.crc) or STD[t.crc]
            return c.width
        raise EvalError("no fixed width")

    def fixed_bits(self, f, value):
        t = f.type
        w = self.type_bits(f)
        return to_bits(value, w, self.order_of(t))

    # ---- beats ---------------------------------------------------------------------------------------
    def set_owner(self, o):
        """Differential reference resets to idle at a change of owner (D29)."""
        if self.chan is None and self.last_owner is not None and o != self.last_owner:
            self.coder.prev = self.coder.idle_line ^ int(self.bits.invert)
        self.last_owner = o

    def put_data_bit(self, bit, owners):
        """Encode one data bit through the coder; emits beats (or stores line bits in a duplex channel)."""
        lbs = self.coder.encode(bit) if self.chan is None else self.chan["coder"].encode(bit)
        for lb in lbs:
            if self.chan is not None:
                self.chan["line"].append(lb)
            else:
                self.plan.append(Beat((DATA_SYMBOL, (lb,)), frozenset(owners)))

    # decode: read beats -----------------------------------------------------------------------------
    def _win(self, start):
        return start, start + self.c.P

    def lv(self, w, t):
        arr = self.bus.get(w)
        i = math.floor(t)
        if arr is None or i < 0 or i >= len(arr):
            return self.c.q[w]
        return arr[i]

    def lvc(self, w, i):
        arr = self.bus[w]
        return arr[i] if 0 <= i < len(arr) else self.c.q[w]

    def classify(self, inst: Inst, start) -> bool:
        P, b = self.c.P, self.c.bounds
        for w, exp in inst.exp.items():
            for j, e in enumerate(exp):
                if e is None:
                    continue
                t = start + (b[j] + b[j + 1]) / 2 * P
                if self.lv(w, t) != e:
                    return False
        return True

    def quiescent_between(self, a, b_):
        for w in self.c.wires:
            arr = self.bus.get(w.name, [])
            lo, hi = max(0, math.floor(a)), min(len(arr), math.ceil(b_))
            q = self.c.q[w.name]
            for i in range(lo, hi):
                if arr[i] != q:
                    return False
        return True

    def first_activity(self, frm):
        """First cycle >= frm where some wire leaves its quiescent level (a transition from quiescent)."""
        lo = max(1, math.floor(frm) - 1)
        for i in range(lo, self.nbus):
            for w in self.c.wires:
                arr = self.bus.get(w.name)
                if arr is None:
                    continue
                q = self.c.q[w.name]
                if arr[i] != q and arr[i - 1] == q:
                    return i
        return None

    def dev_offset(self, inst: Inst):
        """Fraction of the beat at which this symbol first leaves quiescence (None if never)."""
        for j in range(self.c.n):
            for w, exp in inst.exp.items():
                if exp[j] is not None and exp[j] != self.c.q[w]:
                    return self.c.bounds[j]
        return None

    def realign(self, start):
        rc = self.c.roleclk.get(self.role)
        if rc is None or rc.mode != "recovered":
            return start
        a, b_ = rc.win
        P = self.c.P
        if a < b_:
            parts = [(a, b_, (a + b_) / 2)]
        else:       # wrapping window (D30): edges near the beat start, aligned to the boundary
            parts = [(Fraction(0), b_, Fraction(0)), (a, Fraction(1), Fraction(1))]
        for lo_f, hi_f, target in parts:
            lo, hi = math.ceil(start + lo_f * P), math.floor(start + hi_f * P)
            for i in range(max(1, lo), hi + 1):
                if self.lvc(rc.wire, i) != self.lvc(rc.wire, i - 1):
                    return Fraction(i) - target * P
        return start

    def acquire(self, allowed, pos):
        """Find the next beat after `pos` from the first activity. Returns None (bus quiescent) or
        (c_first, [(anchor, inst)]) with the candidate symbols that fit when aligned to that activity."""
        P = self.c.P
        c_first = self.first_activity(pos)
        if c_first is None:
            return None
        cands = []
        for inst in allowed:
            o = self.dev_offset(inst)
            anchor = Fraction(c_first) - (o if o is not None else 0) * P
            if self.classify(inst, anchor):
                cands.append((anchor, inst))
        return c_first, cands

    def look(self, allowed, required):
        """Next beat. allowed: iterable of Inst. Returns ('end',) | ('viol', start) | ('beat', inst, start).
        A non-required look (a decision) never changes the state unless it returns a beat."""
        P = self.c.P
        allowed = list(allowed)
        pos = self.pos
        if self.anchored:
            if not required and self.quiescent_between(self.start, self.nbus):
                return ("end",)
            start = self.realign(self.start)
            for inst in allowed:
                if self.classify(inst, start):
                    self.start = start
                    return ("beat", inst, start)
            if not self.quiescent_between(start, start + P):
                if required:
                    self.start = start
                return ("viol", start)
            pos = start       # an idle beat where something else was expected: look for the next activity
        got = self.acquire(allowed, pos)
        if got is None:
            return ("viol", pos) if required else ("end",)
        c_first, cands = got
        if not cands:
            if required:
                self.anchored, self.start = True, Fraction(c_first)
            return ("viol", Fraction(c_first))
        anchor, inst = cands[0]
        self.anchored, self.start = True, anchor
        return ("beat", inst, anchor)

    def follow_correct(self, start, inst):
        """Follower roles have no rate: re-time the next beat from the clock wire's own edge (capture edge if
        given, else the follow edge), searched within +-30 % of the beat around where this symbol puts it."""
        rc = self.c.roleclk.get(self.role)
        if inst is None or rc is None or rc.mode != "follow":
            return None
        w, edge = (rc.cap_wire or rc.wire), (rc.cap_edge or rc.edge)
        exp = inst.exp.get(w)
        if exp is None:
            return None
        a, c2 = (0, 1) if edge == "rise" else (1, 0)
        P, b = self.c.P, self.c.bounds
        for j in range(1, self.c.n):
            if exp[j - 1] == a and exp[j] == c2:
                f = b[j]
                for i in range(math.ceil(start + (f - Fraction(3, 10)) * P), math.floor(start + (f + Fraction(3, 10)) * P) + 1):
                    if self.lvc(w, i - 1) == a and self.lvc(w, i) == c2:
                        return Fraction(i) - f * P
                return None
        return None

    def consume(self, start, inst=None):
        P = self.c.P
        corrected = self.follow_correct(start, inst)
        if corrected is not None:
            start = corrected
        self.last_start = start
        self.start = start + P
        self.last_end = self.start
        self.pos = self.start

    def unanchor(self, after_gap_cycles=Fraction(0)):
        rc = self.c.roleclk.get(self.role)
        base = self.last_end
        if rc is not None and rc.mode == "started" and self.anchored:
            base = self.last_end - self.c.P / 2          # re-arm at the stop bit's sample point (no drift)
        self.pos = base + after_gap_cycles
        self.anchored = False

    # events fired in a beat window ----------------------------------------------------------------------
    def events_in(self, a, b_):
        out = []
        for r in self.s.recognise:
            if r.kind in ("edge", "edge_while"):
                want = (0, 1) if r.edge == "rises" else (1, 0)
                for i in range(max(1, math.ceil(a)), math.floor(b_) + 1):
                    if self.lvc(r.wire, i - 1) == want[0] and self.lvc(r.wire, i) == want[1]:
                        if r.kind == "edge_while":
                            lvl = 1 if r.while_level == "high" else 0
                            if not (self.lvc(r.while_wire, i) == lvl and self.lvc(r.while_wire, i - 1) == lvl):
                                continue
                        out += r.names
                        break
        return out

    def eof_at(self, r: Recog, start):
        """'no edge on W for N beats': true if no edge arrives within N beats (plus tolerance) of the last edge."""
        P = self.c.P
        n = r.qty.value if r.qty.unit == "beats" else qty_cycles(r.qty, P) / P
        lim = n * P * (1 + self.c.tol) + 1          # +1 cycle: edge times are quantised to the chip clock
        arr = self.bus.get(r.wire, [])
        i = min(len(arr) - 1, math.floor(start) + 1)
        e0 = None
        while i >= 1:
            if arr[i] != arr[i - 1]:
                e0 = i
                break
            if start - i > lim + P:
                break
            i -= 1
        if e0 is None:
            return True
        for j in range(e0 + 1, min(len(arr), math.floor(e0 + lim) + 1)):
            if arr[j] != arr[j - 1]:
                return False
        return True

    def handle_unexpected(self, start, what):
        """No expected symbol matched at `start`. Raise Abort if an abort rule applies, else FrameError."""
        a, b_ = start, start + self.c.P
        fired = self.events_in(a, b_)
        cands = fired + ["violation"]
        for ev in cands:
            for rule in self.s.aborts:
                if rule.event == ev and (rule.in_prod is None or rule.in_prod in self.stack):
                    self.consume(start)
                    self.notes.append(f"abort on {ev}: {what}")
                    self.out_events.append(("abort", ev))
                    if rule.target in ("idle", "report"):
                        if rule.target == "report":
                            self.out_events.append(("report", ev))
                        raise Abort("idle", ev)
                    raise Abort(rule.target, ev)
        raise FrameError(f"violation at cycle {math.floor(start)}: {what}")

    # ---- data bits: decode -----------------------------------------------------------------------------
    def get_line_bit(self):
        ins = [i for i in self.c.insts.values() if i.name == DATA_SYMBOL]
        r = self.look(ins, True)
        if r[0] != "beat":
            if r[0] == "end":
                raise FrameError("frame truncated: the bus went idle where a data bit was expected")
            self.handle_unexpected(r[1], "no data bit here")
        _, inst, st = r
        self.consume(st, inst)
        return inst.args[0]

    def get_data_bit(self):
        if self.chan is not None:
            ch = self.chan
            bit, viol = ch["coder"].decode(lambda: ch["line"].pop(0))
        else:
            bit, viol = self.coder.decode(self.get_line_bit)
        if viol:
            self.handle_unexpected(self.start - self.c.P, viol)
        return bit

    def get_bits(self, n):
        return [self.get_data_bit() for _ in range(n)]

    # ---- walker ---------------------------------------------------------------------------------------
    def walk(self, n, owner):
        m = getattr(self, "w_" + type(n).__name__)
        return m(n, owner)

    def trailing_fixed(self, items, i):
        """Fixed-width fields right after a `bytes until` field (D29): [(field, bits)] and their total width."""
        out, total = [], 0
        for it in items[i:]:
            if isinstance(it, Field) and it.type.kind in ("bit", "u", "s", "crc", "parity") and it.asm is None:
                w = self.type_bits(it)
                out.append(it)
                total += w
            else:
                break
        return out, total

    def w_Seq(self, n, owner):
        items = n.items
        i = 0
        while i < len(items):
            it = items[i]
            if not self.enc and isinstance(it, Field) and it.type.kind == "bytes" and it.type.until:
                tail, width = self.trailing_fixed(items, i + 1)
                if tail:
                    self.f_bytes_until_tail(it, tail, width, owner)
                    i += 1 + len(tail)
                    continue
            self.walk(it, owner)
            i += 1

    def w_Choice(self, n, owner):
        if self.enc:
            for a in n.alts:
                if self.starts(a):
                    return self.walk(a, owner)
            for a in n.alts:
                if self.fev(a)[1]:
                    return self.walk(a, owner)
            raise EncodeError(f"no alternative of the choice at {n.pos} matches event {self.peek_ev()!r}")
        allowed = {}
        res = []
        for a in n.alts:
            toks = self.dec_first(a)
            res.append(toks)
        insts = []
        for toks in res:
            for t in toks:
                insts += self.c.insts_for(t) if t[0] == "sym" else []
        r = self.look(insts, False)
        if r[0] == "beat":
            for a, toks in zip(n.alts, res):
                if any(r[1] in self.c.insts_for(t) for t in toks if t[0] == "sym"):
                    return self.walk(a, owner)
        for a, toks in zip(n.alts, res):
            if END in toks:
                return self.walk(a, owner)
        if r[0] == "viol":
            self.handle_unexpected(r[1], "no alternative matches")
        raise FrameError("choice: nothing matches")

    def dec_first(self, node):
        from .analysis import first_tokens
        return first_tokens(self.s, node, frozenset([END]), "?")

    def w_Dup(self, n, owner):
        oa = {f.by or owner for f in _fields(n.a)} or {owner}
        ob = {f.by or owner for f in _fields(n.b)} or {owner}
        if self.bits.differential is not None or self.bits.stuff is not None:
            raise NotImplementedError("'||' with differential or stuffing coding is not supported by the codec")
        la = self.eval_len(bitlen(self.s, n.a))
        lb = self.eval_len(bitlen(self.s, n.b))
        if la != lb:
            raise EncodeError(f"'||' sides differ: {la} vs {lb} bits")
        owners = oa | ob
        if self.enc:
            lines = []
            for side in (n.a, n.b):
                ch = {"coder": Coder(self.bits, self.c.idle_line_level()), "line": []}
                self.chan = ch
                self.walk(side, owner)
                self.chan = None
                lines.append(ch["line"])
            for x, y in zip(*lines):
                self.plan.append(Beat((DATA_SYMBOL, (x, y)), frozenset(owners)))
            return
        # decode: read la paired beats, then parse each side from its buffer
        ins = [i for i in self.c.insts.values() if i.name == DATA_SYMBOL]
        la_, lb_ = [], []
        for _ in range(la):
            r = self.look(ins, True)
            if r[0] != "beat":
                self.handle_unexpected(r[1], "no data beat in '||'") if r[0] == "viol" else \
                    (_ for _ in ()).throw(FrameError("frame truncated inside '||'"))
            _, inst, st = r
            self.consume(st, inst)
            la_.append(inst.args[0])
            lb_.append(inst.args[1])
        for side, buf in ((n.a, la_), (n.b, lb_)):
            self.chan = {"coder": Coder(self.bits, self.c.idle_line_level()), "line": buf}
            self.walk(side, owner)
            self.chan = None

    def eval_len(self, lin):
        if lin is None:
            raise EncodeError("'||' side length unknown")
        t = 0
        for k, v in lin.items():
            t += v if k == "" else v * self.env[k]
        return t

    def w_Rep(self, n, owner):
        k = n.kind
        if k == "times":
            cnt = self.val(n.arg)
            for _ in range(cnt):
                self.walk(n.node, owner)
        elif k in ("star", "plus", "opt"):
            first = True
            while True:
                if not (k == "plus" and first) and not self.more(n.node):
                    break
                first = False
                self.walk(n.node, owner)
                if k == "opt":
                    break
        elif k == "until":
            while True:
                self.walk(n.node, owner)
                if self.val(n.arg):
                    break
        elif k == "while":
            while self.val(n.arg):
                self.walk(n.node, owner)

    def more(self, node):
        """Does another iteration of `node` follow?"""
        if self.enc:
            return self.starts(node)
        toks = self.dec_first(node)
        toks = frozenset(t for t in toks if t != END)
        # lookahead over the symbols that can begin the body; the body decides, anything else ends the loop
        insts = []
        for t in toks:
            if t[0] == "sym":
                insts += self.c.insts_for(t)
        if not insts:
            return False
        r = self.look(insts, False)
        return r[0] == "beat"

    def w_If(self, n, owner):
        if self.val(n.cond):
            self.walk(n.node, owner)

    def w_Within(self, n, owner):
        self.walk(n.node, owner)

    def w_Retry(self, n, owner):
        self.walk(n.node, owner)       # retry is exchange timing: the codec runs the block once

    def w_AsmBlock(self, n, owner):
        raise NotImplementedError("asm blocks are parsed only")

    def w_Every(self, n, owner):
        pass        # periodic background activity (link pulses): out of scope for this codec

    def w_Assign(self, n, owner):
        st = self.s.state(n.name)
        v = self.val(n.expr) & ((1 << st.width) - 1)
        self.env[n.name] = v
        self.st[n.name] = v

    def w_Switch(self, n, owner):
        v = self.val(n.expr)
        for a, node in n.arms:
            if a == v:
                return self.walk(node, owner)
        if n.other is not None:
            self.walk(n.other, owner)

    def val(self, e):
        try:
            return eval_expr(e, self.env)
        except EvalError as ex:
            raise (EncodeError if self.enc else FrameError)(str(ex))

    def w_Gap(self, n, owner):
        P = self.c.P
        cyc = qty_cycles(n.qty, P)
        self.last_owner = None
        if self.enc:
            self.plan.append(Idle(cyc))
            self.coder.reset()
        else:
            self.coder.reset()
            self.unanchor(cyc)

    def w_Turnaround(self, n, owner):
        P = self.c.P
        # the wire is released, so the line idles; the differential reference follows it (see NOTES.md)
        self.coder.prev = self.coder.idle_line ^ int(self.bits.invert)
        if self.enc:
            self.plan.append(Idle(n.beats * P))
        else:
            self.start += n.beats * P
            self.last_end = self.start
            self.pos = self.start

    def w_ConstBytes(self, n, owner):
        self.set_owner(owner)
        for byte in n.data:
            for b in to_bits(byte, 8, self.bits.order):
                self.const_bit(b, owner)

    def w_ConstBits(self, n, owner):
        self.set_owner(owner)
        for ch in n.bits:
            self.const_bit(int(ch), owner)

    def const_bit(self, b, owner):
        if self.enc:
            self.put_data_bit(b, {owner})
        else:
            got = self.get_data_bit()
            if got != b:
                self._mismatch("const", f"constant bit {b}, got {got}")

    def _mismatch(self, name, msg):
        for rule in self.s.aborts:
            if rule.event == "mismatch" and (rule.in_prod is None or rule.in_prod in self.stack):
                self.out_events.append(("abort", "mismatch"))
                raise Abort(rule.target, "mismatch")
        self.ok = False
        self.notes.append(f"mismatch in {name}: {msg}")

    # ---- references ----------------------------------------------------------------------------------
    def w_Ref(self, n, owner):
        S = self.s
        k = kind_of(S, n.name)
        o = n.by or owner
        if k == "sym":
            sd = S.symbol(n.name)
            args = tuple(self.val(a) & 1 for a in n.args)
            inst = self.c.insts[(n.name, args)]
            if self.enc:
                if not sd.params:
                    self.take_ev(n.name, optional=True)
                self.plan.append(Beat(inst.key, frozenset([o])))
                self.coder.bypass(self.c.final_level(inst))
            else:
                r = self.look([inst], True)
                if r[0] != "beat":
                    if r[0] == "end":
                        raise FrameError(f"frame truncated: expected symbol {inst}")
                    self.handle_unexpected(r[1], f"expected symbol {inst}")
                self.consume(r[2], inst)
                self.coder.bypass(self.c.final_level(inst))
                if not sd.params:
                    self.out_events.append((n.name,))
            return
        if k == "event":
            return self.w_event(n, o)
        # production call
        argv = [self.val(a) for a in n.args]
        ps = S.prods_named(n.name)
        pick = None
        for p in ps:
            if all(q[0] == "id" or q[1] == v for q, v in zip(p.params, argv)):
                pick = p
                break
        if pick is None:
            raise (EncodeError if self.enc else FrameError)(f"no definition of '{n.name}' matches arguments {argv}")
        saved = {q[1]: self.env.get(q[1], _MISSING) for q in pick.params if q[0] == "id"}
        for q, v in zip(pick.params, argv):
            if q[0] == "id":
                self.env[q[1]] = v
        self.stack.append(n.name)
        while True:
            try:
                self.walk(pick.body, o)
                break
            except Abort as a:
                if a.target == n.name:
                    continue
                raise
        self.stack.pop()
        for k2, v in saved.items():
            if v is _MISSING:
                self.env.pop(k2, None)
            else:
                self.env[k2] = v

    def w_event(self, n, owner):
        r = self.s.event(n.name)
        if self.enc:
            for key, inst in self.c.insts.items():
                if r and self.c.sym_fires(inst, r):
                    self.plan.append(Beat(key, frozenset([owner])))
                    return
            raise EncodeError(f"no symbol generates event '{n.name}'")
        look = self.look(list(self.c.insts.values()), True)
        if look[0] == "beat" or look[0] == "viol":
            st = look[-1]
            if n.name in self.events_in(st, st + self.c.P):
                self.consume(st)
                return
        raise FrameError(f"expected event '{n.name}'")

    # ---- fields --------------------------------------------------------------------------------------
    def w_Field(self, f: Field, owner):
        o = f.by or owner
        self.set_owner(o)
        t = f.type
        if f.asm is not None:
            raise NotImplementedError("asm fields are parsed only")
        if t.kind == "crc":
            return self.f_crc(f, o)
        if t.kind == "parity":
            return self.f_parity(f, o)
        if t.kind == "bytes":
            return self.f_bytes(f, o)
        w = self.type_bits(f)
        order = self.order_of(t)
        if self.enc:
            v = self.enc_value(f)
            if t.kind == "s":
                lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
                if not lo <= v <= hi:
                    raise EncodeError(f"field {f.name}: {v} does not fit s{w}")
            elif not 0 <= v < (1 << w):
                raise EncodeError(f"field {f.name}: {v} does not fit {t.kind}{w}")
            for b in to_bits(v, w, order):
                self.put_data_bit(b, {o})
            self.record(f, v, w, order)
        else:
            bits = self.get_bits(w)
            v = from_bits(bits, order)
            if t.kind == "s" and v >> (w - 1):
                v -= 1 << w
            self.record(f, v, w, order)
            self.check_expect(f, v)
            if t.enum and v not in self.s.enums[t.enum].members.values():
                self._mismatch(f.name, f"{v} is not a member of enum {t.enum}")

    def enc_value(self, f: Field):
        """Value to send: the event if given, else '= EXPR'. An enum field also takes a member name."""
        e = self.peek_ev()
        if e is not None and e[0] == f.name:
            self.ei += 1
            v = e[1]
            if isinstance(v, str) and f.type.enum:
                members = self.s.enums[f.type.enum].members
                if v not in members:
                    raise EncodeError(f"field {f.name}: '{v}' is not a member of enum {f.type.enum}")
                v = members[v]
            return v
        if f.value is not None:
            return self.val(f.value)
        got = "end of events" if e is None else repr(e)
        raise EncodeError(f"field '{f.name}' has no value: expected event {f.name!r}, got {got}")

    def check_expect(self, f, v):
        if f.expect is not None:
            exp = self.val(f.expect)
            if exp != v:
                self._mismatch(f.name, f"expected {exp}, got {v}")

    def record(self, f, v, w, order, raw=None):
        if f.name:
            self.env[f.name] = v if not isinstance(v, (bytes, bytearray)) else int.from_bytes(v, "big")
            self.out_events.append((f.name, v)) if not self.enc else None
        self.flog.append((f.name, v, f.type.kind, w, order, raw))

    def f_bytes(self, f, o):
        t = f.type
        order = self.order_of(t)
        if t.until:
            return self.f_bytes_until(f, o)
        n = self.val(t.length)
        if self.enc:
            v = self.enc_value(f)
            data = bytes(v)
            if len(data) != n:
                raise EncodeError(f"field {f.name}: {len(data)} bytes given, length expression says {n}")
            for byte in data:
                for b in to_bits(byte, 8, order):
                    self.put_data_bit(b, {o})
        else:
            data = bytes(from_bits(self.get_bits(8), order) for _ in range(n))
        self.record(f, data, 8 * n, order)
        if not self.enc:
            self.check_expect(f, int.from_bytes(data, "big"))

    def until_hit(self, name):
        S = self.s
        k = kind_of(S, name)
        if k == "sym":
            r = self.look([i for i in self.c.insts.values() if i.name == name], False)
            return r[0] == "beat" or r[0] == "end"
        if k == "event":
            ev = S.event(name)
            st = self.start if self.anchored else self.pos
            if ev and ev.kind == "no_edge":
                if not self.anchored:
                    return True
                return self.eof_at(ev, self.start)
            if self.anchored:
                return name in self.events_in(self.start, self.start + self.c.P)
            return True
        return False

    def read_bytes_until(self, name, order):
        data = []
        while True:
            if self.until_hit(name):
                break
            data.append(from_bits(self.get_bits(8), order))
        return bytes(data)

    def f_bytes_until(self, f, o):
        order = self.order_of(f.type)
        if self.enc:
            data = bytes(self.enc_value(f))
            for byte in data:
                for b in to_bits(byte, 8, order):
                    self.put_data_bit(b, {o})
        else:
            data = self.read_bytes_until(f.type.until, order)
        self.record(f, data, 8 * len(data), order)

    def f_bytes_until_tail(self, f, tail, width, owner):
        """Decode `F:bytes until X` followed by fixed-width fields (a CRC, say): the receiver captures bytes until
        X, then splits the trailing fields' bytes off the end (spec 7.3, D29)."""
        if width % 8:
            raise NotImplementedError("fields trailing a 'bytes until' field must total a whole number of bytes")
        nb = width // 8
        order = self.order_of(f.type)
        data = self.read_bytes_until(f.type.until, order)
        if len(data) < nb:
            raise FrameError(f"frame too short for its {nb} trailing byte(s) ({len(data)} bytes)")
        body, rest = data[:-nb], data[-nb:]
        self.record(f, body, 8 * len(body), order)
        bits = []
        for byte in rest:
            bits += to_bits(byte, 8, order)
        self.chan = {"coder": _RawCoder(), "line": bits}
        try:
            for fld in tail:
                self.walk(fld, owner)
        finally:
            self.chan = None

    # -- crc / parity --
    def covered(self, f):
        t = f.type
        if t.last is None:                                     # open range F1..* (18.2)
            last = len(self.flog) - 1 if self.flog else None
        else:
            last = max((i for i, e in enumerate(self.flog) if e[0] == t.last), default=None)
        if last is None:
            raise EvalError(f"crc/parity range end '{t.last}' has not occurred")
        first = max((i for i, e in enumerate(self.flog[:last + 1]) if e[0] == t.first), default=None)
        if first is None:
            raise EvalError(f"crc/parity range start '{t.first}' has not occurred")
        return self.flog[first:last + 1]

    def covered_bytes(self, f):
        out = bytearray()
        for name, v, kind, w, order, raw in self.covered(f):
            if w % 8:
                raise NotImplementedError(f"crc over '{name}': width {w} is not a whole number of bytes")
            if isinstance(v, (bytes, bytearray)):
                out += v
            else:
                nb = w // 8
                if kind == "s":
                    v &= (1 << w) - 1
                bs = v.to_bytes(nb, "big")
                out += bs if order == "msb" else bs[::-1]
        return bytes(out)

    def crc_of(self, f):
        c = self.s.crcs.get(f.type.crc) or STD[f.type.crc]
        return crc_bytes(c, self.covered_bytes(f))

    def f_crc(self, f, o):
        c = self.s.crcs.get(f.type.crc) or STD[f.type.crc]
        order = self.order_of(f.type)
        if self.enc:
            v = self.crc_of(f)
            if f.name:
                e = self.peek_ev()
                if e is not None and e[0] == f.name:
                    self.ei += 1
                    v = e[1]                      # explicit value (fault injection)
            for b in to_bits(v, c.width, order):
                self.put_data_bit(b, {o})
            self.record(f, v, c.width, order)
        else:
            got = from_bits(self.get_bits(c.width), order)
            want = self.crc_of(f)
            self.record(f, got, c.width, order)
            if got != want:
                self._mismatch(f.name or "crc", f"{c.name} received {got:#x}, computed {want:#x}")

    def f_parity(self, f, o):
        ones = 0
        for name, v, kind, w, order, raw in self.covered(f):
            vv = int.from_bytes(v, "big") if isinstance(v, (bytes, bytearray)) else (v & ((1 << w) - 1))
            ones += bin(vv).count("1")
        bit = ones & 1 if f.type.parity == "even" else 1 - (ones & 1)
        if self.enc:
            e = self.peek_ev()
            if f.name and e is not None and e[0] == f.name:
                self.ei += 1
                bit = e[1]
            self.put_data_bit(bit, {o})
            self.record(f, bit, 1, self.bits.order)
        else:
            got = self.get_data_bit()
            self.record(f, got, 1, self.bits.order)
            if got != bit:
                self._mismatch(f.name or "parity", f"{f.type.parity} parity received {got}, computed {bit}")


_MISSING = object()


def _fields(n, out=None):
    from .analysis import fields_in
    return fields_in(n)
