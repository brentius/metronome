"""Layered protocols (SPEC_V2_SCORE.md part A 18.2): a protocol written over a production of another protocol.

    use uart_8n1 as uart
    protocol modbus_rtu over uart.char

The upper score has no physical layer. Its grammar runs over a stream of bytes; each byte is carried by one
instance of the lower production (`char`), whose single host field is the byte. A `gap` in the upper grammar is
silence on the lower line, and the frame boundary that `bytes until eof` reads to.

Pieces:
* `load_library(name)`: a library score from `code/score/lib/NAME.score`, checked like any score.
* `check_layered(score)`: the static checks for an upper score (codes E-NAMES, E-LAYER, E-OWNER, E-ROLE).
* `ByteCodec`: the upper grammar over byte tokens (encode: events -> bytes and gaps; decode: the reverse).
* `LayeredCodec`: ByteCodec composed with the lower score's reference codec, so an upper score encodes to and
  decodes from wire waveforms like any other score.

Roles map by position: the upper score's first role plays the lower score's first role. Every upper field must
be owned by the role that owns the lower payload field (one direction per layered score).
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from .ast import *  # noqa: F403
from .crc import STD, crc_bytes
from .model import EvalError, eval_expr, qty_cycles

LIB_DIR = Path(__file__).resolve().parents[1] / "lib"
_SUPPORTED = "fields of whole bytes, bytes[N], bytes until eof, const, crc, gap, switch, if, repeats, productions " \
             "and state updates"


class LayerError(Exception):
    pass


# ---- library -------------------------------------------------------------------------------------------------
def find_library(name: str) -> Path | None:
    p = LIB_DIR / f"{name}.score"
    return p if p.is_file() else None


def load_library(name: str) -> Score:
    from .checks import assert_ok
    from .parser import parse_file
    p = find_library(name)
    if p is None:
        raise ScoreError(f"no library score '{name}' (looked for {p or LIB_DIR / (name + '.score')})", None,
                         "E-NAMES")
    s = parse_file(p)
    assert_ok(s)
    return s


def lower_of(score: Score):
    """(lower score, carrier production, payload field) of a layered score. Raises ScoreError."""
    alias, prod = score.over
    if alias not in score.imports:
        raise ScoreError(f"'over {alias}.{prod}': no 'use LIB as {alias}'", None, "E-NAMES")
    lower = load_library(score.imports[alias])
    ps = lower.prods_named(prod)
    if len(ps) != 1 or ps[0].params:
        raise ScoreError(f"'over {alias}.{prod}': {score.imports[alias]} has no single parameterless production "
                         f"'{prod}'", None, "E-LAYER")
    from .analysis import fields_in
    host = [f for f in fields_in(ps[0].body) if f.value is None and f.type.kind != "crc"]
    if len(host) != 1 or host[0].type.kind != "u" or host[0].type.width != 8:
        raise ScoreError(f"'over {alias}.{prod}': the carrier must have exactly one host field of type u8 "
                         f"(found {[f.name for f in host]})", None, "E-LAYER")
    top = lower.prods[0].body
    if not (isinstance(top, Rep) and top.kind in ("star", "plus") and isinstance(top.node, Ref)
            and top.node.name == prod):
        raise ScoreError(f"'over {alias}.{prod}': the lower start production must be '{prod}*'", None, "E-LAYER")
    return lower, ps[0], host[0]


# ---- static checks -------------------------------------------------------------------------------------------
def check_layered(score: Score) -> list[Diag]:
    from .checks import _GW, check_extensions
    d: list[Diag] = []
    E = lambda code, msg, pos=None: d.append(Diag(code, msg, pos))   # noqa: E731
    try:
        lower, prod, payload = lower_of(score)
    except ScoreError as e:
        return [Diag(e.code, e.msg, e.pos)]
    for what, present in (("wire", score.wires or score.groups), ("clock", score.clock), ("symbols", score.symbols),
                          ("recognise", score.recognise), ("abort", score.aborts),
                          ("arbitrate", score.arbitrates), ("constrain", score.constraints)):
        if present:
            E("E-LAYER", f"a layered score has no '{what}' section: the physical layer belongs to "
                         f"{score.imports[score.over[0]]}")
    b = score.bits
    if b.differential is not None or b.stuff is not None or b.invert:
        E("E-LAYER", "in a layered score 'bits' only gives the byte order of multi-byte fields")
    for u in score.uses:
        if u != "std":
            E("E-NAMES", f"unknown library '{u}'")
    d += check_extensions(score)
    # ownership: the upper role that maps onto the lower payload owner is the only one that can send bytes
    lower_owner = payload.by or _prod_owner(lower, prod.name)
    sender = score.roles[lower.roles.index(lower_owner)]
    gw = _GW(score)
    gw.E = lambda code, msg, pos: E(code, msg, pos)                 # noqa: E731
    params = {p.name for p in score.params}

    def walk(n, scope, owner, stack):
        if isinstance(n, Seq):
            for it in n.items:
                scope = walk(it, scope, owner, stack)
            return scope
        if isinstance(n, Rep):
            if n.kind == "times":
                gw.names_ok(n.arg, scope, n.pos)
                gw.role_expr(n.arg, None, n.pos, "a repeat count", scope)
            s1 = walk(n.node, scope, owner, stack)
            if n.kind in ("until", "while"):
                sc = s1 if n.kind == "until" else scope
                gw.names_ok(n.arg, sc, n.pos)
                gw.role_expr(n.arg, None, n.pos, f"a '{n.kind}' condition", sc)
            return s1
        if isinstance(n, If):
            gw.names_ok(n.cond, scope, n.pos)
            gw.role_expr(n.cond, None, n.pos, "an 'if' condition", scope)
            return walk(n.node, scope, owner, stack)
        if isinstance(n, Switch):
            gw.names_ok(n.expr, scope, n.pos)
            gw.role_expr(n.expr, None, n.pos, "a switch", scope)
            out = scope
            for _, a in n.arms:
                out = out | walk(a, scope, owner, stack)
            if n.other is not None:
                out = out | walk(n.other, scope, owner, stack)
            return out
        if isinstance(n, Assign):
            if score.state(n.name) is None:
                E("E-NAMES", f"'{n.name} <- ...': '{n.name}' is not declared in a 'state' section", n.pos)
            gw.names_ok(n.expr, scope, n.pos)
            gw.role_expr(n.expr, None, n.pos, f"the state update '{n.name} <- ...'", scope)
            return scope
        if isinstance(n, Field):
            o = n.by or owner
            if o not in score.roles:
                E("E-NAMES", f"unknown role '{o}'", n.pos)
            elif o != sender:
                E("E-OWNER", f"'{n.name or n.type.kind}' is owned by {o}, but only {sender} can send bytes over "
                             f"{score.over[0]}.{score.over[1]} (its payload is driven by {lower_owner})", n.pos)
            t = n.type
            if t.kind in ("bit", "parity"):
                E("E-LAYER", f"'{n.name or t.kind}': a layered score carries whole bytes ({t.kind} is not one)",
                  n.pos)
            elif t.kind in ("u", "s") and t.width % 8:
                E("E-LAYER", f"'{n.name}': {t.kind}{t.width} is not a whole number of bytes", n.pos)
            elif t.kind == "crc":
                c = score.crcs.get(t.crc) or (STD.get(t.crc) if "std" in score.uses else None)
                if c is None:
                    E("E-NAMES", f"unknown crc '{t.crc}' (declare it with 'crc', or 'use std')", n.pos)
                elif c.width % 8:
                    E("E-LAYER", f"crc '{t.crc}' is {c.width} bits, not a whole number of bytes", n.pos)
                for fn in (t.first, t.last):
                    if fn is not None and fn not in scope:
                        E("E-NAMES", f"'{n.name or 'crc'}': field '{fn}' is not in scope for the range", n.pos)
            elif t.kind == "bytes":
                if t.length is not None:
                    gw.names_ok(t.length, scope, n.pos)
                    gw.role_expr(t.length, None, n.pos, f"the length of '{n.name}'", scope)
                elif t.until != "eof":
                    E("E-LAYER", f"'{n.name}': a layered score reads 'bytes until eof' (the frame end) only", n.pos)
            gw.names_ok(n.value, scope, n.pos)
            gw.names_ok(n.expect, scope, n.pos)
            gw.role_expr(n.value, o, n.pos, f"the value of '{n.name}'", scope)
            return scope | ({n.name} if n.name else set())
        if isinstance(n, (ConstBytes, Gap)):
            if isinstance(n, Gap) and n.qty.unit not in ("chars", "ns", "us", "ms", "s"):
                E("E-LAYER", "a gap in a layered score is given in chars or time", n.pos)
            return scope
        if isinstance(n, Ref):
            if not score.prods_named(n.name):
                E("E-LAYER", f"'{n.name}': a layered score calls productions only (symbols and events belong to the "
                             f"lower protocol)", n.pos)
                return scope
            if n.name in stack:
                E("E-AMBIG", f"production '{n.name}' is recursive (7.1)", n.pos)
                return scope
            out = scope
            for a in n.args:
                gw.names_ok(a, scope, n.pos)
                gw.role_expr(a, None, n.pos, f"an argument of '{n.name}'", scope)
            for p in score.prods_named(n.name):
                if len(p.params) != len(n.args):
                    E("E-NAMES", f"production '{n.name}' takes {len(p.params)} argument(s), got {len(n.args)}",
                      n.pos)
                    continue
                inner = frozenset(scope | {q[1] for q in p.params if q[0] == "id"})
                out = out | (walk(p.body, inner, n.by or owner, stack + (n.name,)) -
                             {q[1] for q in p.params if q[0] == "id"})
            return frozenset(out)
        names = {Choice: "choice '|' (use switch on a field)", Dup: "'||'", ConstBits: "const bits",
                 Every: "every", Retry: "retry", Within: "within", AsmBlock: "asm", Turnaround: "turnaround"}
        E("E-LAYER", f"{names.get(type(n), type(n).__name__)} is not available in a layered score ({_SUPPORTED})",
          getattr(n, "pos", None))
        return scope

    start = score.prods[0]
    walk(start.body, frozenset(), score.roles[0], (start.name,))
    del params
    return d


def _prod_owner(score: Score, prod: str) -> str:
    """Owner of production `prod` when called from the start production (first `by` on the call path)."""
    def find(n, owner):
        if isinstance(n, Ref):
            o = n.by or owner
            if n.name == prod:
                return o
            for p in score.prods_named(n.name):
                r = find(p.body, o)
                if r:
                    return r
            return None
        for k in ("items", "alts"):
            for x in getattr(n, k, []) or []:
                r = find(x, owner)
                if r:
                    return r
        for k in ("node", "a", "b"):
            x = getattr(n, k, None)
            if x is not None and not isinstance(x, (int, str)):
                r = find(x, owner)
                if r:
                    return r
        return None
    return find(score.prods[0].body, score.roles[0]) or score.roles[0]


# ---- the upper grammar over bytes ----------------------------------------------------------------------------
class _BRun:
    """One encode or decode pass of a layered grammar. Encode: events -> tokens [("byte", v) | ("gap", Qty)].
    Decode: tokens [("byte", v) | ("eof",)] -> events."""

    def __init__(self, bc: "ByteCodec", enc, events=None, tokens=None):
        self.bc, self.s, self.enc = bc, bc.score, enc
        self.st = bc.state_for("encode" if enc else "decode")
        self.env = {**self.s.consts(), **bc.params, **self.st}
        self.ev, self.ei = list(events or []), 0
        self.tok, self.ti = list(tokens or []), 0
        self.out: list = []
        self.events: list = []
        self.flog: list = []          # (name, bytes) of the frame's fields, for crc ranges
        self.notes: list = []
        self.ok = True

    # -- helpers --
    def val(self, e):
        try:
            return eval_expr(e, self.env)
        except EvalError as ex:
            raise LayerError(str(ex))

    def order(self, t):
        return t.order or self.s.bits.order

    def peek_ev(self):
        return self.ev[self.ei] if self.ei < len(self.ev) else None

    def fev(self, n, seen=()):
        """Event names that can begin n, and whether n can be empty."""
        if isinstance(n, Seq):
            names = set()
            for it in n.items:
                nm, nl = self.fev(it, seen)
                names |= nm
                if not nl:
                    return names, False
            return names, True
        if isinstance(n, Rep):
            nm, nl = self.fev(n.node, seen)
            return nm, nl or n.kind in ("star", "opt", "while")
        if isinstance(n, If):
            return self.fev(n.node, seen)[0], True
        if isinstance(n, Switch):
            names, nul = set(), n.other is None
            for _, a in n.arms + ([(None, n.other)] if n.other is not None else []):
                nm, nl = self.fev(a, seen)
                names |= nm
                nul = nul or nl
            return names, nul
        if isinstance(n, Field):
            return ({n.name}, n.value is not None or n.type.kind == "crc") if n.name else (set(), True)
        if isinstance(n, Ref) and n.name not in seen:
            names, nul = set(), False
            for p in self.s.prods_named(n.name):
                nm, nl = self.fev(p.body, seen + (n.name,))
                names |= nm
                nul = nul or nl
            return names, nul
        return set(), True

    def more(self, node):
        if self.enc:
            e = self.peek_ev()
            return e is not None and e[0] in self.fev(node)[0]
        return self.ti < len(self.tok) and self.tok[self.ti][0] == "byte"

    def put(self, data: bytes):
        self.out += [("byte", b) for b in data]

    def take(self, n: int) -> bytes:
        got = bytearray()
        for _ in range(n):
            if self.ti >= len(self.tok) or self.tok[self.ti][0] != "byte":
                raise LayerError(f"frame ended early: needed {n} byte(s), got {len(got)}")
            got.append(self.tok[self.ti][1])
            self.ti += 1
        return bytes(got)

    def mismatch(self, name, msg):
        self.ok = False
        self.notes.append(f"mismatch in {name}: {msg}")

    # -- walk --
    def walk(self, n, owner):
        return getattr(self, "w_" + type(n).__name__)(n, owner)

    def w_Seq(self, n, owner):
        i = 0
        while i < len(n.items):
            it = n.items[i]
            if not self.enc and isinstance(it, Field) and it.type.kind == "bytes" and it.type.until == "eof":
                tail = []
                for x in n.items[i + 1:]:
                    if isinstance(x, Field) and x.type.kind in ("u", "s", "crc"):
                        tail.append(x)
                    else:
                        break
                self.bytes_until_eof(it, sum(self.field_width(x) for x in tail))
                i += 1
                continue
            self.walk(it, owner)
            i += 1

    def w_Rep(self, n, owner):
        k = n.kind
        if k == "times":
            for _ in range(self.val(n.arg)):
                self.walk(n.node, owner)
        elif k in ("star", "plus", "opt"):
            first = True
            while (k == "plus" and first) or self.more(n.node):
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

    def w_If(self, n, owner):
        if self.val(n.cond):
            self.walk(n.node, owner)

    def w_Switch(self, n, owner):
        v = self.val(n.expr)
        for a, node in n.arms:
            if a == v:
                return self.walk(node, owner)
        if n.other is not None:
            return self.walk(n.other, owner)
        if not self.enc:
            self.mismatch("switch", f"no arm for value {v}")
            raise LayerError(f"switch: no arm for value {v}")
        raise LayerError(f"switch: no arm for value {v}")

    def w_Assign(self, n, owner):
        st = self.s.state(n.name)
        v = self.val(n.expr) & ((1 << st.width) - 1)
        self.env[n.name] = v
        self.st[n.name] = v

    def w_Gap(self, n, owner):
        self.flog = []                                        # a gap ends the frame: crc ranges restart
        if self.enc:
            self.out.append(("gap", n.qty))
        elif self.ti < len(self.tok) and self.tok[self.ti][0] == "eof":
            self.ti += 1
        elif self.ti < len(self.tok):
            self.ok = False
            self.notes.append(f"expected the end of a frame (gap), got {len(self.tok) - self.ti} more token(s)")

    def w_ConstBytes(self, n, owner):
        if self.enc:
            self.put(n.data)
        else:
            got = self.take(len(n.data))
            if got != n.data:
                self.mismatch("const", f"expected {n.data.hex()}, got {got.hex()}")

    def w_Ref(self, n, owner):
        argv = [self.val(a) for a in n.args]
        pick = None
        for p in self.s.prods_named(n.name):
            if all(q[0] == "id" or q[1] == v for q, v in zip(p.params, argv)):
                pick = p
                break
        if pick is None:
            raise LayerError(f"no definition of '{n.name}' matches arguments {argv}")
        saved = {q[1]: self.env.get(q[1]) for q in pick.params if q[0] == "id"}
        for q, v in zip(pick.params, argv):
            if q[0] == "id":
                self.env[q[1]] = v
        self.walk(pick.body, n.by or owner)
        for k, v in saved.items():
            if v is None:
                self.env.pop(k, None)
            else:
                self.env[k] = v

    # -- fields --
    def field_width(self, f) -> int:
        t = f.type
        if t.kind == "crc":
            return self.crc_decl(f).width // 8
        return t.width // 8

    def crc_decl(self, f):
        return self.s.crcs.get(f.type.crc) or STD[f.type.crc]

    def to_bytes(self, v, f) -> bytes:
        t = f.type
        nb = self.field_width(f)
        if t.kind == "s":
            v &= (1 << (8 * nb)) - 1
        bs = v.to_bytes(nb, "big")
        return bs if self.order(t) == "msb" else bs[::-1]

    def from_bytes(self, bs: bytes, f) -> int:
        t = f.type
        v = int.from_bytes(bs if self.order(t) == "msb" else bs[::-1], "big")
        if t.kind == "s" and v >> (8 * len(bs) - 1):
            v -= 1 << (8 * len(bs))
        return v

    def record(self, f, v, raw: bytes):
        if f.name:
            self.env[f.name] = v if not isinstance(v, (bytes, bytearray)) else int.from_bytes(v, "big")
            if not self.enc:
                self.events.append((f.name, v))
        self.flog.append((f.name, raw))

    def enc_value(self, f):
        e = self.peek_ev()
        if e is not None and e[0] == f.name:
            self.ei += 1
            v = e[1]
            if isinstance(v, str) and f.type.enum:
                v = self.s.enums[f.type.enum].members[v]
            return v
        if f.value is not None:
            return self.val(f.value)
        raise LayerError(f"field '{f.name}' has no value: expected event {f.name!r}, got {e!r}")

    def w_Field(self, f, owner):
        t = f.type
        if t.kind == "crc":
            return self.f_crc(f)
        if t.kind == "bytes":
            if t.until == "eof":
                return self.bytes_until_eof(f, 0)
            n = self.val(t.length)
            if self.enc:
                data = bytes(self.enc_value(f))
                if len(data) != n:
                    raise LayerError(f"field {f.name}: {len(data)} bytes given, length expression says {n}")
                self.put(data)
                self.record(f, data, data)
            else:
                data = self.take(n)
                self.record(f, data, data)
            return
        if self.enc:
            v = self.enc_value(f)
            raw = self.to_bytes(v, f)
            if self.from_bytes(raw, f) != v:
                raise LayerError(f"field {f.name}: {v} does not fit {t.kind}{t.width}")
            self.put(raw)
            self.record(f, v, raw)
        else:
            raw = self.take(self.field_width(f))
            v = self.from_bytes(raw, f)
            self.record(f, v, raw)
            if f.expect is not None and self.val(f.expect) != v:
                self.mismatch(f.name, f"expected {self.val(f.expect)}, got {v}")
            if t.enum and v not in self.s.enums[t.enum].members.values():
                self.mismatch(f.name, f"{v} is not a member of enum {t.enum}")

    def bytes_until_eof(self, f, tail_bytes):
        if self.enc:
            data = bytes(self.enc_value(f))
            self.put(data)
            self.record(f, data, data)
            return
        j = self.ti
        while j < len(self.tok) and self.tok[j][0] == "byte":
            j += 1
        n = j - self.ti - tail_bytes
        if n < 0:
            raise LayerError(f"frame too short for '{f.name}' and the {tail_bytes} byte(s) after it")
        data = self.take(n)
        self.record(f, data, data)

    def covered(self, f) -> bytes:
        t = f.type
        names = [n for n, _ in self.flog]
        if t.last is None:                                   # open range F1..*
            last = len(names) - 1
        elif t.last not in names:
            raise LayerError(f"crc range end '{t.last}' has not occurred")
        else:
            last = max(i for i, n in enumerate(names) if n == t.last)
        firsts = [i for i, n in enumerate(names[:last + 1]) if n == t.first]
        if not firsts:
            raise LayerError(f"crc range start '{t.first}' has not occurred")
        return b"".join(raw for _, raw in self.flog[max(firsts):last + 1])

    def f_crc(self, f):
        c = self.crc_decl(f)
        want = crc_bytes(c, self.covered(f))
        if self.enc:
            v = want
            e = self.peek_ev()
            if f.name and e is not None and e[0] == f.name:      # explicit value: fault injection
                self.ei += 1
                v = e[1]
            raw = self.to_bytes(v, f)
            self.put(raw)
            self.record(f, v, raw)
        else:
            raw = self.take(c.width // 8)
            v = self.from_bytes(raw, f)
            self.record(f, v, raw)
            if v != want:
                self.mismatch(f.name or "crc", f"crc {c.name}: computed {want:#x}, received {v:#x}")


class ByteCodec:
    """The grammar of a layered score over a byte stream (18.2)."""

    def __init__(self, score: Score, params: dict | None = None):
        from .checks import errors
        es = errors(score)
        if es:
            raise ScoreError("; ".join(map(str, es)), es[0].pos, es[0].code)
        self.score = score
        self.params = dict(params or {})
        for p in score.params:
            if p.name not in self.params and p.default is not None:
                self.params[p.name] = eval_expr(p.default, {})
        self.state: dict = {}

    def state_for(self, key) -> dict:
        if key not in self.state:
            self.state[key] = {s.name: s.init for s in self.score.states}
        return self.state[key]

    def reset_state(self):
        self.state.clear()

    def encode(self, events) -> list:
        r = _BRun(self, True, events=events)
        r.walk(self.score.prods[0].body, self.score.roles[0])
        if r.ei < len(r.ev):
            raise LayerError(f"event #{r.ei} {r.ev[r.ei]!r} was not consumed by the grammar")
        return r.out

    def decode(self, tokens):
        """-> (events, ok, notes)."""
        r = _BRun(self, False, tokens=tokens)
        try:
            r.walk(self.score.prods[0].body, self.score.roles[0])
            if r.ti < len(r.tok):
                r.ok = False
                r.notes.append(f"{len(r.tok) - r.ti} token(s) left over")
        except LayerError as e:
            r.ok = False
            r.notes.append(str(e))
        return r.events, r.ok, r.notes


class LayeredCodec:
    """An upper score's ByteCodec over the lower score's reference codec: encodes events to wire waveforms and
    decodes waveforms back to events, like `Codec` does for a physical score."""

    def __init__(self, score: Score, params: dict | None = None, rate=None, lower_params: dict | None = None):
        from .codec import Codec
        self.score = score
        self.bc = ByteCodec(score, params)
        self.lower, self.carrier, self.payload = lower_of(score)
        self.lc = Codec(self.lower, params=lower_params, rate=rate)
        enc = self.lc.encode_all([(self.payload.name, 0)], lead=0, tail=0)
        self.char_cycles = sum(self.lc.P if getattr(x, "kind", "") == "beat" else x.cycles for x in enc.plan)
        self.data_wire = self.lc.data_wire() or self.lower.all_wires()[0].name
        self.idle = self.lc.q[self.data_wire]

    def lower_role(self, role):
        return self.lower.roles[self.score.roles.index(role)]

    def gap_cycles(self, q: Qty) -> Fraction:
        if q.unit == "chars":
            return q.value * self.char_cycles
        return qty_cycles(q, self.lc.P)

    def min_gap_cycles(self):
        gaps = []

        def find(n):
            if isinstance(n, Gap):
                gaps.append(self.gap_cycles(n.qty))
            for k in ("items", "alts"):
                for x in getattr(n, k, []) or []:
                    find(x)
            for k in ("node", "other"):
                x = getattr(n, k, None)
                if x is not None:
                    find(x)
            for _, a in getattr(n, "arms", []) or []:
                find(a)
        for p in self.score.prods:
            find(p.body)
        return min(gaps) if gaps else None

    def encode_all(self, events, lead: int = 8, tail: int = 8):
        """-> (bus {wire: levels}, tokens). Bytes run back to back; each upper gap is that much silence."""
        tokens = self.bc.encode(events)
        runs, cur, gaps = [], [], []
        for t in tokens:
            if t[0] == "byte":
                cur.append(t[1])
            else:
                runs.append(cur)
                gaps.append(self.gap_cycles(t[1]))
                cur = []
        if cur:
            runs.append(cur)
            gaps.append(Fraction(0))
        wires = {w.name: [] for w in self.lower.all_wires() if not w.mirror_of}
        for run, g in zip(runs, gaps):
            if not run:
                continue
            enc = self.lc.encode_all([(self.payload.name, b) for b in run], lead=lead, tail=tail)
            for w in wires:
                lv = enc.bus.wires[w]
                wires[w] += lv + [lv[-1]] * int(-(-g // 1))
        for w in self.lower.all_wires():
            if w.mirror_of:
                wires[w.name] = [1 - v for v in wires[w.mirror_of]]
        return wires, tokens

    def decode(self, role, bus):
        """Decode `bus` as `role` (an upper role). -> (events, ok, notes)."""
        if hasattr(bus, "wires"):
            bus = bus.wires
        lv = bus[self.data_wire]
        g = self.min_gap_cycles()
        # frame boundary: an idle run of at least 2/3 of the smallest gap (reading in NOTES.md, 18.2)
        thr = int(g * 2 / 3) if g else len(lv) + 1
        act = [i for i, v in enumerate(lv) if v != self.idle]
        spans = []
        for i in act:
            if spans and i - spans[-1][1] < thr:
                spans[-1][1] = i
            else:
                spans.append([i, i])
        tokens, notes, ok = [], [], True
        lrole = self.lower_role(role) if role in self.score.roles else self.lower.roles[1]
        for a, b in spans:
            s0, s1 = max(0, a - 8), min(len(lv), b + max(thr // 2, int(self.char_cycles) + 8))
            seg = {w: v[s0:s1] for w, v in bus.items()}
            r = self.lc.decode(lrole, seg)
            if not r.ok:
                ok = False
                notes += [f"lower frame at cycle {a}: {n}" for n in r.notes]
            tokens += [("byte", v) for k, v in r.events if k == self.payload.name] + [("eof",)]
        ev, ok2, n2 = self.bc.decode(tokens)
        return ev, ok and ok2, notes + n2
