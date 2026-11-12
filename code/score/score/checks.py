"""Static checks (spec 12.2): names, ownership, decidability, duplex, fit rules R1-R5, binding."""
from __future__ import annotations

import itertools
import re
from fractions import Fraction

from .analysis import Analyzer, bitlen, fields_in, kind_of, lin_str
from .ast import *  # noqa: F403
from .crc import STD
from .model import (parse_wave, DATA_SYMBOL, EVENT_NAMES, beat_cycles, boundaries, expand_wave, expr_names, idle_level,
                    nseg, resolve_time, symbol_instances, inst_name)

R1_MAX_SYMBOLS = 16
R3_MAX_SEG = 4
R3_MAX_TAPS = 3
R4_MAX_WIRES = 2
R5_MAX_OE_WIRES = 8
MAX_GROUPS = 4


def check(score: Score) -> list[Diag]:
    """All static checks that need no compiler. Returns diagnostics (errors have codes starting E-)."""
    d: list[Diag] = []
    d += check_names(score)
    if not any(x.code in ("E-NAMES",) for x in d):
        d += check_grammar(score)
        d += Analyzer(score).run()
        d += check_fit(score)
    seen, out = set(), []
    for x in d:
        k = (x.code, x.pos, x.msg)
        if k not in seen:
            seen.add(k)
            out.append(x)
    return out


def errors(score: Score) -> list[Diag]:
    return [x for x in check(score) if x.code.startswith("E-")]


def assert_ok(score: Score):
    es = errors(score)
    if es:
        raise ScoreError("\n".join(str(e) for e in es), es[0].pos, es[0].code)


# ---- names ---------------------------------------------------------------------------------------------------
def _groups(score: Score):
    """[(name, wires, clock)] line groups."""
    if score.groups:
        out = [(g.name, g.wires, g.clock) for g in score.groups]
        if score.wires or score.clock:
            out.insert(0, ("main", score.wires, score.clock))
        return out
    return [("main", score.wires, score.clock)]


def check_names(score: Score) -> list[Diag]:
    d: list[Diag] = []
    E = lambda msg, pos=None, code="E-NAMES": d.append(Diag(code, msg, pos))   # noqa: E731
    roles = set(score.roles)
    for u in score.uses:
        if u != "std":
            E(f"unknown library '{u}' (only 'std' exists)")
    wnames = {}
    for w in score.all_wires():
        if w.name in wnames:
            E(f"wire '{w.name}' declared twice", w.pos)
        wnames[w.name] = w
        if w.by and w.by not in roles:
            E(f"wire '{w.name}': unknown role '{w.by}'", w.pos)
        if w.mirror_of and not any(x.name == w.mirror_of for x in score.all_wires()):
            E(f"mirror '{w.name}': unknown wire '{w.mirror_of}'", w.pos)
    clocks = [(n, c) for n, ws, c in _groups(score) if c]
    if not clocks:
        E("no clock declared", None)
    for n, c in clocks:
        for r in score.roles:
            if r not in c.roles:
                E(f"clock: role '{r}' has no clock mode", c.pos)
        for r, rc in c.roles.items():
            if r not in roles:
                E(f"clock: unknown role '{r}'", rc.pos)
            for wn in (rc.wire, rc.cap_wire, rc.stretch):
                if wn and wn not in wnames:
                    E(f"clock: unknown wire '{wn}'", rc.pos)
    if len(_groups(score)) > MAX_GROUPS:
        E(f"{len(_groups(score))} groups; at most {MAX_GROUPS} per loaded image", None, "E-FIT-GROUP")
    syms = {}
    for s in score.symbols:
        if s.name in syms:
            E(f"symbol '{s.name}' declared twice", s.pos)
        syms[s.name] = s
        for p in s.params:
            if len(p) != 1 or p in "01xz.!":
                E(f"symbol '{s.name}': parameter '{p}' must be a single letter other than x and z "
                  f"(parameters are written one character at a time in wave strings)", s.pos)
        seen_w = set()
        for w, wave, pos in s.waves:
            if w not in wnames:
                E(f"symbol '{s.name}': unknown wire '{w}'", pos)
            if w in seen_w:
                E(f"symbol '{s.name}': wire '{w}' given twice", pos)
            seen_w.add(w)
            try:
                from .model import parse_wave
                items = parse_wave(wave, s.params, pos)
                # parameters must be declared; parse_wave rejects unknown characters
                for it in items:
                    pass
            except ScoreError as e:
                d.append(Diag(e.code, e.msg, e.pos))
        for w, tr in s.samples:
            if w is not None and w not in wnames:
                E(f"symbol '{s.name}': sample of unknown wire '{w}'", tr.pos)
            if tr.kind == "edge" and tr.wire not in wnames:
                E(f"symbol '{s.name}': sample edge on unknown wire '{tr.wire}'", tr.pos)
    for r in score.recognise:
        for wn in (r.wire, r.while_wire):
            if wn and wn not in wnames:
                E(f"recognise {r.names[0]}: unknown wire '{wn}'", r.pos)
    for name, c in score.crcs.items():
        pass
    for p in score.params:
        if p.for_role and p.for_role not in roles:
            E(f"param '{p.name}': unknown role '{p.for_role}'", p.pos)
    for wn in score.arbitrates:
        w = score.wire(wn)
        if w is None:
            E(f"arbitrate: unknown wire '{wn}'")
        elif w.dir != "shared":
            E(f"arbitrate: '{wn}' must be a shared wire (8.4)")
    for a in score.aborts:
        if kind_of(score, a.event) != "event":
            E(f"abort: unknown event '{a.event}'", a.pos)
        if a.in_prod and not score.prods_named(a.in_prod):
            E(f"abort: unknown production '{a.in_prod}'", a.pos)
        if a.target not in ("idle", "report") and not score.prods_named(a.target):
            E(f"abort: unknown target '{a.target}'", a.pos)
    # production arity consistency
    byname = {}
    for p in score.prods:
        byname.setdefault(p.name, []).append(p)
    for n, ps in byname.items():
        if len({len(p.params) for p in ps}) > 1:
            E(f"production '{n}' defined with different numbers of parameters", ps[0].pos)
        if len(ps) > 1 and any(q[0] == "id" for p in ps for q in p.params):
            pass
    if any(kind_of(score, p.name) == "sym" for p in score.prods):
        for p in score.prods:
            if score.symbol(p.name):
                E(f"production '{p.name}' has the same name as a symbol", p.pos)
    return d


# ---- grammar walk: scope, ownership, duplex --------------------------------------------------------------------
class _GW:
    def __init__(self, score):
        self.s = score
        self.d: list[Diag] = []
        self.dup: set = set()
        self.sides = None
        self.tx: dict = {}
        self.rx: dict = {}
        self.prev = None          # (owner, shared push-pull wires) of the previous beat terminal
        self.stack: list[str] = []
        self.bitsym = score.symbol(DATA_SYMBOL)

    def E(self, code, msg, pos):
        self.d.append(Diag(code, msg, pos))

    def names_ok(self, e, scope, pos):
        if e is None:
            return
        for n in expr_names(e):
            if n not in scope and not self.s.param(n):
                self.E("E-NAMES", f"'{n}' is not a field, parameter or production argument in scope here",
                       getattr(e, "pos", None) or pos)

    def sym_check(self, sdef: SymbolDef, owner, pos, what, args=None):
        """Ownership of one symbol terminal (10.2, D29): a value (parameter) may only appear in the wave of a
        wire its owner can drive; wires without a value are driven by their owner whoever owns the beat."""
        s = self.s
        beat_owners = ({owner} | self.dup)
        for r in s.roles:
            (self.tx if r in beat_owners else self.rx).setdefault(r, set()).add(sdef.name)
            if r in beat_owners:
                self.rx.setdefault(r, set())
        shared_pp = set()
        sides = self.sides
        for w, wave, wpos in sdef.waves:
            wire = s.wire(w)
            if wire is None:
                continue
            try:
                items = parse_wave(wave, sdef.params, wpos)
            except ScoreError:
                continue
            if wire.dir != "shared":
                owners = s.wire_owners(wire)
                for p in sorted({it[1] for it in items if it[0] == "p"}):
                    i = sdef.params.index(p)
                    if args is not None and i < len(args) and isinstance(args[i], Num):
                        continue                      # a constant is known to every role
                    prov = sides[i] if sides and i < len(sides) else owner
                    if prov not in owners:
                        self.E("E-OWNER", f"grammar: '{what}' owned by {prov} puts its value '{p}' in the wave of "
                                          f"'{w}', which is {wire.dir} by {', '.join(sorted(owners))}", pos)
            elif wire.drive == "push-pull":
                shared_pp.add(w)
        if self.prev is not None and shared_pp & self.prev[1] and self.prev[0] != owner and not self.dup:
            self.E("E-OWNER", f"grammar: '{what}' (owner {owner}) follows a terminal owned by {self.prev[0]} on "
                              f"shared push-pull wire(s) {sorted(shared_pp & self.prev[1])} with no turnaround "
                              f"(10.2)", pos)
        self.prev = (owner, shared_pp)

    def role_ok(self, r, pos):
        if r is not None and r not in self.s.roles:
            self.E("E-NAMES", f"unknown role '{r}'", pos)

    def walk(self, n, scope: frozenset, owner):
        S = self.s
        if isinstance(n, Seq):
            for it in n.items:
                scope = self.walk(it, scope, owner)
            return scope
        if isinstance(n, Choice):
            out, prev0 = scope, self.prev
            for a in n.alts:
                self.prev = prev0
                out = out | self.walk(a, scope, owner)
            return out
        if isinstance(n, Dup):
            oa = {f.by or owner for f in fields_in(n.a)} or {owner}
            ob = {f.by or owner for f in fields_in(n.b)} or {owner}
            if len(oa) != 1 or len(ob) != 1 or oa & ob:
                self.E("E-DUPLEX", f"grammar: '||' sides must each have one owner and the owners must differ "
                                   f"(got {sorted(oa)} and {sorted(ob)})", n.pos)
            la, lb = bitlen(S, n.a), bitlen(S, n.b)
            nm = lambda x: (fields_in(x)[0].name if fields_in(x) else "?")   # noqa: E731
            if la is None or lb is None:
                self.E("E-DUPLEX", f"grammar: '||': length of '{nm(n.a)}' or '{nm(n.b)}' is not known before the "
                                   f"pair starts", n.pos)
            elif la != lb:
                self.E("E-DUPLEX", f"grammar: '||' in '{self.stack[-1] if self.stack else '?'}': '{nm(n.a)}' is "
                                   f"{lin_str(la)}, '{nm(n.b)}' is {lin_str(lb)}; both sides must be equal", n.pos)
            for f in fields_in(n.a) + fields_in(n.b):
                if f.type.kind == "bytes" and f.type.until:
                    self.E("E-DUPLEX", "grammar: '||' sides need a length known before the pair starts", n.pos)
            if bitlen(S, n.a) is not None and self.bitsym and len(self.bitsym.params) != 2:
                self.E("E-DUPLEX", f"grammar: '||' needs the data symbol '{DATA_SYMBOL}' to take two parameters "
                                   f"(one per side); it has {len(self.bitsym.params)}", n.pos)
            for side in (n.a, n.b):
                if _has_sym(side):
                    self.E("E-DUPLEX", "grammar: '||' sides may not contain symbol terminals (D29)", n.pos)
            if S.bits.differential is not None or S.bits.stuff is not None:
                self.E("E-DUPLEX", "grammar: '||' cannot be used with differential coding or stuffing (D29)", n.pos)
            old, olds = self.dup, self.sides
            self.dup = oa | ob
            self.sides = (next(iter(oa)), next(iter(ob)))
            s1 = self.walk(n.a, scope, owner)
            s2 = self.walk(n.b, scope, owner)
            self.dup, self.sides = old, olds
            return s1 | s2
        if isinstance(n, Rep):
            if n.kind == "times":
                self.names_ok(n.arg, scope, n.pos)
            s1 = self.walk(n.node, scope, owner)
            if n.kind in ("until", "while"):
                self.names_ok(n.arg, s1 if n.kind == "until" else scope, n.pos)
            return s1
        if isinstance(n, If):
            self.names_ok(n.cond, scope, n.pos)
            return self.walk(n.node, scope, owner)
        if isinstance(n, (Within, Every)):
            return self.walk(n.node, scope, owner)
        if isinstance(n, Retry):
            if kind_of(S, n.event) != "event":
                self.E("E-NAMES", f"retry: unknown event '{n.event}'", n.pos)
            return self.walk(n.node, scope, owner)
        if isinstance(n, AsmBlock):
            return scope
        if isinstance(n, Switch):
            self.names_ok(n.expr, scope, n.pos)
            out = scope
            for _, a in n.arms:
                out = out | self.walk(a, scope, owner)
            if n.other is not None:
                out = out | self.walk(n.other, scope, owner)
            return out
        if isinstance(n, Field):
            self.role_ok(n.by, n.pos)
            o = n.by or owner
            t = n.type
            if t.kind == "bytes" and t.length is not None:
                self.names_ok(t.length, scope, n.pos)
            if t.kind == "bytes" and t.until:
                if kind_of(S, t.until) not in ("sym", "event"):
                    self.E("E-NAMES", f"'bytes until {t.until}': not a symbol or recognised event", n.pos)
                elif t.until == DATA_SYMBOL:
                    self.E("E-AMBIG", "bytes until the data symbol can never end", n.pos)
            if t.kind in ("crc", "parity"):
                for fn in (t.first, t.last):
                    if fn not in scope:
                        self.E("E-NAMES", f"'{n.name or t.kind}': field '{fn}' is not in scope for the range", n.pos)
                if t.kind == "crc" and t.crc not in S.crcs and not (t.crc in STD and "std" in S.uses):
                    self.E("E-NAMES", f"unknown crc '{t.crc}' (declare it with 'crc', or 'use std')", n.pos)
            self.names_ok(n.value, scope, n.pos)
            self.names_ok(n.expect, scope, n.pos)
            if n.value is not None and n.expect is not None:
                self.E("E-NAMES", "a field cannot have both '= EXPR' and 'expect EXPR'", n.pos)
            if self.bitsym is None:
                self.E("E-NAMES", f"field '{n.name}' needs a symbol named '{DATA_SYMBOL}' to carry coded bits "
                                  f"(spec 5.3/6 do not name it; this implementation requires it)", n.pos)
            else:
                self.sym_check(self.bitsym, o, n.pos, n.name or t.kind)
            return scope | ({n.name} if n.name else set())
        if isinstance(n, (ConstBytes, ConstBits)):
            if self.bitsym is None:
                self.E("E-NAMES", f"'const' needs a symbol named '{DATA_SYMBOL}'", n.pos)
            else:
                self.sym_check(self.bitsym, owner, n.pos, "const")
            return scope
        if isinstance(n, (Gap, Turnaround)):
            self.prev = None
            return scope
        if isinstance(n, Ref):
            self.role_ok(n.by, n.pos)
            o = n.by or owner
            k = kind_of(S, n.name)
            for a in n.args:
                self.names_ok(a, scope, n.pos)
            if k is None:
                self.E("E-NAMES", f"'{n.name}' is not a symbol, recognised event or production", n.pos)
            elif k == "sym":
                sd = S.symbol(n.name)
                if len(n.args) != len(sd.params):
                    self.E("E-NAMES", f"symbol '{n.name}' takes {len(sd.params)} argument(s), got {len(n.args)}",
                           n.pos)
                self.sym_check(sd, o, n.pos, n.name, n.args)
            elif k == "prod":
                ps = S.prods_named(n.name)
                if n.name in self.stack:
                    self.E("E-AMBIG", f"production '{n.name}' is recursive (7.1)", n.pos)
                    return scope
                if len(ps[0].params) != len(n.args):
                    self.E("E-NAMES", f"production '{n.name}' takes {len(ps[0].params)} argument(s), "
                                      f"got {len(n.args)}", n.pos)
                    return scope
                self.stack.append(n.name)
                out = scope
                prev0 = self.prev
                for p in ps:
                    self.prev = prev0
                    inner = frozenset(scope | {q[1] for q in p.params if q[0] == "id"})
                    out = out | (self.walk(p.body, inner, o) - {q[1] for q in p.params if q[0] == "id"})
                self.stack.pop()
                return frozenset(out)
            return scope
        return scope


def _has_sym(n):
    from .analysis import kind_of  # noqa: F401
    if isinstance(n, Ref):
        return True
    if isinstance(n, Seq):
        return any(_has_sym(i) for i in n.items)
    if isinstance(n, (Rep, If, Within, Every, Retry)):
        return _has_sym(n.node)
    if isinstance(n, Choice):
        return any(_has_sym(a) for a in n.alts)
    return False


def check_grammar(score: Score) -> list[Diag]:
    gw = _GW(score)
    start = score.prods[0]
    gw.stack.append(start.name)
    gw.walk(start.body, frozenset(), score.roles[0])
    score._tx, score._rx = gw.tx, gw.rx          # which symbols each role transmits / receives (for R3)
    # unreachable productions are still walked so their names are checked
    return gw.d


# ---- fit -----------------------------------------------------------------------------------------------------
def _norm_wave(score, w, segs):
    """Normalised per-segment values for compatibility: drive values 0/1/z/x with open-drain 1 == z."""
    wire = score.wire(w)
    out = []
    for c in segs:
        if c == "1" and wire is not None and (wire.drive == "open-drain" or wire.dir == "shared"):
            c = "z"
        out.append(c)
    return out


def symbol_waves(score: Score, clock: Clock):
    """{inst_name: {wire: [per-segment values]}}"""
    n = nseg(clock)
    out = {}
    for sd, args in symbol_instances(score):
        wv = {}
        for w, wave, pos in sd.waves:
            wv[w] = _norm_wave(score, w, expand_wave(wave, sd.params, args, n, pos))
        out[inst_name(sd, args)] = wv
    return out


def _compatible(a, b):
    return all(x == y or x == "x" or y == "x" or "." in (x, y) for x, y in zip(a, b))


def find_encoding(score: Score, waves: dict, budget: int = 400_000):
    """Search symbol codes (4 bits) such that every wire's waveform depends on at most 3 code bits (R2).

    Returns {inst_name: code} or None."""
    names = list(waves)
    wires = sorted({w for wv in waves.values() for w in wv})

    def wave(nm, w):
        wv = waves[nm].get(w)
        if wv is not None:
            return wv
        wire = score.wire(w)
        lvl = idle_level(wire) if wire is not None else 0
        return [("z" if lvl is None else str(lvl))] * len(next(iter(waves[nm].values())))

    comp = {}
    for w in wires:
        for i, a in enumerate(names):
            for b in names[i + 1:]:
                comp[(w, a, b)] = comp[(w, b, a)] = _compatible(wave(a, w), wave(b, w))
    if len(names) > 16:
        return None
    nodes = [0]
    for dropped in itertools.product(range(4), repeat=len(wires)):
        codes: dict[str, int] = {}
        used = set()

        def ok(nm, code):
            for other, oc in codes.items():
                x = oc ^ code
                for w, d in zip(wires, dropped):
                    if x == 1 << d and not comp[(w, nm, other)]:
                        return False
            return True

        def dfs(i):
            nodes[0] += 1
            if nodes[0] > budget:
                return False
            if i == len(names):
                return True
            nm = names[i]
            for code in range(16):
                if code in used:
                    continue
                if ok(nm, code):
                    codes[nm] = code
                    used.add(code)
                    if dfs(i + 1):
                        return True
                    del codes[nm]
                    used.discard(code)
            return False

        if dfs(0):
            return dict(codes)
        if nodes[0] > budget:
            return None
    return None


def changes_at_any(score, clock, wn, point):
    """Does any symbol change `wn` level at split boundary `point`?"""
    b = boundaries(clock)
    j = b.index(point)
    n = len(b) - 1
    for sd, args in symbol_instances(score):
        for w, wave, pos in sd.waves:
            if w == wn:
                v = expand_wave(wave, sd.params, args, n, pos)
                if v[j - 1] != v[j] and "." not in (v[j - 1], v[j]):
                    return True
    return False


def derive_samples(score: Score, clock: Clock, waves: dict):
    """No explicit sample clause anywhere: per wire, the middle of the latest segment that differs between
    symbols; if that needs a fourth tap, the segment's start boundary (a split point shares its tap)."""
    b = boundaries(clock)
    n = len(b) - 1
    out = {}
    wires = sorted({w for wv in waves.values() for w in wv if not (score.wire(w) and score.wire(w).mirror_of)})
    for w in wires:
        seqs = []
        for nm, wv in waves.items():
            if w in wv:
                seqs.append(wv[w])
        latest = None
        for j in range(n):
            if len({s[j] for s in seqs} - {"x"}) > 1:
                latest = j
        if latest is None:
            continue
        mid = (b[latest] + b[latest + 1]) / 2
        out[w] = (mid, b[latest])
    return out


def check_fit(score: Score) -> list[Diag]:
    d: list[Diag] = []
    E = lambda code, msg, pos=None: d.append(Diag(code, msg, pos))   # noqa: E731
    oe_wires = set()
    for gname, gwires, clock in _groups(score):
        if clock is None:
            continue
        n = nseg(clock)
        gw = {w.name for w in gwires}
        if len(clock.split) > 3:
            E("E-FIT-SEG", f"clock: {len(clock.split)} split points make {n} segments; a line has 4 "
                           f"(at most 3 split points)", clock.pos)
            continue
        try:
            waves = symbol_waves(score, clock)
        except ScoreError as e:
            d.append(Diag(e.code, e.msg, e.pos))
            continue
        # R1
        if len(waves) > R1_MAX_SYMBOLS:
            E("E-FIT-SYM", f"symbols: {len(waves)} transmitted symbols (each parameter value counts); a line has "
                           f"{R1_MAX_SYMBOLS}")
        # R2
        if waves:
            enc = find_encoding(score, waves)
            if enc is None:
                E("E-FIT-ENC", "symbols: no 4-bit symbol encoding lets every wire's waveform depend on at most 3 "
                               "bits (R2)")
        # R3 / R4: sample points are per line (union over symbols); taps are counted per role
        try:
            period = beat_cycles(clock) if clock.rate else None
        except ValueError:
            period = None
        sampled: dict[str, set] = {}
        sample_syms: dict[tuple, set] = {}          # (wire, point) -> symbols naming it
        explicit = any(sd.samples for sd in score.symbols)
        for sd, args in symbol_instances(score):
            for w, tr in sd.samples:
                wn = w or (sd.waves[0][0] if sd.waves else None)
                try:
                    fr = resolve_time(tr, sd, clock, args, period)
                except ValueError as e:
                    E("E-FIT-TAP", f"symbols '{sd.name}': {e}", tr.pos)
                    continue
                if fr is None:
                    E("E-NAMES", f"symbol '{sd.name}': wire '{tr.wire}' has no {tr.edge} edge to sample at", tr.pos)
                    continue
                sampled.setdefault(wn, set()).add(fr)
        roles = score.roles
        tx_syms = getattr(score, "_tx", {})
        rx_syms = getattr(score, "_rx", {})

        def role_splits(r):
            """Split taps r needs: it transmits a multi-segment wave on a wire it drives."""
            for sd in score.symbols:
                if sd.name not in tx_syms.get(r, set()):
                    continue
                for w, wave, pos in sd.waves:
                    wire = score.wire(w)
                    if wire is None or len(parse_wave(wave, sd.params, pos)) <= 1:
                        continue
                    if wire.dir == "shared" or r in score.wire_owners(wire):
                        return set(clock.split)
            return set()

        def changes_at(r, wn, point):
            """Does a symbol that r receives change `wn` level at boundary `point`?"""
            b = boundaries(clock)
            if point not in b[1:-1]:
                return False
            j = b.index(point)
            for sd, args in symbol_instances(score):
                if sd.name not in rx_syms.get(r, set()):
                    continue
                for w, wave, pos in sd.waves:
                    if w == wn:
                        v = expand_wave(wave, sd.params, args, n, pos)
                        if v[j - 1] != v[j] and "." not in (v[j - 1], v[j]):
                            return True
            return False

        def taps_for(r, samples):
            sp = role_splits(r)
            pts = set(samples)
            taps = set(sp)
            for wn, frs in pts_by_wire(samples).items():
                for fr in frs:
                    if fr in (0, 1):
                        continue
                    if fr in sp and not changes_at(r, wn, fr):
                        continue                  # shares the split's tap
                    taps.add(("s", fr))
            return taps

        def pts_by_wire(smp):
            return smp if isinstance(smp, dict) else {}

        derived_note = None
        if not explicit:
            derived = derive_samples(score, clock, waves)
            for wn, (mid, start) in derived.items():
                cands = [mid] + [x for x in clock.split if not changes_at_any(score, clock, wn, x)]
                for fr in cands:
                    trial = dict(sampled)
                    trial[wn] = set(sampled.get(wn, set())) | {fr}
                    if all(len(taps_for(r, trial)) <= R3_MAX_TAPS for r in roles):
                        sampled.setdefault(wn, set()).add(fr)
                        break
                else:
                    E("E-FIT-TAP", f"clock: derived sample for '{wn}' does not fit 3 taps")
        for r in roles:
            taps = taps_for(r, sampled)
            if len(taps) > R3_MAX_TAPS:
                E("E-FIT-TAP", f"clock: role {r}: {len(role_splits(r))} split point(s) it transmits and sample "
                               f"point(s) {sorted(float(x) for w in sampled.values() for x in w)} need {len(taps)} "
                               f"taps; a line has {R3_MAX_TAPS}", clock.pos)
        if len(sampled) > R4_MAX_WIRES:
            E("E-FIT-SMP", f"symbols: {len(sampled)} wires sampled per beat ({sorted(sampled)}); a line samples "
                           f"at most {R4_MAX_WIRES}")
        elif len(sampled) == 2:
            a_, b2 = sorted(sampled.values(), key=len, reverse=True)
            if len(b2) != 1:
                E("E-FIT-SMP", "symbols: the second sampled wire is sampled at exactly one point (R4)")
        # R5 wires the role ever releases
        for sd, args in symbol_instances(score):
            for w, wave, pos in sd.waves:
                wire = score.wire(w)
                if wire is not None and (wire.drive == "open-drain" or wire.dir == "shared" or "z" in wave):
                    oe_wires.add(w)
        for w in score.all_wires():
            if w.drive == "open-drain" or w.dir == "shared":
                oe_wires.add(w.name)
    if len(oe_wires) > R5_MAX_OE_WIRES:
        E("E-FIT-PIN", f"wires: {len(oe_wires)} wires ever released ({sorted(oe_wires)}); output-enable tables "
                       f"exist only on O0..O7")
    return d


# ---- binding -------------------------------------------------------------------------------------------------
def parse_bind(text: str) -> dict:
    """'scl=P3/O3 sda=P4/O4 tx=-/O1 rx=P2' -> {wire: (P index|None, O index|None)}"""
    out = {}
    for item in text.replace(",", " ").split():
        m = re.fullmatch(r"(\w+)=(?:(P\d+|-)(?:/(O\d+|-))?|(O\d+))", item)
        if not m:
            raise ScoreError(f"bad binding item {item!r} (expected wire=Pn/Om)", None, "E-BIND")
        w, p, o, o2 = m.groups()
        o = o or o2
        pi = int(p[1:]) if p and p != "-" else None
        oi = int(o[1:]) if o and o != "-" else None
        out[w] = (pi, oi)
    return out


def check_binding(score: Score, role: str, bind) -> list[Diag]:
    """E-BIND checks of a pin binding for one role (spec 5.1, R5)."""
    if isinstance(bind, str):
        bind = parse_bind(bind)
    d: list[Diag] = []
    E = lambda msg: d.append(Diag("E-BIND", msg))   # noqa: E731
    used_p, used_o = {}, {}
    for w in score.all_wires():
        drives = role in score.wire_owners(w)
        reads = w.dir == "shared" or not drives
        released = w.drive == "open-drain" or w.dir == "shared" or any(
            "z" in wave for sd in score.symbols for ww, wave, _ in sd.waves if ww == w.name)
        if w.name not in bind:
            if drives or reads:
                E(f"wire '{w.name}' is not bound")
            continue
        pi, oi = bind[w.name]
        if drives and oi is None:
            E(f"wire '{w.name}' is driven by {role} and needs an output pin Om")
        if reads and pi is None and not w.mirror_of:
            E(f"shared wire '{w.name}' is read back and needs an input pin Pk")
        if pi is not None:
            if not 0 <= pi <= 12:
                E(f"wire '{w.name}': input P{pi} does not exist (P0..P12)")
            if pi in used_p:
                E(f"input P{pi} bound to both '{used_p[pi]}' and '{w.name}'")
            used_p[pi] = w.name
        if oi is not None:
            if not 0 <= oi <= 13:
                E(f"wire '{w.name}': output O{oi} does not exist (O0..O13)")
            if oi in used_o:
                E(f"output O{oi} bound to both '{used_o[oi]}' and '{w.name}'")
            used_o[oi] = w.name
            if released and oi > 7:
                E(f"wire '{w.name}' is released by its driver and needs an output-enable table, which exists only "
                  f"on O0..O7 (got O{oi})")
        if w.dir == "shared" and pi is not None and oi is not None and pi != oi:
            E(f"shared wire '{w.name}' binds to uio[k] for both P_k and O_k (got P{pi}/O{oi})")
        if w.dir == "shared" and drives and (pi is None or oi is None):
            E(f"shared wire '{w.name}' needs both an input and an output pin on the same uio[k]")
    for w in bind:
        if not score.wire(w):
            E(f"binding names unknown wire '{w}'")
    return d
