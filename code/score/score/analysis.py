"""Grammar analysis: reference resolution, one-symbol-lookahead FIRST sets (spec 7.6), bit lengths (7.8)."""
from __future__ import annotations

from .ast import *  # noqa: F403
from .model import DATA_SYMBOL, EVENT_NAMES

END = ("end",)
EPS = ("eps",)
DATA_TOKEN = ("sym", DATA_SYMBOL, None)


def kind_of(score: Score, name: str):
    if score.prods_named(name):
        return "prod"
    if score.symbol(name):
        return "sym"
    if score.event(name) or name in EVENT_NAMES:
        return "event"
    return None


def tok_overlap(a, b) -> bool:
    if a[0] != b[0] or a[1] != b[1]:
        return False
    if a[0] == "sym":
        return a[2] is None or b[2] is None or a[2] == b[2]
    return True


def sets_overlap(x, y):
    return [(a, b) for a in x for b in y if tok_overlap(a, b) or (a == b)]


def tok_str(t) -> str:
    if t == END:
        return "<end>"
    if t[0] == "sym":
        return t[1] + ("" if t[2] is None else f"({','.join(map(str, t[2]))})")
    return t[1]


class Analyzer:
    """Computes FIRST(node . cont) and records E-AMBIG diagnostics along the way."""

    def __init__(self, score: Score):
        self.score = score
        self.diags: list[Diag] = []
        self._seen = set()
        self._stack: list[str] = []

    def _diag(self, pos, msg):
        key = (pos, msg)
        if key not in self._seen:
            self._seen.add(key)
            self.diags.append(Diag("E-AMBIG", msg, pos))

    def run(self):
        start = self.score.prods[0]
        self.F(start.body, frozenset([END]), start.name)
        return self.diags

    def _pick(self, name, args):
        ps = self.score.prods_named(name)
        return ps

    def F(self, n, cont, ctx):
        S = self.score
        if isinstance(n, Seq):
            c = cont
            for it in reversed(n.items):
                c = self.F(it, c, ctx)
            return c
        if isinstance(n, Choice):
            res = [self.F(a, cont, ctx) for a in n.alts]
            for i in range(len(res)):
                for j in range(i + 1, len(res)):
                    ov = sets_overlap(res[i], res[j])
                    if ov:
                        a, b = ov[0]
                        self._diag(n.pos, f"grammar: choice in '{ctx}' needs 2 symbols of lookahead: alternatives "
                                          f"{i + 1} and {j + 1} both begin with '{tok_str(a)}'"
                                          f" ({self._path(n.alts[i], a)} vs {self._path(n.alts[j], b)})")
            out = frozenset().union(*res)
            return out
        if isinstance(n, Dup):
            self.F(n.b, cont, ctx)
            return self.F(n.a, cont, ctx)
        if isinstance(n, Rep):
            if n.kind in ("star", "plus"):
                pure = self.F(n.node, frozenset([EPS]), ctx)
                if EPS in pure:
                    self._diag(n.pos, f"grammar: repeated item in '{ctx}' can match nothing, so the loop never "
                                      f"decides")
                body_first = frozenset(t for t in pure if t != EPS)
                loop = self.F(n.node, body_first | cont, ctx)
                ov = sets_overlap(body_first, cont)
                if ov:
                    self._diag(n.pos, f"grammar: repeat in '{ctx}' needs 2 symbols of lookahead: '{tok_str(ov[0][0])}'"
                                      f" both continues the loop and follows it")
                return loop if n.kind == "plus" else (body_first | cont)
            if n.kind == "opt":
                pure = self.F(n.node, frozenset([EPS]), ctx)
                body_first = frozenset(t for t in pure if t != EPS)
                ov = sets_overlap(body_first, cont)
                if ov:
                    self._diag(n.pos, f"grammar: optional item in '{ctx}' needs 2 symbols of lookahead: "
                                      f"'{tok_str(ov[0][0])}' both starts it and follows it")
                self.F(n.node, cont, ctx)
                return body_first | cont
            if n.kind == "times":
                f = self.F(n.node, cont, ctx)
                lit = isinstance(n.arg, Num) and n.arg.value > 0
                return f if lit else (f | cont)
            if n.kind == "until":
                return self.F(n.node, cont, ctx)
            return self.F(n.node, cont, ctx) | cont     # while
        if isinstance(n, If):
            return self.F(n.node, cont, ctx) | cont
        if isinstance(n, (Within, Retry)):
            return self.F(n.node, cont, ctx)
        if isinstance(n, AsmBlock):
            return cont
        if isinstance(n, Every):
            self.F(n.node, cont, ctx)
            return cont
        if isinstance(n, Switch):
            out = frozenset()
            for _, a in n.arms:
                out |= self.F(a, cont, ctx)
            out |= self.F(n.other, cont, ctx) if n.other is not None else cont
            return out
        if isinstance(n, Field):
            t = n.type
            if t.kind == "bytes":
                return frozenset([DATA_TOKEN]) | cont
            return frozenset([DATA_TOKEN])
        if isinstance(n, (ConstBytes, ConstBits)):
            return frozenset([DATA_TOKEN])
        if isinstance(n, (Gap, Turnaround)):
            return cont
        if isinstance(n, Ref):
            k = kind_of(S, n.name)
            if k == "sym":
                args = tuple(a.value for a in n.args) if n.args and all(isinstance(a, Num) for a in n.args) else None
                return frozenset([("sym", n.name, args)])
            if k == "event":
                return frozenset([("ev", n.name)])
            if k == "prod":
                if n.name in self._stack:
                    self._diag(n.pos, f"grammar: production '{n.name}' is recursive (not allowed, 7.1)")
                    return cont
                self._stack.append(n.name)
                out = frozenset()
                for p in S.prods_named(n.name):
                    out |= self.F(p.body, cont, p.name)
                self._stack.pop()
                return out
            return cont
        return cont

    def _path(self, node, tok):
        return f"'{tok_str(tok)} ...'"


def first_tokens(score: Score, node, cont=frozenset([END]), ctx="?"):
    """FIRST(node . cont) without recording diagnostics (used by the codec)."""
    a = Analyzer(score)
    return a.F(node, cont, ctx)


# ---- bit lengths for ||  -----------------------------------------------------------------------------------
def _add(a, b):
    if a is None or b is None:
        return None
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + v
    return r


def bitlen(score: Score, n):
    """Symbolic bit length {'': const, fieldname: coeff} or None if not known before the construct starts."""
    if isinstance(n, Field):
        t = n.type
        if t.kind in ("bit", "parity"):
            return {"": 1}
        if t.kind in ("u", "s"):
            return {"": t.width}
        if t.kind == "crc":
            c = score.crcs.get(t.crc)
            from .crc import STD
            c = c or STD.get(t.crc)
            return {"": c.width} if c else None
        if t.kind == "bytes" and t.length is not None:
            if isinstance(t.length, Num):
                return {"": 8 * t.length.value}
            if isinstance(t.length, Name):
                return {t.length.name: 8}
        return None
    if isinstance(n, ConstBytes):
        return {"": 8 * len(n.data)}
    if isinstance(n, ConstBits):
        return {"": len(n.bits)}
    if isinstance(n, (Gap, Turnaround)):
        return {}
    if isinstance(n, Seq):
        r = {}
        for it in n.items:
            r = _add(r, bitlen(score, it))
        return r
    if isinstance(n, Rep) and n.kind == "times" and isinstance(n.arg, Num):
        b = bitlen(score, n.node)
        return None if b is None else {k: v * n.arg.value for k, v in b.items()}
    if isinstance(n, Ref) and kind_of(score, n.name) == "prod":
        ps = score.prods_named(n.name)
        if len(ps) == 1:
            return bitlen(score, ps[0].body)
    return None


def lin_str(l) -> str:
    parts = []
    if l.get("", 0) or not l:
        parts.append(str(l.get("", 0)))
    parts += [f"{v}*{k}" for k, v in l.items() if k]
    return " + ".join(parts) + " bits"


def fields_in(n, out=None):
    out = [] if out is None else out
    if isinstance(n, Field):
        out.append(n)
    elif isinstance(n, Seq):
        for i in n.items:
            fields_in(i, out)
    elif isinstance(n, (Rep, If, Within, Every, Retry)):
        fields_in(n.node, out)
    elif isinstance(n, Dup):
        fields_in(n.a, out)
        fields_in(n.b, out)
    elif isinstance(n, Choice):
        for a in n.alts:
            fields_in(a, out)
    return out
