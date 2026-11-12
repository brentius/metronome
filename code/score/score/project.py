"""Role projection (spec 10.1): each role's local behaviour derived from the one global grammar."""
from __future__ import annotations

from dataclasses import dataclass, field

from .analysis import kind_of
from .ast import *  # noqa: F403
from .model import expr_names


@dataclass
class LNode:
    kind: str                       # seq choice dup rep if switch call sym field const gap turnaround event every
    info: dict = field(default_factory=dict)
    kids: list = field(default_factory=list)

    def text(self, ind=0):
        pad = "  " * ind
        det = " ".join(f"{k}={v}" for k, v in self.info.items() if v not in (None, "", False))
        out = [f"{pad}{self.kind} {det}".rstrip()]
        for k in self.kids:
            out.append(k.text(ind + 1))
        return "\n".join(out)

    def walk(self):
        yield self
        for k in self.kids:
            yield from k.walk()


@dataclass
class Projection:
    role: str
    root: LNode
    host_tx: list                   # field names read from the host transmit stream, in order of occurrence
    host_rx: list                   # field names written to the host receive stream
    computed: list                  # fields this role computes and transmits
    checked: list                   # fields this role checks (crc, parity, expect)

    def text(self):
        return self.root.text()


class _P:
    def __init__(self, score: Score, role: str):
        self.s, self.role = score, role
        self.fowner: dict = {}
        self.tx, self.rx, self.comp, self.chk = [], [], [], []
        self.stack: list[str] = []

    def side(self, owner):
        return "own" if owner == self.role else "peer"

    def decide(self, names):
        """A choice/repeat decided on values: 'decide' if this role owns them, else 'follow'."""
        owners = {self.fowner.get(n) for n in names if n in self.fowner}
        if not owners:
            return "lookahead"
        return "decide" if owners == {self.role} else "follow"

    def proj(self, n, owner) -> LNode:
        S = self.s
        if isinstance(n, Seq):
            return LNode("seq", {}, [self.proj(i, owner) for i in n.items])
        if isinstance(n, Choice):
            return LNode("choice", {"how": "lookahead"}, [self.proj(a, owner) for a in n.alts])
        if isinstance(n, Dup):
            from .analysis import fields_in
            oa = {f.by or owner for f in fields_in(n.a)} or {owner}
            ob = {f.by or owner for f in fields_in(n.b)} or {owner}
            mine = n.a if self.role in oa else n.b
            theirs = n.b if mine is n.a else n.a
            return LNode("dup", {"transmit_side": "a" if mine is n.a else "b"},
                         [self.proj(mine, owner), self.proj(theirs, owner)])
        if isinstance(n, Rep):
            body = self.proj(n.node, owner)          # project the body first: its fields give the owners
            how = "lookahead" if n.kind in ("star", "plus", "opt") else (
                self.decide(expr_names(n.arg)) if n.arg is not None else None)
            return LNode("rep", {"kind": n.kind, "how": how}, [body])
        if isinstance(n, If):
            return LNode("if", {"how": self.decide(expr_names(n.cond))}, [self.proj(n.node, owner)])
        if isinstance(n, Within):
            k = self.proj(n.node, owner)
            k.info["within"] = f"{n.qty.value} {n.qty.unit}"
            return k
        if isinstance(n, Retry):
            return LNode("retry", {"count": n.count, "on": n.event}, [self.proj(n.node, owner)])
        if isinstance(n, AsmBlock):
            return LNode("asm", dict(n.contract))
        if isinstance(n, Every):
            return LNode("every", {"period": f"{n.qty.value} {n.qty.unit}"}, [self.proj(n.node, owner)])
        if isinstance(n, Switch):
            return LNode("switch", {"how": self.decide(expr_names(n.expr))},
                         [self.proj(a, owner) for _, a in n.arms] + ([self.proj(n.other, owner)] if n.other else []))
        if isinstance(n, Field):
            o = n.by or owner
            t = n.type
            mine = o == self.role
            if n.name:
                self.fowner[n.name] = o
            if t.kind in ("crc", "parity"):
                act = "compute_tx" if mine else "check"
                (self.comp if mine else self.chk).append(n.name or t.kind)
            elif n.value is not None:
                act = "compute_tx" if mine else ("capture+expect" if n.expect is not None else "capture")
                if mine:
                    self.comp.append(n.name)
                elif not n.hidden:
                    self.rx.append(n.name)
            else:
                act = "host_tx" if mine else ("host_rx" if not n.hidden else "capture_hidden")
                if mine:
                    self.tx.append(n.name)
                elif not n.hidden:
                    self.rx.append(n.name)
                if n.expect is not None and not mine:
                    act += "+check"
                    self.chk.append(n.name)
            return LNode("field", {"name": n.name, "type": t.kind + (str(t.width) if t.width else ""),
                                   "owner": o, "action": act, "notify": n.notify, "asm": bool(n.asm)})
        if isinstance(n, (ConstBytes, ConstBits)):
            return LNode("const", {"owner": owner, "action": "transmit" if owner == self.role else "expect"})
        if isinstance(n, Gap):
            return LNode("gap", {"qty": f"{n.qty.value} {n.qty.unit}"})
        if isinstance(n, Turnaround):
            return LNode("turnaround", {"beats": n.beats})
        if isinstance(n, Ref):
            k = kind_of(S, n.name)
            o = n.by or owner
            if k == "sym":
                return LNode("sym", {"name": n.name, "owner": o,
                                     "action": "transmit" if o == self.role else "expect"})
            if k == "event":
                return LNode("event", {"name": n.name, "action": "detect"})
            ps = S.prods_named(n.name)
            if n.name in self.stack:
                return LNode("call", {"name": n.name, "recursive": True})
            self.stack.append(n.name)
            kids = []
            for p in ps:
                sub = self.proj(p.body, o)
                sub.info["variant"] = ",".join(str(q[1]) for q in p.params) or None
                kids.append(sub)
            self.stack.pop()
            return LNode("call", {"name": n.name, "owner": o}, kids)
        return LNode("?")


def project(score: Score, role: str) -> Projection:
    if role not in score.roles:
        raise ValueError(f"unknown role {role!r}")
    p = _P(score, role)
    start = score.prods[0]
    p.stack.append(start.name)
    root = LNode("call", {"name": start.name, "owner": score.roles[0]}, [p.proj(start.body, score.roles[0])])
    return Projection(role, root, p.tx, p.rx, p.comp, p.chk)
