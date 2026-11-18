"""Recursive-descent parser for the score language (SPEC_V2_SCORE.md sections 3-11, appendix A)."""
from __future__ import annotations

import re
from fractions import Fraction

from .ast import *  # noqa: F403
from .lexer import Line, Tok, tokenize

UNITS = {"Hz", "kHz", "MHz", "ns", "us", "ms", "s", "cycles", "beats", "chars"}
SECTIONS = {"arbitrate", "wire", "mirror", "clock", "symbols", "recognise", "bits", "crc", "grammar", "abort", "param",
            "group", "constrain", "enum", "state"}
BINPREC = [("||",), ("&&",), ("|",), ("^",), ("&",), ("==", "!="), ("<", ">", "<=", ">="), ("<<", ">>"),
           ("+", "-"), ("*", "/", "%")]


class TS:
    """Token stream over a list of tokens."""

    def __init__(self, toks, end_pos=None):
        self.toks, self.i = toks, 0
        last = toks[-1] if toks else None
        self.end_pos = (last.line, last.col + len(last.text)) if last is not None else end_pos

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is None:
            raise ScoreError("unexpected end of input", self.end_pos)
        self.i += 1
        return t

    def at(self, text, k=0):
        t = self.peek(k)
        return t is not None and t.text == text and t.kind in ("id", "op")

    def accept(self, text):
        if self.at(text):
            self.i += 1
            return True
        return False

    def expect(self, text, what=None):
        t = self.peek()
        if t is None or t.text != text or t.kind not in ("id", "op"):
            self.fail(f"expected {what or repr(text)}")
        self.i += 1
        return t

    def fail(self, msg):
        t = self.peek()
        got = f", got {t.text!r}" if t else ", got end of input"
        raise ScoreError(msg + got, t.pos if t else self.end_pos)

    def ident(self, what="identifier"):
        t = self.peek()
        if t is None or t.kind != "id":
            self.fail(f"expected {what}")
        self.i += 1
        return t

    def done(self):
        return self.i >= len(self.toks)

    def expect_done(self):
        if not self.done():
            self.fail("unexpected token")


def _int(t: Tok) -> int:
    if t.kind == "hex":
        return int(t.text.replace("_", ""), 16)
    if t.kind == "bin":
        return int(t.text.replace("_", ""), 2)
    if t.kind == "int":
        return int(t.text)
    raise ScoreError(f"expected integer, got {t.text!r}", t.pos)


def expect_int(ts: TS) -> int:
    t = ts.peek()
    if t is None or t.kind not in ("int", "hex", "bin"):
        ts.fail("expected integer")
    ts.i += 1
    return _int(t)


def parse_qty(ts: TS) -> Qty:
    t = ts.peek()
    if t is None or t.kind not in ("int", "dec", "hex", "bin"):
        ts.fail("expected quantity")
    ts.i += 1
    v = Fraction(t.text) if t.kind in ("int", "dec") else Fraction(_int(t))
    u = None
    n = ts.peek()
    if n is not None and n.kind == "id" and n.text in UNITS:
        ts.i += 1
        u = n.text
    elif n is not None and n.kind == "pct":
        pass
    return Qty(v, u, t.pos)


def parse_pct(ts: TS) -> Fraction:
    t = ts.peek()
    if t is None or t.kind != "pct":
        ts.fail("expected percentage such as 50%")
    ts.i += 1
    return Fraction(t.text[:-1]) / 100


# ---- expressions ---------------------------------------------------------------------------------------------
def parse_vexpr(ts: TS, depth: int = 0):
    """Value expression. Bare | and || are grammar operators, so they are bitwise/logical only inside parentheses."""
    c = _parse_bin(ts, 0, depth)
    if ts.at("?"):
        q = ts.next()
        a = parse_vexpr(ts, depth)
        ts.expect(":")
        b = parse_vexpr(ts, depth)
        return Cond(c, a, b, q.pos)
    return c


def _parse_bin(ts, level, depth):
    if level == len(BINPREC):
        return _parse_unary(ts, depth)
    ops = BINPREC[level]
    a = _parse_bin(ts, level + 1, depth)
    while True:
        t = ts.peek()
        if t is None or t.kind != "op" or t.text not in ops:
            return a
        if t.text in ("|", "||") and depth == 0:
            return a
        if t.text in ("*", "+", "-") and not _starts_primary(ts.peek(1)):
            return a
        ts.i += 1
        b = _parse_bin(ts, level + 1, depth)
        a = Bin(t.text, a, b, t.pos)


def _starts_primary(t):
    return t is not None and (t.kind in ("int", "hex", "bin", "id") or (t.kind == "op" and t.text in "(!~-"))


def _parse_unary(ts, depth):
    t = ts.peek()
    if t is not None and t.kind == "op" and t.text in ("!", "~", "-"):
        ts.i += 1
        return Un(t.text, _parse_unary(ts, depth), t.pos)
    return _parse_primary(ts, depth)


def _parse_primary(ts, depth):
    t = ts.peek()
    if t is None:
        ts.fail("expected expression")
    if t.kind in ("int", "hex", "bin"):
        ts.i += 1
        return Num(_int(t), t.pos)
    if t.kind == "id":
        ts.i += 1
        return Name(t.text, t.pos)
    if t.kind == "op" and t.text == "(":
        ts.i += 1
        e = parse_vexpr(ts, depth + 1)
        ts.expect(")")
        return e
    ts.fail("expected expression")


def _asm_contract(raw: str) -> dict:
    out = {}
    for ln in raw.splitlines():
        m = re.match(r"\s*(beats|reads|writes)\s+(.+?)\s*(?:[;#].*)?$", ln)
        if m:
            out[m.group(1)] = m.group(2)
    return out


# ---- grammar -------------------------------------------------------------------------------------------------
def _seq_end(ts: TS) -> bool:
    t = ts.peek()
    if t is None:
        return True
    if t.kind == "op" and t.text in ("|", "||", ")", "}"):
        return True
    if t.kind in ("int", "hex", "bin"):
        return True
    if t.kind == "id" and t.text == "else" and ts.at(":", 1):
        return True
    if t.kind == "id" and t.text in getattr(ts, "labels", ()) and ts.at(":", 1):     # an enum switch label (18.3)
        return True
    return False


def parse_gexpr(ts: TS):
    first = pos = ts.peek().pos if ts.peek() else None
    alts = [_parse_par(ts)]
    while ts.at("|"):
        ts.next()
        alts.append(_parse_par(ts))
    return alts[0] if len(alts) == 1 else Choice(alts, pos)


def _parse_par(ts):
    a = _parse_seq(ts)
    while ts.at("||"):
        t = ts.next()
        a = Dup(a, _parse_seq(ts), t.pos)
    return a


def _parse_seq(ts):
    items, pos = [], (ts.peek().pos if ts.peek() else None)
    while not _seq_end(ts):
        items.append(_parse_item(ts))
    if not items:
        ts.fail("expected a grammar item")
    return items[0] if len(items) == 1 else Seq(items, pos)


def _parse_item(ts):
    node = _parse_atom(ts)
    while True:
        t = ts.peek()
        if t is None:
            break
        if t.kind == "op" and t.text == "*":
            ts.i += 1
            node = Rep(node, "star", None, t.pos)
        elif t.kind == "op" and t.text == "+":
            ts.i += 1
            node = Rep(node, "plus", None, t.pos)
        elif t.kind == "op" and t.text == "?":
            ts.i += 1
            node = Rep(node, "opt", None, t.pos)
        elif t.kind == "id" and t.text == "x" and _starts_primary(ts.peek(1)) and not ts.at(":", 1) \
                and not ts.at(":", 2):
            ts.i += 1
            node = Rep(node, "times", _parse_primary(ts, 0), t.pos)
        elif t.kind == "id" and t.text == "if":
            ts.i += 1
            node = If(node, parse_vexpr(ts), t.pos)
        elif t.kind == "id" and t.text == "within":
            ts.i += 1
            node = Within(node, parse_qty(ts), t.pos)
        elif t.kind == "id" and t.text in ("until", "while"):
            ts.i += 1
            node = Rep(node, t.text, parse_vexpr(ts), t.pos)
        else:
            break
    return node


def _parse_type(ts: TS) -> Type:
    t = ts.ident("type")
    m = re.fullmatch(r"([us])(\d+)", t.text)
    if t.text == "bit":
        ty = Type("bit", 1)
    elif m:
        w = int(m.group(2))
        if not 1 <= w <= 32:
            raise ScoreError(f"integer width {w} out of range 1..32", t.pos)
        ty = Type(m.group(1), w)
    elif t.text == "bytes":
        ty = Type("bytes")
        if ts.accept("["):
            ty.length = parse_vexpr(ts, 1)
            ts.expect("]")
        elif ts.accept("until"):
            ty.until = ts.ident("symbol or event name").text
        else:
            ts.fail("expected '[N]' or 'until X' after bytes")
        return ty
    elif t.text == "crc":
        ty = Type("crc", crc=ts.ident("crc name").text)
        ts.expect("over")
        ty.first = ts.ident("field").text
        ty.last = ty.first
        if ts.accept(".."):
            if ts.accept("*"):
                ty.last = None          # open range F1..* : through the field just before the crc (18.2)
            else:
                ty.last = ts.ident("field").text
        if ts.peek() and ts.peek().text in ("msb", "lsb") and ts.at("first", 1):   # byte order of the crc (18.2)
            ty.order = ts.next().text
            ts.next()
        return ty
    elif t.text == "parity":
        k = ts.ident("even or odd")
        if k.text not in ("even", "odd"):
            raise ScoreError("expected 'even' or 'odd'", k.pos)
        ty = Type("parity", 1, parity=k.text)
        ts.expect("over")
        ty.first = ts.ident("field").text
        ty.last = ty.first
        if ts.accept(".."):
            ty.last = ts.ident("field").text
        return ty
    else:
        # an enum type (18.3); its width is filled in once the whole file is parsed (Parser._resolve)
        ty = Type("u", 0, enum=t.text)
        ty._pos = t.pos
    if ts.peek() and ts.peek().text in ("msb", "lsb") and ts.at("first", 1):
        ty.order = ts.next().text
        ts.next()
    return ty


def _parse_modifiers(ts, f: Field):
    while True:
        t = ts.peek()
        if t is None:
            return
        if t.kind == "id" and t.text == "by" and ts.peek(1) and ts.peek(1).kind == "id":
            ts.i += 1
            f.by = ts.ident("role").text
        elif t.kind == "op" and t.text == "=":
            ts.i += 1
            f.value = parse_vexpr(ts)
        elif t.kind == "id" and t.text == "expect":
            ts.i += 1
            f.expect = parse_vexpr(ts)
        elif t.kind == "id" and t.text == "hidden":
            ts.i += 1
            f.hidden = True
        elif t.kind == "id" and t.text == "notify":
            ts.i += 1
            f.notify = True
        elif t.kind == "id" and t.text == "asm" and ts.peek(1) and ts.peek(1).kind == "asm":
            ts.i += 1
            f.asm = ts.next().text
        elif t.kind == "id" and t.text == "model" and ts.peek(1) and ts.peek(1).kind == "asm":
            ts.i += 1
            f.model = ts.next().text
        else:
            return


def _parse_atom(ts):
    t = ts.peek()
    if t is None:
        ts.fail("expected a grammar item")
    pos = t.pos
    if t.kind == "op" and t.text == "{":
        ts.i += 1
        e = parse_gexpr(ts)
        ts.expect("}")
        return e
    if t.kind == "op" and t.text == "(":
        ts.i += 1
        e = parse_gexpr(ts)
        ts.expect(")")
        return e
    if t.kind != "id":
        ts.fail("expected a grammar item")
    if t.text == "switch":
        ts.i += 1
        e = parse_vexpr(ts)
        ts.expect("{")
        arms, other = [], None
        while not ts.at("}"):
            if ts.at("else"):
                ts.next()
                ts.expect(":")
                other = parse_gexpr(ts)
            else:
                a = ts.peek()
                if a is not None and a.kind == "id":        # an enum member, resolved in Parser._resolve
                    ts.i += 1
                    v = Name(a.text, a.pos)
                else:
                    v = expect_int(ts)
                ts.expect(":")
                arms.append((v, parse_gexpr(ts)))
        ts.expect("}")
        return Switch(e, arms, other, pos)
    if t.text == "retry":
        ts.i += 1
        n = expect_int(ts)
        ts.expect("{")
        body = parse_gexpr(ts)
        ts.expect("}")
        ts.expect("on")
        return Retry(n, body, ts.ident("event").text, pos)
    if t.text == "asm" and ts.peek(1) is not None and ts.peek(1).kind == "asm":
        ts.i += 1
        raw = ts.next().text
        return AsmBlock(raw, _asm_contract(raw), pos)
    if t.text == "every":
        ts.i += 1
        q = parse_qty(ts)
        ts.expect(":")
        return Every(q, _parse_item(ts), pos)
    if t.text == "const":
        ts.i += 1
        if ts.at("bits"):
            ts.next()
            s = ts.peek()
            if s is None or s.kind != "str" or not re.fullmatch(r'"[01]+"', s.text):
                ts.fail("expected a bit string such as \"0110\"")
            ts.i += 1
            return ConstBits(s.text[1:-1], pos)
        data = bytearray()
        while True:
            h = ts.peek()
            if h is None or h.kind not in ("int", "word", "id", "hex") or ts.at(":", 1) or ts.at("(", 1):
                break
            txt = h.text[2:] if h.kind == "hex" else h.text
            if not re.fullmatch(r"[0-9A-Fa-f]{2}", txt):
                break
            data.append(int(txt, 16))
            ts.i += 1
        if not data:
            ts.fail("expected hex bytes after const")
        return ConstBytes(bytes(data), pos)
    if t.text == "gap":
        ts.i += 1
        return Gap(parse_qty(ts), pos)
    if t.text == "turnaround":
        ts.i += 1
        n = expect_int(ts)
        if not ts.accept("beats"):
            ts.accept("beat")
        return Turnaround(n, pos)
    if ts.at("<-", 1):                                     # state update (18.3)
        ts.i += 2
        return Assign(t.text, parse_vexpr(ts), pos)
    if t.text in ("crc", "parity") and ts.peek(1) is not None and ts.peek(1).kind == "id" and not ts.at(":", 1):
        f = Field(None, _parse_type(ts), pos=pos)
        _parse_modifiers(ts, f)
        return f
    if ts.at(":", 1):
        ts.i += 2
        f = Field(t.text, _parse_type(ts), pos=pos)
        _parse_modifiers(ts, f)
        return f
    ts.i += 1
    args = []
    nt = ts.peek()
    if nt is not None and nt.kind == "op" and nt.text == "(" and nt.line == t.line and nt.col == t.col + len(t.text):
        ts.i += 1
        if not ts.at(")"):
            args.append(parse_vexpr(ts, 1))
            while ts.accept(","):
                args.append(parse_vexpr(ts, 1))
        ts.expect(")")
    r = Ref(t.text, args, None, pos)
    if ts.at("by") and ts.peek(1) is not None and ts.peek(1).kind == "id":
        ts.i += 1
        r.by = ts.ident("role").text
    return r


# ---- file ----------------------------------------------------------------------------------------------------
def _chunks(lines: list[Line], base: int | None = None):
    """Split lines into [(head_line, [body lines])] by indentation."""
    out = []
    for ln in lines:
        if base is None:
            base = ln.indent
        if ln.indent <= base:
            out.append((ln, []))
        else:
            if not out:
                raise ScoreError("unexpected indentation", (ln.no, ln.indent + 1))
            out[-1][1].append(ln)
    return out


class Parser:
    def __init__(self, src: str):
        self.src = src
        self.lines = tokenize(src)

    def parse(self) -> Score:
        chunks = _chunks(self.lines, 0)
        if not chunks:
            raise ScoreError("empty score", (1, 1))
        name = version = None
        roles = None
        uses: list[str] = []
        sc = dict(wires=[], clock=None, groups=[], symbols=[], recognise=[], bits=None, crcs={}, prods=[],
                  aborts=[], params=[], arbitrates=[], constraints=[], enums={}, states=[], imports={}, over=None)
        # enum members first: they label switch arms, and the grammar may come before the enum section
        self.labels = set()
        for head, body in chunks:
            if head.toks and head.toks[0].text == "enum":
                for ln in body:
                    if ln.toks and ln.toks[0].kind == "id":
                        self.labels.add(ln.toks[0].text)
        for head, body in chunks:
            ts = TS(head.toks, (head.no, 1))
            kw = ts.next()
            if head.indent != 0:
                raise ScoreError("top-level declaration must start in column 1", kw.pos)
            k = kw.text
            if k == "protocol":
                name = ts.ident("protocol name").text
                if ts.accept("version"):
                    version = expect_int(ts)
                if ts.accept("over"):                       # layering (18.2): protocol P over ALIAS.PROD
                    alias = ts.ident("library alias").text
                    ts.expect(".")
                    sc["over"] = (alias, ts.ident("production of the lower protocol").text)
                ts.expect_done()
            elif k == "constrain":
                ts.expect_done()
                sc["constraints"] += [self.constraint(l) for l in body]
            elif k == "enum":
                e = self.enum(ts, kw, body)
                if e.name in sc["enums"]:
                    raise ScoreError(f"enum '{e.name}' declared twice", kw.pos, "E-NAMES")
                sc["enums"][e.name] = e
            elif k == "state":
                ts.expect_done()
                sc["states"] += [self.state(l) for l in body]
            elif k == "roles":
                r1 = ts.ident("role").text
                ts.expect(",")
                r2 = ts.ident("role").text
                ts.expect_done()
                if r1 == r2:
                    raise ScoreError("the two roles must differ", kw.pos)
                roles = (r1, r2)
            elif k == "use":
                lib = ts.ident("library name").text
                if ts.accept("as"):                         # a protocol library (18.2): use uart_8n1 as uart
                    alias = ts.ident("alias").text
                    if alias in sc["imports"]:
                        raise ScoreError(f"alias '{alias}' used twice", kw.pos, "E-NAMES")
                    sc["imports"][alias] = lib
                else:
                    uses.append(lib)
                ts.expect_done()
            elif k == "wire":
                sc["wires"].append(self.wire(ts, kw))
            elif k == "mirror":
                sc["wires"].append(self.mirror(ts, kw))
            elif k == "clock":
                if sc["clock"] is not None:
                    raise ScoreError("only one top-level clock allowed (use groups for several)", kw.pos, "E-NAMES")
                sc["clock"] = self.clock(ts, head, body)
            elif k == "symbols":
                ts.expect_done()
                sc["symbols"] += [self.symbol(l) for l in body]
            elif k == "recognise":
                ts.expect_done()
                sc["recognise"] += [self.recog(l) for l in body]
            elif k == "bits":
                sc["bits"] = self.bits(ts, kw)
            elif k == "crc":
                c = self.crc(ts, kw)
                sc["crcs"][c.name] = c
            elif k == "grammar":
                ts.expect_done()
                sc["prods"] += self.grammar(body)
            elif k == "abort":
                ts.expect_done()
                sc["aborts"] += [self.abort(l) for l in body]
            elif k == "param":
                ts.expect_done()
                sc["params"] += [self.param(l) for l in body]
            elif k == "group":
                sc["groups"].append(self.group(ts, kw, body))
            elif k == "arbitrate":
                sc["arbitrates"].append(ts.ident("wire").text)
                ts.expect_done()
            else:
                raise ScoreError(f"unknown section {k!r}", kw.pos)
        if name is None:
            raise ScoreError("missing 'protocol NAME' header", (1, 1))
        if roles is None:
            raise ScoreError("missing 'roles A, B' header", (1, 1))
        if not sc["prods"]:
            raise ScoreError("no grammar section", (1, 1))
        s = Score(name=name, version=version, roles=roles, uses=uses, wires=sc["wires"], clock=sc["clock"],
                  groups=sc["groups"], symbols=sc["symbols"], recognise=sc["recognise"],
                  bits=sc["bits"] or Bits(), crcs=sc["crcs"], prods=sc["prods"], aborts=sc["aborts"],
                  params=sc["params"], source=self.src, arbitrates=sc["arbitrates"],
                  constraints=sc["constraints"], enums=sc["enums"], states=sc["states"], imports=sc["imports"],
                  over=sc["over"])
        self._resolve(s)
        return s

    # -- resolution after the whole file is read (enums may be declared after the grammar) --
    def _resolve(self, s: Score):
        consts = {}
        for e in s.enums.values():
            for m, v in e.members.items():
                if m in consts:
                    raise ScoreError(f"enum member '{m}' declared twice", e.pos, "E-NAMES")
                consts[m] = v
        seen = set()

        def walk(n):
            if id(n) in seen or n is None:
                return
            seen.add(id(n))
            if isinstance(n, Field) and n.type.enum:
                e = s.enums.get(n.type.enum)
                if e is None:
                    raise ScoreError(f"unknown type {n.type.enum!r} (not a built-in type or an enum)",
                                     getattr(n.type, "_pos", n.pos), "E-NAMES")
                n.type.width = e.width
            elif isinstance(n, Switch):
                arms = []
                for v, a in n.arms:
                    if isinstance(v, Name):
                        if v.name not in consts:
                            raise ScoreError(f"switch arm '{v.name}' is not an enum member", v.pos, "E-NAMES")
                        v = consts[v.name]
                    arms.append((v, a))
                    walk(a)
                n.arms = arms
                walk(n.other)
            elif isinstance(n, Seq):
                for i in n.items:
                    walk(i)
            elif isinstance(n, Choice):
                for a in n.alts:
                    walk(a)
            elif isinstance(n, Dup):
                walk(n.a)
                walk(n.b)
            elif isinstance(n, (Rep, If, Within, Every, Retry)):
                walk(n.node)
        for p in s.prods:
            walk(p.body)

    def constraint(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        name = ts.ident("constraint name")
        a = self._tevent(ts)
        ts.expect("->")
        b = self._tevent(ts)
        op = ts.next()
        if op.text not in (">=", "<="):
            raise ScoreError("expected '>=' or '<=' and a duration", op.pos)
        q = parse_qty(ts)
        if q.unit not in ("ns", "us", "ms", "s", "cycles", "beats"):
            raise ScoreError("a constraint bound needs a time unit (ns, us, ms, s, cycles or beats)", q.pos)
        ts.expect_done()
        return Constraint(name.text, a, b, op.text, q, name.pos)

    def _tevent(self, ts) -> TEvent:
        t = ts.ident("wire or recognised event")
        if ts.peek() is not None and ts.peek().text in ("rise", "fall", "change"):
            ev = TEvent("edge", wire=t.text, edge=ts.next().text, pos=t.pos)
            if ts.accept("when"):
                ev.when_wire = ts.ident("wire").text
                lv = ts.ident("high or low")
                if lv.text not in ("high", "low"):
                    raise ScoreError("expected high or low", lv.pos)
                ev.when_level = lv.text
            return ev
        return TEvent("event", event=t.text, pos=t.pos)

    def enum(self, ts, kw, body):
        name = ts.ident("enum name").text
        ts.expect(":")
        ty = ts.ident("uN")
        m = re.fullmatch(r"u(\d+)", ty.text)
        if not m or not 1 <= int(m.group(1)) <= 32:
            raise ScoreError("an enum's type must be uN, N = 1..32", ty.pos)
        w = int(m.group(1))
        ts.expect_done()
        members = {}
        for ln in body:
            t = TS(ln.toks, (ln.no, 1))
            mn = t.ident("member name")
            t.expect("=")
            v = expect_int(t)
            t.expect_done()
            if mn.text in members:
                raise ScoreError(f"enum {name}: member '{mn.text}' given twice", mn.pos, "E-NAMES")
            if not 0 <= v < (1 << w):
                raise ScoreError(f"enum {name}: {mn.text} = {v} does not fit u{w}", mn.pos)
            members[mn.text] = v
        if not members:
            raise ScoreError(f"enum {name} has no members", kw.pos)
        return EnumDecl(name, w, members, kw.pos)

    def state(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        name = ts.ident("state name")
        ts.expect(":")
        ty = ts.ident("uN")
        m = re.fullmatch(r"u(\d+)", ty.text)
        if not m or not 1 <= int(m.group(1)) <= 32:
            raise ScoreError("a state value's type must be uN, N = 1..32", ty.pos)
        init = 0
        if ts.accept("="):
            init = expect_int(ts)
        ts.expect_done()
        return StateDecl(name.text, int(m.group(1)), init, name.pos)

    # -- sections --
    def wire(self, ts, kw):
        name = ts.ident("wire name").text
        d = ts.ident("direction")
        if d.text not in ("out", "in", "shared"):
            raise ScoreError("direction must be out, in or shared", d.pos)
        drive = idle = by = None
        while not ts.done():
            t = ts.next()
            if t.text in ("push-pull", "open-drain"):
                drive = t.text
            elif t.text == "idle":
                v = ts.ident("idle level")
                if v.text not in ("low", "high", "released"):
                    raise ScoreError("idle must be low, high or released", v.pos)
                idle = v.text
            elif t.text == "by":
                by = ts.ident("role").text
            else:
                raise ScoreError(f"unexpected {t.text!r} in wire declaration", t.pos)
        if drive is None:
            drive = "open-drain" if d.text == "shared" else "push-pull"
        return Wire(name, d.text, drive, idle, by, kw.pos)

    def mirror(self, ts, kw):
        name = ts.ident("wire name").text
        ts.expect("=")
        ts.expect("!")
        other = ts.ident("wire name").text
        ts.expect_done()
        return Wire(name, "out", "push-pull", None, None, kw.pos, mirror_of=other)

    def clock(self, ts, head, body):
        c = Clock(None, pos=head.toks[0].pos)
        if ts.accept("free"):
            c.rate = None
        else:
            q = parse_qty(ts)
            if q.unit not in ("Hz", "kHz", "MHz"):
                raise ScoreError("clock rate needs a frequency unit (Hz, kHz, MHz) or 'free'", q.pos)
            c.rate = q.value * {"Hz": 1, "kHz": 1000, "MHz": 10 ** 6}[q.unit]
        ts.expect_done()
        for ln in body:
            t = TS(ln.toks, (ln.no, 1))
            first = t.next()
            if first.text == "split":
                c.split = []
                while not t.done():
                    c.split.append(parse_pct(t))
                if not c.split:
                    raise ScoreError("split needs at least one fraction", first.pos)
                if sorted(set(c.split)) != c.split or not all(0 < s < 1 for s in c.split):
                    raise ScoreError("split fractions must be increasing and inside (0%, 100%)", first.pos)
            elif first.text == "tolerance":
                c.tolerance = parse_pct(t)
                t.expect_done()
            elif first.kind == "id" and t.at(":"):
                t.next()
                c.roles[first.text] = self.mode(t, first)
            else:
                raise ScoreError(f"unexpected {first.text!r} in clock block", first.pos)
        return c

    def mode(self, ts, role_tok):
        m = ts.ident("clock mode")
        rc = RoleClock(role_tok.text, m.text, pos=m.pos)
        if m.text == "generated":
            if ts.accept(","):
                ts.expect("stretch")
                ts.expect("on")
                rc.stretch = ts.ident("wire").text
        elif m.text == "started":
            ts.expect("by")
            rc.wire = ts.ident("wire").text
            rc.edge = self._edge(ts)
        elif m.text == "recovered":
            ts.expect("from")
            rc.wire = ts.ident("wire").text
            ts.expect("edges")
            ts.expect(",")
            ts.expect("window")
            a = parse_pct(ts)
            ts.expect("..")
            b = parse_pct(ts)
            if a == b:
                raise ScoreError("window must not be empty (A = B); A > B wraps through the beat boundary", m.pos)
            rc.win = (a, b)
        elif m.text == "follow":
            rc.wire = ts.ident("wire").text
            rc.edge = self._edge(ts)
            if ts.accept(","):
                ts.expect("capture")
                ts.expect("on")
                rc.cap_wire = ts.ident("wire").text
                rc.cap_edge = self._edge(ts)
        else:
            raise ScoreError(f"unknown clock mode {m.text!r}", m.pos)
        ts.expect_done()
        return rc

    def _edge(self, ts):
        e = ts.ident("rise or fall")
        if e.text not in ("rise", "fall"):
            raise ScoreError("expected 'rise' or 'fall'", e.pos)
        return e.text

    def _time(self, ts) -> TimeRef:
        t = ts.peek()
        if t is not None and t.kind == "pct":
            return TimeRef("frac", frac=parse_pct(ts), pos=t.pos)
        if t is not None and t.kind == "id" and ts.peek(1) is not None and ts.peek(1).text in ("rise", "fall"):
            ts.i += 2
            return TimeRef("edge", wire=t.text, edge=ts.toks[ts.i - 1].text, pos=t.pos)
        if t is not None and t.kind in ("int", "dec"):
            q = parse_qty(ts)
            if q.unit is None:
                raise ScoreError("time needs a unit (ns, us, ms, s, cycles)", q.pos)
            return TimeRef("dur", qty=q, pos=t.pos)
        ts.fail("expected a time: 50%, WIRE rise|fall, or a duration")

    def symbol(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        name = ts.ident("symbol name")
        params = []
        if ts.accept("("):
            params.append(ts.ident("parameter").text)
            while ts.accept(","):
                params.append(ts.ident("parameter").text)
            ts.expect(")")
        waves, samples = [], []
        while not ts.done() and not ts.at("sample"):
            w = ts.ident("wire name")
            s = ts.peek()
            if s is None or s.kind != "str":
                ts.fail("expected a wave string such as \"0110\"")
            ts.i += 1
            waves.append((w.text, s.text[1:-1], w.pos))
        while ts.accept("sample"):
            w = None
            if not ts.at("at"):
                w = ts.ident("wire name").text
            ts.expect("at")
            samples.append((w, self._time(ts)))
            while ts.accept(","):                 # several points on one wire (SPEC A 5.3, D29)
                samples.append((w, self._time(ts)))
        ts.expect_done()
        if not waves:
            raise ScoreError(f"symbol {name.text!r} has no wave strings", name.pos)
        return SymbolDef(name.text, params, waves, samples, name.pos)

    def recog(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        pos = ts.peek().pos
        names = [ts.ident("event name").text]
        while ts.accept(","):
            names.append(ts.ident("event name").text)
        r = Recog(names, "edge", pos=pos)
        if ts.accept("no"):
            ts.expect("edge")
            ts.expect("on")
            r.kind, r.wire = "no_edge", ts.ident("wire").text
            ts.expect("for")
            r.qty = parse_qty(ts)
            if r.qty.unit is None:
                r.qty.unit = "beats"
        else:
            r.wire = ts.ident("wire").text
            v = ts.ident("rises, falls, low or high")
            if v.text in ("rises", "falls"):
                r.edge = v.text
                if ts.accept("while"):
                    r.kind = "edge_while"
                    r.while_wire = ts.ident("wire").text
                    lv = ts.ident("high or low")
                    if lv.text not in ("high", "low"):
                        raise ScoreError("expected high or low", lv.pos)
                    r.while_level = lv.text
            elif v.text in ("low", "high"):
                r.kind, r.edge = "level_for", v.text
                ts.expect("for")
                ts.expect(">")
                r.qty = parse_qty(ts)
            else:
                raise ScoreError("expected rises, falls, low or high", v.pos)
        ts.expect_done()
        return r

    def bits(self, ts, kw):
        b = Bits(pos=kw.pos)
        o = ts.ident("msb or lsb")
        if o.text not in ("msb", "lsb"):
            raise ScoreError("expected 'msb first' or 'lsb first'", o.pos)
        ts.expect("first")
        b.order = o.text
        while ts.accept(","):
            c = ts.ident("coding")
            if c.text == "differential":
                b.differential = 0
                if ts.accept("on"):
                    b.differential = expect_int(ts)
            elif c.text == "stuff":
                bit = None
                if ts.peek() is not None and ts.peek().kind == "int":
                    bit = expect_int(ts)
                ts.expect("after")
                n = expect_int(ts)
                k = ts.ident("equal, ones or zeros")
                if k.text not in ("equal", "ones", "zeros"):
                    raise ScoreError("expected equal, ones or zeros", k.pos)
                b.stuff = (bit, n, k.text)
            elif c.text == "invert":
                b.invert = True
            else:
                raise ScoreError(f"unknown coding {c.text!r}", c.pos)
        ts.expect_done()
        return b

    def crc(self, ts, kw):
        name = ts.ident("crc name").text
        v = dict(width=None, poly=None, init=None, xorout=None)
        refin = refout = False
        while not ts.done():
            t = ts.ident("crc parameter")
            if t.text in v:
                v[t.text] = expect_int(ts)
            elif t.text == "refin":
                refin = True
            elif t.text == "refout":
                refout = True
            else:
                raise ScoreError(f"unknown crc parameter {t.text!r}", t.pos)
        for k, x in v.items():
            if x is None:
                raise ScoreError(f"crc {name}: missing '{k}'", kw.pos)
        if not 1 <= v["width"] <= 32:
            raise ScoreError("crc width must be 1..32", kw.pos)
        return CrcDecl(name, v["width"], v["poly"], v["init"], refin, refout, v["xorout"], kw.pos)

    def param(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        name = ts.ident("parameter name")
        ts.expect(":")
        ty = ts.ident("type").text
        default = role = None
        if ts.accept("="):
            default = parse_vexpr(ts)
        if ts.accept("for"):
            role = ts.ident("role").text
        ts.expect_done()
        return ParamDecl(name.text, ty, default, role, name.pos)

    def abort(self, ln):
        ts = TS(ln.toks, (ln.no, 1))
        ts.expect("on")
        ev = ts.ident("event").text
        inp = None
        if ts.accept("in"):
            inp = ts.ident("production").text
        ts.expect("->")
        tgt = ts.ident("target production, idle or report").text
        ts.expect_done()
        return AbortRule(ev, inp, tgt, ln.toks[0].pos)

    def group(self, ts, kw, body):
        name = ts.ident("group name").text
        ts.expect(":")
        ts.expect_done()
        wires, clock = [], None
        for head, sub in _chunks(body):
            t = TS(head.toks, (head.no, 1))
            k = t.next()
            if k.text == "wire":
                wires.append(self.wire(t, k))
            elif k.text == "mirror":
                wires.append(self.mirror(t, k))
            elif k.text == "clock":
                clock = self.clock(t, head, sub)
            else:
                raise ScoreError("only wire, mirror and clock may appear in a group", k.pos)
        return Group(name, wires, clock, kw.pos)

    def grammar(self, body):
        prods = []
        for head, sub in _chunks(body):
            toks = list(head.toks)
            for s in sub:
                toks += s.toks
            ts = TS(toks, (head.no, 1))
            ts.labels = getattr(self, "labels", set())
            name = ts.ident("production name")
            params = []
            if ts.accept("("):
                while True:
                    t = ts.next()
                    if t.kind == "id":
                        params.append(("id", t.text))
                    elif t.kind in ("int", "hex", "bin"):
                        params.append(("lit", _int(t)))
                    else:
                        raise ScoreError("production parameter must be a name or a constant", t.pos)
                    if not ts.accept(","):
                        break
                ts.expect(")")
            ts.expect("=")
            body_node = parse_gexpr(ts)
            ts.expect_done()
            prods.append(Prod(name.text, params, body_node, name.pos))
        return prods


def parse(src: str) -> Score:
    return Parser(src).parse()


def parse_file(path) -> Score:
    with open(path, encoding="utf-8") as f:
        return parse(f.read())
