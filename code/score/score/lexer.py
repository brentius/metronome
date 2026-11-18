"""Tokenizer for score files. Produces tokens with line/column and groups them into indented lines."""
from __future__ import annotations

import re
from dataclasses import dataclass

from .ast import ScoreError

_TOKEN = re.compile(r"""
    (?P<ws>[ \t\r]+)
  | (?P<comment>\#[^\n]*)
  | (?P<nl>\n)
  | (?P<str>"[^"\n]*")
  | (?P<pct>\d+(?:\.\d+)?%)
  | (?P<hex>0[xX][0-9A-Fa-f_]+)
  | (?P<bin>0[bB][01_]+)
  | (?P<dec>\d+\.\d+)
  | (?P<word>\d+[A-Za-z_][A-Za-z0-9_]*)
  | (?P<int>\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<op>->|<-|\.\.|\|\||&&|<<|>>|<=|>=|==|!=|[(){}\[\],:=|*+?!~&^<>\-/%;.])
""", re.X)


@dataclass
class Tok:
    kind: str     # id int dec word hex bin str pct op asm
    text: str
    line: int
    col: int

    @property
    def pos(self):
        return (self.line, self.col)

    def __repr__(self):
        return f"{self.kind}:{self.text!r}@{self.line}:{self.col}"


@dataclass
class Line:
    no: int
    indent: int
    toks: list


def tokenize(src: str) -> list[Line]:
    toks: list[Tok] = []
    i, line, ls = 0, 1, 0       # ls = index of line start
    n = len(src)
    while i < n:
        m = _TOKEN.match(src, i)
        if not m:
            raise ScoreError(f"unexpected character {src[i]!r}", (line, i - ls + 1))
        k, text = m.lastgroup, m.group()
        col = i - ls + 1
        if k == "nl":
            line += 1
            ls = m.end()
        elif k in ("ws", "comment"):
            pass
        else:
            if k == "id" and text in ("push", "open") and src.startswith(("-pull", "-drain"), m.end()):
                suffix = "-pull" if src.startswith("-pull", m.end()) else "-drain"
                text += suffix
                i = m.end() + len(suffix)
                toks.append(Tok("id", text, line, col))
                continue
            toks.append(Tok(k, text, line, col))
            if k == "id" and text in ("asm", "model"):
                j = m.end()
                mm = re.compile(r"[ \t\r\n]*\{").match(src, j)
                if mm:
                    start = mm.end()
                    depth, p = 1, start
                    while p < n and depth:
                        if src[p] == "{":
                            depth += 1
                        elif src[p] == "}":
                            depth -= 1
                        p += 1
                    if depth:
                        raise ScoreError(f"unterminated {text} block", (line, col))
                    raw = src[start:p - 1]
                    toks.append(Tok("asm", raw, line, col))
                    lines_in = src.count("\n", i, p)
                    last_nl = src.rfind("\n", i, p)
                    line += lines_in
                    if last_nl >= 0:
                        ls = last_nl + 1
                    i = p
                    continue
        i = m.end()
    by_line: dict[int, list[Tok]] = {}
    for t in toks:
        by_line.setdefault(t.line, []).append(t)
    return [Line(no, ts[0].col - 1, ts) for no, ts in sorted(by_line.items())]
