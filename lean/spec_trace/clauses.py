"""Split a SPEC markdown file into numbered, hashed clauses.

Clause kinds: code (non-blank line in a fenced block), bullet, item (numbered
list item), table (data row), p (prose sentence).  ID: ``§<section>/<kind><n>``
with n counting per (section, kind) from 1.  ``§0`` is the preamble.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path

HEADING = re.compile(r"^(#{1,6})\s+(.*)$")
SECNUM = re.compile(r"^(\d+[a-z]?(?:\.\d+[a-z]?)*)\.?(?:\s|$)")
BULLET = re.compile(r"^(\s*)[-*+]\s+(.*)$")
NUMBERED = re.compile(r"^(\s*)\d+[.)]\s+(.*)$")
ABBREV = re.compile(r"\b(e\.g\.|i\.e\.|etc\.|vs\.|cf\.|approx\.|resp\.)", re.I)
_MASK = {".": "\x01", "!": "\x02", "?": "\x03"}
_UNMASK = {ord(v): k for k, v in _MASK.items()}


def norm(text: str) -> str:
    return " ".join(text.split())


def text_hash(text: str) -> str:
    return hashlib.sha256(norm(text).encode("utf-8")).hexdigest()[:10]


@dataclass
class Clause:
    id: str
    section: str
    kind: str
    text: str
    hash: str
    line: int
    block: int


def _mask(s: str) -> str:
    def m_all(mo):
        return "".join(_MASK.get(c, c) for c in mo.group(0))
    s = re.sub(r"`[^`]*`", m_all, s)
    return ABBREV.sub(m_all, s)


_END = re.compile(r"[.!?]+(?:\*\*|\*|[)\"\]])*(?=\s)")
_START = re.compile(r"\s+(?=[A-Z`*(\[\"<])")


def split_sentences(paragraph: str) -> list[str]:
    s = _mask(norm(paragraph))
    out, pos = [], 0
    for mo in _END.finditer(s):
        nxt = _START.match(s, mo.end())
        if nxt:
            out.append(s[pos:mo.end()])
            pos = nxt.end()
    if pos < len(s):
        out.append(s[pos:])
    return [norm(x.translate(_UNMASK)) for x in out if x.strip()]


def parse(text: str) -> list[Clause]:
    lines = text.splitlines()
    clauses: list[Clause] = []
    counters: dict[tuple[str, str], int] = {}
    state = {"section": "0", "block": 0}
    cur: dict | None = None  # {"kind": "p"|"bullet"|"item", "parts": [], "line": n}
    in_fence = False
    table_row = -1

    def emit(kind, txt, line, block):
        txt = norm(txt)
        if not txt:
            return
        key = (state["section"], kind)
        counters[key] = counters.get(key, 0) + 1
        clauses.append(Clause(f"§{state['section']}/{kind}{counters[key]}",
                              state["section"], kind, txt, text_hash(txt), line, block))

    def flush():
        nonlocal cur
        if cur is None:
            return
        state["block"] += 1
        joined = " ".join(cur["parts"])
        if cur["kind"] == "p":
            for sent in split_sentences(joined):
                emit("p", sent, cur["line"], state["block"])
        else:
            emit(cur["kind"], joined, cur["line"], state["block"])
        cur = None

    for n, raw in enumerate(lines, 1):
        stripped = raw.strip()
        if stripped.startswith("```"):
            flush()
            in_fence = not in_fence
            table_row = -1
            if in_fence:
                state["block"] += 1
            continue
        if in_fence:
            if stripped:
                emit("code", stripped, n, state["block"])
            continue
        if not stripped:
            flush()
            table_row = -1
            continue
        hm = HEADING.match(stripped)
        if hm:
            flush()
            table_row = -1
            sm = SECNUM.match(hm.group(2))
            if sm and len(hm.group(1)) >= 2:
                state["section"] = sm.group(1)
            continue
        if stripped.startswith("|"):
            flush()
            table_row += 1
            if table_row >= 2:
                if table_row == 2:
                    state["block"] += 1
                emit("table", stripped, n, state["block"])
            continue
        table_row = -1
        bm, nm = BULLET.match(raw), NUMBERED.match(raw)
        if bm or nm:
            flush()
            cur = {"kind": "bullet" if bm else "item",
                   "parts": [(bm or nm).group(2)], "line": n}
            continue
        if cur is None:
            cur = {"kind": "p", "parts": [stripped], "line": n}
        else:
            cur["parts"].append(stripped)
    flush()
    return clauses


def parse_file(path: Path) -> list[Clause]:
    return parse(Path(path).read_text(encoding="utf-8"))


def main(argv=None) -> int:
    root = Path(__file__).resolve().parents[2]
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--spec", default=str(root / "wiki" / "SPEC_V2.md"))
    ap.add_argument("--json", action="store_true", help="emit JSON")
    a = ap.parse_args(argv)
    cl = parse_file(Path(a.spec))
    if a.json:
        sys.stdout.reconfigure(encoding="utf-8")
        print(json.dumps([asdict(c) for c in cl], ensure_ascii=False, indent=1))
    else:
        sys.stdout.reconfigure(encoding="utf-8")
        for c in cl:
            print(f"{c.id}\t{c.hash}\t{c.text[:100]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
