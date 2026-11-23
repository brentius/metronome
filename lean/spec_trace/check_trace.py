"""Clause-trace checker between wiki/SPEC_V2.md and the Lean machine spec.

Usage:  python check_trace.py [--update] [--allow-unmapped] [--allow-orphans]
See README.md for the classification rules.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, OrderedDict
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    import tomli as tomllib  # type: ignore

sys.path.insert(0, str(Path(__file__).resolve().parent))
from clauses import Clause, parse_file  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
KINDS = ("unmapped", "machine", "theorem", "table", "informative", "outside")
NEEDS_DECLS = ("machine", "table")
NEEDS_REASON = ("informative", "outside")
FIELD_ORDER = ("hash", "text", "kind", "decls", "reason", "was", "old_text")
NS_ROOT = "Metronome.Machine"
UTIL_NS = NS_ROOT + ".Util"
TABLES_NS = NS_ROOT + ".Tables"

# --------------------------------------------------------------------------
# Lean scanner
# --------------------------------------------------------------------------

_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(def|theorem|lemma|structure|inductive|abbrev|instance|opaque)\s+"
    r"([^\s:({\[]+)")
_NS = re.compile(r"^\s*namespace\s+(\S+)")
_SEC = re.compile(r"^\s*section(?:\s+(\S+))?\s*$")
_END = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")


def strip_comments(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def scan_lean_text(src: str, fname: str = "") -> list[dict]:
    """Return [{name, private, file, line}] for the declarations of one file."""
    decls = []
    stack: list[tuple[str, str]] = []  # (kind, name); a namespace name may be dotted
    for ln, line in enumerate(strip_comments(src).splitlines(), 1):
        m = _NS.match(line)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        m = _SEC.match(line)
        if m:
            stack.append(("sec", m.group(1) or ""))
            continue
        m = _END.match(line)
        if m and stack:
            stack.pop()
            continue
        m = _DECL.match(line)
        if m:
            mods, _kind, name = m.groups()
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = ".".join(n for k, n in stack if k == "ns" and n)
                full = f"{prefix}.{name}" if prefix else name
            decls.append({"name": full, "private": "private" in mods.split(),
                          "file": fname, "line": ln})
    return decls


def scan_lean_dir(lean_dir: Path) -> list[dict]:
    out = []
    for f in sorted(Path(lean_dir).rglob("*.lean")):
        out += scan_lean_text(f.read_text(encoding="utf-8"), f.name)
    return out


def is_exempt(d: dict) -> bool:
    n = d["name"]
    if d["private"] or not n.startswith(NS_ROOT + "."):
        return True
    if n.startswith(UTIL_NS + ".") or n.startswith(TABLES_NS + ".") or d["file"] == "Tables.lean":
        return True
    return False


# --------------------------------------------------------------------------
# TOML read / write
# --------------------------------------------------------------------------

def load_toml(path: Path) -> tuple[dict, dict]:
    if not Path(path).exists():
        return {}, {}
    data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    helpers = data.pop("helpers", {})
    return data, helpers


def _q(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def _val(v) -> str:
    if isinstance(v, list):
        return "[" + ", ".join(_q(x) for x in v) + "]"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    return _q(str(v))


def write_toml(path: Path, entries: dict, helpers: dict) -> None:
    out = ["# Clause trace: wiki/SPEC_V2.md <-> Metronome.Machine.  See README.md.",
           "# Edit kind, decls and reason; do not edit hash (run check_trace.py --update).", ""]
    for cid, e in entries.items():
        out.append(f"[{_q(cid)}]")
        keys = [k for k in FIELD_ORDER if k in e] + sorted(k for k in e if k not in FIELD_ORDER)
        for k in keys:
            out.append(f"{k} = {_val(e[k])}")
        out.append("")
    for name, h in helpers.items():
        out.append(f"[helpers.{_q(name)}]")
        out.append(f"reason = {_q(h.get('reason', ''))}")
        out.append("")
    Path(path).write_text("\n".join(out), encoding="utf-8", newline="\n")


def short(text: str, n: int = 100) -> str:
    return text if len(text) <= n else text[: n - 3].rstrip() + "..."


# --------------------------------------------------------------------------
# Pre-classification (obvious non-machine clauses only)
# --------------------------------------------------------------------------

CALC = re.compile(r"\b(calculated|estimated)\b", re.I)


def preclassify(cl: list[Clause]) -> dict[str, dict]:
    """Return {id: {kind, reason?, decls?}} for the obvious non-machine clauses."""
    res: dict[str, dict] = {}
    head_of: dict[tuple, str] = {}
    for c in cl:
        head_of.setdefault((c.section, c.block, c.kind == "code"), c.text)

    def setk(c, kind, reason=None):
        if c.id in res:
            return
        d = {"kind": kind}
        if kind == "theorem":
            d["decls"] = []
        if reason:
            d["reason"] = reason
        res[c.id] = d

    in_toolchain = False
    in_consequences = False
    for c in cl:
        head = c.text if c.kind == "code" else head_of[(c.section, c.block, False)]
        if c.section == "0":
            setk(c, "informative", "preamble: status, scope, evidence and change log of the SPEC itself")
        elif c.section == "11":
            setk(c, "informative", "section 11: differences from SPEC v1 (rationale, not machine behaviour)")
        elif c.section == "12.5":
            setk(c, "outside", "12.5 is the model-diagnostic program-load contract, not machine behaviour")
        elif head.startswith("**Status") and c.kind == "p":
            setk(c, "informative", "status paragraph (implementation and evidence status)")
        elif head.startswith("Cost:") and c.kind == "p":
            setk(c, "informative", "cost estimate paragraph (area), not machine behaviour")
        # 10.4 toolchain obligations: the numbered item and its nested bullets
        if c.section == "10":
            if c.kind == "item":
                in_toolchain = c.text.startswith("**Toolchain obligations")
            if in_toolchain and c.kind in ("item", "bullet"):
                setk(c, "outside", "10.4 toolchain obligation: a static check of programs, not the machine step")
        # a lead-in label, then the list or table of calculated consequences
        if c.kind == "p" and c.text.startswith("Consequences (calculated"):
            in_consequences = True
            setk(c, "informative", "lead-in label for the calculated consequences that follow")
            continue
        if in_consequences:
            if c.kind in ("bullet", "item", "table"):
                setk(c, "theorem")
            else:
                in_consequences = False
        if c.kind in ("bullet", "item"):
            if CALC.search(c.text[:140]):
                setk(c, "theorem")
        elif c.kind == "p":
            # a paragraph labelled calculated in its first 140 characters is wholly a consequence
            if CALC.search(head[:140]) or CALC.search(c.text):
                setk(c, "theorem")
    return res


def new_entry(c: Clause, pre: dict | None) -> OrderedDict:
    e = OrderedDict(hash=c.hash, text=short(c.text), kind="unmapped")
    if pre:
        e["kind"] = pre["kind"]
        if "decls" in pre:
            e["decls"] = pre["decls"]
        if "reason" in pre:
            e["reason"] = pre["reason"]
    return e


# --------------------------------------------------------------------------
# --update
# --------------------------------------------------------------------------

def update(cl: list[Clause], old: dict) -> tuple[OrderedDict, dict]:
    pre = preclassify(cl)
    by_hash: dict[str, list[str]] = {}
    for oid, e in old.items():
        by_hash.setdefault(e.get("hash", ""), []).append(oid)
    used: set[str] = set()
    stats = Counter()
    new: dict = {}
    pending = []
    # pass 1: same id and same hash
    for c in cl:
        o = old.get(c.id)
        if o and o.get("hash") == c.hash:
            e = OrderedDict(o)
            e["text"] = short(c.text)
            new[c.id] = e
            used.add(c.id)
            stats["kept"] += 1
        else:
            pending.append(c)
    # pass 2: same text under another id (a clause moved or was renumbered)
    pending2 = []
    for c in pending:
        cand = [i for i in by_hash.get(c.hash, []) if i not in used]
        if cand:
            used.add(cand[0])
            e = OrderedDict(old[cand[0]])
            e["text"] = short(c.text)
            new[c.id] = e
            stats["moved"] += 1
        else:
            pending2.append(c)
    # pass 3: same id with a changed hash is stale; otherwise new
    for c in pending2:
        o = old.get(c.id)
        if o is not None and c.id not in used:
            used.add(c.id)
            e = OrderedDict(o)
            was = o.get("kind", "unmapped")
            e["was"] = o.get("was", "unmapped") if was == "stale" else was
            e["old_text"] = o.get("text", "")
            e["hash"] = c.hash
            e["text"] = short(c.text)
            e["kind"] = "stale"
            new[c.id] = e
            stats["stale"] += 1
        else:
            new[c.id] = new_entry(c, pre.get(c.id))
            stats["new"] += 1
    stats["dropped"] = len([i for i in old if i not in used])
    return OrderedDict((c.id, new[c.id]) for c in cl), dict(stats)


# --------------------------------------------------------------------------
# Check
# --------------------------------------------------------------------------

def check(cl, entries, helpers, lean, allow_unmapped=False, allow_orphans=False):
    errors: list[str] = []
    warns: list[str] = []
    ids = {c.id for c in cl}
    declared = {d["name"] for d in lean}

    for c in cl:
        e = entries.get(c.id)
        if e is None:
            errors.append(f"(a) {c.id}: clause has no entry in the toml (run --update)")
            continue
        kind = e.get("kind", "unmapped")
        if kind not in KINDS and kind != "stale":
            errors.append(f"(a) {c.id}: unknown kind {kind!r}")
            continue
        if e.get("hash") != c.hash:
            errors.append(f"(a) {c.id}: hash mismatch (spec {c.hash}, toml {e.get('hash')}); run --update and review")
        if kind == "stale":
            errors.append(f"(a) {c.id}: stale (spec text changed); review and reclassify")
        elif kind == "unmapped" and not allow_unmapped:
            errors.append(f"(a) {c.id}: unmapped")
        decls = e.get("decls", [])
        if kind in NEEDS_DECLS and not decls:
            errors.append(f"(a) {c.id}: kind {kind} needs a non-empty decls list")
        if kind == "theorem" and not decls:
            warns.append(f"{c.id}: theorem with empty decls (consequence not yet stated or proved)")
        if kind in NEEDS_REASON and not str(e.get("reason", "")).strip():
            errors.append(f"(a) {c.id}: kind {kind} needs a reason")
        for d in decls:
            if d not in declared:
                errors.append(f"(b) {c.id}: declaration {d} not found in the Lean sources")
    for eid in entries:
        if eid not in ids:
            errors.append(f"(a) {eid}: toml entry for a clause that is not in the spec (run --update)")

    referenced = {d for e in entries.values() for d in e.get("decls", [])}
    for name, h in helpers.items():
        if not str(h.get("reason", "")).strip():
            errors.append(f"(c) helper {name}: needs a reason")
        if name not in declared:
            errors.append(f"(b) helper {name}: not found in the Lean sources")
    for d in lean:
        if is_exempt(d) or d["name"] in referenced or d["name"] in helpers:
            continue
        msg = f"(c) {d['name']} ({d['file']}:{d['line']}): public declaration with no clause and not a helper"
        (warns if allow_orphans else errors).append(msg)
    return errors, warns


def summary(cl, entries) -> str:
    kinds = Counter()
    secs: dict[str, Counter] = {}
    for c in cl:
        k = entries.get(c.id, {}).get("kind", "unmapped")
        kinds[k] += 1
        secs.setdefault(c.section, Counter())[k] += 1
    lines = [f"clauses: {len(cl)}"]
    lines.append("per kind: " + ", ".join(f"{k}={kinds[k]}" for k in list(KINDS) + ["stale"] if kinds.get(k)))
    lines.append("per section:")
    for s, cnt in secs.items():
        lines.append(f"  §{s:<6} {sum(cnt.values()):4d}  " + " ".join(f"{k}={v}" for k, v in cnt.items()))
    return "\n".join(lines)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--spec", default=str(ROOT / "wiki" / "SPEC_V2.md"))
    ap.add_argument("--toml", default=str(HERE / "spec_trace.toml"))
    ap.add_argument("--lean-dir", default=str(HERE.parent / "Metronome" / "Machine"))
    ap.add_argument("--update", action="store_true", help="add new clauses, mark changed ones stale, rewrite the toml")
    ap.add_argument("--allow-unmapped", action="store_true", help="do not fail on kind = unmapped")
    ap.add_argument("--allow-orphans", action="store_true", help="report unreferenced Lean declarations as warnings")
    a = ap.parse_args(argv)
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    cl = parse_file(Path(a.spec))
    entries, helpers = load_toml(Path(a.toml))
    if a.update:
        entries, stats = update(cl, entries)
        write_toml(Path(a.toml), entries, helpers)
        print("update:", stats)
    lean_dir = Path(a.lean_dir)
    lean = scan_lean_dir(lean_dir) if lean_dir.exists() else []
    if not lean_dir.exists():
        print(f"note: {lean_dir} does not exist yet; no Lean declarations")
    errors, warns = check(cl, entries, helpers, lean, a.allow_unmapped, a.allow_orphans)
    print(summary(cl, entries))
    for w in warns:
        print("warning:", w)
    for e in errors:
        print("ERROR:", e)
    print(f"{len(errors)} error(s), {len(warns)} warning(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
