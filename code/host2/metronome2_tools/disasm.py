"""v2 disassembler.  python -m metronome2_tools.disasm prog.json   (or --words 0x... ...)

The output is valid assembler input: jump targets become labels L<hex>, a jump's condition is always written
explicitly (`goto L if COND`), and the text re-assembles to the same words (for words whose unused moves are
no-ops and whose unused imm / jcond fields are 0).
"""
from __future__ import annotations

import argparse
import sys

from ._md import M
from .encode import Insn, Move, decode

GUARD_PREFIX = {"always": "", "if": "? ", "ifnot": "! ", "never": "never "}


def _empty(mv: Move) -> bool:
    return mv.src == "ZERO" and mv.dst == "NULL"


def insn_text(insn: Insn, target_label=None) -> str:
    parts = []
    moves = [mv for mv in insn.moves if not _empty(mv)]
    if insn.cond != "TRUE":
        parts.append(f"when {insn.cond}")
    uses_imm = any(mv.src == "IMM" for mv in moves)
    mtxt = []
    for mv in moves:
        src = f"#{insn.imm}" if mv.src == "IMM" else mv.src
        mtxt.append(f"{GUARD_PREFIX[mv.guard]}{src} -> {mv.dst}")
    if mtxt:
        parts.append(", ".join(mtxt))
    if insn.jmode != "next":
        lbl = target_label(insn.imm) if target_label else f"{insn.imm}"
        suffix = {"always": "", "if": f" if {insn.jcond}", "ifnot": f" ifnot {insn.jcond}"}[insn.jmode]
        parts.append(f"goto {lbl}{suffix}")
    if insn.pause:
        parts.append("pause")
    text = " ".join(parts) if parts else "nop"
    if insn.jmode == "next" and insn.imm and not uses_imm:
        text += f"   ; (unused imm field = {insn.imm})"
    return text


def disassemble(words: dict, core: int = 0, labels: dict | None = None) -> str:
    words = dict(sorted(words.items()))
    insns = {a: decode(w) for a, w in words.items()}
    targets = {i.imm for i in insns.values() if i.jmode != "next"}
    names = {a: f"L{a:02X}" for a in targets if a in words}
    for name, (c, a) in (labels or {}).items():
        if c == core:
            names[a] = name
    out = [f".core {core}"]
    prev = None
    for a, insn in insns.items():
        if prev is None or a != prev + 1:
            out.append(f".org 0x{a:02X}")
        lbl = f"{names[a]}: " if a in names else ""
        out.append(f"{lbl:<8}{insn_text(insn, lambda t: names.get(t, f'{t}'))}")
        prev = a
    return "\n".join(out)


def disassemble_image(image: dict) -> str:
    per_core: dict = {}
    for run in image["program"]:
        for i, w in enumerate(run["words"]):
            per_core.setdefault(run["core"], {})[run["addr"] + i] = int(w, 16)
    labels = {k: tuple(v) for k, v in image.get("labels", {}).items()}
    return "\n\n".join(disassemble(w, c, labels) for c, w in sorted(per_core.items()))


def main(argv=None) -> int:
    from .image import read_image
    ap = argparse.ArgumentParser(prog="metronome2_tools.disasm")
    ap.add_argument("image", nargs="?", help="program image JSON")
    ap.add_argument("--words", nargs="+", help="hex instruction words (core 0, from address 0)")
    a = ap.parse_args(argv)
    if a.words:
        print(disassemble({i: int(w, 16) for i, w in enumerate(a.words)}))
    elif a.image:
        print(disassemble_image(read_image(a.image)))
    else:
        ap.error("give an image or --words")
    return 0


if __name__ == "__main__":
    sys.exit(main())
