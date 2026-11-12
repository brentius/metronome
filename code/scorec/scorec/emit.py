"""Assembly text builder: configuration blocks and per-core instruction lists (toolchain v2 syntax, TOOLCHAIN_V2.md)."""
from __future__ import annotations

from dataclasses import dataclass, field


def imm(v: int, dst: str) -> str:
    """Move text for a constant: ZERO is free, anything else uses the shared 8-bit imm field."""
    return f"ZERO -> {dst}" if v == 0 else f"#{v} -> {dst}"


@dataclass
class Instr:
    moves: list                    # strings like "? #3 -> L.SYM"
    when: str | None = None
    goto: str | None = None        # label
    jmode: str | None = None       # if | ifnot
    jcond: str | None = None
    pause: bool = False
    note: str = ""

    def text(self) -> str:
        parts = []
        if self.when:
            parts.append(f"when {self.when}")
        parts.append(", ".join(self.moves) if self.moves else "nop" if not (self.pause or self.goto) else "")
        s = " ".join(p for p in parts if p)
        tail = []
        if self.pause:
            tail.append("pause")
        if self.goto:
            g = f"goto {self.goto}"
            if self.jmode:
                g += f" {self.jmode}" + (f" {self.jcond}" if self.jcond else "")
            tail.append(g)
        out = s
        if tail:
            out += "   " + " ".join(tail)
        return out.strip()


class Core:
    def __init__(self, n):
        self.n = n
        self.items: list = []          # ("label", name) | ("insn", Instr) | ("comment", text)

    def label(self, name):
        self.items.append(("label", name))

    def comment(self, text):
        self.items.append(("comment", text))

    def i(self, moves=(), when=None, goto=None, jmode=None, jcond=None, pause=False, note=""):
        self.items.append(("insn", Instr(list(moves), when, goto, jmode, jcond, pause, note)))

    @property
    def ninsn(self):
        return sum(1 for k, _ in self.items if k == "insn")

    def text(self) -> list[str]:
        out = [f".core {self.n}"]
        for kind, v in self.items:
            if kind == "label":
                out.append(f"{v}:")
            elif kind == "comment":
                out.append(f"        ; {v}")
            else:
                out.append("        " + v.text() + (f"          ; {v.note}" if v.note else ""))
        return out


class Builder:
    def __init__(self, title: str):
        self.title = title
        self.header: list[str] = []
        self.cfg: list[str] = []
        self.cores = {0: Core(0), 1: Core(1)}

    def comment(self, text):
        self.header.append(f"; {text}")

    def block(self, head: str, lines: list[str]):
        self.cfg.append(head)
        self.cfg += [f"    {l}" for l in lines]
        self.cfg.append(".end")

    def text(self) -> str:
        out = [f"; {self.title}", *self.header, "", ".clock 60e6", ""]
        out += self.cfg
        for c in self.cores.values():
            if c.items:
                out.append("")
                out += c.text()
        return "\n".join(out) + "\n"

    @property
    def ninsn(self):
        return sum(c.ninsn for c in self.cores.values())
