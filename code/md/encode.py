"""Instruction encode/decode shared by the assembler, the reference model and the tests.

Moves are (src, dst) or (src, dst, guard) with names from machine.py; guard is "always" (default), "if", "ifnot"
or "never". Unused move slots are encoded as ZERO -> NULL, guard always (a no-op).
"""
from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import machine as m  # noqa: E402


@dataclass(frozen=True)
class Move:
    src: str = "ZERO"
    dst: str = "NULL"
    guard: str = "always"


@dataclass(frozen=True)
class Insn:
    moves: tuple[Move, ...] = field(default_factory=tuple)
    cond: str = "TRUE"
    jmode: str = "next"
    imm: int = 0
    pause: bool = False


def _put(word: int, name: str, value: int) -> int:
    f = m.FIELD[name]
    if not 0 <= value < (1 << f.width):
        raise ValueError(f"{name}={value} does not fit {f.width} bits")
    return word | (value << f.lsb)


def _get(word: int, name: str) -> int:
    f = m.FIELD[name]
    return (word >> f.lsb) & ((1 << f.width) - 1)


def encode(insn: Insn) -> int:
    if len(insn.moves) > m.N_MOVES:
        raise ValueError(f"at most {m.N_MOVES} moves per instruction")
    w = 0
    w = _put(w, "pause", int(insn.pause))
    w = _put(w, "jmode", m.JMODES[insn.jmode])
    w = _put(w, "imm", insn.imm & 0xFF if insn.imm >= -128 else insn.imm)
    w = _put(w, "cond", m.GUARD_ID[insn.cond])
    moves = list(insn.moves) + [Move()] * (m.N_MOVES - len(insn.moves))
    for i, mv in enumerate(moves):
        w = _put(w, f"m{i}_guard", m.GUARDS[mv.guard])
        w = _put(w, f"m{i}_src", m.SRC_ID[mv.src])
        w = _put(w, f"m{i}_dst", m.DST_ID[mv.dst])
    return w


def decode(word: int) -> Insn:
    inv_j = {v: k for k, v in m.JMODES.items()}
    inv_g = {v: k for k, v in m.GUARDS.items()}
    moves = []
    for i in range(m.N_MOVES):
        moves.append(Move(m.SRC[_get(word, f"m{i}_src")].name if _get(word, f"m{i}_src") < len(m.SRC) else "ZERO",
                          m.DST[_get(word, f"m{i}_dst")].name if _get(word, f"m{i}_dst") < len(m.DST) else "NULL",
                          inv_g[_get(word, f"m{i}_guard")]))
    cond_i = _get(word, "cond")
    return Insn(tuple(moves), m.GUARD_CONDS[cond_i].name if cond_i < len(m.GUARD_CONDS) else "TRUE",
                inv_j[_get(word, "jmode")], _get(word, "imm"), bool(_get(word, "pause")))


def fields(word: int) -> dict[str, int]:
    """Raw numeric fields (what the hardware sees), for models and testbenches."""
    return {f.name: _get(word, f.name) for f in m.FIELDS}


if __name__ == "__main__":
    i = Insn((Move("SH0.O", "E.SYM"), Move("SH0.O", "LF0.ST"), Move("ZERO", "SH0.SH")),
             cond="SH0.DONE", jmode="ifnot", imm=5, pause=True)
    w = encode(i)
    assert decode(w) == i, (decode(w), i)
    print(f"{w:016x}", decode(w))
