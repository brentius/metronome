"""v2 instruction encode / decode from the field table in machine.py (adds the separate 5-bit jump condition)."""
from __future__ import annotations

from dataclasses import dataclass

from ._md import M


@dataclass(frozen=True)
class Move:
    src: str = "ZERO"
    dst: str = "NULL"
    guard: str = "always"


@dataclass(frozen=True)
class Insn:
    moves: tuple = ()
    cond: str = "TRUE"        # move guard condition (6-bit, any guard)
    jmode: str = "next"       # next | always | if | ifnot
    jcond: str = "TRUE"       # jump condition (5-bit, a name from JUMP_GUARDS)
    imm: int = 0
    pause: bool = False


NOP_MOVE = Move()


def _put(word: int, name: str, value: int) -> int:
    f = M.FIELD[name]
    if not 0 <= value < (1 << f.width):
        raise ValueError(f"{name}={value} does not fit {f.width} bits")
    return word | (value << f.lsb)


def _get(word: int, name: str) -> int:
    f = M.FIELD[name]
    return (word >> f.lsb) & ((1 << f.width) - 1)


def encode(insn: Insn) -> int:
    if len(insn.moves) > M.N_MOVES:
        raise ValueError(f"at most {M.N_MOVES} moves per instruction")
    w = _put(0, "pause", int(insn.pause))
    w = _put(w, "jmode", M.JMODES[insn.jmode])
    w = _put(w, "imm", insn.imm & 0xFF)
    w = _put(w, "cond", M.GUARD_ID[insn.cond])
    w = _put(w, "jcond", M.JGUARD_ID[insn.jcond])
    moves = list(insn.moves) + [Move("ZERO", "NULL", "never")] * (M.N_MOVES - len(insn.moves))
    for i, mv in enumerate(moves):
        w = _put(w, f"m{i}_guard", M.GUARDS[mv.guard])
        w = _put(w, f"m{i}_src", M.SRC_ID[mv.src])
        w = _put(w, f"m{i}_dst", M.DST_ID[mv.dst])
    return w


def decode(word: int) -> Insn:
    """Out-of-table indices decode to ZERO / NULL / TRUE (a disassembly-only simplification of SPEC 9a.1)."""
    inv_j = {v: k for k, v in M.JMODES.items()}
    inv_g = {v: k for k, v in M.GUARDS.items()}
    moves = []
    for i in range(M.N_MOVES):
        s, d = _get(word, f"m{i}_src"), _get(word, f"m{i}_dst")
        moves.append(Move(M.SRC[s].name if s < len(M.SRC) else "ZERO", M.DST[d].name if d < len(M.DST) else "NULL",
                          inv_g[_get(word, f"m{i}_guard")]))
    c, j = _get(word, "cond"), _get(word, "jcond")
    return Insn(tuple(moves), M.GUARD_CONDS[c].name if c < len(M.GUARD_CONDS) else "TRUE",
                inv_j[_get(word, "jmode")], M.JUMP_GUARDS[j] if j < len(M.JUMP_GUARDS) else "TRUE",
                _get(word, "imm"), bool(_get(word, "pause")))
