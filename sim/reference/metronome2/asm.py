"""Minimal instruction encoder for tests (the v2 assembler is a later build step)."""
from .md import m


def _put(w, name, v):
    f = m.FIELD[name]
    assert 0 <= v < (1 << f.width), (name, v)
    return w | (v << f.lsb)


def insn(*moves, cond="TRUE", jmode="next", jcond="TRUE", imm=0, pause=0):
    """moves: (src, dst) or (src, dst, guard) with names from the v2 tables; guard in always/if/ifnot/never."""
    assert len(moves) <= m.N_MOVES
    w = 0
    w = _put(w, "pause", int(pause))
    w = _put(w, "jmode", m.JMODES[jmode])
    w = _put(w, "imm", imm & 0xFF)
    w = _put(w, "cond", m.GUARD_ID[cond])
    w = _put(w, "jcond", m.JGUARD_ID[jcond])
    for i in range(m.N_MOVES):
        if i < len(moves):
            src, dst, *g = moves[i]
            guard = g[0] if g else "always"
        else:
            src, dst, guard = "ZERO", "NULL", "never"
        w = _put(w, f"m{i}_guard", m.GUARDS[guard])
        w = _put(w, f"m{i}_src", m.SRC_ID[src])
        w = _put(w, f"m{i}_dst", m.DST_ID[dst])
    return w
