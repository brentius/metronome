"""Encoding round trips: encode/decode, assemble/disassemble/assemble, and agreement with the model's encoder."""
import random

from metronome2 import asm as model_asm
from metronome2_tools._md import M
from metronome2_tools.asm import assemble_text
from metronome2_tools.model import AsmError
from metronome2_tools.disasm import disassemble, insn_text
from metronome2_tools.encode import Insn, Move, decode, encode


def rand_insn(rng):
    moves = []
    for _ in range(rng.randint(0, M.N_MOVES)):
        moves.append(Move(rng.choice(M.SRC).name, rng.choice(M.DST[1:]).name, rng.choice(list(M.GUARDS))))
    jmode = rng.choice(list(M.JMODES))
    return Insn(tuple(moves), rng.choice(M.GUARD_CONDS).name, jmode,
                rng.choice(M.JUMP_GUARDS) if jmode in ("if", "ifnot") else "TRUE",
                rng.randrange(256), bool(rng.getrandbits(1)))


def test_encode_decode_round_trip_random():
    rng = random.Random(1)
    for _ in range(2000):
        i = rand_insn(rng)
        w = encode(i)
        assert 0 <= w < (1 << M.INSN_BITS)
        j = decode(w)
        pad = tuple(j.moves[len(i.moves):])
        assert j.moves[:len(i.moves)] == i.moves and all(p == Move("ZERO", "NULL", "never") for p in pad)
        assert (j.cond, j.jmode, j.jcond, j.imm, j.pause) == (i.cond, i.jmode, i.jcond, i.imm, i.pause)
        assert encode(j) == w


def test_every_field_lands_in_its_documented_bits():
    i = Insn((Move("IMM", "L.SYM", "if"),), cond="F3", jmode="ifnot", jcond="CNT1.Z", imm=0xA7, pause=True)
    w = encode(i)
    g = lambda n: (w >> M.FIELD[n].lsb) & ((1 << M.FIELD[n].width) - 1)
    assert (g("pause"), g("jmode"), g("imm"), g("cond")) == (1, M.JMODES["ifnot"], 0xA7, M.GUARD_ID["F3"])
    assert g("jcond") == M.JGUARD_ID["CNT1.Z"] and g("m0_src") == M.SRC_ID["IMM"] and g("m0_dst") == M.DST_ID["L.SYM"]
    assert g("m0_guard") == M.GUARDS["if"]


def test_matches_the_models_test_encoder():
    rng = random.Random(2)
    for _ in range(500):
        i = rand_insn(rng)
        mv = [(m.src, m.dst, m.guard) for m in i.moves]
        assert encode(i) == model_asm.insn(*mv, cond=i.cond, jmode=i.jmode, jcond=i.jcond, imm=i.imm, pause=i.pause)


def test_disassembly_reassembles_to_the_same_words():
    rng = random.Random(3)
    n = 0
    for _ in range(500):
        i = rand_insn(rng)
        i = Insn(tuple(m for m in i.moves if not (m.src == "ZERO" and m.dst == "NULL")), i.cond, i.jmode, i.jcond,
                 i.imm, i.pause)
        w = encode(i)
        d = decode(w)
        if d.jmode == "next" and d.imm and not any(m.src == "IMM" for m in d.moves):
            continue                    # imm unused: the text carries it only as a comment
        text = disassemble({0: w}, 0)          # a jump target outside the listing stays a number
        try:
            prog = assemble_text(text)
        except AsmError as e:                  # the assembler rightly rejects non-exclusive same-group moves
            assert "same group" in str(e) or "needs a condition" in str(e), (text, e)
            continue
        assert prog.words(0)[0] == w, (text, hex(w))
        n += 1
    assert n > 100


def test_insn_text_shapes():
    i = Insn((Move("ZERO", "L.SYM", "if"), Move("IMM", "L.SYM", "ifnot")), "SH0.OUT", "if", "SH0.DONE", 1, True)
    assert insn_text(i) == "when SH0.OUT ? ZERO -> L.SYM, ! #1 -> L.SYM goto 1 if SH0.DONE pause"
