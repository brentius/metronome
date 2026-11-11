import random

import pytest

from metronome_tools._md import M, Insn, Move, decode, encode
from metronome_tools.asm import AsmError, assemble_text, parse_insn, write_group
from metronome_tools.disasm import insn_text


def one(text, labels=None, core=0):
    return parse_insn(text, {}, labels or {}, core, 1)


@pytest.mark.parametrize("dst", [p.name for p in M.DST])
@pytest.mark.parametrize("src", [p.name for p in M.SRC if p.name != "IMM"][:: 7])
def test_every_dst_with_some_sources_matches_encode(src, dst):
    got = one(f"{src} -> {dst}")
    assert got == Insn((Move(src, dst),))
    assert decode(encode(got)).moves[0] == Move(src, dst, "always")


def test_all_sources_encode():
    for p in M.SRC:
        text = "#5 -> R0" if p.name == "IMM" else f"{p.name} -> R0"
        assert encode(one(text)) == encode(Insn((Move(p.name, "R0"),), imm=5 if p.name == "IMM" else 0))


def test_all_guard_conditions_encode():
    for p in M.GUARD_CONDS[1:]:
        i = one(f"when {p.name}  ? ZERO -> R0, ! ZERO -> R1")
        assert i.cond == p.name and [m.guard for m in i.moves] == ["if", "ifnot"]
        assert M.GUARD_ID[p.name] == (encode(i) >> M.FIELD["cond"].lsb) & 0x3F


def test_syntax_forms():
    i = one("when SH0.DONE  ? SH0.O -> E.SYM, ! #0x5A -> ACC.LD  pause goto 90 ifnot")
    assert i == Insn((Move("SH0.O", "E.SYM", "if"), Move("IMM", "ACC.LD", "ifnot")), "SH0.DONE", "ifnot", 0x5A, True)
    assert one("goto 7") == Insn((), "TRUE", "always", 7, False)
    assert one("nop") == Insn()
    assert one("pause").pause
    assert one("goto 3 if F2").cond == "F2" and one("goto 3 if F2").jmode == "if"
    assert one("#-1 -> ACC.LD").imm == 0xFF
    assert one("#0 -> ACC.LD").moves[0].src == "ZERO"          # zero needs no imm field
    assert one("never ZERO -> R0").moves[0].guard == "never"


def test_imm_field_shared_between_jump_and_immediate():
    one("#3 -> R0, #3 -> R1  goto 3")                        # same value: fine
    with pytest.raises(AsmError, match="imm field is shared"):
        one("#3 -> R0  goto 4")
    with pytest.raises(AsmError, match="imm field is shared"):
        one("#3 -> R0, #4 -> R1")
    one("#0 -> R0  goto 4")                                  # a zero immediate never conflicts


def test_condition_required_and_conflicts():
    with pytest.raises(AsmError, match="needs a condition"):
        one("? ZERO -> R0")
    with pytest.raises(AsmError, match="needs a condition"):
        one("goto 3 if")
    with pytest.raises(AsmError, match="conflicting"):
        one("when F0  goto 3 if F1")


def test_write_group_rules():
    with pytest.raises(AsmError, match="same group"):
        one("ZERO -> ACC.LD, ZERO -> ACC.ADD")
    with pytest.raises(AsmError, match="same group"):
        one("ZERO -> SH0.LD, ZERO -> SH0.SH")
    with pytest.raises(AsmError, match="same group"):
        one("ZERO -> LF0.ST, ZERO -> LF0.B1")
    one("when F0  ? ZERO -> E.SYM, ! #1 -> E.SYM")           # exclusive guards are fine
    one("ZERO -> SH0.LD, ZERO -> SH1.LD, ZERO -> SH0.CFG")   # different groups
    assert write_group("CNT2.DEC") == write_group("CNT2.LO") == "CNT2"


def test_errors_suggest_and_limits():
    with pytest.raises(AsmError, match="did you mean ACC.LD"):
        one("ZERO -> ACC.LDD")
    with pytest.raises(AsmError, match="at most 3"):
        one("ZERO -> R0, ZERO -> R1, ZERO -> R2, ZERO -> R3")
    with pytest.raises(AsmError, match="8-bit"):
        one("#300 -> R0")


def test_labels_equ_org_and_cores():
    p = assemble_text("""
.equ K, 0x10 + 2
.org 4
a:      #K -> R0
b:      goto a
.core 1
.org 0x20
c:      goto c
""")
    assert p.labels == {"a": (0, 4), "b": (0, 5), "c": (1, 0x20)}
    assert p.code[0][4].insn.imm == 0x12 and p.code[0][5].insn.imm == 4
    assert p.code[1][0x20].insn.imm == 0x20
    with pytest.raises(AsmError, match="core 1"):
        assemble_text("a: nop\n.core 1\n goto a")
    with pytest.raises(AsmError, match="duplicate label"):
        assemble_text("a: nop\na: nop")
    with pytest.raises(AsmError, match="occupied"):
        assemble_text("nop\n.org 0\nnop")
    with pytest.raises(AsmError, match="<src>:2:"):
        assemble_text("nop\nZERO -> NOPE")


def test_forward_reference_and_label_as_immediate():
    p = assemble_text("goto end\nnop\nend: #end -> R1")
    assert p.code[0][0].insn.imm == 2 and p.code[0][2].insn.imm == 2


def random_insn(rng):
    srcs = [p.name for p in M.SRC if p.name != "IMM"]
    dsts = [p.name for p in M.DST if p.name != "NULL"]
    jmode = rng.choice(list(M.JMODES))
    n = rng.randint(0, 3)
    moves, groups = [], set()
    imm = rng.randint(1, 255)
    for _ in range(n):
        dst = rng.choice(dsts)
        if write_group(dst) in groups:
            continue
        groups.add(write_group(dst))
        moves.append(Move(rng.choice(srcs + ["IMM"]), dst, rng.choice(list(M.GUARDS))))
    cond_needed = jmode in ("if", "ifnot") or any(m.guard in ("if", "ifnot") for m in moves)
    cond = rng.choice([g.name for g in M.GUARD_CONDS[1:]]) if cond_needed else "TRUE"
    uses_imm = any(m.src == "IMM" for m in moves) or jmode != "next"
    return Insn(tuple(moves), cond, jmode, imm if uses_imm else 0, rng.random() < 0.5)


def test_disassembler_roundtrip_random():
    rng = random.Random(1)
    for _ in range(500):
        insn = random_insn(rng)
        word = encode(insn)
        text = insn_text(decode(word))
        again = encode(one(text))
        assert again == word, (text, insn)
