"""Consistency checks on the v2 machine description (code/md2/machine.py)."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "code/md2"))
import machine as m  # noqa: E402


def test_table_limits():
    assert len(m.SRC) <= 64
    assert len(m.DST) <= 64
    assert len(m.GUARD_CONDS) <= 64
    assert len(m.JUMP_GUARDS) <= 32
    assert len(m.TRIGGERS) <= 32


def test_names_unique():
    for lst in (m.SRC, m.DST, m.GUARD_CONDS):
        names = [p.name for p in lst]
        assert len(names) == len(set(names))
    assert len(m.JUMP_GUARDS) == len(set(m.JUMP_GUARDS))
    assert len(m.TRIGGERS) == len(set(m.TRIGGERS))


def test_fields_tile_the_word():
    bits = [0] * m.INSN_BITS
    for f in m.FIELDS:
        for b in range(f.lsb, f.msb + 1):
            bits[b] += 1
    assert bits == [1] * m.INSN_BITS
    assert m.FIELD["jcond"].width == 5 and m.FIELD["cond"].width == 6


def test_jump_guards_are_guards():
    assert m.JUMP_GUARDS[0] == "TRUE"
    for n in m.JUMP_GUARDS:
        assert n in m.GUARD_ID, n


def test_every_destination_in_exactly_one_write_group():
    grouped = [d for ds in m.WRITE_GROUPS.values() for d in ds]
    assert len(grouped) == len(set(grouped))
    assert set(grouped) == {p.name for p in m.DST} - {"NULL"}


def test_symbol_ports_share_one_group():
    assert m.WRITE_GROUPS["L.SYM"] == ["L.SYM", "L.DBIT", "L.XOR"]


def test_design_required_ports_present():
    for s in ("L.IN", "LF0.O", "LF1.O", "S0.BIT", "S1.BIT"):
        assert s in m.SRC_ID
    for d in ("L.SYM", "L.DBIT", "L.XOR", "S0.ADV", "S0.RX", "S0.CTL", "S1.ADV", "S1.RX", "S1.CTL"):
        assert d in m.DST_ID
    for g in ("S0.END", "S0.MARK", "S0.BYTE", "S1.END", "S1.MARK", "S1.BYTE"):
        assert g in m.GUARD_ID


def test_config_inventory():
    # v1 held 1,460 configuration bits (V2_DESIGN 4.7). v2 doubles the pin and input tables, so the inventory is
    # larger; the bound below catches accidental growth beyond what the area ledger can absorb.
    assert m.CONFIG_BITS_TOTAL == sum(m.CONFIG_BITS.values())
    assert 1460 < m.CONFIG_BITS_TOTAL <= 2200


def test_generated_files_current():
    p = subprocess.run([sys.executable, str(ROOT / "code/md2/gen.py"), "--check"], capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr


def test_host_map_blocks_do_not_overlap_and_registers_fit():
    spans = []
    for b, (base, st, n, regs) in m.HOST_BLOCKS.items():
        stride = m.HOST_STRIDE[st] if st else 0x10
        for off, (name, nbytes, acc, _) in regs.items():
            assert off + nbytes <= stride, (b, name)
            assert acc in ("W", "R", "RW", "W1C"), (b, name)
        offs = sorted((o, o + r[1]) for o, r in regs.items())
        for (a0, a1), (b0, _) in zip(offs, offs[1:]):
            assert a1 <= b0, (b, a0, b0)
        lo = m.HOST_MAP[base]
        spans.append((lo, lo + stride * n, b))
    prog_hi = m.HOST_MAP["PROG_BASE"] + m.N_CORES * m.HOST_STRIDE["PROG_CORE"]
    spans += [(m.HOST_MAP["PROG_BASE"], prog_hi, "PROG"),
              (m.HOST_MAP["DATA_BASE"], m.HOST_MAP["DATA_BASE"] + m.DATA_BYTES, "DATA")]
    assert m.HOST_STRIDE["PROG_CORE"] == 8 * m.PROG_WORDS
    spans.sort()
    for (a0, a1, x), (b0, _, y) in zip(spans, spans[1:]):
        assert a1 <= b0, (x, y)
    assert spans[-1][1] <= 0x10000


def test_latch_config_fields_have_host_bytes():
    # every latch configuration bit has a home in a write-only register of the matching block
    w_bytes = {b: sum(r[1] for r in regs.values() if r[2] == "W")
               for b, (_, _, _, regs) in m.HOST_BLOCKS.items()}
    assert sum(m.LINE_CFG.values()) <= 8 * w_bytes["LINE"]
    assert sum(m.THREAD_CFG.values()) <= 8 * w_bytes["THREAD"]
    assert sum(m.OUT_CFG.values()) + sum(m.OE_CFG.values()) <= 8 * w_bytes["OUT"]
    assert sum(m.STREAM_CFG.values()) <= 8 * w_bytes["STREAM"]
    assert sum(m.LFSR_CFG.values()) <= 8 * w_bytes["LFSR"]
