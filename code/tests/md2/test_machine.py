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
