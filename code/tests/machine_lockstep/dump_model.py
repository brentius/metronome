"""State dump of the Python cycle model (sim/reference/metronome2) in the key set of BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md.

`dump(chip)` returns {key: int} for the state AFTER the last `Chip.step` (values of cycle t+1) plus the pins that step
returned. It only reads model attributes. Memory sums are cached: the byte image is compared (memcmp) with the last
one and the weighted sum is recomputed only when it changed, so the per-cycle cost is small and no flag is needed.
"""
from __future__ import annotations

import operator
import struct
import sys
import weakref
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for _p in (ROOT / "sim/reference",):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from metronome2 import m  # noqa: E402

MASK32 = 0xFFFFFFFF
_WEIGHTS = range(1, m.DATA_BYTES + 1)           # 2048 bytes both for data RAM and for a core's 256 x 64-bit program
_PACK = struct.Struct("<%dQ" % m.PROG_WORDS)
_cache: "weakref.WeakKeyDictionary" = weakref.WeakKeyDictionary()


def weighted_sum(b: bytes) -> int:
    """sum_i b[i] * (i + 1) mod 2^32."""
    return sum(map(operator.mul, b, _WEIGHTS)) & MASK32


def _cached(chip, name: str, image: bytes) -> int:
    c = _cache.setdefault(chip, {})
    hit = c.get(name)
    if hit is not None and hit[0] == image:
        return hit[1]
    s = weighted_sum(image)
    c[name] = (image, s)
    return s


def dump(chip, pins=None) -> dict:
    """pins: the (uo_out, uio_out, uio_oe) tuple returned by the step just taken (recomputed if None)."""
    d: dict = {}
    uo, uio, oe = pins if pins is not None else chip.outputs()
    d["uo_out"], d["uio_out"], d["uio_oe"] = int(uo), int(uio), int(oe)
    for l, ln in enumerate(chip.lines):
        p = f"L{l}."
        for k in ("PH", "RUN", "ARM", "REN", "HELD", "FIRST", "SC", "SP", "FIRED", "W", "SN", "REM",
                  "STAGED", "COMMITTED", "TAPMISS"):
            d[p + k] = int(getattr(ln, k))      # W is already {B1,A2,A1,A0} in bits 3..0 (line.py)
    for t, th in enumerate(chip.threads):
        for k in ("PC", "EN", "READY", "RUNNING", "ARMED", "LATE", "OVR"):
            d[f"T{t}.{k}"] = int(getattr(th, k))
    for c, co in enumerate(chip.cores):
        for k in ("XV", "IR", "RV", "FPC", "XT", "XL", "RR"):
            d[f"C{c}.{k}"] = int(getattr(co, k))
    d["F"], d["FP"] = chip.flags.F, chip.flags.FP
    a = chip.acc
    d["A"], d["Z"], d["C"], d["N"] = a.A, a.Z, a.C, a.N
    for k in range(4):
        d[f"R{k}"] = a.R[k]
    for k, s in enumerate(chip.sh):
        d[f"SH{k}.D"], d[f"SH{k}.CNT"], d[f"SH{k}.LEN"], d[f"SH{k}.MSB"] = s.D, s.CNT, s.LEN, s.MSB
    for k, c in enumerate(chip.cnt):
        d[f"CNT{k}.V"] = c.V
    for k, lf in enumerate(chip.lf):
        d[f"LF{k}.S"] = lf.S
    p0 = chip.mem.ptr
    d["P0.PTR"], d["P0.D"], d["P0.RDY"] = p0.PTR, p0.D, p0.RDY
    for k, s in enumerate(chip.mem.streams):
        for n in ("POS", "BIDX", "BA", "CUR", "CV", "WB", "WV", "RQ", "LD", "PEND", "PV", "STARVED"):
            d[f"S{k}.{n}"] = int(getattr(s, n))
    ctl, h = chip.ctrl, chip.host
    for n in ("RUN", "IRQEN", "CONFLICT", "MEMHAZ", "CWOVR"):
        d[n] = int(getattr(ctl, n))
    for n in ("INB", "INV", "INVP", "OUTB", "OUTV"):
        d[n] = int(getattr(h, n))
    for n in ("FREEZE", "FRZ", "FRZD", "MEN", "MISR", "CEN", "EMASK", "DC"):
        d[n] = int(getattr(chip, n))
    d["CWA"], d["CWV"] = chip.CWA, int(chip.CWV)
    d["CWQA"], d["CWQD"] = chip.CWQ
    d["BWP"], d["RPL"], d["RLV"] = int(chip.BWP), int(chip.RPL), chip.RLV
    d["DMEM.sum"] = _cached(chip, "D", bytes(chip.mem.data))
    for c, co in enumerate(chip.cores):
        d[f"PMEM{c}.sum"] = _cached(chip, f"P{c}", _PACK.pack(*[w & 0xFFFFFFFFFFFFFFFF for w in co.prog]))
    return d
