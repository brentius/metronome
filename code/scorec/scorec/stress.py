"""Stress projection: score -> stressed score, compiled by the same compiler (rival-ideas list section 2, item 1).

A stress is a transform of the parsed score, never a change to the compiler or the chip.  The stressed score is
compiled like any other, so the fault is placed exactly where the score's own timing puts it: on the beat, by the
rational divider.  Every transform returns a deep copy; the original score is untouched.

Modes (each is `(name, *args)`; `apply` takes a list of them):

- ``("tempo", ppm)``           the clock rate moves by `ppm` parts per million (a sender running fast or slow).
- ``("crc_init", bit)``        the named frame's CRC is computed with init bit `bit` flipped, so every transmitted CRC
                               is wrong (CRC is affine in its init, so the error is non-zero for every frame).
- ``("const", index, bit)``    bit `bit` of constant byte `index` in the frame is flipped (preamble, SFD, sync byte).
- ``("terminal", index, args)`` the `index`-th symbol terminal of the frame is sent with other arguments, e.g. UART's
                               stop `bit(1)` sent as `bit(0)` (a framing error).

Checking a stress needs two oracles, both independent of the compiler: the reference codec of the *original* score must
reject (or mis-decode) the stressed waveform, and the codec of the *stressed* score must accept it.  The second proves
the fault is exactly the one asked for, not collateral breakage.
"""
from __future__ import annotations

import copy
from fractions import Fraction

from . import _paths  # noqa: F401
from score.ast import ConstBytes, Field, Prod, Ref, Rep, Seq

from .plan import CompileError

MODES = ("tempo", "crc_init", "const", "terminal")


def _frame_prod(score) -> Prod:
    """The production repeated by the start production's star: the frame every mode acts on."""
    start = score.prods[0]
    body = start.body
    items = body.items if isinstance(body, Seq) else [body]
    for it in items:
        if isinstance(it, Rep) and isinstance(it.node, Ref):
            ps = score.prods_named(it.node.name)
            if ps:
                return ps[0]
    return start


def _walk(n, out):
    """Depth-first terminals of one production body, in transmit order."""
    if isinstance(n, Seq):
        for it in n.items:
            _walk(it, out)
    elif isinstance(n, (Ref, ConstBytes, Field)):
        out.append(n)
    elif hasattr(n, "node"):
        _walk(n.node, out)
    return out


def _crc_names(score, prod):
    return [n.type.crc for n in _walk(prod.body, []) if isinstance(n, Field) and n.type.kind == "crc"]


def apply(score, stresses):
    """Return a stressed deep copy of `score`.  Raises CompileError('E-STRESS') when a mode does not apply."""
    s = copy.deepcopy(score)
    for st in stresses:
        mode, *a = st
        if mode == "tempo":
            clk = s.clock_for()
            if clk is None or clk.rate is None:
                raise CompileError("E-STRESS", "tempo: the score has no fixed clock rate")
            clk.rate = clk.rate * (1 + Fraction(a[0]) / 1_000_000)
        elif mode == "crc_init":
            names = _crc_names(s, _frame_prod(s))
            if not names:
                raise CompileError("E-STRESS", "crc_init: the frame has no crc field")
            if names[0] not in s.crcs:                 # a library crc: give this score its own copy to stress
                from score.crc import STD
                s.crcs[names[0]] = copy.deepcopy(STD[names[0]])
            d = s.crcs[names[0]]
            if not 0 <= a[0] < d.width:
                raise CompileError("E-STRESS", f"crc_init: bit {a[0]} outside crc '{d.name}' width {d.width}")
            d.init ^= 1 << a[0]
        elif mode == "const":
            idx, bit = a
            consts = [n for n in _walk(_frame_prod(s).body, []) if isinstance(n, ConstBytes)]
            flat = [(c, i) for c in consts for i in range(len(c.data))]
            if not 0 <= idx < len(flat):
                raise CompileError("E-STRESS", f"const: byte {idx} outside the frame's {len(flat)} constant bytes")
            c, i = flat[idx]
            b = bytearray(c.data)
            b[i] ^= 1 << bit
            c.data = bytes(b)
        elif mode == "terminal":
            idx, args = a
            refs = [n for n in _walk(_frame_prod(s).body, []) if isinstance(n, Ref) and s.symbol(n.name)]
            if not 0 <= idx < len(refs):
                raise CompileError("E-STRESS", f"terminal: {idx} outside the frame's {len(refs)} symbol terminals")
            r = refs[idx]
            from score.ast import Num
            r.args = [Num(int(v)) for v in args]
        else:
            raise CompileError("E-STRESS", f"unknown stress mode '{mode}' (modes: {', '.join(MODES)})")
    return s


def describe(stresses) -> str:
    return ", ".join(f"{m}({', '.join(map(str, a))})" for m, *a in stresses) or "none"


def compile_stressed(source, role, bind, stresses, **kw):
    """Compile `role` of the stressed score; the report names the stress so an image is never mistaken for nominal."""
    from .api import _load, compile_score
    stressed = apply(_load(source), stresses)
    c = compile_score(stressed, role, bind, **kw)
    c.report = f"STRESSED: {describe(stresses)}\n" + c.report
    c.host["stress"] = list(stresses)
    return c
