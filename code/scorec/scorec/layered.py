"""Compile a layered score (SPEC_V2_SCORE.md part A 18.2).

`protocol modbus_rtu over uart.char` splits into two parts:

* the **lower** protocol (the library score, here UART 8N1) is compiled for the chip with `compile_score`, as
  usual: the chip carries bytes on the wire at the wire's tempo;
* the **upper** grammar (framing, function codes, CRC, state) runs on the host through `ByteCodec`, which turns
  upper events into the byte runs the host feeds to the chip, and received bytes back into upper events.

Running the upper grammar on the chip as well (an exchange stage in the compiler) is future work; this split is
what the machine supports today and keeps one score as the single description of both layers.
"""
from __future__ import annotations

from dataclasses import dataclass

from . import _paths  # noqa: F401
from score import errors, parse
from score.ast import Score
from score.layer import ByteCodec, lower_of

from .api import Compiled, compile_score
from .plan import CompileError


@dataclass
class LayeredCompiled:
    upper: Score
    lower: Compiled              # the chip image of the lower protocol
    codec: ByteCodec             # the upper grammar, for the host
    lower_role: str
    payload: str                 # the lower carrier's host field (one byte per carrier instance)

    def host_runs(self, events):
        """Upper events -> [(bytes, gap)]: each run of bytes the host sends back to back, then the silence the upper
        grammar asks for after it (a Qty in chars or time, or None)."""
        out, cur = [], bytearray()
        for t in self.codec.encode(events):
            if t[0] == "byte":
                cur.append(t[1])
            else:
                out.append((bytes(cur), t[1]))
                cur = bytearray()
        if cur:
            out.append((bytes(cur), None))
        return out

    def host_decode(self, frames):
        """Received byte frames (one bytes object per frame, split at the silences) -> (events, ok, notes)."""
        toks = []
        for f in frames:
            toks += [("byte", b) for b in f] + [("eof",)]
        return self.codec.decode(toks)


def compile_layered(source, role: str, bind, **kw) -> LayeredCompiled:
    """Compile the lower protocol of a layered score for the chip in the role that `role` maps to (roles map by
    position), and build the host-side codec of the upper grammar. Keyword arguments go to compile_score."""
    upper = source if isinstance(source, Score) else parse(source)
    if upper.over is None:
        raise CompileError("E-LAYER", f"'{upper.name}' is not layered (no 'over'): use compile_score")
    if role not in upper.roles:
        raise CompileError("E-NAMES", f"unknown role '{role}' (roles: {', '.join(upper.roles)})")
    es = errors(upper)
    if es:
        raise CompileError(es[0].code, "; ".join(map(str, es)))
    lower, carrier, payload = lower_of(upper)
    lrole = lower.roles[upper.roles.index(role)]
    c = compile_score(lower, lrole, bind, **kw)
    return LayeredCompiled(upper, c, ByteCodec(upper), lrole, payload.name)
