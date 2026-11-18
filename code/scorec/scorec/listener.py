"""Listener projection (V3 plan C, rival-ideas section 2.3): a third, input-only role projected from the same score.

The listener drives no pin.  It samples the wire(s), checks every terminal of the grammar and appends one *record* per
frame (UART, Ethernet receive: `kind frame`) or per chip-select transaction (SPI) to a log in data RAM.  The host reads
the log and decodes it with `ListenerDecoder`.  Everything here is derived from the parsed score; the reference codec
is only used by the tests, as an oracle.

Record layout (data RAM, from `log_base`, little-endian bytes; the layout is also in `compiled.host["listener"]`):

  frame protocols (UART, Ethernet): 3 bytes   status, ts_lo, ts_hi
  SPI                               5 bytes   status, bits_lo, bits_hi, ts_lo, ts_hi

* `status`  bit 0 constant mismatch (preamble, SFD), bit 2 CRC error, bits 3..7 violation at the k-th checked terminal
            of the grammar (`positions` in the compile result names it and gives its beat within the frame).  SPI:
            bit 1 framing (the transaction ended inside a byte), other bits reserved.  0 means the frame was clean.
* `ts`      the raw value of a free-running 16-bit *down* counter, ticked once per ruler tick (`tick_beats` beats, default one or more so a tick is at least ~48
            chip cycles, for frame protocols; `tick_cycles` chip cycles for SPI), set to 0xFFFF at start.  Elapsed ticks at the record
            = 0xFFFF - raw, taken when the frame/transaction ended.  The ruler is free running, so a timestamp is
            quantised to one tick.  It wraps after 65535 ticks (the decoder unwraps successive records).
* `bits`    SPI: 0xFFFF - raw, the number of SCK rising edges seen while selected.

The log holds `log_records` records and then stops logging (later frames are dropped from the log; the receive stream
and the status mailbox still work).  The host must read it before it fills.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .emit import imm
from .plan import CompileError

LOG_RECORDS = 341        # 3-byte records in data RAM 0x000..0x3FF (the transmit region, unused by a listener)
LOG_BYTES_MAX = 0x400


def add_ruler(x, inc, mod, line=1, thread=1, core=1):
    """Free-running timestamp ruler: `line` ticks every inc/mod chip cycles, a thread decrements CNT1 (16-bit)."""
    x.b.block(f".line {line}", [f"inc {inc}", f"mod {mod}", "taps - - -", "ctl run"])
    k = x.b.cores[core]
    k.label("tick")
    k.i(["ZERO -> CNT1.DEC"], goto="tick", pause=True, note="listener ruler: one tick per beat")
    x.init_moves += [imm(255, "CNT1.LO"), imm(255, "CNT1.HI")]
    return [(thread, core, line, f"L{line}.BEAT", "tick")]


def add_log_init(x, record_bytes):
    n = LOG_BYTES_MAX // record_bytes
    x.init_moves += [imm(n & 255, "CNT2.LO"), imm(n >> 8, "CNT2.HI"), "ZERO -> P0.AL", "ZERO -> P0.AH"]
    return n


def emit_log_record(emit, srcs, ruler_regs=True):
    """Append one record: the sources in `srcs`, then the ruler (two bytes).  `emit(moves, when=...)` appends one
    instruction.  CNT2 is the remaining record budget (a full log drops the record, the guard is the same for every
    byte because CNT2 only changes in the last instruction)."""
    emit(["CNT1.LO -> R0", "CNT1.HI -> R1"], note="listener: snapshot the ruler")
    for sname in srcs:
        emit([f"! {sname} -> P0.W"], when="CNT2.Z", note="log record byte")
    emit(["! R0 -> P0.W"], when="CNT2.Z")
    emit(["! R1 -> P0.W", "! ZERO -> CNT2.DEC"], when="CNT2.Z", note="log record complete")


# ---- host side ---------------------------------------------------------------------------------------------------------
@dataclass
class Violation:
    code: str                 # 'framing' (last terminal of a frame, or a transaction ending inside a byte) | 'grammar'
                              # (an earlier terminal) | 'crc' | 'const'
    terminal: str | None      # the grammar terminal that failed ('bit(1)'), when known
    beat_in_frame: int | None
    beat: int | None          # absolute ruler tick at which the failed terminal was sampled (+-1 tick)


@dataclass
class Record:
    index: int
    status: int
    end_tick: int             # unwrapped ruler ticks at the end of the frame
    bits: int | None          # SPI payload bits
    violations: list = field(default_factory=list)

    @property
    def clean(self):
        return not self.violations


class ListenerDecoder:
    """Decodes the listener's log (and, for SPI, its two receive streams) into records and violations.

    `decode_log(log_bytes)` takes the bytes of the log region (the host reads data RAM from `log_base`).
    """

    def __init__(self, info: dict):
        self.info = info
        self.size = info["record_bytes"]
        self.positions = {p["flag"]: p for p in info.get("positions", [])}
        self.protocol = info["protocol"]

    def decode_log(self, log: bytes, n_records: int | None = None) -> list[Record]:
        out, wrap, last = [], 0, None
        total = len(log) // self.size if n_records is None else n_records
        for i in range(total):
            r = log[i * self.size:(i + 1) * self.size]
            if len(r) < self.size:
                break
            status = r[0]
            raw = r[-2] | (r[-1] << 8)
            tick = 0xFFFF - raw
            if last is not None and tick + wrap * 65536 < last:
                wrap += 1
            t = tick + wrap * 65536
            last = t
            bits = None
            if self.protocol == "spi":
                bits = 0xFFFF - (r[1] | (r[2] << 8))
            rec = Record(i, status, t, bits)
            rec.violations = self._violations(status, t)
            out.append(rec)
        return out

    def _violations(self, status, end_tick):
        v = []
        if self.protocol == "spi":
            if status & 2:
                v.append(Violation("framing", "transaction ends inside a byte", None, end_tick))
            return v
        fb = self.info.get("frame_beats")
        if status & 1:
            v.append(Violation("const", "constant bits (preamble/SFD)", None, end_tick))
        if status & 4:
            v.append(Violation("crc", "crc field", fb, end_tick))
        for flag in range(3, 8):
            if status & (1 << flag) and flag in self.positions:
                p = self.positions[flag]
                # the record is written when the last terminal is sampled (beat fb-1), so a terminal that sits k beats
                # earlier in the frame was seen k ticks earlier
                tb = self.info.get("tick_beats", 1)
                b = None if fb is None or p["beat"] is None else end_tick - round((fb - 1 - p["beat"]) / tb)
                last = fb is not None and p["beat"] == fb - 1
                v.append(Violation("framing" if last else "grammar", p["terminal"], p["beat"], b))
        return v


def compile_listener(source, bind, *, rate_hz=None, follow_period=None, tick_cycles=None, tick_beats=None,
                     raise_on_check=True, skip_periodic=False):
    """Project the input-only listener role from `source` (score text, path or Score).

    `bind` names input pins only (e.g. 'tx=P5' for UART, 'sck=P1 cs_n=P2 mosi=P0 miso=P3' for SPI).  Returns the usual
    `Compiled`; `compiled.host["listener"]` documents the record layout, `ListenerDecoder(compiled.host["listener"])`
    decodes the log.  Raises `CompileError` for protocols without a listener template (I2C and `arbitrate` are gaps)."""
    from . import api
    from score import parse_bind
    score = api._load(source)
    bindd = parse_bind(bind) if isinstance(bind, str) else dict(bind)
    if any(o is not None for _, o in bindd.values()):
        raise CompileError("E-BIND", "a listener drives no pin: bind input pins P<k> only")
    if any(w.dir == "shared" for w in score.all_wires()):
        raise CompileError("E-UNSUPPORTED", "listener: shared/open-drain buses (I2C bus monitor) are not compiled yet")
    modes = {r: api.plan_clock(score, r, rate_hz, follow_period).mode for r in score.roles}
    followers = [r for r, m in modes.items() if m == "follow"]
    if followers:
        from . import spi_listener
        return spi_listener.compile_spi_listener(score, bindd, followers[0], follow_period, tick_cycles,
                                                 raise_on_check)
    rxroles = [r for r, m in modes.items() if m in ("started", "recovered")]
    if not rxroles:
        raise CompileError("E-UNSUPPORTED", "listener: the score has no receiving role to project from")
    return api.compile_score(score, rxroles[0], bindd, rate_hz=rate_hz, listener=True, tick_beats=tick_beats, skip_periodic=skip_periodic,
                             raise_on_check=raise_on_check)


def split_spi_payload(records, streams: dict[str, bytes]) -> list[dict[str, bytes]]:
    """Slice the SPI listener's receive streams per transaction: each one occupies ceil(bits/8) bytes in every stream."""
    out, pos = [], 0
    for r in records:
        n = -(-(r.bits or 0) // 8)
        out.append({w: b[pos:pos + n] for w, b in streams.items()})
        pos += n
    return out
