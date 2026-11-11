"""Lockstep scenarios running the example programs (uart_tx, uart_rx) with the real assembler and host_writes.

check(trace) decodes the RTL pins (trace[t][3]) with the independent checkers in code/tests/checkers/protocols.py.
The lockstep testbench separately asserts that RTL and reference model agree on every cycle.
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in (ROOT / "code/tests/checkers", ROOT / "code/host", ROOT / "code/md"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from metronome_tools.asm import assemble_file  # noqa: E402
from metronome_tools.image import host_writes  # noqa: E402
from protocols import uart_decode, uart_encode  # noqa: E402
from scenarios import HALF, Scenario, ctrl_reg  # noqa: E402

EX = ROOT / "code/host/examples"
CPB = 60e6 / 115200


class _S(Scenario):
    hi = 0x08           # P8 idles high

    def _spi(self, tx, ui_hi=None, uio=0):
        return super()._spi(tx, self.hi if ui_hi is None else ui_hi, uio)

    def load(self, name):
        for addr, data, _ in host_writes(assemble_file(EX / name)):
            self.write(addr, data)

    def p8(self, levels):
        for lv in levels:
            self.idle(1, ui_hi=lv << 3)


def uart_tx() -> Scenario:
    """3 bytes through HOSTIN, fixed pacing: a write every 10.5 bit times (mailbox is one deep, frame is 10 bits)."""
    s = _S()
    s.reset()
    s.hi = 0x08
    s.load("uart_tx.mas")
    data = [0x55, 0xA3, 0x4B]
    for i, b in enumerate(data):
        s.write(ctrl_reg("HOSTIN"), [b])
        s.idle(int(10.5 * CPB) if i < len(data) - 1 else int(13 * CPB), ui_hi=0x08)
    start = len(s.cycles)

    def check(trace):
        lv = [tr[3][0] >> 2 & 1 for tr in trace]
        frames = uart_decode(lv[100:], CPB)
        assert [f.value for f in frames] == data, [hex(f.value) for f in frames]
        assert not any(f.framing_error for f in frames)
        s.log = f"rtl uart_tx decoded {[hex(f.value) for f in frames]} in {len(trace)} cycles"
    s.check = check
    return s


def _mosi_read(trace, start):
    v = 0
    for k in range(8):
        v = (v << 1) | (trace[start + k * 2 * HALF + 2][3][0] & 1)
    return v


def uart_rx() -> Scenario:
    """Good frame (+2% baud), bad-stop frame, good frame (-2% baud); host reads HOSTSTAT/HOSTOUT after each."""
    s = _S()
    s.reset()
    s.hi = 0x08
    s.load("uart_rx.mas")
    s.idle(100, ui_hi=0x08)
    plan = [(0xA5, 1.02, False), (0x5A, 1.0, True), (0x96, 0.98, False)]
    stat_reads = []
    for byte, scale, bad in plan:
        cpb = CPB * scale
        w = uart_encode(bytes([byte]), cpb, idle_cycles=30)
        if bad:
            w[30 + int(9 * cpb):30 + int(10 * cpb)] = [0] * (int(10 * cpb) - int(9 * cpb))
        s.p8(w)
        n0 = len(s.reads)
        s.read(ctrl_reg("HOSTSTAT"))
        s.read(ctrl_reg("HOSTOUT"))
        stat_reads.append((s.reads[n0][0], s.reads[n0 + 1][0]))
        s.write(ctrl_reg("HOSTSTAT"), [0x02])

    def check(trace):
        got = []
        for st, out in stat_reads:
            stat = _mosi_read(trace, st)
            got.append(_mosi_read(trace, out) if stat & 2 else None)
        assert got == [0xA5, None, 0x96], got
        s.log = f"rtl uart_rx host saw {got} in {len(trace)} cycles"
    s.check = check
    return s


# --------------------------------------------------------------------------------------------------------------
# SPI controller: closed-loop slave
# --------------------------------------------------------------------------------------------------------------
class _Live(_S):
    """Scenario that is also stepped through the reference model while it is built, so a stimulus generator can react
    to the chip's outputs (a mode-0 SPI slave). The recorded cycles are then replayed open-loop on the RTL."""

    def __init__(self):
        super().__init__()
        from metronome import Chip
        self.chip = Chip()
        self.model_trace = []       # (ui, uio, rst, (uo_out, uio_out, uio_oe)) per cycle
        self.done = 0

    def sync(self):
        for t in range(self.done, len(self.cycles)):
            ui, uio, rst = self.cycles[t]
            self.model_trace.append((ui, uio, rst, tuple(self.chip.step(ui, uio, rst))))
        self.done = len(self.cycles)

    def write(self, addr, data):
        super().write(addr, data)
        self.sync()

    def read(self, addr, n=1):
        super().read(addr, n)
        self.sync()

    def slave(self, n, reply):
        """n cycles with CS_N high on the host link; a mode-0 slave answers `reply` on P8 (MISO) MSB first. MISO is
        driven from the CS_N falling edge and advances on each SCK falling edge; it idles high."""
        bit, prev_sck, prev_cs, miso = 8, 0, 1, 1
        for _ in range(n):
            uo = self.model_trace[-1][3][0]
            sck, cs = uo >> 2 & 1, uo >> 4 & 1
            if prev_cs and not cs:
                bit = 7
                miso = reply >> 7 & 1
            elif not cs and prev_sck and not sck:
                bit -= 1
                miso = reply >> bit & 1 if bit >= 0 else 0
            elif cs:
                miso = 1
            prev_sck, prev_cs = sck, cs
            self.idle(1, ui_hi=miso << 3)
            self.sync()


def spi_controller() -> Scenario:
    """Host sends 0xA5, 0x3C, 0xFF through HOSTIN; the slave answers 0x5A, 0xC3, 0x81. Host reads HOSTOUT back."""
    s = _Live()
    s.reset()
    s.sync()
    s.load("spi_controller.mas")
    s.slave(100, 0)
    plan = [(0xA5, 0x5A), (0x3C, 0xC3), (0xFF, 0x81)]
    out_reads = []
    for tx, rx in plan:
        s.write(ctrl_reg("HOSTIN"), [tx])
        s.slave(int(14 * 60), rx)             # a transfer takes 10 beats (600 clocks); allow 14
        n0 = len(s.reads)
        s.read(ctrl_reg("HOSTSTAT"))
        s.read(ctrl_reg("HOSTOUT"))
        out_reads.append((s.reads[n0][0], s.reads[n0 + 1][0]))
        s.write(ctrl_reg("HOSTSTAT"), [0x02])
    s.slave(200, 0)
    s.plan = plan
    s.out_reads = out_reads

    def decode(sck, mosi, miso, cs_n):
        from protocols import spi_decode
        txs = spi_decode(sck, mosi, miso, cs_n, mode=0)
        txs = [t for t in txs if len(t[0]) == 1]
        assert [t[0][0] for t in txs] == [p[0] for p in plan], txs
        assert [t[1][0] for t in txs] == [p[1] for p in plan], txs
        return txs

    s.decode = decode

    def lines(tr):                              # tr: list of (uo_out, ui_in)
        return ([u >> 2 & 1 for u, _ in tr], [u >> 3 & 1 for u, _ in tr], [i >> 3 & 1 for _, i in tr],
                [u >> 4 & 1 for u, _ in tr])
    s.lines = lines

    def check(trace):
        # SPI decode of the RTL pins (SCK=O8 uo[2], MOSI=O9 uo[3], CS_N=O10 uo[4], MISO=P8 ui[3])
        decode(*lines([(tr[3][0], tr[1]) for tr in trace]))
        got = []
        for st, out in out_reads:
            got.append(_mosi_read(trace, out) if _mosi_read(trace, st) & 2 else None)
        assert got == [p[1] for p in plan], got
    s.check = check
    return s


def eth_tx() -> Scenario:
    """One 10BASE-T frame: body in data RAM (length at RAM[0..1]), started with a HOSTIN write; O8 decoded with eth_decode."""
    import zlib
    import machine as m
    from protocols import eth_decode
    s = _S()
    s.hi = 0x00
    s.reset()
    s.load("eth_tx.mas")
    body = bytes.fromhex("0123456789ab" "fedcba987654" "0800") + bytes(range(0x30, 0x30 + 5))
    s.write(m.HOST_MAP["DATA_BASE"], len(body).to_bytes(2, "little") + body)
    s.write(ctrl_reg("HOSTIN"), [1])
    s.idle((len(body) + 14) * 8 * 6 + 200)

    def check(trace):
        lv = [tr[3][0] >> 2 & 1 for tr in trace]
        frames = eth_decode(lv, 6.0)
        assert len(frames) == 1 and frames[0].data == body and frames[0].fcs_ok, frames
        s.log = f"rtl eth_tx fcs {zlib.crc32(body):08x} ok in {len(trace)} cycles"
    s.check = check
    return s
