"""Program image: ordered host writes (SPEC v2 9), JSON image format and SPI byte streams.

An image is a JSON object::

    {"format": "metronome-image", "version": 2, "machine_version": 2, "clock_hz": 60000000.0,
     "program": [{"core": 0, "addr": 0, "words": ["0x...", ...]}],        # informational copy of the program words
     "writes":  [{"addr": 8192, "data": "7000", "note": "L0.INC"}, ...],  # THE ordered host write list
     "labels":  {"idle": [0, 0]}}

`writes` is complete and ordered.  Replaying it over the SPI link configures the chip.

D24 (no two configuration writes in consecutive cycles): the SPI link completes at most one byte per 8 SCK rising
edges, and SCK is at most clk/16, so consecutive host writes are at least 128 cycles apart.  The image relies on
nothing else: it never asks for a faster path, and `min_write_gap_cycles` gives the spacing for a given SCK rate.
Hold CS_N high and wait a few cycles after reset: a configuration write in the two cycles after `rst_q` rises is
ignored (SPEC v2 1).
"""
from __future__ import annotations

import json
from pathlib import Path

from ._md import M
from .model import Program

IMAGE_FORMAT = "metronome-image"
IMAGE_VERSION = 2
CMD_WRITE, CMD_READ = 0x02, 0x03
HM = M.HOST_MAP


def _rev(table: dict) -> dict:
    return {name: (off, size) for off, (name, size, _acc, _doc) in table.items()}


LINE_R, THREAD_R, LFSR_R, STREAM_R, OUT_R, CTRL_R, LRT_R, TRT_R, SRT_R = (
    _rev(t) for t in (M.LINE_REGS, M.THREAD_REGS, M.LFSR_REGS, M.STREAM_REGS, M.OUT_REGS, M.CTRL_REGS, M.LRT_REGS,
                      M.TRT_REGS, M.SRT_REGS))


def _addr(base: str, stride: str | None, i: int, regs: dict, reg: str) -> int:
    return HM[base] + (M.HOST_STRIDE[stride] * i if stride else 0) + regs[reg][0]


def line_addr(l, reg): return _addr("LINE_BASE", "LINE", l, LINE_R, reg)
def thread_addr(t, reg): return _addr("THREAD_BASE", "THREAD", t, THREAD_R, reg)
def lfsr_addr(k, reg): return _addr("LFSR_BASE", "LFSR", k, LFSR_R, reg)
def stream_addr(k, reg): return _addr("STREAM_BASE", "STREAM", k, STREAM_R, reg)
def out_addr(o, reg): return _addr("OUT_BASE", "OUT", o, OUT_R, reg)
def ctrl_addr(reg): return _addr("CTRL_BASE", None, 0, CTRL_R, reg)
def lrt_addr(l, reg): return _addr("LRT_BASE", "LRT", l, LRT_R, reg)
def trt_addr(t, reg): return _addr("TRT_BASE", "TRT", t, TRT_R, reg)
def srt_addr(k, reg): return _addr("SRT_BASE", "SRT", k, SRT_R, reg)


def prog_addr(core: int, word: int) -> int:
    return HM["PROG_BASE"] + core * M.HOST_STRIDE["PROG_CORE"] + word * 8


# Register byte packing.  The bit layouts are those documented in machine.LINE_REGS / THREAD_REGS / STREAM_REGS /
# OUT_REGS; tests/test_image.py checks them against the v2 model's decode of the written bytes.
def pack_edge(ln) -> int: return ln.edge_pin | (ln.edge_pol << 4) | (ln.wen << 6) | (ln.follow << 7)
def pack_t0edge(ln) -> int: return ln.t0_pin | (ln.t0_pol << 4) | (ln.t0src << 6)
def pack_hold(ln) -> int: return ln.hpin | (ln.hlvl << 4) | (ln.htap << 5) | (ln.hen << 7)
def pack_thread_cfg(t) -> int: return t.core | (t.bound_line << 1) | (M.TRIG_ID[t.trigger] << 3)


class _W:
    def __init__(self):
        self.writes: list = []

    def reg(self, addr: int, value: int, size: int, note: str) -> None:
        if not 0 <= value < (1 << (8 * size)):
            raise ValueError(f"{note}: value {value} does not fit {size} byte(s)")
        self.writes.append((addr, value.to_bytes(size, "little"), note))

    def blob(self, addr: int, data: bytes, note: str) -> None:
        self.writes.append((addr, bytes(data), note))


def host_writes(prog: Program) -> list:
    """The ordered (address, bytes, note) list that configures the chip for `prog`.

    Order: program memory, data RAM, LFSR polynomials, stream and output configuration, line configuration, thread
    configuration (CFG last), thread PC and EN, stream rewind (MODE/START apply at a rewind), line PHASE, line CTL
    (starts the lines), IRQEN, CTRL.RUN last.  Program memory is written while RUN_global is 0 (SPEC v2 9a.8).
    """
    w = _W()
    for core in range(M.N_CORES):
        words = prog.words(core)
        run: list = []
        for a in sorted(words) + [None]:
            if run and (a is None or a != run[-1] + 1):
                blob = b"".join(words[x].to_bytes(8, "little") for x in run)
                w.blob(prog_addr(core, run[0]), blob, f"core {core} program words 0x{run[0]:02X}..0x{run[-1]:02X}")
                run = []
            if a is not None:
                run.append(a)
    for addr, data in prog.data:
        w.blob(HM["DATA_BASE"] + addr, data, f"data RAM {addr}..{addr + len(data) - 1}")
    for n, lf in sorted(prog.lfsrs.items()):
        w.reg(lfsr_addr(n, "POLY"), lf.poly, LFSR_R["POLY"][1], f"LF{n}.POLY")
    for k, s in sorted(prog.streams.items()):
        w.reg(stream_addr(k, "MODE"), s.rx | (s.msb << 1), 1, f"S{k}.MODE")
        w.reg(stream_addr(k, "START"), s.start, 2, f"S{k}.START")
        w.reg(stream_addr(k, "LEN"), s.len, 2, f"S{k}.LEN")
        w.reg(stream_addr(k, "MARK"), s.mark, 2, f"S{k}.MARK")
    for o, oc in sorted(prog.outs.items()):
        bound = oc.line_ is not None
        w.reg(out_addr(o, "BIND"), (oc.line_ or 0) | (int(bound) << 2), 1, f"O{o}.BIND")
        w.reg(out_addr(o, "SEL"), oc.sel[0] | (oc.sel[1] << 2) | (oc.sel[2] << 4), 1, f"O{o}.SEL")
        w.reg(out_addr(o, "LUT"), oc.lut, 4, f"O{o}.LUT")
        if o < M.N_OE_PINS:
            w.reg(out_addr(o, "OE"), oc.oe, 4, f"O{o}.OE")
    for l, ln in sorted(prog.lines.items()):
        w.reg(line_addr(l, "INC"), ln.inc, 2, f"L{l}.INC")
        w.reg(line_addr(l, "MOD"), ln.mod, 2, f"L{l}.MOD")
        for k in range(3):
            w.reg(line_addr(l, f"T{k}"), ln.tap(k), 2, f"L{l}.T{k}")
        w.reg(line_addr(l, "PRE"), ln.pre, 2, f"L{l}.PRE")
        w.reg(line_addr(l, "WLO"), ln.wlo, 2, f"L{l}.WLO")
        w.reg(line_addr(l, "WHI"), ln.whi, 2, f"L{l}.WHI")
        w.reg(line_addr(l, "EDGE"), pack_edge(ln), 1, f"L{l}.EDGE")
        w.reg(line_addr(l, "T0EDGE"), pack_t0edge(ln), 1, f"L{l}.T0EDGE")
        w.reg(line_addr(l, "PINS"), ln.pina | (ln.pinb << 4), 1, f"L{l}.PINS")
        w.reg(line_addr(l, "SNAP"), ln.snap, 1, f"L{l}.SNAP")
        w.reg(line_addr(l, "LUT0"), ln.lut0, 4, f"L{l}.LUT0")
        w.reg(line_addr(l, "LUT1"), ln.lut1, 4, f"L{l}.LUT1")
        if ln.hen:
            w.reg(line_addr(l, "HOLD"), pack_hold(ln), 1, f"L{l}.HOLD")
    for n, t in sorted(prog.threads.items()):
        for k in (0, 1):
            if t.watch[k]:
                w.reg(thread_addr(n, f"W{k}C"), M.GUARD_ID[t.watch[k][0]], 1, f"T{n}.W{k}C")
                w.reg(thread_addr(n, f"W{k}H"), t.watch_addr[k], 1, f"T{n}.W{k}H")
        w.reg(thread_addr(n, "CFG"), pack_thread_cfg(t), 1, f"T{n}.CFG")
        if t.start_addr is not None:
            w.reg(trt_addr(n, "PC"), t.start_addr, 1, f"T{n}.PC")
        w.reg(trt_addr(n, "STAT"), int(t.enable) << 3, 1, f"T{n}.EN")      # bit 3 = EN; bits 4, 5 = 0 clear nothing
    for k in sorted(prog.streams):
        w.reg(srt_addr(k, "CTL"), 1, 1, f"S{k}.REWIND")
    for l, ln in sorted(prog.lines.items()):
        if ln.phase is not None:
            w.reg(lrt_addr(l, "PHASE"), ln.phase, 2, f"L{l}.PHASE")
    for l, ln in sorted(prog.lines.items()):
        if ln.ctl:
            w.reg(lrt_addr(l, "CTL"), ln.ctl, 1, f"L{l}.CTL")
    if prog.irqen is not None:
        w.reg(ctrl_addr("IRQEN"), prog.irqen, 1, "CTRL.IRQEN")
    if prog.run:
        w.reg(ctrl_addr("RUN"), 1, 1, "CTRL.RUN")
    return w.writes


def build_image(prog: Program) -> dict:
    program = []
    for core in range(M.N_CORES):
        words = prog.words(core)
        run: list = []
        for a in sorted(words) + [None]:
            if run and (a is None or a != run[-1] + 1):
                program.append({"core": core, "addr": run[0], "words": [f"0x{words[x]:016X}" for x in run]})
                run = []
            if a is not None:
                run.append(a)
    return {"format": IMAGE_FORMAT, "version": IMAGE_VERSION, "machine_version": M.VERSION,
            "clock_hz": prog.clock_hz, "source": prog.source_name, "program": program,
            "writes": [{"addr": a, "data": d.hex(), "note": n} for a, d, n in host_writes(prog)],
            "labels": {k: list(v) for k, v in prog.labels.items()}}


def write_image(image: dict, path) -> None:
    Path(path).write_text(json.dumps(image, indent=1) + "\n", encoding="utf-8")


def read_image(path) -> dict:
    img = json.loads(Path(path).read_text(encoding="utf-8"))
    if img.get("format") != IMAGE_FORMAT:
        raise ValueError(f"{path}: not a {IMAGE_FORMAT} file")
    if img.get("machine_version") != M.VERSION:
        raise ValueError(f"{path}: image is for machine version {img.get('machine_version')}, tools are {M.VERSION}")
    return img


def image_writes(image: dict) -> list:
    return [(w["addr"], bytes.fromhex(w["data"])) for w in image["writes"]]


def min_write_gap_cycles(sck_divider: int = 16) -> int:
    """Cycles between two consecutive host writes over SPI with SCK = clk / sck_divider: 8 SCK periods per byte
    (>= 128 cycles at the maximum rate), so D24 (no consecutive configuration writes) holds by construction."""
    if sck_divider < 16:
        raise ValueError("SCK above clk/16 is outside SPEC v2 9")
    return 8 * sck_divider


# -- SPI host link (mode 0): command, 16-bit big-endian address, data -------------------------------------------
def spi_write_frame(addr: int, data: bytes) -> bytes:
    if not 0 <= addr <= 0xFFFF:
        raise ValueError("address out of range")
    return bytes([CMD_WRITE, addr >> 8, addr & 0xFF]) + bytes(data)


def spi_read_frame(addr: int, n: int) -> bytes:
    """MOSI bytes of a read: command, address, then n dummy bytes during which MISO carries the data."""
    return bytes([CMD_READ, addr >> 8, addr & 0xFF]) + bytes(n)


def spi_streams(writes: list, coalesce: bool = True, max_frame: int | None = None) -> list:
    """(addr, bytes[, note]) writes -> SPI frames, merging address-contiguous neighbours into one frame."""
    merged: list = []
    for item in writes:
        addr, data = item[0], bytes(item[1])
        if coalesce and merged and merged[-1][0] + len(merged[-1][1]) == addr and \
                (max_frame is None or len(merged[-1][1]) + len(data) <= max_frame):
            merged[-1] = (merged[-1][0], merged[-1][1] + data)
        else:
            merged.append((addr, data))
    frames = []
    for addr, data in merged:
        step = max_frame or max(len(data), 1)
        for i in range(0, len(data), step):
            frames.append(spi_write_frame(addr + i, data[i:i + step]))
    return frames


def image_to_spi(image: dict, **kw) -> list:
    return spi_streams(image_writes(image), **kw)


def apply_writes(writes: list, mem: dict | None = None) -> dict:
    mem = {} if mem is None else mem
    for item in writes:
        for i, b in enumerate(item[1]):
            mem[item[0] + i] = b
    return mem
