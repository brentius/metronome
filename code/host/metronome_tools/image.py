"""Program image: host register writes, JSON image format and SPI byte streams (SPEC 9).

An image is a JSON object::

    {"format": "metronome-image", "version": 1, "machine_version": 1, "clock_hz": 60000000.0,
     "program": [{"core": 0, "addr": 0, "words": ["0x...", ...]}],      # informational copy of the program words
     "writes":  [{"addr": 8192, "data": "7000", "note": "BG0.INC"}, ...], # THE ordered host write list
     "labels":  {"idle": [0, 0]}}

`writes` is complete and ordered (program memory, data RAM, LFSR polynomials, output cells, engines, beat generators
without CTL, beat generator CTL, IRQEN, and finally CTRL.RUN).  Replaying it over the SPI link configures the chip.
"""
from __future__ import annotations

import json
from pathlib import Path

from ._md import M
from .model import Program

IMAGE_FORMAT = "metronome-image"
IMAGE_VERSION = 1
CMD_WRITE, CMD_READ = 0x02, 0x03


def _rev(table: dict) -> dict:
    return {name: (off, size) for off, (name, size) in table.items()}


BG_R, ENG_R, OUT_R, UNIT_R, CTRL_R = (_rev(t) for t in (M.BG_REGS, M.ENG_REGS, M.OUT_REGS, M.UNIT_REGS, M.CTRL_REGS))
HM = M.HOST_MAP


def bg_addr(g: int, reg: str) -> int:
    return HM["BG_BASE"] + g * 0x20 + BG_R[reg][0]


def eng_addr(e: int, reg: str) -> int:
    return HM["ENG_BASE"] + e * 0x20 + ENG_R[reg][0]


def out_addr(o: int, reg: str) -> int:
    return HM["OUT_BASE"] + o * 0x08 + OUT_R[reg][0]


def ctrl_addr(reg: str) -> int:
    return HM["CTRL_BASE"] + CTRL_R[reg][0]


def prog_addr(core: int, word: int) -> int:
    return HM["PROG_BASE"] + core * 0x800 + word * 8


class _W:
    def __init__(self):
        self.writes: list = []

    def reg(self, addr: int, value: int, size: int, note: str) -> None:
        if not 0 <= value < (1 << (8 * size)):
            raise ValueError(f"{note}: value {value} does not fit {size} byte(s)")
        self.writes.append((addr, value.to_bytes(size, "little"), note))

    def blob(self, addr: int, data: bytes, note: str) -> None:
        self.writes.append((addr, bytes(data), note))


def host_writes(prog: Program) -> list[tuple[int, bytes, str]]:
    """The ordered (address, bytes, note) list that configures the chip for `prog`."""
    w = _W()
    # 1. program memory: contiguous runs of 8-byte little-endian words (a word is written when its byte 7 lands)
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
    # 2. data RAM
    for addr, data in prog.data:
        w.blob(HM["DATA_BASE"] + addr, data, f"data RAM {addr}..{addr + len(data) - 1}")
    # 3. LFSR polynomials
    for n, lf in sorted(prog.lfsrs.items()):
        off, size = UNIT_R[f"LF{n}.POLY"]
        w.reg(HM["UNIT_BASE"] + off, lf.poly, size, f"LF{n}.POLY")
    # 4. output cells
    for o, oc in sorted(prog.outs.items()):
        w.reg(out_addr(o, "ENG"), oc.eng, 1, f"O{o}.ENG")
        w.reg(out_addr(o, "LUT"), oc.lut, 2, f"O{o}.LUT")
        if o < M.N_OE_PINS:
            w.reg(out_addr(o, "OE"), oc.oe, 2, f"O{o}.OE")
    # 5. beat generators (all but CTL)
    for g, bg in sorted(prog.bgs.items()):
        w.reg(bg_addr(g, "INC"), bg.inc, 2, f"BG{g}.INC")
        w.reg(bg_addr(g, "MOD"), bg.mod, 2, f"BG{g}.MOD")
        for k in range(3):
            w.reg(bg_addr(g, f"T{k}"), bg.tap(k), 2, f"BG{g}.T{k}")
        w.reg(bg_addr(g, "PRE"), bg.pre, 2, f"BG{g}.PRE")
        w.reg(bg_addr(g, "WLO"), bg.wlo, 2, f"BG{g}.WLO")
        w.reg(bg_addr(g, "WHI"), bg.whi, 2, f"BG{g}.WHI")
        if bg.phase is not None:
            w.reg(bg_addr(g, "PHASE"), bg.phase, 2, f"BG{g}.PHASE")
        w.reg(bg_addr(g, "EDGE"), bg.edge_pin | (bg.edge_pol << 4), 1, f"BG{g}.EDGE")
    # 6. engines (CFG, which holds EN, after the other registers)
    for n, e in sorted(prog.engines.items()):
        if e.start_addr is not None:
            w.reg(eng_addr(n, "PC"), e.start_addr, 1, f"E{n}.PC")
        w.reg(eng_addr(n, "TRIG"), M.TRIG_ID[e.trigger], 1, f"E{n}.TRIG")
        w.reg(eng_addr(n, "PINS"), e.pina | (e.pinb << 4), 1, f"E{n}.PINS")
        w.reg(eng_addr(n, "LUT0"), e.lut0, 2, f"E{n}.LUT0")
        w.reg(eng_addr(n, "LUT1"), e.lut1, 2, f"E{n}.LUT1")
        for k in (0, 1):
            if e.watch[k]:
                w.reg(eng_addr(n, f"W{k}C"), M.GUARD_ID[e.watch[k][0]], 1, f"E{n}.W{k}C")
                w.reg(eng_addr(n, f"W{k}H"), e.watch_addr[k], 1, f"E{n}.W{k}H")
        cfg = int(e.enable) | (e.core << 1) | (e.bg_eff << 2)
        w.reg(eng_addr(n, "CFG"), cfg, 1, f"E{n}.CFG")
    # 7. beat generator CTL (starts the generators)
    for g, bg in sorted(prog.bgs.items()):
        w.reg(bg_addr(g, "CTL"), bg.ctl, 1, f"BG{g}.CTL")
    # 8. IRQ enable, then global RUN last
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


def write_image(image: dict, path: str | Path) -> None:
    Path(path).write_text(json.dumps(image, indent=1) + "\n", encoding="utf-8")


def read_image(path: str | Path) -> dict:
    img = json.loads(Path(path).read_text(encoding="utf-8"))
    if img.get("format") != IMAGE_FORMAT:
        raise ValueError(f"{path}: not a {IMAGE_FORMAT} file")
    if img.get("machine_version") != M.VERSION:
        raise ValueError(f"{path}: image is for machine version {img.get('machine_version')}, tools are {M.VERSION}")
    return img


def image_writes(image: dict) -> list[tuple[int, bytes]]:
    return [(w["addr"], bytes.fromhex(w["data"])) for w in image["writes"]]


# -- SPI host link (mode 0): command, 16-bit big-endian address, data ----------------------------------------
def spi_write_frame(addr: int, data: bytes) -> bytes:
    """One chip-select frame writing `data` to consecutive addresses starting at `addr` (ADDR auto-increments)."""
    if not 0 <= addr <= 0xFFFF:
        raise ValueError("address out of range")
    return bytes([CMD_WRITE, addr >> 8, addr & 0xFF]) + bytes(data)


def spi_read_frame(addr: int, n: int) -> bytes:
    """The MOSI bytes of one read frame: command, address, then n dummy bytes that clock the data out.  The n data
    bytes arrive on MISO in the n bytes after the address (SPEC 9: the read issued when byte 2 completes loads TX at
    the next SCK fall, so MISO carries data byte 0 during byte slot 3).  See `spi_read_result`."""
    return bytes([CMD_READ, addr >> 8, addr & 0xFF]) + bytes(n)


def spi_read_result(miso: bytes, n: int) -> bytes:
    """Extract the n data bytes from the MISO bytes captured during a `spi_read_frame` (slots 3..3+n-1)."""
    return bytes(miso[3:3 + n])


def spi_streams(writes: list, coalesce: bool = True, max_frame: int | None = None) -> list[bytes]:
    """Turn (addr, bytes[, note]) writes into SPI frames, merging address-contiguous neighbours into one frame.
    `max_frame` bounds the data bytes per frame (a frame is one CS_N low period)."""
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


def image_to_spi(image: dict, **kw) -> list[bytes]:
    return spi_streams(image_writes(image), **kw)


def decode_spi(frames: list[bytes]) -> list[tuple[int, bytes]]:
    """Inverse of `spi_streams` for write frames (used by tests and loaders)."""
    out = []
    for f in frames:
        if f[0] != CMD_WRITE:
            raise ValueError(f"not a write frame: command 0x{f[0]:02X}")
        out.append(((f[1] << 8) | f[2], bytes(f[3:])))
    return out


def apply_writes(writes: list, mem: dict | None = None) -> dict:
    """Replay writes into a flat byte map {address: value} (a minimal model of the host-visible address space)."""
    mem = {} if mem is None else mem
    for item in writes:
        for i, b in enumerate(item[1]):
            mem[item[0] + i] = b
    return mem
