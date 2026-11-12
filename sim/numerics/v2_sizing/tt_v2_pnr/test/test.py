# SPDX-FileCopyrightText: © 2024 Tiny Tapeout
# SPDX-License-Identifier: Apache-2.0
"""Smoke test of the Metronome v2 place-and-route sizing top (tt_um_brentius_metronome), RTL and gate level.
It only uses the chip's pins, so it runs unchanged on the post-route netlist.

Over the SPI host link (docs/info.md has the sizing host map) it loads a short v2 program into core 0, a data byte
into the data RAM, and the configuration of thread 0 and stream S0 into the latch bank; then it sets RUN and rings
thread 0's doorbell. Checks:
  1. sequential moves: R0 (uio_out) goes 0x00 -> 0x11 -> 0x33 and R1 (uio_oe) becomes 0x22;
  2. a taken conditional jump (on flag F2, set by the instruction before) skips a move of 0xEE to R0, which must
     never appear on uio_out;
  3. stream bits reach a pin: each further doorbell runs one instruction that moves S0.BIT to L.DBIT of line 0
     (uo_out[2]) and advances the stream, so uo_out[2] shows 0xA5 LSB first;
  4. host reads: the ID byte 0xA2 and the data RAM byte read back over MISO.
The instruction words come from a small assembler on the field positions of code/md2/machine.py.
"""

import importlib.util
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge


def _load_machine():
    """Import code/md2/machine.py by path (the repository copy if this project sits in the repository, else the
    vendored copy test/md2_machine.py)."""
    here = Path(__file__).resolve().parent
    path = here / "md2_machine.py"
    for parent in here.parents:
        cand = parent / "code" / "md2" / "machine.py"
        if cand.is_file():
            path = cand
            break
    spec = importlib.util.spec_from_file_location("md2_machine", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["md2_machine"] = mod
    spec.loader.exec_module(mod)
    return mod


M = _load_machine()

SCK, CS_N, MOSI = 0, 1, 2   # ui_in bits (host SPI target, mode 0)
HALF = 8                    # SCK half period in clk cycles (SCK = clk / 16)

# sizing host map (docs/info.md)
A_PROG = 0x0000             # + core * 0x800 + 8 * word + byte
A_DATA = 0x1000
A_CFG = 0x2000
A_CFG_S0 = A_CFG + 48
A_RUN, A_DOORBELL, A_ID, A_STATUS = 0x2400, 0x2401, 0x2402, 0x2403


# ------------------------------------------------------------------------------------------------ assembler
def put(word, name, value):
    f = M.FIELD[name]
    assert 0 <= value < (1 << f.width), (name, value)
    return word | (value << f.lsb)


def insn(moves=(), imm=0, pause=False, jmode="next", jcond="TRUE", cond="TRUE"):
    """One 64-bit instruction. moves: up to three (src, dst) or (guard, src, dst); unused slots never execute."""
    w = put(0, "pause", int(pause))
    w = put(w, "jmode", M.JMODES[jmode])
    w = put(w, "imm", imm)
    w = put(w, "cond", M.GUARD_ID[cond])
    w = put(w, "jcond", M.JGUARD_ID[jcond])
    assert len(moves) <= M.N_MOVES
    for m in range(M.N_MOVES):
        if m < len(moves):
            mv = moves[m]
            guard, src, dst = mv if len(mv) == 3 else ("always", *mv)
        else:
            guard, src, dst = "never", "ZERO", "NULL"
        w = put(w, f"m{m}_guard", M.GUARDS[guard])
        w = put(w, f"m{m}_src", M.SRC_ID[src])
        w = put(w, f"m{m}_dst", M.DST_ID[dst])
    return w


PROGRAM = [
    insn([("IMM", "S0.CTL")], imm=0x01),                          # 0: rewind stream S0
    insn([("IMM", "R0")], imm=0x11),                              # 1: R0 := 0x11
    insn([("IMM", "R1"), ("IMM", "FLAGS.SET")], imm=0x22),        # 2: R1 := 0x22, set F2 (bus[3:0] = 2)
    insn(jmode="if", jcond="F2", imm=5),                          # 3: jump to 5 if F2 (taken)
    insn([("IMM", "R0")], imm=0xEE),                              # 4: wrong path, must not execute
    insn([("IMM", "R0")], imm=0x33, pause=True),                  # 5: R0 := 0x33, pause (PC := 6)
    insn([("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV")],              # 6: one stream bit to line 0, advance;
         imm=6, pause=True, jmode="always"),                      #    pause with PC := 6
]
STREAM_BYTE = 0xA5


def program_bytes(core, words):
    """(address, byte) pairs of the sizing host map: byte b of word w at 0x0000 + core*0x800 + 8*w + b."""
    return [(A_PROG + core * 0x800 + 8 * w + b, (word >> (8 * b)) & 0xFF)
            for w, word in enumerate(words) for b in range(8)]


def thread_cfg(core=0, line=0, en=1, trig="NONE", start=0):
    """Eight latch bytes of one thread: {EN, LINE, CORE}, TRIG, W0C, W1C, W0H, W1H, START PC, reserved."""
    return [core | (line << 1) | (en << 3), M.TRIG_ID[trig], 0, 0, 0, 0, start, 0]


def stream_cfg(mode=0, msb=0, start=0, length=1, mark=0):
    return [mode | (msb << 1), start & 0xFF, start >> 8, length & 0xFF, length >> 8, mark & 0xFF, mark >> 8, 0]


# ------------------------------------------------------------------------------------------------ SPI host
class Host:
    def __init__(self, dut):
        self.dut = dut

    async def _drive(self, sck, cs_n, mosi):
        self.dut.ui_in.value = (sck << SCK) | (cs_n << CS_N) | (mosi << MOSI)
        await ClockCycles(self.dut.clk, HALF)

    async def frame(self, tx):
        """One chip-select frame, MSB first; MOSI changes while SCK is low. Returns MISO sampled at each rising
        edge, one byte per transmitted byte."""
        await FallingEdge(self.dut.clk)
        await self._drive(0, 0, 0)
        rx = []
        for b in tx:
            v = 0
            for i in range(7, -1, -1):
                bit = (b >> i) & 1
                await self._drive(0, 0, bit)
                v = (v << 1) | (int(self.dut.uo_out.value) & 1)
                await self._drive(1, 0, bit)
            rx.append(v)
        await self._drive(0, 0, 0)
        await self._drive(0, 1, 0)
        return rx

    async def write(self, addr, data):
        await self.frame([0x02, addr >> 8, addr & 0xFF, *data])

    async def read(self, addr, n):
        rx = await self.frame([0x03, addr >> 8, addr & 0xFF] + [0] * n)
        return rx[3:]


async def watch_r0(dut, seen):
    """Record each new value of uio_out (R0)."""
    while True:
        await RisingEdge(dut.clk)
        try:
            v = int(dut.uio_out.value)
        except ValueError:
            continue
        if not seen or seen[-1] != v:
            seen.append(v)


@cocotb.test()
async def test_project(dut):
    dut._log.info("Start")
    # About 60 MHz, the clock the demo board's RP2350 supplies (info.yaml clock_hz); an even number of ps.
    cocotb.start_soon(Clock(dut.clk, 16666, unit="ps").start())

    dut._log.info("Reset")
    dut.ena.value = 1
    dut.ui_in.value = 1 << CS_N
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 10)

    host = Host(dut)
    seen = []
    cocotb.start_soon(watch_r0(dut, seen))

    assert await host.read(A_ID, 1) == [0xA2], "ID byte"

    # program for core 0, one frame per word (auto-increment within the frame)
    pb = program_bytes(0, PROGRAM)
    for w in range(len(PROGRAM)):
        chunk = pb[8 * w: 8 * w + 8]
        await host.write(chunk[0][0], [b for _, b in chunk])
    await host.write(A_DATA, [STREAM_BYTE])
    assert await host.read(A_DATA, 1) == [STREAM_BYTE], "data RAM readback"
    await host.write(A_CFG, thread_cfg(core=0, line=0, en=1, start=0))
    await host.write(A_CFG_S0, stream_cfg(mode=0, msb=0, start=0, length=1))
    await host.write(A_RUN, [0x01])
    await host.write(A_DOORBELL, [0x01])
    await ClockCycles(dut.clk, 40)

    dut._log.info(f"R0 values seen: {[hex(v) for v in seen]}")
    assert 0xEE not in seen, "the move on the jump's wrong path executed"
    assert seen[-3:] == [0x00, 0x11, 0x33], f"R0 sequence {[hex(v) for v in seen]}"
    assert int(dut.uio_oe.value) == 0x22, "R1 (uio_oe)"

    bits = []
    for _ in range(8):
        await host.write(A_DOORBELL, [0x01])
        await ClockCycles(dut.clk, 20)
        bits.append((int(dut.uo_out.value) >> 2) & 1)
    expect = [(STREAM_BYTE >> i) & 1 for i in range(8)]
    dut._log.info(f"stream bits on uo_out[2]: {bits}")
    assert bits == expect, f"stream bits {bits}, expected {expect}"

    status = (await host.read(A_STATUS, 1))[0]
    assert status & 0x40, f"S0.END expected in status {status:#04x}"
    assert not status & 0x80, f"S0 starved in status {status:#04x}"
    cfg = getattr(dut.user_project, "u_cfg", None)      # RTL only; the netlist has no hierarchy
    if cfg is not None and hasattr(cfg, "wr_spacing_err"):
        assert int(cfg.wr_spacing_err.value) == 0, "host wrote the latch bank on consecutive cycles"
        dut._log.info("latch write spacing rule held over every host write")
    dut._log.info("Pass")
