"""Smoke test of the Lean `machine-sim` executable (Metronome.Machine.step).

Drives the pins only: reset, then SPI (ui_in[0] SCK, [1] CS_N, [2] MOSI; mode 0; SCK = clk/16) to
  1. read ID (0x2407, expect 0xA2),
  2. write a two-instruction program into core 0
       word 0: ACC.LD  IMM 5
       word 1: ACC.ADD IMM 1; pause; jump always to word 1 (imm is both the value and the target)
  3. configure thread 0 (core 0, line 0, TRIG = ALWAYS), set its EN, set CTRL.RUN,
and checks that ACC becomes 5 and then grows by 1 per burst, and that PMEM0.sum matches the bytes written.

Usage: python code/tests/lean/machine_smoke.py [path-to-machine-sim]
"""
from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MJ = json.loads((HERE.parents[2] / "code" / "md2" / "machine.json").read_text(encoding="utf-8"))


def exe_path() -> Path:
    if len(sys.argv) > 1:
        return Path(sys.argv[1])
    b = HERE / ".lake" / "build" / "bin"
    return b / ("machine-sim.exe" if (b / "machine-sim.exe").exists() else "machine-sim")


class Sim:
    def __init__(self, exe: Path):
        self.p = subprocess.Popen([str(exe)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.last: dict = {}
        self.cycles = 0
        self.accs: list[int] = []

    def cycle(self, ui: int, uio: int = 0, rst_n: int = 1) -> dict:
        self.p.stdin.write(f"{ui} {uio} {rst_n}\n")
        self.p.stdin.flush()
        self.last = json.loads(self.p.stdout.readline())
        self.cycles += 1
        if not self.accs or self.accs[-1] != self.last["A"]:
            self.accs.append(self.last["A"])
        return self.last

    def close(self):
        self.p.stdin.write("quit\n")
        self.p.stdin.flush()
        self.p.wait(timeout=10)


SCK, CSN, MOSI = 1, 2, 4
HALF = 8  # SCK half period in clocks: clk/16


def spi_xfer(sim: Sim, data: list[int]) -> list[int]:
    """One transaction (CS low around all bytes); returns the bytes read on MISO (uo_out[0])."""
    out = []
    for _ in range(HALF):
        sim.cycle(CSN)
    for _ in range(HALF):
        sim.cycle(0)
    for byte in data:
        r = 0
        for i in range(7, -1, -1):
            m = MOSI if (byte >> i) & 1 else 0
            for _ in range(HALF):
                sim.cycle(m)
            r = (r << 1) | (sim.last["uo_out"] & 1)   # sample before the rising edge
            for _ in range(HALF):
                sim.cycle(m | SCK)
        out.append(r)
    for _ in range(HALF):
        sim.cycle(0)
    for _ in range(HALF):
        sim.cycle(CSN)
    return out


def spi_write(sim: Sim, addr: int, data: list[int]):
    spi_xfer(sim, [0x02, addr >> 8, addr & 0xFF, *data])


def spi_read(sim: Sim, addr: int, n: int) -> list[int]:
    return spi_xfer(sim, [0x03, addr >> 8, addr & 0xFF] + [0] * n)[3:]


def insn(**f) -> int:
    w = 0
    for name, val in f.items():
        lsb, width = MJ["fields"][name]
        assert 0 <= val < (1 << width), (name, val)
        w |= val << lsb
    return w


def main() -> int:
    t0 = time.time()
    src, dst, trig = MJ["src"].index, MJ["dst"].index, MJ["triggers"].index
    g, jm = MJ["guards"], MJ["jmodes"]
    hm, hb = MJ["host_map"], MJ["host_blocks"]
    never = dict(m1_guard=g["never"], m2_guard=g["never"])
    w0 = insn(imm=5, m0_guard=g["always"], m0_src=src("IMM"), m0_dst=dst("ACC.LD"), **never)
    # the immediate is shared by the jump target and the move source: word 1 adds imm and jumps to imm
    w1 = insn(pause=1, jmode=jm["always"], imm=1, m0_guard=g["always"], m0_src=src("IMM"),
              m0_dst=dst("ACC.ADD"), **never)
    prog = list(w0.to_bytes(8, "little")) + list(w1.to_bytes(8, "little"))

    sim = Sim(exe_path())
    ok = True
    for _ in range(4):
        sim.cycle(CSN, 0, 0)
    for _ in range(4):
        sim.cycle(CSN)
    ident = spi_read(sim, hm["CTRL_BASE"] + 0x07, 1)
    print(f"ID read: {ident[0]:#04x} (expect 0xa2)")
    ok &= ident == [0xA2]

    spi_write(sim, hm["PROG_BASE"], prog)
    psum = sum(b * (i + 1) for i, b in enumerate(prog)) % (1 << 32)
    print(f"PMEM0.sum = {sim.last['PMEM0.sum']} (expect {psum})")
    ok &= sim.last["PMEM0.sum"] == psum

    thr = hb["THREAD"]["base"]
    spi_write(sim, thr + 0x00, [(trig("ALWAYS") << 3) | (0 << 1) | 0])     # CORE 0, LINE 0, TRIG ALWAYS
    spi_write(sim, hb["TRT"]["base"] + 0x01, [0x08])                      # thread 0 EN
    print(f"T0.EN = {sim.last['T0.EN']}  A = {sim.last['A']}")
    ok &= sim.last["T0.EN"] == 1 and sim.last["A"] == 0
    spi_write(sim, hm["CTRL_BASE"] + 0x00, [0x01])                        # RUN_global
    for _ in range(40):
        d = sim.cycle(CSN)
    accs = sim.accs
    print(f"ACC sequence after RUN: {accs}")
    ok &= accs[:2] == [0, 5] and all(b - a == 1 for a, b in zip(accs[1:], accs[2:])) and len(accs) > 4
    print(f"cycles: {sim.cycles}, C0.FPC={d['C0.FPC']} T0.PC={d['T0.PC']} T0.OVR={d['T0.OVR']} "
          f"CONFLICT={d['CONFLICT']}")
    sim.close()
    print(f"{'PASS' if ok else 'FAIL'} ({time.time() - t0:.2f}s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
