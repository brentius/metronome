"""Tiny beat-level functional model of one engine, used only to sanity-check example programs in the tests.

It is NOT the reference model and not cycle-accurate: it runs one burst per call, with all moves of an instruction
reading the state at the start of the instruction (SPEC 6) and writing at its end.  Only the ports the examples use
are implemented; anything else raises NotImplementedError.
"""
from __future__ import annotations

import metronome_tools  # noqa: F401  (path setup)
from metronome_tools._md import M


class FuncSim:
    def __init__(self, prog, engine: int = 0):
        self.prog = prog
        self.eng = prog.engines[engine]
        self.code = prog.code[self.eng.core]
        self.pc = self.eng.start_addr or 0
        self.acc = 0
        self.zcn = [1, 0, 0]
        self.r = [0] * M.N_ACC_REGS
        self.flags = 0
        self.sh = [dict(d=0, cnt=0, ln=0, msb=0) for _ in range(M.N_SHIFTERS)]
        self.cnt = [0] * M.N_COUNTERS
        self.inb, self.inv = 0, 0
        self.outq: list[int] = []
        self.staged = 0
        self.committed = 0
        self.ctl_writes: list[tuple[int, int]] = []
        self.stopped = False
        self.ein = 0
        self.stats = {"bursts": 0, "insns": 0}

    # -- helpers
    def _length(self, s):
        return s["ln"] or 8

    def _cond(self, name: str) -> int:
        if name == "TRUE":
            return 1
        if name[0] == "F" and name[1:].isdigit():
            return (self.flags >> int(name[1:])) & 1
        if name.startswith("SH") and name.endswith(".DONE"):
            return int(self.sh[int(name[2])]["cnt"] == 0)
        if name.startswith("SH") and name.endswith(".OUT"):
            return self._shout(self.sh[int(name[2])])
        if name.startswith("CNT") and name.endswith(".Z"):
            return int(self.cnt[int(name[3])] == 0)
        if name == "ACC.Z":
            return self.zcn[0]
        if name == "ACC.C":
            return self.zcn[1]
        if name == "ACC.N":
            return self.zcn[2]
        if name == "E.IN0":
            return self.ein & 1
        if name == "E.IN1":
            return (self.ein >> 1) & 1
        if name == "HOST.INV":
            return self.inv
        if name == "HOST.OUTE":
            return 1
        raise NotImplementedError(name)

    @staticmethod
    def _shout(s):
        return (s["d"] >> 7) & 1 if s["msb"] else s["d"] & 1

    def _src(self, name: str, imm: int) -> int:
        if name == "ZERO":
            return 0
        if name == "IMM":
            return imm
        if name == "E.IN":
            return self.ein & 3
        if name == "FLAGS.LO":
            return self.flags & 0xFF
        if name == "FLAGS.HI":
            return (self.flags >> 8) & 0xFF
        if name == "ACC":
            return self.acc
        if name[0] == "R" and name[1:].isdigit():
            return self.r[int(name[1:])]
        if name.startswith("SH") and name.endswith(".D"):
            return self.sh[int(name[2])]["d"]
        if name.startswith("SH") and name.endswith(".O"):
            return self._shout(self.sh[int(name[2])])
        if name.startswith("CNT") and name.endswith(".LO"):
            return self.cnt[int(name[3])] & 0xFF
        if name.startswith("CNT") and name.endswith(".HI"):
            return self.cnt[int(name[3])] >> 8
        if name == "HOST.IN":
            self.inv = 0
            return self.inb
        raise NotImplementedError(name)

    def _dst(self, name: str, v: int) -> None:
        if name == "NULL":
            return
        if name == "E.SYM":
            self.staged = v & 3
        elif name == "E.STOP":
            self.stopped = True
        elif name == "FLAGS.SET":
            self.flags |= 1 << (v & 15)
        elif name == "FLAGS.CLR":
            self.flags &= ~(1 << (v & 15))
        elif name.startswith("ACC."):
            op = name[4:]
            a = self.acc
            if op == "LD":
                res = v
            elif op == "ADD":
                res = a + v
            elif op in ("SUB", "CMP"):
                res = a - v
            else:
                res = {"AND": a & v, "OR": a | v, "XOR": a ^ v}[op]
            self.zcn = [int((res & 0xFF) == 0), int((res >> 8) & 1) if op == "ADD" else int(a >= v) if op in ("SUB", "CMP") else self.zcn[1], (res >> 7) & 1]
            if op != "CMP":
                self.acc = res & 0xFF
        elif name[0] == "R" and name[1:].isdigit():
            self.r[int(name[1:])] = v
        elif name.startswith("SH"):
            s, op = self.sh[int(name[2])], name[4:]
            if op == "LD":
                s["d"], s["cnt"] = v, self._length(s)
            elif op == "SH":
                s["d"] = ((s["d"] << 1) & 0xFF | (v & 1)) if s["msb"] else ((s["d"] >> 1) | ((v & 1) << 7))
                s["cnt"] = max(s["cnt"] - 1, 0)
            else:
                s["ln"], s["msb"] = v & 15, (v >> 4) & 1
        elif name.startswith("CNT"):
            k, op = int(name[3]), name[5:]
            if op == "LO":
                self.cnt[k] = (self.cnt[k] & 0xFF00) | v
            elif op == "HI":
                self.cnt[k] = (self.cnt[k] & 0xFF) | (v << 8)
            else:
                self.cnt[k] = max(self.cnt[k] - 1, 0)
        elif name == "HOST.OUT":
            self.outq.append(v)
        elif name.startswith("BG") and name.endswith(".CTL"):
            self.ctl_writes.append((int(name[2]), v))
        else:
            raise NotImplementedError(name)

    # -- one burst
    def burst(self, ein: int = 0, limit: int = 64) -> int:
        self.ein = ein
        n = 0
        while True:
            ai = self.code[self.pc]
            insn = ai.insn
            c = self._cond(insn.cond)
            writes = []
            for mv in insn.moves:
                en = {"always": 1, "if": c, "ifnot": 1 - c, "never": 0}[mv.guard]
                if en:
                    writes.append((mv.dst, self._src(mv.src, insn.imm)))
            for d, v in writes:
                self._dst(d, v)
            taken = {"next": 0, "always": 1, "if": c, "ifnot": 1 - c}[insn.jmode]
            npc = insn.imm if taken else (self.pc + 1) % M.PROG_WORDS
            self.pc = npc
            n += 1
            if insn.pause:
                break
            if n > limit:
                raise RuntimeError("burst did not terminate")
        self.stats["bursts"] += 1
        self.stats["insns"] += n
        return n

    def commit(self) -> int:
        self.committed = self.staged
        return self.committed

    def level(self, out_pin: int, seg: int = 0) -> int:
        return (self.prog.outs[out_pin].lut >> (seg * 4 + self.committed)) & 1
