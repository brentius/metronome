"""Host-loader contract (V3 plan section 7.6, host side): refuse writes that would corrupt a line, thread or memory in use.

SPEC v2 section 1: configuration is written one byte at a time, so a multi-byte field written while it is in use passes
through mixed values; section 9a.8: a host program-memory write in the cycle of a fetch is undefined.  Double-buffering
the 2,084 configuration latches in RTL was rejected for area, so the guarantee is a loader contract: this wrapper reads
the runtime state through the host map *before* each write and refuses (raises ContractViolation) any write that
touches state in use.  It wraps any `Link` (the SPI link, or the cycle model through its backdoor).

Rules (each cites the register that is read first):

  C1  line l configuration  (LINE_BASE + 0x20*l ..)   refused while L<l>.CTL has RUN (bit 0) or ARM (bit 1) set
  C2  thread t configuration (THREAD_BASE + 0x08*t)   refused while T<t>.STAT has EN (bit 3), RUNNING (1) or
                                                      READY (0) set (ARMED with EN = 0 is passive and allowed)
  C3  output-cell configuration                       refused while any line has RUN or ARM set, unless the loader's
                                                      shadow knows the cell's bound line and that line is stopped
                                                      (BIND is write-only, so it cannot be read back)
  C4  LFSR / stream configuration                     refused while CTRL.RUN (RUN_global) is set (a thread may use it)
  C5  program memory                                  refused while CTRL.RUN is set (SPEC 9a.8)
  C6  thread PC write                                 refused while that thread has EN set
  C7  data RAM                                        allowed (mailbox/stream data is written while running by design);
                                                      pass `strict_data=True` to refuse it while CTRL.RUN is set
  C8  D24 spacing                                     two configuration writes must not be in consecutive cycles; the
                                                      SPI link gives >= 128 cycles by construction.  `Link.min_gap`
                                                      (cycles between writes) below 2 is rejected at construction.
  Runtime registers (CTRL, LRT, SRT, TRT.STAT) are the start/stop mechanism and are always writable.

`atomic_replace(writes)` is the supported way to change a running configuration: stop the lines and threads the
writes touch (CTL = 0, EN = 0), apply, and the caller restarts them; it never leaves a half-written field live.
Evidence class: host-side software tested against the v2 cycle-level model (code/host2/tests/test_loader_contract.py);
it is not RTL or hardware evidence, and it only protects writes issued through it.
"""
from __future__ import annotations

from typing import Protocol

from ._md import M

HM = M.HOST_MAP
ST = M.HOST_STRIDE


class ContractViolation(Exception):
    """A host write that the load contract refuses (state in use)."""

    def __init__(self, rule: str, addr: int, why: str):
        super().__init__(f"{rule}: write to 0x{addr:04X} refused: {why}")
        self.rule, self.addr, self.why = rule, addr, why


class Link(Protocol):
    min_gap: int

    def write(self, addr: int, data: bytes) -> None: ...

    def read(self, addr: int, n: int = 1) -> bytes: ...


def _within(addr: int, base: int, stride: int, n: int):
    """(instance, offset) if addr lies in the n-instance block at base, else None."""
    if base <= addr < base + stride * n:
        return divmod(addr - base, stride)
    return None


def classify(addr: int):
    """('prog',) | ('data',) | (block, instance, offset) | None for a host address (machine.HOST_MAP)."""
    if HM["PROG_BASE"] <= addr < HM["PROG_BASE"] + ST["PROG_CORE"] * M.N_CORES:
        return ("prog",)
    if HM["DATA_BASE"] <= addr < HM["DATA_BASE"] + M.DATA_BYTES:
        return ("data",)
    for blk, (base, stride, n) in {
        "LINE": (HM["LINE_BASE"], ST["LINE"], M.N_LINES), "THREAD": (HM["THREAD_BASE"], ST["THREAD"], M.N_THREADS),
        "LFSR": (HM["LFSR_BASE"], ST["LFSR"], M.N_LFSRS), "STREAM": (HM["STREAM_BASE"], ST["STREAM"], M.N_STREAMS),
        "OUT": (HM["OUT_BASE"], ST["OUT"], M.N_OUT_PINS), "LRT": (HM["LRT_BASE"], ST["LRT"], M.N_LINES),
        "TRT": (HM["TRT_BASE"], ST["TRT"], M.N_THREADS), "SRT": (HM["SRT_BASE"], ST["SRT"], M.N_STREAMS),
    }.items():
        r = _within(addr, base, stride, n)
        if r is not None:
            return (blk, r[0], r[1])
    if HM["CTRL_BASE"] <= addr < HM["CTRL_BASE"] + 0x10:
        return ("CTRL", 0, addr - HM["CTRL_BASE"])
    return None


class ContractLoader:
    """Wraps a Link; every write is checked against the live state read through the same link."""

    def __init__(self, link: Link, strict_data: bool = False):
        if getattr(link, "min_gap", 128) < 2:
            raise ValueError("C8: the link can issue configuration writes in consecutive cycles (D24)")
        self.link = link
        self.strict_data = strict_data
        self.out_bind: dict[int, int] = {}      # shadow: output cell -> bound line (written by this loader)
        self.checked = 0
        self.refused = 0

    # -- state reads (the host map, first) -------------------------------------------------------------------
    def run_global(self) -> bool:
        return bool(self.link.read(HM["CTRL_BASE"] + 0, 1)[0] & 1)

    def line_ctl(self, l: int) -> int:
        return self.link.read(HM["LRT_BASE"] + ST["LRT"] * l + 2, 1)[0]

    def thread_stat(self, t: int) -> int:
        return self.link.read(HM["TRT_BASE"] + ST["TRT"] * t + 1, 1)[0]

    def line_active(self, l: int) -> bool:
        return bool(self.line_ctl(l) & 0b11)

    def thread_in_use(self, t: int) -> bool:
        return bool(self.thread_stat(t) & 0b1011)

    # -- the contract ----------------------------------------------------------------------------------------
    def check(self, addr: int, nbytes: int = 1) -> None:
        """Raise ContractViolation if writing `nbytes` at `addr` touches state in use."""
        for a in range(addr, addr + nbytes):
            self._check_byte(a)
        self.checked += 1

    def _refuse(self, rule, addr, why):
        self.refused += 1
        raise ContractViolation(rule, addr, why)

    def _check_byte(self, a: int) -> None:
        c = classify(a)
        if c is None:
            return
        if c[0] == "prog":
            if self.run_global():
                self._refuse("C5", a, "program memory written while CTRL.RUN is set (SPEC 9a.8)")
        elif c[0] == "data":
            if self.strict_data and self.run_global():
                self._refuse("C7", a, "data RAM written while CTRL.RUN is set (strict_data)")
        elif c[0] == "LINE":
            ctl = self.line_ctl(c[1])
            if ctl & 0b11:
                self._refuse("C1", a, f"line {c[1]} is armed/running (CTL=0x{ctl:02X}); a multi-byte field would be "
                                      "seen half-written (SPEC 1)")
        elif c[0] == "THREAD":
            st = self.thread_stat(c[1])
            if st & 0b1011:
                self._refuse("C2", a, f"thread {c[1]} is enabled/running (STAT=0x{st:02X})")
        elif c[0] == "OUT":
            bound = self.out_bind.get(c[1])
            lines = [bound] if bound is not None else range(M.N_LINES)
            for l in lines:
                if self.line_active(l):
                    self._refuse("C3", a, f"output cell {c[1]} may be driven by active line {l}"
                                          + ("" if bound is not None else " (binding unknown: BIND is write-only)"))
        elif c[0] in ("LFSR", "STREAM"):
            if self.run_global():
                self._refuse("C4", a, f"{c[0].lower()} {c[1]} configured while CTRL.RUN is set")
        elif c[0] == "TRT" and c[2] == 0:
            if self.thread_stat(c[1]) & 0b1000:
                self._refuse("C6", a, f"thread {c[1]} PC written while EN is set")

    # -- writing ---------------------------------------------------------------------------------------------
    def write(self, addr: int, data: bytes) -> None:
        data = bytes(data)
        self.check(addr, len(data))
        self.link.write(addr, data)
        for i in range(len(data)):
            c = classify(addr + i)
            if c and c[0] == "OUT" and c[2] == 0:      # BIND byte: bit 2 = bound, bits 1:0 = line
                self.out_bind[c[1]] = data[i] & 3 if data[i] & 4 else None
                if self.out_bind[c[1]] is None:
                    del self.out_bind[c[1]]

    def load(self, writes) -> int:
        """Apply an ordered host-write list ((addr, bytes[, note]) items, e.g. image.host_writes) under the contract.
        Each write is checked immediately before it is issued, so an image that starts a line and then reconfigures
        it is refused at the first offending write; nothing after it is issued.  Returns the writes issued."""
        n = 0
        for item in writes:
            self.write(item[0], item[1])
            n += 1
        return n

    def atomic_replace(self, writes) -> int:
        """Stop what the writes touch, apply them, leave everything stopped (the caller restarts).  Lines touched by
        configuration (and every line when output cells are touched) get CTL = 0; touched threads get EN = 0."""
        stop_lines, stop_threads = set(), set()
        for item in writes:
            addr, data = item[0], item[1]
            for i in range(len(data)):
                c = classify(addr + i)
                if not c:
                    continue
                if c[0] == "LINE":
                    stop_lines.add(c[1])
                elif c[0] == "THREAD":
                    stop_threads.add(c[1])
                elif c[0] == "OUT":
                    stop_lines.update(range(M.N_LINES))
                elif c[0] == "TRT" and c[2] == 0:
                    stop_threads.add(c[1])
        if any(classify(it[0] + i) and classify(it[0] + i)[0] in ("prog", "LFSR", "STREAM")
               for it in writes for i in range(len(it[1]))):
            self.link.write(HM["CTRL_BASE"], bytes([0]))                        # RUN_global = 0 (C4, C5)
        for t in sorted(stop_threads):
            self.link.write(HM["TRT_BASE"] + ST["TRT"] * t + 1, bytes([0]))     # EN = 0 (bits 4, 5 = 0 clear nothing)
        for l in sorted(stop_lines):
            self.link.write(HM["LRT_BASE"] + ST["LRT"] * l + 2, bytes([0]))     # CTL = 0
        getattr(self.link, "settle", lambda: None)()          # let in-flight bursts drain (the model link steps)
        return self.load(writes)
