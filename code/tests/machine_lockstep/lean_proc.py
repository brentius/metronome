"""Driver for the Lean `machine-sim` executable (line protocol of BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md).

in : "ui uio rst_n" (decimal) = one clock cycle;  "reset" = power-on state;  "quit" = exit.
out: one JSON object per cycle line with the state after the cycle.
Inputs can be written ahead (`send`) and results read later (`recv`): the Lean side never feeds back into the stimulus.
A reader thread drains stdout/stderr so a full pipe cannot deadlock, and `recv` times out so a hung exe fails.
"""
from __future__ import annotations

import json
import os
import queue
import subprocess
import sys
import threading
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE.parent / "lean"


class LeanError(RuntimeError):
    pass


def default_exe() -> Path:
    env = os.environ.get("MACHINE_SIM")
    if env:
        return Path(env)
    b = LEAN_DIR / ".lake/build/bin"
    for n in ("machine-sim.exe", "machine-sim"):
        if (b / n).exists():
            return b / n
    return b / "machine-sim.exe"


def exe_available() -> bool:
    return default_exe().exists()


class LeanProc:
    def __init__(self, cmd=None, timeout=60.0):
        self.cmd = [str(c) for c in (cmd or [default_exe()])]
        self.timeout = timeout
        self.q: "queue.Queue" = queue.Queue()
        self.err: list = []
        self.p = subprocess.Popen(self.cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  bufsize=1 << 16)
        threading.Thread(target=self._rd_out, daemon=True).start()
        threading.Thread(target=self._rd_err, daemon=True).start()

    def _rd_out(self):
        for line in self.p.stdout:
            self.q.put(line)
        self.q.put(None)

    def _rd_err(self):
        for line in self.p.stderr:
            self.err.append(line.decode("utf-8", "replace").rstrip())
            del self.err[:-50]

    def send(self, ui: int, uio: int, rst_n: int):
        self.p.stdin.write(b"%d %d %d\n" % (ui, uio, rst_n))

    def flush(self):
        self.p.stdin.flush()

    def recv(self) -> dict:
        try:
            line = self.q.get(timeout=self.timeout)
        except queue.Empty:
            self.kill()
            raise LeanError(f"timeout after {self.timeout}s waiting for {self.cmd[0]}; stderr: {self.err[-5:]}")
        if line is None:
            raise LeanError(f"exe exited (rc={self.p.poll()}); stderr: {self.err[-10:]}")
        try:
            return json.loads(line)
        except ValueError as e:
            raise LeanError(f"bad JSON line {line[:200]!r}: {e}; stderr: {self.err[-5:]}")

    def step(self, ui: int, uio: int, rst_n: int) -> dict:
        self.send(ui, uio, rst_n)
        self.flush()
        return self.recv()

    def reset(self):
        """Send `reset`. The protocol does not say whether an ack line follows, so the harness uses a fresh process
        per scenario instead of relying on this."""
        self.p.stdin.write(b"reset\n")
        self.flush()

    def kill(self):
        try:
            self.p.kill()
        except OSError:
            pass

    def close(self):
        try:
            self.p.stdin.write(b"quit\n")
            self.p.stdin.flush()
            self.p.stdin.close()
            self.p.wait(timeout=5)
        except Exception:
            self.kill()

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()


def fake_cmd(flip=None):
    """Command line of fake_sim.py (a second Python model speaking the protocol). flip = "cycle:key:bit"."""
    c = [sys.executable, str(HERE / "fake_sim.py")]
    if flip:
        c += ["--flip", flip]
    return c
