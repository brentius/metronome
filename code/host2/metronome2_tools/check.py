"""Static check of SPEC v2 10.4 (toolchain obligations).   python -m metronome2_tools.check prog.mas [-v]

Timing model (SPEC v2 5), all counts in cycles:
  * a burst's length is its instructions plus one idle cycle per taken jump on a non-pausing instruction;
  * a trigger in cycle t on an otherwise idle core executes the burst's instruction at burst-cycle i in t + i + 2;
  * with other threads on the core, the response bound adds  sum_p (L_p + 1)  over the other enabled threads
    bound to the same core, L_p being the longest burst of thread p (each counted once).
The bound assumes finite bursts, RUN_global = 1, and unchanged program and configuration during the interval.

Per thread triggered by a line event on its own line g (trigger Lg.BEAT / Lg.TAPk), with Sigma the sum above:
  * commit    last symbol write at burst-cycle s:   s + 2 + Sigma <= gap(trigger, next boundary)   else LATE
  * snapshot  last input read at burst-cycle r:     r + 2 + Sigma <  gap(trigger, next snapshot)   else a read
              could see the next snapshot (the text of 10.4 says "before the next snapshot cycle")
  * overrun   resp + 1 <= gap(trigger, trigger)  where resp = n + 2 + Sigma, else the next trigger sets OVR
`gap` comes from timing.py; where it cannot be derived the check says so with a warning instead of passing silently.
"""
from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass, field

from ._md import M
from .asm import AsmError, assemble_file, write_group
from .model import Program
from .timing import LineTiming


@dataclass
class Burst:
    thread: int
    kind: str                 # start | watch0 | watch1 | resume
    entry: int
    n: int                    # cycles
    path: list
    sym_n: int = 0            # burst-cycle of the last symbol write (1-based), 0 if none
    in_n: int = 0             # burst-cycle of the last input read, 0 if none


@dataclass
class ThreadReport:
    n: int
    core: int
    bursts: list = field(default_factory=list)
    n_max: int = 0
    sym_max: int = 0
    in_max: int = 0
    others: int = 0           # Sigma = sum (L_p + 1) over the other enabled threads on the core
    resp_last: int = 0        # worst-case cycles from trigger to the last instruction (n + 2 + Sigma)
    gap_beat: object = None   # lower bounds, cycles (None = not derivable, inf = never)
    gap_snap: object = None
    gap_self: object = None


@dataclass
class Report:
    errors: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    threads: dict = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return not self.errors

    def format(self, verbose: bool = False) -> str:
        out = [f"check error: {e}" for e in self.errors] + [f"check warning: {w}" for w in self.warnings]
        if verbose or self.errors:
            for tr in self.threads.values():
                out.append(f"thread {tr.n} (core {tr.core}): longest burst {tr.n_max} cycles, trigger->last insn "
                           f"{tr.resp_last} cycles" + (f" (Sigma {tr.others} from other threads)" if tr.others else "")
                           + (f", last symbol write at burst-cycle {tr.sym_max}" if tr.sym_max else "")
                           + (f", last input read at burst-cycle {tr.in_max}" if tr.in_max else "")
                           + f"; gaps: boundary {tr.gap_beat}, snapshot {tr.gap_snap}, self {tr.gap_self}")
        if not out:
            out.append("checks passed: SPEC v2 10.4")
        return "\n".join(out)


def _fmt_path(prog: Program, core: int, path: list) -> str:
    return " -> ".join(prog.addr_name(core, a) for a in path)


class _Core:
    def __init__(self, prog: Program, core: int, rep: Report):
        self.prog, self.core, self.rep = prog, core, rep
        self.code = prog.code[core]
        self.acyclic = True
        self._memo: dict = {}
        self._missing: set = set()

    def _present(self, a: int, edges: list) -> list:
        out = []
        for s, x in edges:
            if s in self.code:
                out.append((s, x))
            elif (a, s) not in self._missing:
                self._missing.add((a, s))
                self.rep.errors.append(
                    f"core {self.core}: {self.prog.addr_name(self.core, a)} continues to 0x{s:02X}, which holds no "
                    f"instruction (unprogrammed memory would execute as a no-op and run on)")
        return out

    def succ(self, a: int) -> list:
        ins = self.code[a]
        return [] if ins.pause else self._present(a, ins.edges())

    def resume_points(self, a: int) -> list:
        ins = self.code[a]
        return [s for s, _ in self._present(a, ins.edges())] if ins.pause else []

    def find_cycles(self) -> None:
        color, stack, seen = {}, [], set()

        def dfs(a):
            color[a] = 1
            stack.append(a)
            for s, _ in self.succ(a):
                if color.get(s) == 1:
                    cyc = stack[stack.index(s):] + [s]
                    key = frozenset(cyc)
                    if key not in seen:
                        seen.add(key)
                        self.acyclic = False
                        self.rep.errors.append(
                            f"burst rule violated on core {self.core}: loop {_fmt_path(self.prog, self.core, cyc)} "
                            f"never passes through a pause (every cycle in the control-flow graph needs a pause)")
                elif s not in color:
                    dfs(s)
            stack.pop()
            color[a] = 2

        for a in sorted(self.code):
            if a not in color:
                dfs(a)

    def best(self, a: int, pred: str):
        """(burst-cycle of the last instruction satisfying `pred` counted from a (a is cycle 1), next on path)."""
        key = (a, pred)
        if key in self._memo:
            return self._memo[key]
        ins = self.code[a]
        if pred == "len":
            here = 1
        elif pred == "sym":
            here = 1 if ins.writes_sym() else 0
        else:
            here = 1 if ins.reads_input() else 0
        best, nxt = here, None
        for s, x in self.succ(a):
            n, _ = self.best(s, pred)
            cand = (1 + x + n) if (pred == "len" or n > 0) else 0
            if cand > best:
                best, nxt = cand, s
        self._memo[key] = (best, nxt)
        return self._memo[key]

    def path(self, a: int, pred: str) -> list:
        out = [a]
        while True:
            _, nxt = self.best(out[-1], pred)
            if nxt is None:
                return out
            out.append(nxt)

    def reachable(self, entry: int) -> set:
        seen, work = set(), [entry]
        while work:
            a = work.pop()
            if a in seen or a not in self.code:
                continue
            seen.add(a)
            work.extend(s for s, _ in self.succ(a))
        return seen


def _ren_used(prog: Program, l: int) -> bool:
    """Line l's REN bit may be set: by its initial CTL, or by a move to Ll.CTL with an immediate that has bit 2 set
    or with a source the tools cannot evaluate (assumed to set it)."""
    ln = prog.lines[l]
    if ln.ctl & 4:
        return True
    for core in prog.code.values():
        for ai in core.values():
            for mv in ai.enabled_moves():
                if mv.dst == f"L{l}.CTL":
                    if mv.src == "ZERO":
                        continue
                    if mv.src != "IMM" or (ai.insn.imm >> 2) & 1:
                        return True
    return False


def _check_lines(prog: Program, rep: Report) -> dict:
    timings = {}
    trig_taps = {(t.trigger_line, int(t.trigger[-1])) for t in prog.threads.values()
                 if t.trigger_line is not None and t.trigger[-4:-1] == "TAP"}
    for l, ln in sorted(prog.lines.items()):
        name = f"line {l}"
        if not (1 <= ln.inc < ln.mod <= 0xFFFF):
            rep.errors.append(f"{name}: INC {ln.inc} must be at least 1 and below MOD {ln.mod} (SPEC v2 9a.6, 10.4)")
        timings[l] = LineTiming(ln)
        tm = timings[l]
        if tm.tapmiss_free:
            rep.warnings.append(f"{name}: free-running, an enabled tap is skipped in some beats (TAPMISS): a tap "
                                f"within INC of MOD is crossed in the beat it belongs to only after the wrap")
        live = [ln.tap(k) for k in range(3) if ln.phase_tap(k)]
        if live != sorted(live):
            rep.warnings.append(f"{name}: phase taps are not in ascending order; SEG is the count of fired taps, "
                                f"not their index")
        if ln.hen:
            if ln.hpin >= M.N_IN_PINS:
                if ln.hlvl == 1:
                    rep.errors.append(f"{name}: hold on pin {ln.hpin} (>= {M.N_IN_PINS} reads 0) with HLVL = 1 "
                                      f"would hold forever (SPEC v2 3.2a)")
                else:
                    rep.warnings.append(f"{name}: hold level 0 on a constant-0 pin never holds")
            if ln.htap > 2 or not ln.phase_tap(ln.htap):
                rep.warnings.append(f"{name}: hold tap {ln.htap} is disabled or edge-sourced; the hold has no effect")
        if ln.follow and ln.edge_pol == 0:
            rep.warnings.append(f"{name}: FOLLOW = 1 with no edge polarity: the line never produces a boundary")
        if ln.follow and ln.minperiod is None and any(
                t.trigger_line == l for t in prog.threads.values()):
            rep.warnings.append(f"{name}: follower line with triggered threads but no 'minperiod': response bounds "
                                f"against its boundaries cannot be checked")
        # window / tap rule (10.4)
        aligns = (not ln.follow) and ln.edge_pol != 0 and ln.edge_pin < M.N_IN_PINS and _ren_used(prog, l)
        if aligns and ln.wen:
            if ln.wlo > ln.whi:
                rep.errors.append(f"{name}: re-aligns with a wrapping window (WLO {ln.wlo} > WHI {ln.whi}); "
                                  f"SPEC v2 10.4 requires WLO <= WHI")
            else:
                used = [k for k in range(3) if ln.phase_tap(k) and (
                    ln.snap == k or (l, k) in trig_taps or ((ln.pina < 13 or ln.pinb < 13) and (ln.lut0 | ln.lut1)))]
                for k in used:
                    t = ln.tap(k)
                    if (t < ln.wlo and t <= ln.pre) or (t > ln.whi + ln.inc and t > ln.pre):
                        continue
                    rep.errors.append(
                        f"{name}: tap {k} (T{k} = {t}) violates the window rule of SPEC v2 10.4: need "
                        f"T < WLO ({ln.wlo}) and T <= PRE ({ln.pre}), or T > WHI + INC ({ln.whi + ln.inc}) and "
                        f"T > PRE; an accepted edge could skip or repeat it (TAPMISS)")
        elif aligns and not ln.wen:
            rep.warnings.append(f"{name}: re-aligns on any edge (WEN = 0); taps can be skipped (TAPMISS) and the "
                                f"timing bounds are approximate")
    return timings


def check(prog: Program) -> Report:
    rep = Report()
    cores = {c: _Core(prog, c, rep) for c in range(M.N_CORES)}
    for c in cores.values():
        c.find_cycles()
    timings = _check_lines(prog, rep)

    for n, th in sorted(prog.threads.items()):
        tr = ThreadReport(n, th.core)
        rep.threads[n] = tr
        cc = cores[th.core]
        if not cc.acyclic:
            continue
        if th.start_addr is None:
            rep.warnings.append(f"thread {n} has no 'start' label or 'pc'; assuming its PC starts at 0")
            th.start_addr = 0
        work = [("start", th.start_addr)] + [(f"watch{k}", th.watch_addr[k]) for k in (0, 1)
                                              if th.watch_addr[k] is not None]
        seen = set()
        while work:
            kind, a = work.pop(0)
            if a in seen:
                continue
            seen.add(a)
            if a not in cc.code:
                rep.errors.append(f"thread {n}: entry {prog.addr_name(th.core, a)} holds no instruction")
                continue
            tr.bursts.append(Burst(n, kind, a, cc.best(a, "len")[0], cc.path(a, "len"),
                                   cc.best(a, "sym")[0], cc.best(a, "in")[0]))
            for r in cc.reachable(a):
                for s in cc.resume_points(r):
                    work.append(("resume", s))
        tr.n_max = max((b.n for b in tr.bursts), default=0)
        tr.sym_max = max((b.sym_n for b in tr.bursts), default=0)
        tr.in_max = max((b.in_n for b in tr.bursts), default=0)

    for n, tr in rep.threads.items():
        th = prog.threads[n]
        if not tr.bursts:
            continue
        others = [rep.threads[m] for m, t2 in prog.threads.items()
                  if m != n and t2.core == th.core and t2.enable and rep.threads[m].bursts]
        tr.others = sum(o.n_max + 1 for o in others)
        tr.resp_last = tr.n_max + 2 + tr.others
        worst = max(tr.bursts, key=lambda b: b.n)
        where = (f"thread {n} burst at {prog.addr_name(th.core, worst.entry)} [{worst.kind}], worst path "
                 f"{_fmt_path(prog, th.core, worst.path)} ({worst.n} cycles)")
        sharing = (f" + Sigma {tr.others} from other threads on core {th.core} "
                   f"({', '.join(f'{o.n}:{o.n_max}+1' for o in others)})" if others else "")
        tl = th.trigger_line
        ev = th.trigger.split(".")[1] if tl is not None else None
        if tl is None:
            if tr.sym_max:
                rep.warnings.append(f"thread {n}: trigger {th.trigger} is not a line event; its symbol-commit "
                                    f"deadline cannot be checked")
        elif tl not in prog.lines:
            rep.warnings.append(f"thread {n}: trigger {th.trigger} refers to line {tl}, which has no .line block")
        elif tl != th.bound_line:
            rep.warnings.append(f"thread {n}: triggered by line {tl} but bound to line {th.bound_line}; "
                                f"commit and snapshot deadlines cannot be checked across lines")
        else:
            ln, tm = prog.lines[tl], timings[tl]
            if ev.startswith("TAP") and not ln.tap_enabled(int(ev[3])):
                rep.warnings.append(f"thread {n}: trigger {th.trigger}: tap {ev[3]} is disabled, so it never fires")
            else:
                tr.gap_beat = tm.gap(ev, "BEAT")
                tr.gap_self = tm.gap(ev, ev)
                snap_ev = tm.snapshot_event()
                tr.gap_snap = tm.gap(ev, snap_ev) if tr.in_max else None
                if tr.sym_max:
                    _deadline(rep, th.trigger, tr.gap_beat, tr.sym_max + 2 + tr.others,
                              f"last symbol write at burst-cycle {tr.sym_max}: cycle {tr.sym_max + 2 + tr.others}"
                              f"{sharing} after the trigger, but the next boundary of line {tl} is only "
                              f"{{g}} cycles after {th.trigger} (the symbol would be LATE); {where}", strict=False,
                              what=f"thread {n}: commit deadline vs boundary of line {tl}")
                if tr.in_max and tr.gap_snap != math.inf:
                    _deadline(rep, th.trigger, tr.gap_snap, tr.in_max + 2 + tr.others,
                              f"last input read at burst-cycle {tr.in_max}: cycle {tr.in_max + 2 + tr.others}"
                              f"{sharing} after the trigger, but the next snapshot ({snap_ev}) of line {tl} is "
                              f"{{g}} cycles after {th.trigger}; the read must come before it; {where}",
                              strict=True, what=f"thread {n}: input read vs next snapshot of line {tl}")
                _deadline(rep, th.trigger, tr.gap_self, tr.resp_last + 1,
                          f"{tr.resp_last} cycles trigger-to-last-instruction{sharing} plus the cycle that clears "
                          f"RUNNING exceeds the {{g}}-cycle minimum spacing of {th.trigger}; the next trigger would "
                          f"set OVR; {where}", strict=False,
                          what=f"thread {n}: trigger spacing of {th.trigger}")
        for (bn, kind, val, line) in prog.budgets:
            if bn != n:
                continue
            got, unit = (tr.resp_last, "cycles") if kind == "cycles" else (tr.n_max, "cycles of burst")
            if got > val:
                rep.errors.append(f"{where}: worst case {got} {unit}{sharing if kind == 'cycles' else ''} exceeds "
                                  f"declared budget of {val} (.budget, line {line})")
    for (bn, kind, val, line) in prog.budgets:
        if bn not in prog.threads:
            rep.errors.append(f".budget names thread {bn}, which is not defined (line {line})")

    users: dict = {}
    for n, tr in rep.threads.items():
        th = prog.threads[n]
        if cores[th.core].acyclic:
            for a in cores[th.core].reachable(th.start_addr or 0):
                for mv in cores[th.core].code[a].enabled_moves():
                    g = write_group(mv.dst)
                    if g and g != "L.SYM" and g != "T.STOP":
                        users.setdefault(g, set()).add(n)
    for g, ts in sorted(users.items()):
        if len(ts) > 1:
            cs = {prog.threads[t].core for t in ts}
            rep.warnings.append(f"write group {g} is written by threads {sorted(ts)}"
                                + (" on different cores (bursts can overlap: CONFLICT possible)" if len(cs) > 1
                                   else " on one core (bursts are serialised, but state is shared)"))
    return rep


def _deadline(rep: Report, trig: str, gap, need: int, msg: str, strict: bool, what: str) -> None:
    """Record an error if `need` cycles do not fit within `gap` (strict: need must be < gap)."""
    if gap is None:
        rep.warnings.append(f"{what}: not statically checkable for {trig} (gap to the next event is not derivable "
                            f"from the line configuration; declare minperiod/minhalf for a follower line)")
        return
    if gap == math.inf:
        return
    if (need >= gap) if strict else (need > gap):
        rep.errors.append(msg.replace("{g}", str(gap)))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="metronome2_tools.check")
    ap.add_argument("source")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args(argv)
    try:
        prog = assemble_file(a.source)
    except AsmError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    rep = check(prog)
    print(rep.format(verbose=True))
    return 0 if rep.ok else 2


if __name__ == "__main__":
    sys.exit(main())
