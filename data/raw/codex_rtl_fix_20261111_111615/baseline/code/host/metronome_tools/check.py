"""Static checks: the burst rule, worst-case burst lengths, response-time bounds and engine budgets.

python -m metronome_tools.check prog.mas [-v]

Model (SPEC 5, 10).  A trigger in cycle t makes the engine READY in t+1; on an idle core its first instruction runs
in t+2, so a burst of n instructions occupies cycles t+2 .. t+n+1 and the last instruction runs n+1 cycles after the
trigger.  An engine sharing a core can additionally wait for other engines' bursts; the bound used here is the
conservative "own burst + longest burst of every other enabled engine on that core" (each other engine counted once).
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field

from ._md import M
from .asm import AsmError, assemble_file, write_group
from .model import Program


@dataclass
class Burst:
    engine: int
    kind: str                 # start | watch0 | watch1 | resume
    entry: int
    n: int                    # worst-case instructions
    path: list                # addresses along the worst-case path
    sym_n: int = 0            # worst-case position (1-based) of the last E.SYM write, 0 if none
    sym_path: list = field(default_factory=list)


@dataclass
class EngineReport:
    n: int
    core: int
    bursts: list = field(default_factory=list)
    n_max: int = 0
    sym_max: int = 0
    others: int = 0                       # W: summed longest bursts of the other enabled engines on the core
    resp_last: int = 0                    # worst-case cycles trigger -> last instruction
    resp_sym: int = 0                     # worst-case cycles trigger -> last E.SYM write
    budget_sym: int | None = None         # cycles from trigger to the commit beat (derived from the beat generator)
    period_min: int | None = None         # minimum cycles between triggers (derived)


@dataclass
class Report:
    errors: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    engines: dict = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return not self.errors

    def format(self, verbose: bool = False) -> str:
        out = []
        for e in self.errors:
            out.append(f"check error: {e}")
        for w in self.warnings:
            out.append(f"check warning: {w}")
        if verbose or self.errors:
            for er in self.engines.values():
                out.append(f"engine {er.n} (core {er.core}): worst burst {er.n_max} insns, trigger->last insn "
                           f"{er.resp_last} cycles" + (f" (+{er.others} insns of other engines)" if er.others else "")
                           + (f", trigger->commit window {er.budget_sym} cycles" if er.budget_sym else "")
                           + (f", min trigger spacing {er.period_min} cycles" if er.period_min else ""))
        if not out:
            out.append("checks passed: burst rule, burst lengths, budgets")
        return "\n".join(out)


def _fmt_path(prog: Program, core: int, path: list) -> str:
    return " -> ".join(prog.addr_name(core, a) for a in path)


class _Core:
    """Per-core control-flow analysis."""

    def __init__(self, prog: Program, core: int, rep: Report):
        self.prog, self.core, self.rep = prog, core, rep
        self.code = prog.code[core]
        self.acyclic = True
        self._len: dict = {}
        self._sym: dict = {}
        self._missing: set = set()

    def succ(self, a: int) -> list[int]:
        """Successors inside a burst (empty after a pause)."""
        ins = self.code[a]
        return [] if ins.pause else self._present(a, ins.successors())

    def _present(self, a: int, succs: list[int]) -> list[int]:
        out = []
        for s in succs:
            if s in self.code:
                out.append(s)
            elif (a, s) not in self._missing:
                self._missing.add((a, s))
                self.rep.errors.append(
                    f"core {self.core}: {self.prog.addr_name(self.core, a)} continues to 0x{s:02X}, which holds no "
                    f"instruction (unprogrammed memory would execute as a no-op and run on)")
        return out

    def resume_points(self, a: int) -> list[int]:
        ins = self.code[a]
        return self._present(a, ins.successors()) if ins.pause else []

    def find_cycles(self) -> None:
        """Burst rule: every cycle must pass through a pause.  Report each loop that does not."""
        color, stack, seen = {}, [], set()

        def dfs(a):
            color[a] = 1
            stack.append(a)
            for s in self.succ(a):
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

    # longest path (instructions) from a to the end of the burst, and the last E.SYM write position
    def longest(self, a: int):
        if a in self._len:
            return self._len[a]
        best, nxt = 0, None
        for s in self.succ(a):
            n, _ = self.longest(s)
            if n > best:
                best, nxt = n, s
        self._len[a] = (1 + best, nxt)
        return self._len[a]

    def sym_pos(self, a: int):
        if a in self._sym:
            return self._sym[a]
        here = 1 if self.code[a].writes_sym() else 0
        best, nxt = here, None
        for s in self.succ(a):
            n, _ = self.sym_pos(s)
            if n > 0 and n + 1 > best:
                best, nxt = n + 1, s
        self._sym[a] = (best, nxt)
        return self._sym[a]

    def path(self, a: int, table: dict, fn) -> list[int]:
        out = [a]
        while True:
            _, nxt = fn(out[-1])
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
            work.extend(self.succ(a))
        return seen


def _ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def _trigger_window(prog: Program, trig: str):
    """(cycles from trigger to the commit beat, minimum cycles between triggers) for a beat-generator trigger."""
    m = re.fullmatch(r"BG(\d)\.(BEAT|TAP(\d))", trig)
    if not m:
        return None, None, None
    bg = prog.bgs.get(int(m.group(1)))
    if bg is None:
        return None, None, f"trigger {trig} refers to BG{m.group(1)}, which has no .beatgen block"
    if m.group(2) == "BEAT":
        ph_max = bg.inc - 1
    else:
        k = int(m.group(3))
        if bg.taps[k] is None:
            return None, None, f"trigger {trig}: tap {k} is disabled (T{k} = MOD), so it never fires"
        ph_max = bg.taps[k] + bg.inc - 1
    j_min = max(0, _ceil_div(bg.mod - bg.inc - ph_max, bg.inc))
    return 1 + j_min, bg.mod // bg.inc, None


def check(prog: Program) -> Report:
    rep = Report()
    cores = {c: _Core(prog, c, rep) for c in range(M.N_CORES)}
    for c in cores.values():
        c.find_cycles()

    # per-engine burst analysis
    for n, eng in sorted(prog.engines.items()):
        er = EngineReport(n, eng.core)
        rep.engines[n] = er
        cc = cores[eng.core]
        if not cc.acyclic:
            continue
        entries = []
        if eng.start_addr is None:
            rep.warnings.append(f"engine {n} has no 'start' label or 'pc'; assuming its PC starts at 0")
            eng.start_addr = 0
        entries.append(("start", eng.start_addr))
        for k in (0, 1):
            if eng.watch_addr[k] is not None:
                entries.append((f"watch{k}", eng.watch_addr[k]))
        seen_entry, work = set(), list(entries)
        while work:
            kind, a = work.pop(0)
            if a in seen_entry:
                continue
            seen_entry.add(a)
            if a not in cc.code:
                rep.errors.append(f"engine {n}: entry {prog.addr_name(eng.core, a)} holds no instruction")
                continue
            ln, _ = cc.longest(a)
            sp, _ = cc.sym_pos(a)
            b = Burst(n, kind, a, ln, cc.path(a, cc._len, cc.longest),
                      sp, cc.path(a, cc._sym, cc.sym_pos) if sp else [])
            er.bursts.append(b)
            for r in cc.reachable(a):
                for s in cc.resume_points(r):
                    work.append(("resume", s))
        er.n_max = max((b.n for b in er.bursts), default=0)
        er.sym_max = max((b.sym_n for b in er.bursts), default=0)

    # response bounds and budgets
    for n, er in rep.engines.items():
        eng = prog.engines[n]
        if not er.bursts:
            continue
        others = [rep.engines[m] for m, e2 in prog.engines.items() if m != n and e2.core == eng.core and e2.enable]
        er.others = sum(o.n_max for o in others)
        er.resp_last = er.n_max + 1 + er.others
        er.resp_sym = er.sym_max + 1 + er.others if er.sym_max else 0
        worst = max(er.bursts, key=lambda b: b.n)
        where = (f"engine {n} burst at {prog.addr_name(eng.core, worst.entry)} [{worst.kind}], worst path "
                 f"{_fmt_path(prog, eng.core, worst.path)} ({worst.n} insns)")
        sharing = (f" + {er.others} insns from other engines on core {eng.core} "
                   f"({', '.join(str(o.n) + ':' + str(o.n_max) for o in others)}; conservative: each counted once)"
                   if er.others else "")
        win, per, warn = _trigger_window(prog, eng.trigger)
        if warn:
            rep.warnings.append(f"engine {n}: {warn}")
        er.budget_sym, er.period_min = win, per
        bg = prog.bgs.get(eng.bg_eff)
        if win is not None:
            if er.sym_max and er.resp_sym > win:
                sb = max(er.bursts, key=lambda b: b.sym_n)
                rep.errors.append(
                    f"engine {n} burst at {prog.addr_name(eng.core, sb.entry)} [{sb.kind}]: last E.SYM write is at "
                    f"instruction {sb.sym_n} of path {_fmt_path(prog, eng.core, sb.sym_path)}, i.e. {er.resp_sym} "
                    f"cycles after the trigger{sharing}, but the commit beat comes {win} cycles after "
                    f"{eng.trigger} (the symbol would be LATE)")
            if er.resp_last + 1 > per:
                rep.errors.append(
                    f"{where}: {er.resp_last} cycles trigger-to-last-instruction{sharing} plus the cycle that "
                    f"clears RUNNING exceeds the {per}-cycle minimum spacing of {eng.trigger}; the next trigger "
                    f"would set OVR")
            if bg and bg.edge_pol:
                rep.warnings.append(f"engine {n}: BG{bg.n} re-aligns on edges (preset can shorten a beat); the "
                                    f"trigger-spacing check ignores this")
        elif eng.trigger in ("NONE",):
            rep.warnings.append(f"engine {n}: trigger NONE; it only runs on a host doorbell")
        for (en, kind, val, line) in prog.budgets:
            if en != n:
                continue
            got, unit = (er.resp_last, "cycles") if kind == "cycles" else (er.n_max, "instructions")
            if got > val:
                rep.errors.append(
                    f"{where}: worst case {got} {unit}{sharing if kind == 'cycles' else ''} exceeds declared budget "
                    f"of {val} {unit} (.budget, line {line})")
    for (en, kind, val, line) in prog.budgets:
        if en not in prog.engines:
            rep.errors.append(f".budget names engine {en}, which is not defined (line {line})")

    # unit sharing advisory: a write group touched by more than one engine
    users: dict = {}
    for n, er in rep.engines.items():
        eng = prog.engines[n]
        for a in cores[eng.core].reachable(eng.start_addr or 0) if cores[eng.core].acyclic else []:
            for mv in cores[eng.core].code[a].insn.moves:
                g = write_group(mv.dst)
                if g and not g.startswith("E.") and mv.guard != "never":
                    users.setdefault(g, set()).add(n)
    for g, es in sorted(users.items()):
        if len(es) > 1:
            cs = {prog.engines[e].core for e in es}
            rep.warnings.append(f"write group {g} is written by engines {sorted(es)}"
                                + (" on different cores (bursts can overlap: CONFLICT possible)" if len(cs) > 1
                                   else " on one core (bursts are serialised, but state is shared)"))
    return rep


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="metronome_tools.check")
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
