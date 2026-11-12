"""Event timing of a line, for the static check (SPEC v2 3.2-3.4, 10.4).

`LineTiming.gap(e, s)` is a lower bound, in cycles, on the time from an occurrence of event `e` to the next occurrence
of event `s` strictly after it (events: "BEAT", "TAP0", "TAP1", "TAP2").  Returns `math.inf` if `s` never occurs,
or `None` if the bound cannot be derived from the configuration (the checker then warns).

* free-running generated line (no accepted edges possible): exact, by simulating the tap/fired-bit rules of SPEC 3.4
  over one period of the phase orbit.  A hold (3.2a) only lengthens beats, so the bound stays valid with it.
* line that may re-align (edge, `FOLLOW = 0`): the minimum of the free-running bound and the time to the event
  after an accepted edge loads `PRE` (conservative, an approximation: it ignores the window).
* follower line: from the declared `minperiod` (smallest clock period) and `minhalf` (smallest edge-to-edge time),
  both assumptions the program author states in the `.line` block.
"""
from __future__ import annotations

import math
from math import gcd

from ._md import M

EVENTS = ("BEAT", "TAP0", "TAP1", "TAP2")


def _ceil_div(a: int, b: int) -> int:
    return -(-a // b)


class LineTiming:
    def __init__(self, ln):
        self.ln = ln
        self.valid = 1 <= ln.inc < ln.mod <= 0xFFFF
        self.follow = bool(ln.follow)
        self.realign = (not ln.follow) and ln.edge_pol != 0 and ln.edge_pin < M.N_IN_PINS
        self._free = None
        self.tapmiss_free = False
        if self.valid and not self.follow:
            self._simulate()

    # -- free-running simulation ------------------------------------------------------------------------------
    def _start_phases(self) -> list:
        ln = self.ln
        out = [ln.pre % ln.mod]
        for p in (ln.phase, 0):
            if p is not None and p % ln.mod not in out:
                out.append(p % ln.mod)
        return out

    def _step(self, ph: int, fired: list):
        ln = self.ln
        n = ph + ln.inc
        wrap = n >= ln.mod
        nx = n - ln.mod if wrap else n
        taps, nf, miss = {}, list(fired), False
        cur_ks = []
        for k in range(3):
            if not ln.phase_tap(k):
                continue
            tk = ln.tap(k)
            cross = (tk > ph or tk <= nx) if wrap else (ph < tk <= nx)
            nxt = cross and wrap and tk <= nx
            cur = cross and not nxt
            taps[k] = (cur and not fired[k]) or nxt
            cur_ks.append((k, cur, nxt))
        if wrap:
            miss = any(not fired[k] and not cur for k, cur, nxt in cur_ks)
            nf = [False, False, False]
            for k, cur, nxt in cur_ks:
                nf[k] = nxt
        else:
            for k, cur, nxt in cur_ks:
                nf[k] = fired[k] or cur
        return nx, wrap, taps, nf, miss

    def _simulate(self) -> None:
        ln = self.ln
        period = ln.mod // gcd(ln.inc, ln.mod)
        best: dict = {}
        for ph0 in self._start_phases():
            ph = ph0
            fired = [ln.phase_tap(k) and ln.tap(k) <= ph for k in range(3)]
            for _ in range(period + 2):                         # run to the first boundary
                ph, wrap, taps, fired, _m = self._step(ph, fired)
                if wrap:
                    break
            ev = {e: [] for e in EVENTS}
            for c in range(period):                             # then one full period of the orbit
                ph, wrap, taps, fired, miss = self._step(ph, fired)
                self.tapmiss_free = self.tapmiss_free or miss
                if wrap:
                    ev["BEAT"].append(c)
                for k, f in taps.items():
                    if f:
                        ev[f"TAP{k}"].append(c)
            best[ph0] = (period, ev)
        self._free = best

    def _free_gap(self, e: str, s: str):
        if self.ln.t0src and "TAP0" in (e, s):
            return None
        out = math.inf
        for period, ev in self._free.values():
            if not ev[e]:
                return None
            if not ev[s]:
                continue
            ys = ev[s]
            for x in ev[e]:
                nxt = next((y for y in ys if y > x), ys[0] + period)
                out = min(out, nxt - x)
        return out

    def _w_boundary(self) -> int:
        ln = self.ln
        return max(0, _ceil_div(ln.mod - ln.pre, ln.inc) - 1)

    def _realign_gap(self, s: str):
        ln = self.ln
        if s == "BEAT":
            return 2 + self._w_boundary()
        k = int(s[3])
        if not ln.tap_enabled(k):
            return math.inf
        if not ln.phase_tap(k):
            return None
        tk = ln.tap(k)
        w = max(0, _ceil_div(tk - ln.pre, ln.inc) - 1) if tk > ln.pre else self._w_boundary()
        return 2 + w

    # -- follower ---------------------------------------------------------------------------------------------
    def _offset(self, k: int):
        """Cycles from the boundary cycle to the cycle tap k crosses, or None if it never fires in a beat."""
        ln = self.ln
        if not ln.phase_tap(k):
            return None
        tk = ln.tap(k)
        if tk <= ln.pre:
            return None
        return 1 + max(0, _ceil_div(tk - ln.pre, ln.inc) - 1)

    def _follow_gap(self, e: str, s: str):
        ln = self.ln
        T, H = ln.minperiod, ln.minhalf

        def tap_enabled(x):
            return x == "BEAT" or ln.tap_enabled(int(x[3]))

        if not tap_enabled(s):
            return math.inf
        if not tap_enabled(e):
            return None
        e_edge = e == "TAP0" and ln.t0src
        s_edge = s == "TAP0" and ln.t0src
        if e == s:
            return T
        if (e == "BEAT" or e_edge) and (s == "BEAT" or s_edge):
            return H
        if e == "BEAT" and not s_edge:
            return self._offset(int(s[3]))
        if s == "BEAT" and not e_edge:
            o = self._offset(int(e[3]))
            return None if (o is None or T is None) else T - o
        if e_edge or s_edge:
            return None
        oe, os_ = self._offset(int(e[3])), self._offset(int(s[3]))
        if oe is None or os_ is None:
            return None
        if os_ > oe:
            return os_ - oe
        return None if T is None else T - oe + os_

    # -- public ---------------------------------------------------------------------------------------------
    def gap(self, e: str, s: str):
        if not self.valid:
            return None
        if self.follow:
            g = self._follow_gap(e, s)
            return g
        g = self._free_gap(e, s)
        if g is None:
            return None
        if self.realign:
            r = self._realign_gap(s)
            if r is None:
                return None
            g = min(g, r)
        return g

    def snapshot_event(self):
        return "BEAT" if self.ln.snap == 3 else f"TAP{self.ln.snap}"
