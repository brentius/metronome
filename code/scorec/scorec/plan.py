"""Line planning: clock, taps, symbol encoding, output-pin tables and input tables for one role (SPEC A 5, 13; B 3, 8).

Everything here is derived from part A's text and part B's tables.  The reference codec is not consulted.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction

from . import _paths  # noqa: F401
from score.ast import Clock, Num, ScoreError  # noqa: F401
from score.checks import R3_MAX_TAPS, derive_samples, find_encoding, symbol_waves  # noqa: F401
from score.model import (DATA_SYMBOL, FCLK, boundaries, expand_wave, idle_level, inst_name, nseg, parse_wave,
                         pulled_level, resolve_time, symbol_instances)


class CompileError(Exception):
    """A rejection stated in protocol terms (spec 12.3). `code` is the spec's diagnostic code."""

    def __init__(self, code: str, msg: str):
        self.code, self.msg = code, msg
        super().__init__(f"{code}: {msg}")


# ---- levels -----------------------------------------------------------------------------------------------------
def _flip(c: str) -> str:
    return {"0": "1", "1": "0"}.get(c, c)


def wire_idle(score, wire) -> str:
    """Idle drive of a wire as '0', '1' or 'z'."""
    if wire.mirror_of:
        return _flip(wire_idle(score, score.wire(wire.mirror_of)))
    lv = idle_level(wire)
    return "z" if lv is None else str(lv)


def seg_levels(score, clock, sdef, args, wire_name: str) -> list[str]:
    """Per-segment levels ('0','1','z') of one wire for one symbol instance; an unmentioned wire idles."""
    n = nseg(clock)
    wire = score.wire(wire_name)
    if wire.mirror_of:
        return [_flip(c) for c in seg_levels(score, clock, sdef, args, wire.mirror_of)]
    for w, wave, pos in sdef.waves:
        if w == wire_name:
            raw = expand_wave(wave, sdef.params, args, n, pos)
            out, prev = [], wire_idle(score, wire)
            for c in raw:
                if c == ".":
                    c = prev
                elif c == "x":
                    c = wire_idle(score, wire)
                if c == "1" and (wire.drive == "open-drain" or wire.dir == "shared"):
                    c = "z"
                out.append(c)
                prev = c
            return out
    return [wire_idle(score, wire)] * n


def driven_wires(score, role: str) -> list[str]:
    out = []
    for w in score.all_wires():
        if w.dir == "shared":
            raise CompileError("E-UNSUPPORTED", f"wire '{w.name}': shared wires (open-drain buses) are not compiled yet")
        if role in score.wire_owners(w):
            out.append(w.name)
    return out


def read_wires(score, role: str) -> list[str]:
    return [w.name for w in score.all_wires() if not w.mirror_of and role not in score.wire_owners(w)]


# ---- clock ------------------------------------------------------------------------------------------------------
@dataclass
class ClockPlan:
    mode: str                    # generated | started | recovered | follow
    period: Fraction | None      # chip cycles per beat (None for follow)
    inc: int = 1
    mod: int = 1
    ppm: float = 0.0
    note: str = ""

    @property
    def mod_over_inc(self) -> Fraction:
        return Fraction(self.mod, self.inc)


def plan_clock(score, role, rate_hz=None, follow_mod=None) -> ClockPlan:
    clock = score.clock_for()
    rc = clock.roles[role]
    rate = rate_hz if rate_hz is not None else clock.rate
    if rc.mode == "follow":
        mod = follow_mod or 0
        return ClockPlan("follow", None, 1, mod)
    if rate is None:
        raise CompileError("E-RATE", "clock is 'free': pass the beat rate as an argument (rate_hz=...)")
    period = Fraction(FCLK) / Fraction(rate)
    frac = (Fraction(rate) / Fraction(FCLK))
    inc, mod, ppm = frac.numerator, frac.denominator, 0.0
    if inc > 0xFFFF or mod > 0xFFFF:
        f2 = frac.limit_denominator(0xFFFF)
        while f2.numerator > 0xFFFF:
            f2 = Fraction(f2.numerator, f2.denominator).limit_denominator(f2.denominator - 1)
        inc, mod = f2.numerator, f2.denominator
        ppm = abs(float(f2 / frac) - 1) * 1e6
    if inc >= mod:
        raise CompileError("E-RATE", f"beat rate {float(rate):g} Hz is not below the chip clock {FCLK} Hz")
    note = f"inc/mod {inc}/{mod}" + (f" (rate error {ppm:.0f} ppm)" if ppm else " (exact)")
    return ClockPlan(rc.mode, period, inc, mod, ppm, note)


# ---- taps -------------------------------------------------------------------------------------------------------
@dataclass
class Tap:
    idx: int                   # tap index 0..2
    frac: Fraction | None      # position as a fraction of the beat (None: edge-sourced)
    T: int                     # phase value written to Tk
    why: str


def tx_split_points(score, clock, role, driven) -> list[Fraction]:
    """Split points at which a driven wire changes level for some symbol: those need a tap (R3)."""
    b = boundaries(clock)
    out = []
    for j in range(1, len(b) - 1):
        for sdef, args in symbol_instances(score):
            if sdef.name not in getattr(score, "_tx", {}).get(role, set()):
                continue
            hit = False
            for wn in driven:
                lv = seg_levels(score, clock, sdef, args, wn)
                if lv[j - 1] != lv[j]:
                    hit = True
            if hit:
                out.append(b[j])
                break
    return out


def explicit_samples(score, clock, role, period) -> dict:
    """{wire: set(fraction)} sample points on wires `role` reads (spec 5.3 receive rule)."""
    reads = set(read_wires(score, role))
    got: dict = {}
    for sdef, args in symbol_instances(score):
        for w, tr in sdef.samples:
            wn = w or (sdef.waves[0][0] if sdef.waves else None)
            if wn not in reads:
                continue
            fr = resolve_time(tr, sdef, clock, args, period)
            if fr is None:
                raise CompileError("E-NAMES", f"symbol '{sdef.name}': wire '{tr.wire}' has no {tr.edge} edge to sample at")
            got.setdefault(wn, set()).add(Fraction(fr))
    return got


def plan_taps(score, role, clk: ClockPlan, driven, rx_ptsmap, mode_note="") -> tuple[list[Tap], dict]:
    """Assign tap indices.  Returns (taps ascending by phase, {(wire, frac): slot}) where slot 0..2 is the A capture
    slot of the tap, or 'B' for wire B (captured by tap 1, spec 5.3 R4)."""
    clock = score.clock_for()
    splits = tx_split_points(score, clock, role, driven)
    wires = sorted(rx_ptsmap, key=lambda w: (-len(rx_ptsmap[w]), w))
    A = wires[0] if wires else None
    B = wires[1] if len(wires) > 1 else None
    pts = set(splits)
    for w in wires:
        pts |= set(rx_ptsmap[w])
    pts = sorted(p for p in pts if 0 < p < 1)
    if len(pts) > R3_MAX_TAPS:
        raise CompileError("E-FIT-TAP", f"clock: role {role} needs {len(pts)} taps (split points {[float(s) for s in splits]} "
                                        f"and sample points {[float(p) for w in wires for p in sorted(rx_ptsmap[w])]}); a line has 3")
    bp = None
    if B is not None:
        bp = next(iter(rx_ptsmap[B]))
        if bp not in pts:
            raise CompileError("E-FIT-TAP", "internal: wire B sample point missing")
    # indices must ascend with phase; the B sample takes tap 1
    n = len(pts)
    if bp is not None:
        k = pts.index(bp)
        if k > 1 or n - k - 1 > 1:
            raise CompileError("E-FIT-TAP", f"clock: wire B ('{B}') is captured by tap 1, but {k} tap(s) precede and "
                                            f"{n - k - 1} follow its sample point")
        idxs = [1 if i == k else (0 if i < k else 2) for i in range(n)]
    else:
        idxs = {0: [], 1: [1], 2: [0, 1], 3: [0, 1, 2]}[n]
    taps = []
    for p, ix in zip(pts, idxs):
        why = []
        if p in splits:
            why.append("split")
        for w in wires:
            if p in rx_ptsmap[w]:
                why.append(f"sample {w}")
        T = int(round(p * clk.mod)) if clk.mode != "follow" else int(round(p * clk.mod))
        taps.append(Tap(ix, p, T, "+".join(why)))
    slots = {}
    for t in taps:
        for w in wires:
            if t.frac in rx_ptsmap[w]:
                slots[(w, t.frac)] = "B" if w == B else t.idx
    if A:
        slots["A"], slots["B"] = A, B
    return taps, slots


# ---- symbol classes and encoding ---------------------------------------------------------------------------------
@dataclass
class TxClass:
    key: object
    vec: dict                 # wire -> tuple of levels per interval (SEG value)
    kind: int = 0
    members: list = field(default_factory=list)   # instance names
    code: int = 0


@dataclass
class TxPlan:
    wires: list
    classes: list
    code_of: dict             # instance name -> code
    idle_code: int
    family_k: int             # relevant data parameters of the `bit` family for this role
    family_params: list       # indices of the relevant parameters of `bit`
    family_codes: dict        # tuple of relevant param values -> code
    sel: dict                 # wire -> (b0, b1, b2)
    nint: int
    encoding: str

    def code(self, name: str) -> int:
        return self.code_of[name]

    def bit_code(self, vals: tuple) -> int:
        return self.family_codes[tuple(vals)]

    @property
    def dbit_ok(self) -> bool:
        """Does staging the data bit by L.DBIT (symbol bit 0) alone select the right class?"""
        return bool(self.family_codes) and self.family_k == 1 and all(
            (c & 1) == v[0] for v, c in self.family_codes.items()) and \
            (self.family_codes[(0,)] ^ self.family_codes[(1,)]) == 1


def intervals_for(clock, pts, vec_by_seg: list) -> tuple:
    """Level per interval j (0 .. len(pts)): the level of the segment containing the interval's start."""
    b = boundaries(clock)
    out = []
    for j in range(len(pts) + 1):
        start = Fraction(0) if j == 0 else pts[j - 1]
        s = max(i for i in range(len(b) - 1) if b[i] <= start)
        out.append(vec_by_seg[s])
    return tuple(out)


def plan_tx(score, role, driven, taps: list[Tap]) -> TxPlan:
    clock = score.clock_for()
    pts = [t.frac for t in taps if t.frac is not None]
    nint = len(pts) + 1
    tx_names = set(getattr(score, "_tx", {}).get(role, set()))
    insts = [(s, a) for s, a in symbol_instances(score) if s.name in tx_names]
    idle_vec = {w: (wire_idle(score, score.wire(w)),) * nint for w in driven}

    def vec(sdef, args):
        return {w: intervals_for(clock, pts, seg_levels(score, clock, sdef, args, w)) for w in driven}

    fam = [(s, a) for s, a in insts if s.name == DATA_SYMBOL]
    others = [(s, a) for s, a in insts if s.name != DATA_SYMBOL]
    # relevant data parameters of the family for this role's wires
    fam_params, fam_vec = [], {}
    if fam:
        nparam = len(fam[0][0].params)
        for a_ in [a for _, a in fam]:
            fam_vec[a_] = vec(*[(s, a) for s, a in fam if a == a_][0])
        for i in range(nparam):
            for a_ in fam_vec:
                b_ = a_[:i] + (a_[i] ^ 1,) + a_[i + 1:]
                if b_ in fam_vec and fam_vec[a_] != fam_vec[b_]:
                    fam_params.append(i)
                    break
    classes: list[TxClass] = [TxClass("idle", idle_vec, 0, ["<idle>"])]
    for s, a in others:
        v = vec(s, a)
        for c in classes:
            if c.vec == v:
                c.members.append(inst_name(s, a))
                break
        else:
            classes.append(TxClass(inst_name(s, a), v, len(classes), [inst_name(s, a)]))
    for i, c in enumerate(classes):
        c.kind = i
    k = len(fam_params)
    fam_classes: dict = {}
    if fam:
        fam_kind = len(classes)
        groups: dict = {}
        for a_, v in fam_vec.items():
            key = tuple(a_[i] for i in fam_params)
            groups.setdefault(key, []).append((a_, v))
        for key, lst in groups.items():
            assert all(v == lst[0][1] for _, v in lst)
            c = TxClass(("bit",) + key, lst[0][1], fam_kind, [inst_name(fam[0][0], a_) for a_, _ in lst])
            sh = sum(bit << j for j, bit in enumerate(key))
            c.code = (fam_kind << k) | sh
            fam_classes[key] = c
            classes.append(c)
    for c in classes:
        if not (isinstance(c.key, tuple) and c.key and c.key[0] == "bit"):
            c.code = c.kind << k
    # idle must be code 0; verify R2 (<= 3 bits per wire) and fit 4 bits
    sel, ok = _select_bits(classes, driven)
    encoding = "kind<<k | data bits (idle = 0)"
    if not ok or max(c.code for c in classes) > 15:
        enc = _fallback_encoding(score, classes, driven)
        if enc is None:
            raise CompileError("E-FIT-ENC", "symbols: no 4-bit symbol encoding lets every wire's waveform depend on at "
                                            "most 3 bits (R2)")
        for c, code in zip(classes, enc):
            c.code = code
        sel, ok = _select_bits(classes, driven)
        encoding = "search (idle translated to 0)"
        if not ok:
            raise CompileError("E-FIT-ENC", "internal: search encoding failed R2")
    code_of = {}
    for c in classes:
        for m in c.members:
            code_of[m] = c.code
    fam_codes = {key: c.code for key, c in fam_classes.items()}
    return TxPlan(driven, classes, code_of, classes[0].code, k, fam_params, fam_codes, sel, nint, encoding)


def _select_bits(classes, wires):
    sel = {}
    for w in wires:
        found = None
        for combo in itertools.combinations(range(4), 3):
            good = True
            seen: dict = {}
            for c in classes:
                key = tuple((c.code >> b) & 1 for b in combo)
                if key in seen and seen[key] != c.vec[w]:
                    good = False
                    break
                seen[key] = c.vec[w]
            if good:
                found = combo
                break
        if found is None:
            return None, False
        sel[w] = found
    return sel, True


def _fallback_encoding(score, classes, wires):
    waves = {f"c{i}": {w: list(c.vec[w]) for w in wires} for i, c in enumerate(classes)}
    enc = find_encoding(score, waves)
    if enc is None:
        return None
    base = enc["c0"]
    return [enc[f"c{i}"] ^ base for i in range(len(classes))]


def pin_tables(score, tx: TxPlan, wire: str, oe_needed: bool):
    """(lut, oe) 32-bit raw tables for one output pin: index {SEG[1:0], sym[SEL2], sym[SEL1], sym[SEL0]}."""
    sel = tx.sel[wire]
    lut = oe = 0
    for idx in range(32):
        seg, sb = idx >> 3, idx & 7
        level = None
        for c in tx.classes:
            cb = ((c.code >> sel[0]) & 1) | (((c.code >> sel[1]) & 1) << 1) | (((c.code >> sel[2]) & 1) << 2)
            if cb == sb:
                v = c.vec[wire]
                level = v[min(seg, len(v) - 1)]
                break
        if level is None:
            v = tx.classes[0].vec[wire]
            level = v[min(seg, len(v) - 1)]
        if level == "1":
            lut |= 1 << idx
        if level != "z":
            oe |= 1 << idx
    return lut, oe


# ---- receive: input tables --------------------------------------------------------------------------------------
@dataclass
class RxPlan:
    lut0: int
    lut1: int
    pina: int | None
    pinb: int | None
    snap: str
    data_param: int | None
    classes: str


def expected_level(score, clock, sdef, args, wire_name, p: Fraction) -> str:
    """Level a receiver expects to read on a wire at fraction p of the beat for one symbol: '0', '1' or 'x'."""
    wire = score.wire(wire_name)
    lv = seg_levels(score, clock, sdef, args, wire_name)
    b = boundaries(clock)
    s = max(i for i in range(len(b) - 1) if b[i] <= p)
    v = lv[s]
    if v == "z":
        return str(pulled_level(wire))
    return v


def plan_rx(score, role, taps, slots, bind, snap_tap: str) -> RxPlan | None:
    if "A" not in slots:
        return None
    clock = score.clock_for()
    A, B = slots["A"], slots.get("B")
    rx_names = set(getattr(score, "_rx", {}).get(role, set()))
    reads = set(read_wires(score, role))
    for sd in score.symbols:                  # a symbol sampled on a wire the role reads is received (both roles of a ||)
        if any((w or (sd.waves[0][0] if sd.waves else None)) in reads for w, _ in sd.samples):
            rx_names.add(sd.name)
    insts = [(s, a) for s, a in symbol_instances(score) if s.name in rx_names]
    # which data parameter does the received wire carry?
    data_param = None
    for s, a in insts:
        if s.name == DATA_SYMBOL:
            for w, wave, pos in s.waves:
                if w in (A, B):
                    for it in parse_wave(wave, s.params, pos):
                        if it[0] == "p":
                            data_param = s.params.index(it[1])
    pa = _pin(bind, A)
    pb = _pin(bind, B) if B else None
    pairs = [(w, p, slots[(w, p)]) for (w, p) in [k for k in slots if isinstance(k, tuple)]]
    lut0 = lut1 = 0
    names_nondata: list = []
    for idx in range(32):
        bits = {0: idx & 1, 1: (idx >> 1) & 1, 2: (idx >> 2) & 1, "B": (idx >> 3) & 1}
        labels = set()
        for s, a in insts:
            good = True
            for w, p, slot in pairs:
                e = expected_level(score, clock, s, a, w, p)
                if e != "x" and int(e) != bits[slot]:
                    good = False
                    break
            if good:
                if s.name == DATA_SYMBOL and data_param is not None:
                    labels.add(("d", a[data_param]))
                else:
                    labels.add(("s", s.name))
        data = {l for l in labels if l[0] == "d"}
        if not labels:
            code = 3
        elif data:
            # symbols that read the same as data at the sample points (tpidl vs a 1 bit) are told apart by the grammar's
            # position, not by the input class; the class reports the data bit unless the data values disagree
            code = next(iter(data))[1] if len({l[1] for l in data}) == 1 else 3
        elif {l[0] for l in labels} == {"s"} and len(labels) >= 1:
            nm = sorted(labels)[0][1]
            if len(labels) > 1:
                code = 3
            else:
                if nm not in names_nondata:
                    names_nondata.append(nm)
                code = 2 if names_nondata.index(nm) == 0 else 3
                if names_nondata.index(nm) > 1:
                    raise CompileError("E-FIT-CLASS", f"symbols: role {role} must tell apart more than 4 input classes from "
                                                      f"the samples; more classes need the raw capture (R4)")
        else:
            code = 3
        lut0 |= (code & 1) << idx
        lut1 |= ((code >> 1) & 1) << idx
    return RxPlan(lut0, lut1, pa, pb, snap_tap, data_param, f"data bit = IN0; 2 = {names_nondata[:1]}, 3 = violation")


def _pin(bind, wire):
    p = bind.get(wire, (None, None))[0]
    if p is None:
        raise CompileError("E-BIND", f"wire '{wire}' is read but has no input pin P<k>")
    return p
