"""Integer reference of on-chip UART inference (v4 Phase 0, BOTS/PLANS/V4_PLAN.md section 5).

The host tool (`infer.py`) uses floats, medians and least squares. This module computes the same answers with the
operations the Metronome firmware has (8-bit add/subtract/compare with carry chains, right shifts through an LFSR at
polynomial 0, one restoring-division routine), from the records the chip actually captures (SPEC v2 12.4:
`{DC, PIN}` per edge, DC = cycles since the previous edge). Every intermediate keeps a declared width (`_w`), so a
value that would not fit the firmware's registers fails here first.

Result: the learned configuration a firmware would write: idle level, framing and the receiver's beat as
`INC / MOD` (cycles per bit = MOD / INC, the beat generator does the division), plus the decoded words for checking.
Evidence: model level (compared with `infer.py` on the transcription corpus); nothing on RTL or hardware.
"""
from __future__ import annotations

from dataclasses import dataclass, field

FRAC = 4                    # fixed point: T16 = 16 x (cycles per bit)
KMAX = 15                   # longest run accepted, in bits (4-bit k)
MIN_T = 4                   # cycles per bit, as the host tool
DC_BITS = 19


class ChipInferenceError(Exception):
    pass


def _w(v, bits, what):
    if not 0 <= v < (1 << bits):
        raise ChipInferenceError(f"{what} = {v} does not fit {bits} bits")
    return v


def div(n, d, nbits=32, dbits=24):
    """Restoring division as the firmware loop does it (one quotient bit per iteration). Returns (q, r)."""
    _w(n, nbits, "dividend")
    _w(d, dbits, "divisor")
    if d == 0:
        raise ChipInferenceError("division by zero")
    q, r = 0, 0
    for i in range(nbits - 1, -1, -1):
        r = (r << 1) | ((n >> i) & 1)
        q <<= 1
        if r >= d:
            r -= d
            q |= 1
    return q, r


def records_from_levels(levels):
    """Capture records of a 0/1 level sequence, as S0 edge capture makes them (DC_0 counted from the trace start)."""
    recs, last = [], 0
    for i in range(1, len(levels)):
        if levels[i] != levels[i - 1]:
            recs.append((min(i - last, (1 << DC_BITS) - 1), levels[i] & 1))
            last = i
    return recs


@dataclass
class ChipUart:
    idle: int
    T16: int                    # 16 x cycles per bit
    inc: int                    # learned beat: cycles per bit = mod / inc
    mod: int
    data_bits: int
    parity: str
    stop_bits: int
    words: list
    n_runs: int
    n_used: int
    ops: dict = field(default_factory=dict)    # operation counts, for the firmware cycle estimate


def _quantise(runs, T16):
    """k = round(r / T) and the accept test |r/T - k| < 0.34375, in fixed point. Returns (ks, used flags)."""
    ks, used = [], []
    thr = (T16 >> 2) + (T16 >> 4) + (T16 >> 5)          # 0.34375 T16
    for r in runs:
        r16 = _w(r << FRAC, DC_BITS + FRAC, "r16")
        k, _ = div(2 * r16 + T16, 2 * T16)
        dev = abs(r16 - k * T16)
        ok = 1 <= k <= KMAX and dev < thr
        ks.append(k if ok else 0)
        used.append(ok)
    return ks, used


def _bit_time(runs):
    """Candidates for T16 (as the host: the shortest-run cluster may be 1, 2 or 3 bits), refined twice."""
    m = min(runs)
    lim = m + (m >> 1)                                   # cluster: runs <= 1.5 x min (host: 1.4)
    cl = [r for r in runs if r <= lim]
    s = _w(sum(cl), 24, "cluster sum")
    base16, _ = div(s << FRAC, len(cl))
    out = []
    for mult in (1, 2, 3):
        T16, _ = div(base16, mult)
        if T16 < MIN_T << FRAC:
            continue
        for _ in range(3):
            ks, used = _quantise(runs, T16)
            sk = sum(ks)
            if sk == 0:
                break
            sr = sum(r for r, u in zip(runs, used) if u)
            T16, _ = div(_w(sr, 28, "run sum") << FRAC, sk)
        ks, used = _quantise(runs, T16)
        if sum(used) * 10 >= 9 * len(runs):
            out.append((T16, ks, used))
    return out


def _decode(bits, idle, n, par):
    """Frames in the bit domain: start = first active bit after idle; L bits; stop at idle; parity. (words, bad,
    starts)."""
    L = 1 + n + (par != "none") + 1
    i = 0
    while i < len(bits) and bits[i] != idle:
        i += 1
    words, bad, starts = [], 0, []
    while True:
        while i < len(bits) and bits[i] == idle:
            i += 1
        if i + L > len(bits):
            break
        f = [1 if b == idle else 0 for b in bits[i:i + L]]          # logical 1 = idle level
        data = f[1:1 + n]
        ok = f[0] == 0 and f[-1] == 1
        if par != "none":
            ok = ok and (sum(data) + f[1 + n]) % 2 == (0 if par == "even" else 1)
        bad += not ok
        words.append(sum(b << j for j, b in enumerate(data)))
        starts.append(i)
        i += L
    return words, bad, starts


def infer(records) -> ChipUart:
    if len(records) < 8:
        raise ChipInferenceError("too few edges")
    idle = records[0][1] ^ 1
    runs = [dc for dc, _ in records[1:]]                 # run i ends at edge i; its level is records[i-1].level
    levels = [lv for _, lv in records[:-1]]
    cands = _bit_time(runs)
    if not cands:
        raise ChipInferenceError("no consistent bit time")
    for T16, ks, used in cands:
        if not all(used):                                # an unquantisable run inside the capture breaks the bits
            # keep only the longest fully-quantised stretch would be the general rule; the firmware restarts
            pass
        bits = [idle] * 2
        for lv, k, u in zip(levels, ks, used):
            bits += [lv] * (k if u else 0)
        bits += [idle] * 2
        valid = []
        for n in range(5, 10):
            for par in ("none", "even", "odd"):
                words, bad, starts = _decode(bits, idle, n, par)
                if words and bad * 20 <= len(words):
                    valid.append((1 + n + (par != "none") + 1, n, par, words, starts))
        if not valid:
            continue
        Lmin = min(v[0] for v in valid)
        top = [v for v in valid if v[0] == Lmin]
        withpar = [v for v in top if v[2] != "none"]
        nopar = [v for v in top if v[2] == "none"]
        L, n, par, words, starts = withpar[0] if (withpar and len(top[0][3]) >= 6) or not nopar else nopar[0]
        stop = 1
        if len(starts) >= 2:
            sp = min(b - a for a, b in zip(starts, starts[1:]))
            if sp >= L:
                stop = 1 + sp - L
        # learned beat: as many used runs as fit MOD (16 bits); INC = their bits
        mod = inc = 0
        for r, k, u in zip(runs, ks, used):
            if u and mod + r <= 0xFFFF and inc + k <= 0xFFFF:
                mod += r
                inc += k
        return ChipUart(idle, T16, inc, mod, n, par, stop, words, len(runs), sum(used))
    raise ChipInferenceError("no UART framing fits")


# ---- stage 1: the exact algorithm of the firmware (fw_stage1.py) -------------------------------------------------
@dataclass
class Stage1:
    ok: bool
    reason: str
    idle: int = 0
    TU: int = 0                 # 32 x cycles per bit (16 bits): the learned beat is INC = 32, MOD = TU
    used: int = 0
    runs: int = 0
    mult: int = 0


def r_of_word(w):
    """Record bytes 1..3 with byte 1 masked to bits 7:5: DC << 5 (24 bits), the firmware's run value."""
    return (w >> 8) & 0xFFFFE0


def stage1(words, pin):
    """Bit time from capture record words (SPEC v2 12.4), in the firmware's integer steps. All values in 1/32 cycle."""
    if len(words) < 8:
        return Stage1(False, "too few records")
    idle = ((words[0] >> pin) & 1) ^ 1
    runs = [r_of_word(w) for w in words[1:]]
    n = len(runs)
    m = min(runs)
    lim = m + (m >> 1)
    cl = [r for r in runs if r <= lim]
    S, cnt = sum(cl), len(cl)
    if (S >> 16) >= cnt:
        return Stage1(False, "bit time too long (>= 2048 cycles)", idle)
    TU0 = S // cnt
    for mult in (1, 2, 3):
        TU = TU0 // mult
        if TU < 128:
            continue
        good = True
        for _ in range(3):
            thr = (TU >> 2) + (TU >> 4) + (TU >> 5)
            sR = sk = used = 0
            for R in runs:
                x, q, rej = R, 0, False
                while x >= TU:
                    if q == 15:
                        rej = True
                        break
                    x -= TU
                    q += 1
                if rej:
                    continue
                if x < thr:
                    k = q
                elif TU - x < thr:
                    k = q + 1
                else:
                    continue
                if not 1 <= k <= 15:
                    continue
                sR += R
                sk += k
                used += 1
            if sk == 0 or (sR >> 16) >= sk:
                good = False
                break
            TU = sR // sk
        if good and used * 10 >= 9 * n and TU >= 128:
            return Stage1(True, "", idle, TU, used, n, mult)
    return Stage1(False, "no consistent bit time", idle)
