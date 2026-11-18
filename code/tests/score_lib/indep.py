"""Independent decoders and encoders for the library protocols, written from each standard's own definitions.

Nothing here imports the score parser, the reference codec, the compiler or the machine model.  Inputs are lists of
0/1 samples taken once per 60 MHz chip cycle (the cycle model's pins, or the codec's bus).  Where a standard fixes
a time, it is checked in nanoseconds with the tolerance the standard gives.
"""
from __future__ import annotations

CLK = 60_000_000
NS = 1e9 / CLK                    # one chip cycle in ns (16.667)


def edges(s, level=None):
    """Indices i where s[i] != s[i-1] (optionally only transitions to `level`)."""
    return [i for i in range(1, len(s)) if s[i] != s[i - 1] and (level is None or s[i] == level)]


def runs(s):
    """[(level, start, length)] of constant runs."""
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        out.append((s[i], i, j - i))
        i = j
    return out


# ---------------------------------------------------------------------------------------------------------------
# WS2812 / WS2812B (Worldsemi datasheet): T0H 0.40 us, T0L 0.85 us, T1H 0.80 us, T1L 0.45 us, each +-150 ns;
# a low of more than 50 us latches (reset).  Data is G, R, B per LED, most significant bit first.
# ---------------------------------------------------------------------------------------------------------------
WS_T0H, WS_T0L, WS_T1H, WS_T1L, WS_TOL, WS_RESET = 400, 850, 800, 450, 150, 50_000


def ws2812_decode(s, tol_ns=WS_TOL, reset_ns=WS_RESET):
    """-> (frames, violations).  frames = list of byte strings (one per latch).  A violation is a pulse whose high or
    low time is outside the datasheet window."""
    rs = runs(s)
    frames, cur, bad = [], [], []
    k = 0
    # skip the idle-low lead-in
    while k < len(rs) and rs[k][0] == 0:
        k += 1
    while k < len(rs):
        lvl, st, n = rs[k]
        if lvl == 1:
            hi = n * NS
            low = rs[k + 1][2] * NS if k + 1 < len(rs) else None
            if abs(hi - WS_T0H) <= tol_ns:
                bit, tl = 0, WS_T0L
            elif abs(hi - WS_T1H) <= tol_ns:
                bit, tl = 1, WS_T1L
            else:
                bad.append((st, "high", hi))
                bit, tl = None, None
            if bit is not None:
                cur.append(bit)
                if low is not None and low <= reset_ns and abs(low - tl) > tol_ns:
                    bad.append((st, "low", low))
            if low is not None and low > reset_ns:
                if len(cur) % 8:
                    bad.append((st, "partial byte", len(cur)))
                frames.append(bytes(sum(b << (7 - i) for i, b in enumerate(cur[j:j + 8])) for j in range(0, len(cur) - 7, 8)))
                cur = []
            k += 2
        else:
            k += 1
    return frames, bad
