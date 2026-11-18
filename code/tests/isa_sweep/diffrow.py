"""Decode and diff one trace row (debug helper): python diffrow.py ROOT OUTDIR/group BATCH ROW [N]"""
import sys
from pathlib import Path
import sweep
root = Path(sys.argv[1]); sweep.load_tools(root)
fl = sweep.fields()
g = Path(sys.argv[2]); b = sys.argv[3]; r0 = int(sys.argv[4]); n = int(sys.argv[5]) if len(sys.argv) > 5 else 1
def rows(f):
    d = {}
    for l in open(f):
        bb, rr, v = l.split()
        d[(bb, int(rr))] = int(v, 16)
    return d
R = rows(g / "rtl_trace.txt"); Mo = rows(g / "model_trace.txt")
total = sum(w for _n, w, _p, _m in fl)
def dec(v):
    out = {}; sh = total
    for name, w, _p, _m in fl:
        sh -= w; out[name] = (v >> sh) & ((1 << w) - 1)
    return out
for r in range(r0, r0 + n):
    a, c = dec(R[(b, r)]), dec(Mo[(b, r)])
    print(r, {k: (hex(a[k]), hex(c[k])) for k in a if a[k] != c[k]})
