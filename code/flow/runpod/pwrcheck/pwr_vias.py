# openroad -python pwr_vias.py ODB : expand every VPWR/VGND special via into layer shapes; report any via shape
# that overlaps an opposite-net special shape (wire or via) on the same layer.
import sys, odb
from collections import defaultdict
db = odb.dbDatabase.create(); odb.read_db(db, sys.argv[1]); blk = db.getChip().getBlock(); dbu = blk.getDbUnitsPerMicron()
def um(b): return [round(v / dbu, 2) for v in b]
def ov(a, b): return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]
S = defaultdict(list); nv = defaultdict(int)
for nm in ("VPWR", "VGND"):
    for sw in blk.findNet(nm).getSWires():
        for b in sw.getWires():
            if not b.isVia():
                S[(nm, b.getTechLayer().getName())].append((b.xMin(), b.yMin(), b.xMax(), b.yMax(), "wire"))
                continue
            x, y = b.getViaXY()
            via = b.getTechVia() or b.getBlockVia()
            nv[nm] += 1
            for vb in via.getBoxes():
                L = vb.getTechLayer()
                if L is None: continue
                S[(nm, L.getName())].append((vb.xMin() + x, vb.yMin() + y, vb.xMax() + x, vb.yMax() + y, "via:" + via.getName()))
print("vias", dict(nv))
hits = 0; per = defaultdict(int)
for layer in sorted({k[1] for k in S}):
    P = S.get(("VPWR", layer), []); G = sorted(S.get(("VGND", layer), []))
    for p in P:
        for g in G:
            if g[0] >= p[2]: break
            if ov(p, g):
                hits += 1; per[(layer, p[4].split(":")[0], g[4].split(":")[0])] += 1
                if hits <= 10: print("SHORT", layer, um(p[:4]), p[4], "x", um(g[:4]), g[4])
print("shorts", hits, dict(per))
