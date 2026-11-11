# openroad -python stripes_json.py ODB OUT.json : Metal4 power stripes over each SRAM macro, in master coordinates.
import sys, odb, json
db = odb.dbDatabase.create(); odb.read_db(db, sys.argv[1]); blk = db.getChip().getBlock(); dbu = blk.getDbUnitsPerMicron()
out = {}
for inst in blk.getInsts():
    m = inst.getMaster()
    if not m.isBlock(): continue
    ox, oy = inst.getLocation(); W, H = m.getWidth(), m.getHeight(); fs = inst.getOrient() == "MX"
    rows = []
    for nm in ("VPWR", "VGND"):
        for sw in blk.findNet(nm).getSWires():
            for b in sw.getWires():
                if b.isVia() or b.getTechLayer().getName() != "Metal4": continue
                x0, x1 = b.xMin() - ox, b.xMax() - ox
                y0, y1 = max(b.yMin() - oy, 0), min(b.yMax() - oy, H)
                if x1 <= 0 or x0 >= W or y1 <= y0: continue
                if fs: y0, y1 = H - y1, H - y0
                rows.append([nm, x0 / dbu, y0 / dbu, x1 / dbu, y1 / dbu])
    out[inst.getName()] = {"master": m.getName(), "stripes": rows}
json.dump(out, open(sys.argv[2], "w"))
print({k: len(v["stripes"]) for k, v in out.items()})
