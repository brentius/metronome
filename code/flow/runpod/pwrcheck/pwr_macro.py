# openroad -python pwr_macro.py ODB : for every Metal4 power stripe crossing an SRAM macro, check it lies only on
# same-polarity macro power-pin shapes and touches no opposite-polarity pin or macro OBS on Metal4.
import sys, odb
db = odb.dbDatabase.create(); odb.read_db(db, sys.argv[1]); blk = db.getChip().getBlock()
dbu = blk.getDbUnitsPerMicron()
def um(b): return [round(v / dbu, 2) for v in b]
def ov(a, b): return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]
stripes = []
for nm in ("VPWR", "VGND"):
    for sw in blk.findNet(nm).getSWires():
        for b in sw.getWires():
            if not b.isVia() and b.getTechLayer().getName() == "Metal4":
                stripes.append((nm, (b.xMin(), b.yMin(), b.xMax(), b.yMax())))
bad = 0
per = {}
for inst in blk.getInsts():
    m = inst.getMaster()
    if not m.isBlock():
        continue
    ox, oy = inst.getLocation(); H = m.getHeight(); fs = inst.getOrient() == 'MX'
    def T(g):
        y0, y1 = (H - g.yMax(), H - g.yMin()) if fs else (g.yMin(), g.yMax())
        return (g.xMin() + ox, y0 + oy, g.xMax() + ox, y1 + oy)
    assert inst.getOrient() in ('R0', 'MX'), inst.getOrient()
    bb = inst.getBBox(); ib = (bb.xMin(), bb.yMin(), bb.xMax(), bb.yMax())
    pins = {"VPWR": [], "VGND": [], "SIG": []}
    for mt in m.getMTerms():
        key = "VPWR" if mt.getName() in ("VDD!", "VDDARRAY!") else "VGND" if mt.getName() == "VSS!" else "SIG"
        for mp in mt.getMPins():
            for g in mp.getGeometry():
                if g.getTechLayer() and g.getTechLayer().getName() == "Metal4":
                    pins[key].append(T(g))
    obs = []
    for g in m.getObstructions():
        if g.getTechLayer() and g.getTechLayer().getName() == "Metal4":
            obs.append(T(g))
    n_cross = 0
    for nm, s in stripes:
        if not ov(s, ib):
            continue
        n_cross += 1
        other = "VGND" if nm == "VPWR" else "VPWR"
        for kind, lst in ((other, pins[other]), ("SIG", pins["SIG"]), ("OBS", obs)):
            for p in lst:
                if ov(s, p):
                    bad += 1
                    per[(inst.getName(), nm, kind)] = per.get((inst.getName(), nm, kind), 0) + 1
                    if bad <= 3:
                        print("CONFLICT", inst.getName(), nm, "stripe", um(s), "touches", kind, um(p))
                    break
    print(inst.getName(), m.getName(), "orient", inst.getOrient(), "bbox", um(ib), "stripes crossing", n_cross,
          "pins M4 pwr/gnd/sig", len(pins["VPWR"]), len(pins["VGND"]), len(pins["SIG"]), "obs M4", len(obs))
print("conflicts", bad, per)
