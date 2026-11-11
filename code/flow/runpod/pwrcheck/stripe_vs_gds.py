# klayout -b -r stripe_vs_gds.py -rd js=STRIPES.json -rd gdsdir=DIR -rd lefdir=DIR : each stripe vs real macro Metal4
import pya, json
S = json.load(open(js))
def lef_pins(path):
    pins = {}; cur = None; layer = None
    for line in open(path):
        w = line.split()
        if not w: continue
        if w[0] == "PIN": cur = w[1]
        elif w[0] == "OBS": cur = None
        elif w[0] == "LAYER": layer = w[1]
        elif w[0] == "RECT" and layer == "Metal4" and cur in ("VDD!", "VDDARRAY!", "VSS!"):
            pins.setdefault(cur, []).append([float(x) for x in w[1:5]])
    return pins
done = {}
for inst, d in S.items():
    mname = d["master"]
    if mname not in done:
        ly = pya.Layout(); ly.read(f"{gdsdir}/{mname}.gds"); dbu = ly.dbu; top = ly.cell(mname)
        m4 = pya.Region(top.begin_shapes_rec(ly.find_layer(50, 0))).merged()
        pins = lef_pins(f"{lefdir}/{mname}.lef")
        def R(r): return pya.Region(pya.Box(int(round(r[0] / dbu)), int(round(r[1] / dbu)), int(round(r[2] / dbu)), int(round(r[3] / dbu))))
        pv = pya.Region(); pg = pya.Region()
        for k, lst in pins.items():
            for r in lst: (pg if k == "VSS!" else pv).insert(R(r))
        done[mname] = (m4, pv, pg, R, dbu)
    m4, pv, pg, R, dbu = done[mname]
    bad = 0
    for nm, x0, y0, x1, y1 in d["stripes"]:
        sr = R([x0, y0, x1, y1])
        for poly in m4.interacting(sr).each():
            pr = pya.Region(poly)
            onv, ong = not pr.interacting(pv).is_empty(), not pr.interacting(pg).is_empty()
            wrong = (nm == "VPWR" and (ong or not onv)) or (nm == "VGND" and (onv or not ong))
            if wrong:
                bad += 1
                if bad <= 6:
                    b = poly.bbox()
                    print(inst, nm, "stripe x", round(x0, 2), "touches M4 poly", [round(v * dbu, 2) for v in (b.left, b.bottom, b.right, b.top)], "onVDD", onv, "onVSS", ong)
    print(inst, mname, "stripes", len(d["stripes"]), "wrong-polarity contacts", bad)
