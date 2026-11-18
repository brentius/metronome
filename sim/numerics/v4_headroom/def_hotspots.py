"""Hotspot and hierarchy-ownership map of a routed DEF (v4 Phase 1, E0).

    python3 def_hotspots.py ROUTED.def STDCELL.lef OUT.json [--bins 24x10]

Bins the die into a grid and reports per bin: placed std-cell area by owning hierarchy (first instance-name level;
repair, clock and filler cells by their flow prefix), and routed wire length per routing layer with a track-usage
fraction (length / (bin area / track pitch)). It also tracks wire on the configuration-latch nets (nets driven by a
latch Q pin, cell name containing 'dlhr'), to test whether the cfg bank's fan-out drives congestion.
Evidence class: flow-measured geometry (post detailed route), analysed offline; usage is a wire-length proxy, not
the router's own congestion metric.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("deff")
ap.add_argument("lef", nargs="+")
ap.add_argument("--out", required=True)
ap.add_argument("--bins", default="24x10")
a = ap.parse_args()
NX, NY = map(int, a.bins.split("x"))

size = {}
for lef in a.lef:
    cur = None
    for line in open(lef, errors="replace"):
        t = line.split()
        if not t:
            continue
        if t[0] == "MACRO":
            cur = t[1]
        elif t[0] == "SIZE" and cur:
            size[cur] = float(t[1]) * float(t[3])

txt = open(a.deff, errors="replace").read()
dbu = float(re.search(r"UNITS DISTANCE MICRONS (\d+)", txt).group(1))
x0, y0, x1, y1 = map(float, re.search(r"DIEAREA \( (\S+) (\S+) \) \( (\S+) (\S+) \)", txt).groups())
W, H = (x1 - x0) / dbu, (y1 - y0) / dbu
bw, bh = W / NX, H / NY
pitch = {}
for m in re.finditer(r"TRACKS ([XY]) \S+ DO \d+ STEP (\d+) LAYER (\S+)", txt):
    pitch.setdefault(m.group(3), {})[m.group(1)] = float(m.group(2)) / dbu

def owner(name, cell):
    n = name.lstrip("\\")
    if "fill" in cell.lower() or "decap" in cell.lower():
        return "_fill"
    if "tap" in n.lower() or "tap" in cell.lower():
        return "_tap"
    m = re.match(r"([A-Za-z_]+?)(?:_?\d+)?$", n)
    if "." not in n and "/" not in n:
        low = n.lower()
        for k in ("clkbuf", "clkload", "cts", "clknet"):
            if k in low:
                return "_clock"
        for k in ("rebuffer", "split", "wire", "hold", "input", "output", "max_length", "max_cap", "load_slew", "fanout", "rsz", "gate_cloning", "buffer", "ANTENNA", "clone"):
            if low.startswith(k.lower()):
                return "_repair"
        return "top"
    top = re.split(r"[./]", n)[0]
    return re.sub(r"\\?\[\d+\\?\]$", "[]", top).replace("\\", "")

comp = {}
positions = {}
line_latch_locations = defaultdict(list)
area_bin = defaultdict(lambda: defaultdict(float))
area_owner = defaultdict(float)
cnt_owner = defaultdict(int)
sec = txt[txt.index("\nCOMPONENTS"):txt.index("END COMPONENTS")]
for m in re.finditer(r"^\s*- (\S+) (\S+)(.*?);", sec, re.M | re.S):
    name, cell, rest = m.groups()
    p = re.search(r"\( (-?\d+) (-?\d+) \)", rest)
    if not p:
        continue
    x, y = float(p.group(1)) / dbu, float(p.group(2)) / dbu
    o = owner(name, cell)
    comp[name] = (cell, o)
    positions[name] = (x, y)
    if "dlhr" in cell:
        path = name.replace("\\", "")
        local = re.match(r"g_ln\[(\d+)\]\.u_cfg_line\.", path)
        central = re.match(r"u_cfg(_rest)?\..*?g_byte\[(\d+)\]", path)
        if local:
            line_latch_locations[f"line{local[1]}"].append((x, y))
        elif central:
            byte = int(central[2])
            group = f"line{byte // 32}" if not central[1] and byte < 128 else "remaining"
            line_latch_locations[group].append((x, y))
    ar = size.get(cell, 0.0)
    if ar > 5000:   # macros
        o = "_macro"
    i, j = min(NX - 1, int(x / bw)), min(NY - 1, int(y / bh))
    area_bin[(i, j)][o] += ar
    area_owner[o] += ar
    cnt_owner[o] += 1

wire_bin = defaultdict(lambda: defaultdict(float))
cfg_bin = defaultdict(float)
wire_owner = defaultdict(float)
nsec = txt[txt.index("\nNETS"):txt.index("END NETS")]
OUTPINS = ("Q", "X", "Y", "Z", "QN", "Q_N", "GCLK")
nets = []
drv_of = {}      # instance -> output net (buffers/inverters)
in_of = defaultdict(list)   # instance -> input nets
for m in re.finditer(r"^\s*- (\S+)(.*?);\s*$", nsec, re.M | re.S):
    net, body = m.groups()
    conns = re.findall(r"\( (\S+) (\S+) \)", body.split("+ ROUTED")[0])
    nets.append((net, body, conns))
    for i, pin in conns:
        if i in comp:
            (drv_of.__setitem__(i, net) if pin in OUTPINS else in_of[i].append(net))
# cfg-latch nets, followed through single-input buffer and inverter cells (repair trees)
cfg = {net for net, body, conns in nets
       if any(comp.get(i, ("", ""))[0].find("dlhr") >= 0 and pin.startswith("Q") for i, pin in conns)}
direct_cfg = set(cfg)
latch_nets_hpwl = 0.0
for net, _, conns in nets:
    if net in direct_cfg:
        points = [positions[i] for i, _ in conns if i in positions]
        if points:
            xs, ys = zip(*points)
            latch_nets_hpwl += (max(xs) - min(xs)) + (max(ys) - min(ys))
isbuf = lambda c: re.search(r"_(buf|inv|dlygate)", c) is not None
changed = True
while changed:
    changed = False
    for i, (c, o) in comp.items():
        if isbuf(c) and i in drv_of and drv_of[i] not in cfg and len(in_of[i]) == 1 and in_of[i][0] in cfg:
            cfg.add(drv_of[i]); changed = True
for net, body, conns in nets:
    cfgnet = net in cfg
    drv = None
    for i, pin in conns:
        if i in comp and pin in OUTPINS:
            drv = comp[i][1]
            break
    if "+ ROUTED" not in body:
        continue
    for seg in re.split(r"\+ ROUTED|\bNEW\b", body)[1:]:
        t = seg.split()
        if not t:
            continue
        layer = t[0]
        pts = re.findall(r"\( (\S+) (\S+)(?: \S+)? \)", seg)
        px = py = None
        for sx, sy in pts:
            nx_ = px if sx == "*" else float(sx) / dbu
            ny_ = py if sy == "*" else float(sy) / dbu
            if px is not None and (nx_ != px or ny_ != py):
                L = abs(nx_ - px) + abs(ny_ - py)
                # split the segment over bins by sampling its midpoint per ~bin step
                steps = max(1, int(L / min(bw, bh) * 2) + 1)
                for s in range(steps):
                    fx = px + (nx_ - px) * (s + 0.5) / steps
                    fy = py + (ny_ - py) * (s + 0.5) / steps
                    b = (min(NX - 1, max(0, int(fx / bw))), min(NY - 1, max(0, int(fy / bh))))
                    wire_bin[b][layer] += L / steps
                    if cfgnet:
                        cfg_bin[b] += L / steps
                wire_owner[(drv or "?") if not cfgnet else "cfg_latch_nets"] += L
            px, py = nx_, ny_

def tracks_cap(layer):
    p = pitch.get(layer, {})
    st = min(p.values()) if p else None
    return (bw * bh / st) if st else None

bins = []
for j in range(NY):
    for i in range(NX):
        wb = wire_bin[(i, j)]
        use = {L: round(v / tracks_cap(L), 3) for L, v in wb.items() if tracks_cap(L)}
        bins.append({"i": i, "j": j, "x_um": round(i * bw, 1), "y_um": round(j * bh, 1),
                     "area": {k: round(v) for k, v in area_bin[(i, j)].items()},
                     "wire_um": {k: round(v) for k, v in wb.items()}, "usage": use,
                     "cfg_wire_um": round(cfg_bin[(i, j)])})
latch_placement = {}
for group, points in sorted(line_latch_locations.items()):
    xs, ys = zip(*points)
    latch_placement[group] = {"count": len(points),
                              "centroid_um": [round(sum(axis) / len(axis), 2) for axis in (xs, ys)],
                              "bounds_um": [round(v, 2) for v in (min(xs), min(ys), max(xs), max(ys))]}
res = {"cfg_nets_direct": len(direct_cfg), "cfg_nets_with_buffer_trees": len(cfg),
       "cfg_direct_hpwl_um": round(latch_nets_hpwl), "latch_placement": latch_placement,
       "def": a.deff, "die_um": [W, H], "bins": [NX, NY], "bin_um": [bw, bh], "pitch": pitch,
       "area_by_owner": {k: round(v) for k, v in sorted(area_owner.items(), key=lambda kv: -kv[1])},
       "count_by_owner": dict(cnt_owner), "wire_by_driver_owner": {k: round(v) for k, v in sorted(wire_owner.items(), key=lambda kv: -kv[1])},
       "bins_detail": bins}
json.dump(res, open(a.out, "w"), indent=1)
print("owners", json.dumps(res["area_by_owner"]))
print("wire", json.dumps(res["wire_by_driver_owner"]))
# heat maps: max(Metal2, Metal3) usage, and share of cfg-latch wire
print("cfg nets", len(direct_cfg), "with buffer trees", len(cfg))
for title, f in (("u_cfg latch area um2/1000", lambda b: b["area"].get("u_cfg", 0) / 1000), ("usage Metal2", lambda b: b["usage"].get("Metal2", 0)), ("usage Metal3", lambda b: b["usage"].get("Metal3", 0)),
                 ("usage Metal4", lambda b: b["usage"].get("Metal4", 0)),
                 ("cfg-latch wire share", lambda b: b["cfg_wire_um"] / max(1, sum(b["wire_um"].values())))):
    print(title, "(rows top to bottom, y high first)")
    for j in reversed(range(NY)):
        print(" ".join(f"{f(bins[j*NX+i]):4.2f}" for i in range(NX)))
