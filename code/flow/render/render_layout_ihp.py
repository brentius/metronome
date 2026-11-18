"""Metronome layout renderer for IHP SG13CMOS5L (adapted from the ns-accel V3-8 renderer). Two stages.

Stage 1 (KLayout Python module, geometry; no GUI needed):
  python render_layout_ihp.py --render OUTDIR --gds TOP.gds --lyp sg13cmos5l.lyp [--detail CX,CY,W] [--W 4000]
    [--style ihp|ns-accel]
  Loads the GDS with the PDK's own layer-properties file (official IHP colours and stipples), renders
  raw_full.png (all layers the .lyp shows), raw_block.png (metals and vias only), raw_detail.png
  (all layers, zoomed), and writes views.json (exact view boxes in um, hard-macro boxes, layer legend).
Stage 2 (PIL, annotation and provenance):
  python render_layout_ihp.py --annotate OUTDIR --inst instances.txt --cells instances_cells.tsv [--tag T]
    [--version v3 --name r1 --font-dir DIR --detail-caption TEXT]
  Writes ihp-full-chip.png, ihp-block-overview.png, ihp-routing-detail.png and provenance.json.
  The ns-accel style uses the reference's custom M1-M4 palette on IHP drawing layers,
  opaque fills and the same annotation layout; the style is saved in views.json.

instances.txt and instances_cells.tsv come from render_dump_def.py (final DEF). Rendering is not DRC, LVS
or timing evidence.
"""
import hashlib
import json
import os
import statistics
import sys
import time

METAL_VIA = ["8/0", "19/0", "10/0", "29/0", "30/0", "49/0", "50/0"]  # Metal1, Via1, Metal2, Via2, Metal3, Via3, Metal4
NS_LAYERS = {
    "8/0": ("M1", "#7f7f7f"), "10/0": ("M2", "#1f77b4"),
    "30/0": ("M3", "#d62728"), "50/0": ("M4", "#2ca02c"),
}
NS_VIEWS = {"full": ("8/0", "10/0", "30/0", "50/0"),
            "block": ("10/0", "30/0", "50/0"),
            "detail": ("8/0", "10/0", "30/0", "50/0")}
FONT_DIRS = [r"C:\Windows\Fonts", "/usr/share/fonts/truetype/dejavu"]
BG = "#101418"


def arg(name, default=None):
    a = sys.argv
    return a[a.index(name) + 1] if name in a else default


def stage1(out):
    import klayout.db as db
    import klayout.lay as lay
    gds, lyp = arg("--gds"), arg("--lyp")
    style = arg("--style", "ihp")
    if style not in ("ihp", "ns-accel"):
        raise ValueError("--style must be ihp or ns-accel")
    W = int(arg("--W", 4000))
    os.makedirs(out, exist_ok=True)
    log = open(os.path.join(out, "stage1.log"), "w")

    def L(*a):
        print(*a, file=log, flush=True)
    t0 = time.time()
    lv = lay.LayoutView()
    lv.load_layout(gds, True)
    ly = lv.active_cellview().layout()
    top = ly.top_cells()[0]
    die = top.dbbox()
    L("load_s", round(time.time() - t0, 1), "dbu", ly.dbu, "top", top.name, "bbox_um", die.to_s())
    macros = []
    for inst in top.each_inst():
        if inst.cell.name.startswith("RM_IHP"):
            b = inst.dbbox()
            macros.append({"master": inst.cell.name, "box": [b.left, b.bottom, b.right, b.top]})
    L("macros", macros)
    present = {f"{ly.get_info(i).layer}/{ly.get_info(i).datatype}" for i in ly.layer_indexes()}
    L("gds_layers", sorted(present))
    m = 8.0 if style == "ns-accel" else 6.0
    full = db.DBox(die.left - m, die.bottom - m, die.right + m, die.top + m)
    cx, cy, dw = [float(x) for x in arg("--detail", "325.9,389.3,60").split(",")]
    specs = (("full", full, W, None), ("block", full, int(W * 1.25), METAL_VIA),
             ("detail", db.DBox(cx - dw / 2, cy - dw * 0.3, cx + dw / 2, cy + dw * 0.3), 2400, None))
    views = {"macros": macros, "die_um": [die.left, die.bottom, die.right, die.top], "gds_layers": sorted(present),
             "style": style}
    for name, b, w, only in specs:
        h = int(round(w * b.height() / b.width()))
        lv.load_layer_props(lyp)
        legend = []
        it = lv.begin_layers()
        while not it.at_end():
            node = it.current()
            src = node.source.split("@")[0].strip()
            if style == "ns-accel":
                shown = src in present and src in NS_VIEWS[name]
            else:
                shown = src in present and (only is None or src in only)
            if node.has_children():
                it.next()
                continue
            lp = node.dup()
            lp.visible = shown
            if style == "ns-accel" and src in NS_LAYERS:
                nm, colour = NS_LAYERS[src]
                lp.name = nm
                lp.fill_color = int(colour[1:], 16)
                lp.frame_color = lp.fill_color
                lp.dither_pattern = 0
                lp.transparent = False
            lv.set_layer_properties(it, lp)
            if shown:
                legend.append({"source": src, "name": lp.name if style == "ns-accel" else node.name,
                               "fill": "#%06x" % (lp.fill_color & 0xFFFFFF),
                               "frame": "#%06x" % (lp.frame_color & 0xFFFFFF), "dither": lp.dither_pattern})
            it.next()
        lv.max_hier_levels = 99
        lv.set_config("background-color", BG)
        lv.set_config("grid-visible", "false")
        lv.set_config("text-visible", "false")
        lv.resize(w, h)
        lv.zoom_box(b)
        t1 = time.time()
        lv.save_image_with_options(os.path.join(out, f"raw_{name}.png"), w, h, 0, 0, 0, b, False)
        L("rendered", name, w, h, "s", round(time.time() - t1, 1), "layers", [x["name"] for x in legend])
        views[name] = {"file": f"raw_{name}.png", "px": [w, h], "box_um": [b.left, b.bottom, b.right, b.top],
                       "legend": legend}
    json.dump(views, open(os.path.join(out, "views.json"), "w"), indent=1)
    for k, p in (("gds", gds), ("lyp", lyp)):
        d = open(p, "rb").read()
        open(os.path.join(out, f"{k}.sha256"), "w").write(f"{hashlib.sha256(d).hexdigest()} {len(d)} {p}\n")
    L("klayout", db.__version__ if hasattr(db, "__version__") else "")
    L("done_s", round(time.time() - t0, 1))


# ---------------------------------------------------------------- stage 2
FAMILY = {  # unit prefix -> (family label, colour)
    "core": ("core", (255, 96, 96)),
    "line": ("line", (255, 205, 70)),
    "thread": ("thread", (110, 215, 255)),
    "stream": ("stream", (120, 255, 150)),
    "shifter": ("shifter", (255, 140, 225)),
    "cfg_latches": ("config latch bank (u_cfg)", (185, 160, 255)),
    "host": ("host SPI port (u_host)", (255, 255, 255)),
    "mem_arbiter": ("memory arbiter (u_mem)", (255, 150, 60)),
    "acc": ("accumulator / ALU (u_acc)", (70, 215, 200)),
    "counter": ("counter", (215, 215, 140)),
    "lfsr": ("LFSR", (215, 215, 140)),
}
MACRO_LABEL = {
    "u_dmem": "data RAM u_dmem (512x32, 2 KB)",
    "u_pmem0": "program RAM core 0 (256x64)",
    "u_pmem1": "program RAM core 1 (256x64)",
}


def family(u):
    for k in sorted(FAMILY, key=len, reverse=True):
        if u.startswith(k):
            return k
    return None


def pretty(u):
    f = family(u)
    num = u[len(f):] if f and u[len(f):].isdigit() else ""
    return {"core": f"core {num}", "line": f"line {num}", "thread": f"thread {num}", "stream": f"stream {num}",
            "shifter": f"shifter {num}", "counter": f"counter {num}", "lfsr": f"lfsr {num}",
            "cfg_latches": "config latch bank", "host": "host SPI", "mem_arbiter": "mem arbiter",
            "acc": "accumulator"}.get(f, u)


def font(size, bold=False):
    from PIL import ImageFont
    for d in ([arg('--font-dir')] if arg('--font-dir') else []) + FONT_DIRS:
        for n in (("DejaVuSans-Bold.ttf", "arialbd.ttf") if bold else ("DejaVuSans.ttf", "arial.ttf")):
            p = os.path.join(d, n)
            if os.path.exists(p):
                return ImageFont.truetype(p, int(size))
    return ImageFont.load_default(int(size))


def hexrgb(s):
    return tuple(int(s[i:i + 2], 16) for i in (1, 3, 5))


def nice_len(target):
    import math
    e = 10 ** math.floor(math.log10(target))
    for m in (1, 2, 5, 10):
        if m * e >= target * 0.6:
            return m * e
    return 10 * e


def load_inst(path):
    units, seeds, info = {}, {}, {}
    for line in open(path):
        p = line.split()
        if p and p[0] == "UNIT":
            units[p[2]] = int(p[3])
        elif p and p[0] == "SEED":
            seeds[p[1]] = int(p[2])
        elif p and p[0] in ("NINST", "NSTD"):
            info[p[0]] = p[1:]
    return units, seeds, info


def load_cells(path):
    cells = []
    with open(path) as f:
        next(f)
        for line in f:
            n, m, x, y, u, s = line.rstrip("\n").split("\t")
            cells.append((float(x), float(y), u, s == "1"))
    return cells


def load_unit_boxes(path):
    boxes = {}
    with open(path) as f:
        for line in f:
            p = line.split()
            if p and p[0] == "UNIT":
                boxes[p[2]] = [float(x) for x in p[4:8]]
    return boxes


def stage2(out, instf, cellsf, tag):
    from PIL import Image, ImageDraw, ImageEnhance
    views = json.load(open(os.path.join(out, "views.json")))
    units, seeds, info = load_inst(instf)
    cells = load_cells(cellsf)
    style = arg("--style", views.get("style", "ihp"))
    if style not in ("ihp", "ns-accel"):
        raise ValueError("--style must be ihp or ns-accel")
    if style != views.get("style", "ihp"):
        raise ValueError("annotation style must match the geometry render in views.json")
    unit_boxes = load_unit_boxes(instf) if style == "ns-accel" else {}
    macros = views["macros"]
    die = views["die_um"]
    produced = {}
    name = f"Metronome {arg('--version', 'v2')} {arg('--name', 'r4b')}"
    for vname, fname, title in (("full", "ihp-full-chip.png", f"{name} - full chip (IHP SG13CMOS5L)"),
                                ("block", "ihp-block-overview.png", f"{name} - block overview"),
                                ("detail", "ihp-routing-detail.png", f"{name} - routing detail")):
        v = views[vname]
        im = Image.open(os.path.join(out, v["file"])).convert("RGB")
        w, h = im.size
        x0, y0, x1, y1 = v["box_um"]
        sx, sy = w / (x1 - x0), h / (y1 - y0)

        def P(x, y):
            return ((x - x0) * sx, h - (y - y0) * sy)
        base = max(14, w // 110) if style == "ns-accel" else max(16, w // 100)
        pad_t = int(base * 5.5)
        pad_b = int(base * (9 if style == "ns-accel" else (18.5 if vname == "block" else 8)))
        if vname == "block" and style != "ns-accel":
            im = ImageEnhance.Brightness(im).enhance(0.42)
        canvas = Image.new("RGB", (w, h + pad_t + pad_b), hexrgb(BG))
        canvas.paste(im, (0, pad_t))
        d = ImageDraw.Draw(canvas, "RGBA")
        oy = pad_t
        if vname in ("full", "block") and style != "ns-accel":
            # placed std cells, coloured by inferred unit (block view only)
            if vname == "block":
                r = max(1.5, sx * 1.6)
                for x, y, u, s in cells:
                    f = family(u)
                    if not f:
                        continue
                    col = FAMILY[f][1]
                    a, b = P(x + 1.0, y + 1.9)
                    d.ellipse([a - r, b + oy - r, a + r, b + oy + r], fill=col + (170 if s else 105,))
            for mc in macros:
                bx0, by0, bx1, by1 = mc["box"]
                a, b = P(bx0, by1)
                c, e = P(bx1, by0)
                d.rectangle([a, b + oy, c, e + oy], outline=(235, 235, 235, 255 if vname == "block" else 170),
                            width=max(2, w // 1200))
            # macro labels: match instance by position (pmem0 at bottom right, pmem1 top right, dmem left)
            fm = font(base * 1.15, True)
            for mc in macros:
                bx0, by0, bx1, by1 = mc["box"]
                key = "u_dmem" if "512x32" in mc["master"] else ("u_pmem0" if by0 < (die[3] / 2) else "u_pmem1")
                a, b = P(bx0, by1)
                c, e = P(bx1, by0)
                txt = MACRO_LABEL[key]
                tw = d.textlength(txt, font=fm)
                cxp, cyp = (a + c) / 2, (b + e) / 2 + oy
                d.rectangle([cxp - tw / 2 - 6, cyp - base * 0.85, cxp + tw / 2 + 6, cyp + base * 0.85], fill=(0, 0, 0, 200))
                d.text((cxp, cyp), txt, fill=(235, 235, 235), font=fm, anchor="mm")
            if vname == "block":
                # unit labels at the median of the unit's seed cells (registers and SRAM-fed cells)
                fl = font(base * 0.95, True)
                placed = []
                by = {}
                for x, y, u, s in cells:
                    by.setdefault(u, {"all": [], "seed": []})["all"].append((x, y))
                    if s:
                        by[u]["seed"].append((x, y))
                order = sorted(by, key=lambda u: -len(by[u]["all"]))
                for u in order:
                    f = family(u)
                    if not f:
                        continue
                    pts = by[u]["seed"] or by[u]["all"]
                    mx = statistics.median(p[0] for p in pts)
                    my = statistics.median(p[1] for p in pts)
                    px, py = P(mx, my)
                    py += oy
                    txt = pretty(u)
                    tw = d.textlength(txt, font=fl)
                    hh = base * 0.75
                    for step in range(40):  # nudge vertically to avoid overlapping earlier labels
                        cand = [px - tw / 2 - 8, py - hh - 3, px + tw / 2 + 8, py + hh + 3]
                        if not any(not (cand[2] < q[0] or cand[0] > q[2] or cand[3] < q[1] or cand[1] > q[3]) for q in placed):
                            break
                        py += (hh * 2.2) * (1 if step % 2 == 0 else -1) * (step // 2 + 1) * (1 if step % 2 == 0 else 1)
                    placed.append(cand)
                    col = FAMILY[f][1]
                    d.rectangle(cand, fill=(0, 0, 0, 215), outline=col + (255,), width=2)
                    d.text((px, py), txt, fill=col, font=fl, anchor="mm")
        elif style == "ns-accel" and vname in ("full", "block"):
            fm = font(base, True)
            for mc in macros:
                bx0, by0, bx1, by1 = mc["box"]
                a, b = P(bx0, by1)
                c, e = P(bx1, by0)
                d.rectangle([a, b + oy, c, e + oy], outline=(255, 255, 255, 255 if vname == "block" else 140),
                            width=max(1, w // 1600))
                if vname == "full":
                    continue
                key = "u_dmem" if "512x32" in mc["master"] else (
                    "u_pmem0" if by0 < (die[3] / 2) else "u_pmem1")
                txt = MACRO_LABEL[key]
                cxp, cyp = (a + c) / 2, (b + e) / 2 + oy
                tw = d.textlength(txt, font=fm)
                d.rectangle([cxp - tw / 2 - 4, cyp - base * 0.8, cxp + tw / 2 + 4,
                             cyp + base * 0.8], fill=(0, 0, 0, 170))
                d.text((cxp, cyp), txt, fill=(255, 255, 255), font=fm, anchor="mm")
            if vname == "block" and "cfg_latches" in unit_boxes:
                ux0, uy0, ux1, uy1 = unit_boxes["cfg_latches"]
                a, b = P(ux0, uy1)
                c, e = P(ux1, uy0)
                col = (200, 160, 255)  # ns-accel's unit-box purple
                d.rectangle([a, b + oy, c, e + oy], fill=col + (45,), outline=col + (255,), width=3)
                txt = "config latch bank (u_cfg)"
                f = font(base * 0.95, True)
                tw = d.textlength(txt, font=f)
                tx = min(max(a, 4), w - tw - 8)
                ty = b + oy - base * 1.1 if (c - a) < tw else b + oy + base * 0.6
                d.rectangle([tx - 3, ty - base * 0.65, tx + tw + 3, ty + base * 0.65], fill=(0, 0, 0, 200))
                d.text((tx, ty), txt, fill=col, font=f, anchor="lm")
        d.text((14, 8), title, fill=(255, 255, 255), font=font(base * 1.8, True))
        dim = f"view {x1 - x0:.1f} x {y1 - y0:.1f} um"
        dim = (f"die {die[2] - die[0]:.2f} x {die[3] - die[1]:.2f} um "
               f"({(die[2] - die[0]) * (die[3] - die[1]) / 1e6:.3f} mm2, TT 8x4 tiles); ") + dim
        d.text((14, 8 + base * 2.4), dim + f"; {w}x{h} px; {sx:.2f} px/um; 60 MHz (16.667 ns)",
               fill=(200, 200, 200), font=font(base))
        if vname == "detail":
            caption = arg('--detail-caption', 'config latch bank, byte 0 clock gate (u_cfg.g_byte[0].g_used.u_cg)')
            d.text((14, 8 + base * 3.9), f"centred on ({(x0 + x1) / 2:.1f}, {(y0 + y1) / 2:.1f}) um: "
                   f"{caption}; " + ("M1-M4 drawing" if style == "ns-accel" else "all layers"), fill=(200, 200, 200),
                   font=font(base * 0.9))
        L_um = nice_len((x1 - x0) * (0.2 if style == "ns-accel" else 0.15))
        barpx = L_um * sx
        bx_, by_ = 20, h + pad_t + int((pad_b * 0.4) if style == "ns-accel" else base * 1.6)
        d.rectangle([bx_, by_, bx_ + barpx, by_ + max(6, base // 2)], fill=(255, 255, 255))
        lbl = f"{L_um:g} um" if L_um < 1000 else f"{L_um / 1000:g} mm"
        d.text((bx_ + barpx + 12, by_ + base // 4), lbl, fill=(255, 255, 255), font=font(base * 1.3, True), anchor="lm")
        # layer legend in official IHP colours
        lx = int(max(w * 0.30, bx_ + barpx + (200 if style == "ns-accel" else 220)))
        legend_title = ("layers (bottom to top; drawing datatype only):" if style == "ns-accel" else
                        "layers (IHP sg13cmos5l.lyp colours and stipples; drawing purpose shown, pin/text/res purposes also drawn):")
        d.text((lx, h + pad_t + 8), legend_title,
               fill=(200, 200, 200), font=font(base))
        xx, yy = lx, h + pad_t + 8 + base * 1.6
        sw = base * 1.2
        fL = font(base)
        shown = (v["legend"] if style == "ns-accel" else
                 [lg for lg in v["legend"] if (lg["name"] or "").endswith((".drawing", ".boundary"))])
        for lg in shown:
            nm = lg["name"].split(".")[0] if lg["name"] else lg["source"]
            if xx + sw + d.textlength(nm, font=fL) + 20 > w - 10:
                xx = lx
                yy += base * 1.6
            d.rectangle([xx, yy, xx + sw, yy + sw], fill=hexrgb(lg["fill"]), outline=(255, 255, 255))
            d.text((xx + sw + 5, yy + sw / 2), nm, fill=(230, 230, 230), font=fL, anchor="lm")
            xx += sw + d.textlength(nm, font=fL) + 22
        if vname == "block" and style != "ns-accel":
            yy += base * 2.2
            xx = lx
            d.text((xx, yy), "units (dots = placed std cells; bright = seed cells):", fill=(200, 200, 200), font=fL)
            yy += base * 1.6
            fams = {}
            for u, n in units.items():
                f = family(u)
                if f:
                    fams.setdefault(f, [0, 0])
                    fams[f][0] += 1
                    fams[f][1] += n
            for f, (k, n) in sorted(fams.items(), key=lambda kv: -kv[1][1]):
                lab, col = FAMILY[f]
                txt = (f"{k} x {lab}" if k > 1 else lab) + f" ({n:,} cells)"
                if xx + sw + d.textlength(txt, font=fL) + 20 > w - 10:
                    xx = lx
                    yy += base * 1.6
                d.ellipse([xx, yy, xx + sw, yy + sw], fill=col)
                d.text((xx + sw + 5, yy + sw / 2), txt, fill=(230, 230, 230), font=fL, anchor="lm")
                xx += sw + d.textlength(txt, font=fL) + 26
            nstd, lab = info.get("NSTD", ["?", "?", "?"])[0], info.get("NSTD", ["?", "?", "?"])[2]
            notes = [
                "Synthesis flattened the netlist: only u_cfg and the SRAM wrappers keep instance hierarchy. Units are inferred: "
                "seed = cell driving a net with an RTL-prefixed name, or fed directly by that unit's SRAM read data;",
                f"other cells take the majority unit of the cells they drive (backward through the fan-in cone). "
                f"{lab} of {nstd} logic cells attributed; clock tree, fill, decap and tap cells are not drawn.",
                "Core split is approximate: synthesis kept one name for nets shared by both cores, so shared decode logic "
                "leans to core 0. Labels sit at the median of each unit's seed cells.",
            ]
            for li, t in enumerate(notes):
                d.text((14, h + pad_t + pad_b - 10 - base * (3.7 - 1.2 * li)), t, fill=(190, 190, 190),
                       font=font(base * 0.8), anchor="ld")
        elif vname == "block" and style == "ns-accel":
            d.text((14, h + pad_t + pad_b - 8 - base * 3.6),
                   "Unit box: 5th-95th percentile of placed standard-cell positions; config latch bank only.",
                   fill=(190, 190, 190), font=font(base * 0.8), anchor="ld")
            d.text((14, h + pad_t + pad_b - 8 - base * 2.4),
                   "Other logic is not outlined: synthesis flattened its unit hierarchy.",
                   fill=(190, 190, 190), font=font(base * 0.8), anchor="ld")
        d.text((w - 12, h + pad_t + pad_b - 8),
               (f"{tag}: " if tag else "") + "rendering only, not DRC/LVS/timing evidence",
               fill=(255, 160, 120), font=font(base), anchor="rd")
        canvas.save(os.path.join(out, fname))
        produced[fname] = {"px": list(canvas.size), "view_box_um": v["box_um"], "px_per_um": sx,
                           "scale_bar_um": L_um, "source_raw": v["file"],
                           "layers": [x["name"] for x in v["legend"]]}

    def rd(p):
        try:
            return open(os.path.join(out, p)).read().strip()
        except OSError:
            return None
    palette = [{"name": name, "gds": src, "rgb": colour} for src, (name, colour) in NS_LAYERS.items()]
    reference = "ns-accel/code/flow/runpod/render_layout.py"
    reference_sha = "3a63b015a1626eba41f075014e318116ca888c19fb6bc3a03825146a4b98eb9d"
    prov = {"tag": tag, "style": style,
            "style_reference": {"script": reference if style == "ns-accel" else None,
                                "sha256": reference_sha if style == "ns-accel" else None},
            "palette": palette if style == "ns-accel" else None,
            "gds": rd("gds.sha256"), "lyp": rd("lyp.sha256"), "views": produced, "die_um": die,
            "macros": macros, "units": units, "seeds": seeds, "attribution": info,
            "stage1_log": rd("stage1.log"),
            "script": "code/flow/render/render_layout_ihp.py, code/flow/render/render_dump_def.py",
            "note": "Rendering only; does not establish DRC, LVS or timing closure."}
    json.dump(prov, open(os.path.join(out, "provenance.json"), "w"), indent=1)


if __name__ == "__main__":
    if "--render" in sys.argv:
        stage1(arg("--render"))
    elif "--annotate" in sys.argv:
        stage2(arg("--annotate"), arg("--inst"), arg("--cells"), arg("--tag", ""))
    else:
        print(__doc__)
