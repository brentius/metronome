"""Dump die area, hard macros and per-unit placement boxes from a final DEF (no OpenROAD needed).

Usage: python render_dump_def.py FINAL.def OUT_instances.txt [--levels N]

Output lines (same format as the ns-accel render_layout_dump.tcl, units in um):
  DIE x0 y0 x1 y1
  INST name master x0 y0 x1 y1 orient          (hard macros: SRAMs)
  UNIT depth prefix n x5 y5 x95 y95 xmin ymin xmax ymax
  NINST n

The v2 netlist is flattened by synthesis, so instance names carry no hierarchy except u_cfg (latch bank).
Unit membership is therefore inferred:
  1. seed: a cell driving a net whose name has an RTL prefix (g_core[k].u_core, g_s[k].u, ...) gets that unit;
     u_cfg cells keep their instance prefix.
  2. propagate: unlabelled standard cells take the majority unit of the labelled cells they drive, iterated
     up to --levels times (backward through the fan-in cone). Clock tree, fill, decap and tap cells are skipped.
Boxes use the 5th-95th percentile of cell lower-left x/y. This is an attribution heuristic for a picture,
not a netlist partition; cells shared by several units go to the majority.
"""
import collections
import re
import sys

SKIP_MASTER = re.compile(r"fill|decap|tap|antenna", re.I)
OUT_PINS = {"Q", "Q_N", "Y", "X", "Z", "ZN", "A_DOUT", "B_DOUT"}
UNIT_RULES = [  # (regex on net or instance name, unit key)
    (r"^g_core\[(\d+)\]\.u_core\.", "core{0}"),
    (r"^g_s\[(\d+)\]\.u\.", "stream{0}"),
    (r"^g_ln\[(\d+)\]\.", "line{0}"),
    (r"^g_thr\[(\d+)\]\.", "thread{0}"),
    (r"^g_sh\[(\d+)\]\.", "shifter{0}"),
    (r"^g_cn\[(\d+)\]\.", "counter{0}"),
    (r"^g_lf\[(\d+)\]\.", "lfsr{0}"),
    (r"^u_mem\.", "mem_arbiter"),
    (r"^u_host\.", "host"),
    (r"^u_acc\.|^acc_", "acc"),
    (r"^u_cfg\.", "cfg_latches"),
]


def unit_of(name):
    for rx, key in UNIT_RULES:
        m = re.match(rx, name)
        if m:
            return key.format(*m.groups())
    return None


def parse(path):
    dbu, die, comps, nets = 1000.0, None, {}, []
    sec = None
    buf = ""
    for line in open(path):
        s = line.strip()
        if s.startswith("UNITS DISTANCE MICRONS"):
            dbu = float(s.split()[3])
        elif s.startswith("DIEAREA"):
            n = [float(x) for x in re.findall(r"-?\d+", s)]
            die = [v / dbu for v in n[:4]]
        elif re.match(r"^(COMPONENTS|NETS) ", s):
            sec = s.split()[0]
            buf = ""
        elif s.startswith("END "):
            sec = None
        elif sec:
            buf += " " + s
            if s.endswith(";"):
                rec, buf = buf.strip(), ""
                if not rec.startswith("-"):
                    continue
                if sec == "COMPONENTS":
                    t = rec.split()
                    m = re.search(r"\+ (?:PLACED|FIXED) \( (-?\d+) (-?\d+) \) (\w+)", rec)
                    if m:
                        comps[t[1].replace("\\", "")] = (t[2], int(m.group(1)) / dbu, int(m.group(2)) / dbu, m.group(3))
                else:
                    name = rec.split()[1].replace("\\", "")
                    head = rec.split("+", 1)[0]
                    conns = [(a.replace("\\", ""), b) for a, b in re.findall(r"\( (\S+) (\S+) \)", head)]
                    nets.append((name, conns))
    return dbu, die, comps, nets


def main():
    src, out = sys.argv[1], sys.argv[2]
    levels = int(sys.argv[sys.argv.index("--levels") + 1]) if "--levels" in sys.argv else 12
    dbu, die, comps, nets = parse(src)
    std = {n for n, (m, *_r) in comps.items() if not SKIP_MASTER.search(m) and not m.startswith("RM_IHP")
           and not n.startswith(("clkbuf_", "clkload", "delaybuf_"))}
    label, seed, seeded = {}, collections.Counter(), set()
    drives = collections.defaultdict(set)  # driver cell -> sink cells
    for name, conns in nets:
        isout = [p in OUT_PINS or p.startswith("A_DOUT") for _c, p in conns]
        drv = [c for (c, p), o in zip(conns, isout) if o and c in comps]
        sinks = [c for (c, p), o in zip(conns, isout) if not o and c in std]
        u = unit_of(name)
        if u and drv and all(d not in std for d in drv):
            # net driven by a macro (SRAM read data): its first-level sinks belong to the named consumer.
            # Synthesis keeps one name for equivalent nets, so this restores core1's fetch/decode seeds.
            for s_ in sinks:
                if s_ not in label:
                    label[s_] = u
                    seed[u] += 1
                    seeded.add(s_)
        for d in drv:
            if u and d in std:
                label[d] = u
                seed[u] += 1
                seeded.add(d)
            for s_ in sinks:
                if s_ != d:
                    drives[d].add(s_)
    for n in std:
        u = unit_of(n)
        if u:
            label[n] = u
            seed[u] += 1
            seeded.add(n)
    for _ in range(levels):
        new = {}
        for d in std:
            if d in label or d not in drives:
                continue
            votes = collections.Counter(label[s_] for s_ in drives[d] if s_ in label)
            if votes:
                new[d] = votes.most_common(1)[0][0]
        if not new:
            break
        label.update(new)
    by = collections.defaultdict(list)
    for n, u in label.items():
        _m, x, y, _o = comps[n]
        by[u].append((x, y))
    with open(out, "w") as f:
        f.write("DIE %.3f %.3f %.3f %.3f\n" % tuple(die))
        for n, (m, x, y, o) in comps.items():
            if m.startswith("RM_IHP"):
                f.write(f"INST {n} {m} {x:.3f} {y:.3f} 0 0 {o}\n")  # size filled from GDS by the renderer
        for u, pts in sorted(by.items()):
            xs = sorted(p[0] for p in pts)
            ys = sorted(p[1] for p in pts)
            k = len(xs)
            a, z = int(k * 0.05), min(k - 1, int(k * 0.95))
            f.write(f"UNIT 1 {u} {k} {xs[a]:.3f} {ys[a]:.3f} {xs[z]:.3f} {ys[z]:.3f} "
                    f"{xs[0]:.3f} {ys[0]:.3f} {xs[-1]:.3f} {ys[-1]:.3f}\n")
        f.write(f"NINST {len(comps)}\n")
        for u, k in sorted(seed.items()):
            f.write(f"SEED {u} {k}\n")
        f.write(f"NSTD {len(std)} LABELLED {len(label)} SEEDED {sum(seed.values())}\n")
    with open(out.rsplit(".", 1)[0] + "_cells.tsv", "w") as f:
        f.write("cell\tmaster\tx_um\ty_um\tunit\tseed\n")
        for n, u in sorted(label.items()):
            m, x, y, _o = comps[n]
            f.write(f"{n}\t{m}\t{x:.3f}\t{y:.3f}\t{u}\t{int(n in seeded)}\n")
    print(f"std {len(std)} labelled {len(label)} ({100 * len(label) / max(1, len(std)):.1f}%) units {len(by)}")


if __name__ == "__main__":
    main()
