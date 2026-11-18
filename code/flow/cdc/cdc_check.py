"""Netlist CDC check: every asynchronous input passes a 2-flop synchroniser before any other logic.

    python cdc_check.py NETLIST.v [--json OUT.json] [--clk clk]

Works on a flat gate-level Verilog netlist (Yosys / OpenROAD output, IHP sg13cmos5l cells).  Method, per
asynchronous primary input bit (ui_in, uio_in; ena is reported separately):
  1. follow the net forward through transparent single-input cells (buffers, inverters, delay gates), which the
     router inserts on input nets;
  2. every terminal sink must be the D pin of a flop (stage 1);
  3. each stage-1 flop's Q, again through transparent cells, must feed nothing but D pins of flops (stage 2);
  4. stage-1 and stage-2 flops must be clocked by the primary clock (traced back through buffers);
  5. stage-2 outputs may feed any logic.
rst_n is checked against the asynchronous-assertion, synchronous-release rule: raw rst_n may reach only RESET_B pins
of flops/latches, and each reset flop's D must be tied high or the Q of another flop (a release synchroniser chain),
and a first-stage (tie-high) flop must feed only a further flop.  Anything else is an exception.
Exit status 1 if there is any exception.

Limits (stated, not hidden): structural only; it does not prove metastability resolution time or that the clock
period covers it; transparent cells are recognised by library cell name (buf, inv, dlygate, clkbuf), sequential
cells by name (df*, dl*); SRAM macro inputs count as logic sinks (none is expected on an async net).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict

TRANSPARENT = re.compile(r"sg13cmos5l_(buf|inv|dlygate\w*|clkbuf|clkinv)_?\w*$")
FLOP = re.compile(r"sg13cmos5l_df\w+$")
LATCH = re.compile(r"sg13cmos5l_dl\w+$")
OUT_PINS = {"Q", "Q_N", "X", "Y", "GCLK", "L_HI", "L_LO", "A_DOUT", "SUM", "COUT"}
INST = re.compile(r"^\s*(\\?[A-Za-z_][\w$]*)\s+(\\?\S+)\s*\((.*?)\)\s*;", re.S | re.M)
PIN = re.compile(r"\.(\w+)\s*\(\s*(.*?)\s*\)\s*(?:,|$)", re.S)
SKIP_TYPES = {"module", "input", "output", "wire", "assign", "endmodule"}


def norm(net: str) -> str:
    net = net.strip()
    if net.startswith("\\"):
        net = net[1:].strip()
    return re.sub(r"\s+", "", net)


def parse(text: str):
    insts = []
    for m in INST.finditer(text):
        typ, name, ports = m.group(1), m.group(2), m.group(3)
        if typ in SKIP_TYPES:
            continue
        pins = {pm.group(1): norm(pm.group(2)) for pm in PIN.finditer(ports + ",")}
        insts.append((typ, norm(name), pins))
    return insts


class Netlist:
    def __init__(self, text: str):
        self.insts = parse(text)
        self.loads = defaultdict(list)    # net -> [(instance index, pin)]
        self.driver = {}                  # net -> (instance index, pin)
        for i, (typ, _name, pins) in enumerate(self.insts):
            for p, n in pins.items():
                if p in OUT_PINS and not (typ.startswith("RM_") and p != "A_DOUT"):
                    self.driver[n] = (i, p)
                else:
                    self.loads[n].append((i, p))

    def sinks(self, net, seen=None):
        """Terminal (instance index, pin) sinks of `net`, through transparent cells; also the cells traversed."""
        seen = set() if seen is None else seen
        out, via = [], []
        if net is None or net in seen:
            return out, via
        seen.add(net)
        for i, p in self.loads.get(net, []):
            typ, name, pins = self.insts[i]
            if TRANSPARENT.match(typ) and p == "A":
                via.append(name)
                o, v = self.sinks(pins.get("X") or pins.get("Y"), seen)
                out += o
                via += v
            elif typ.startswith("sg13cmos5l_") and typ.split("_")[1] in ("fill", "decap", "antennanp"):
                continue
            else:
                out.append((i, p))
        return out, via

    def root_of(self, net):
        """Trace a net backwards through transparent cells; returns the root net name."""
        seen = set()
        while net in self.driver and net not in seen:
            seen.add(net)
            i, _ = self.driver[net]
            typ, _, pins = self.insts[i]
            if not TRANSPARENT.match(typ):
                break
            net = pins["A"]
        return net


def sync_gate(nl: Netlist, i, p):
    """Waiver (reported, not silent): a combinational cell between the pin and the first flop is accepted only if
    every other input of the cell comes from a flop Q (a synchronous-domain level, e.g. the synchronous-reset AND
    `raw & rst_q` that synthesis builds in front of s1) and its single output feeds only flop D pins.
    Returns the output net or None."""
    typ, name, pins = nl.insts[i]
    if FLOP.match(typ) or LATCH.match(typ) or typ.startswith("RM_") or TRANSPARENT.match(typ):
        return None
    outs = [pn for pn in pins if pn in OUT_PINS]
    if len(outs) != 1:
        return None
    for pn, net in pins.items():
        if pn in OUT_PINS or pn == p:
            continue
        root = nl.root_of(net)
        drv = nl.driver.get(root)
        if not (drv and FLOP.match(nl.insts[drv[0]][0])):
            return None
    out = pins[outs[0]]
    ss, _ = nl.sinks(out)
    if ss and all(FLOP.match(nl.insts[a][0]) and b == "D" for a, b in ss):
        return out
    return None


def check(nl: Netlist, clk="clk"):
    res = {"inputs": {}, "rst_n": {}, "ena": [], "exceptions": []}
    exc = res["exceptions"]

    def desc(i, p):
        return f"{nl.insts[i][1]}({nl.insts[i][0].replace('sg13cmos5l_', '')}).{p}"

    for bus, width in (("ui_in", 8), ("uio_in", 8)):
        for b in range(width):
            net = f"{bus}[{b}]"
            sinks, via = nl.sinks(net)
            info = {"net": net, "buffers": via, "stage1": [], "stage2": [], "ok": True, "notes": []}
            if not sinks:
                info["notes"].append("no sinks (unused input)")
            expanded = []
            for i, p in sinks:
                out = sync_gate(nl, i, p)
                if out is not None:
                    info["notes"].append(f"waived: {desc(i, p)} (AND with a flop-driven level) before stage 1")
                    res.setdefault("waivers", []).append(f"{net}: {desc(i, p)}")
                    expanded += nl.sinks(out)[0]
                else:
                    expanded.append((i, p))
            for i, p in expanded:
                typ, name, pins = nl.insts[i]
                if not (FLOP.match(typ) and p == "D"):
                    info["ok"] = False
                    msg = f"{net}: reaches {desc(i, p)} before a synchroniser flop"
                    info["notes"].append(msg)
                    exc.append(msg)
                    continue
                info["stage1"].append(name)
                if nl.root_of(pins["CLK"]) != clk:
                    info["ok"] = False
                    exc.append(f"{net}: stage-1 flop {name} is not clocked by {clk}")
                s2 = []
                for a, b in nl.sinks(pins["Q"])[0]:
                    out = sync_gate(nl, a, b)
                    if out is not None:
                        res.setdefault("waivers", []).append(f"{net}: {desc(a, b)} between stage 1 and 2")
                        s2 += nl.sinks(out)[0]
                    else:
                        s2.append((a, b))
                if not s2:
                    info["ok"] = False
                    exc.append(f"{net}: stage-1 flop {name} output is unused")
                for j, pp in s2:
                    t2, n2, p2 = nl.insts[j]
                    if FLOP.match(t2) and pp == "D":
                        info["stage2"].append(n2)
                        if nl.root_of(p2["CLK"]) != clk:
                            info["ok"] = False
                            exc.append(f"{net}: stage-2 flop {n2} is not clocked by {clk}")
                    else:
                        info["ok"] = False
                        exc.append(f"{net}: stage-1 flop {name} output feeds {desc(j, pp)} (not a second flop)")
            res["inputs"][net] = info
    s, _ = nl.sinks("ena")
    res["ena"] = [desc(i, p) for i, p in s]
    # rst_n: asynchronous assert, synchronous release
    s, via = nl.sinks("rst_n")
    chain = []
    for i, p in s:
        typ, name, pins = nl.insts[i]
        if not ((FLOP.match(typ) or LATCH.match(typ)) and p == "RESET_B"):
            exc.append(f"rst_n: raw reset reaches {desc(i, p)} (only RESET_B pins of flops are allowed)")
            continue
        drv = nl.driver.get(nl.root_of(pins.get("D")))
        if drv and nl.insts[drv[0]][0].endswith("tiehi"):
            kind = "tied high"
        elif drv and FLOP.match(nl.insts[drv[0]][0]):
            kind = f"Q of {nl.insts[drv[0]][1]}"
        else:
            kind = "OTHER"
            exc.append(f"rst_n: reset flop {name} has D from neither tie-high nor another flop")
        clk_ok = nl.root_of(pins["CLK"]) == clk if "CLK" in pins else None
        if clk_ok is False:
            exc.append(f"rst_n: reset flop {name} not clocked by {clk}")
        entry = {"flop": name, "type": typ.replace("sg13cmos5l_", ""), "D": kind, "clk_ok": clk_ok}
        if kind == "tied high" and "Q" in pins:
            ss, _ = nl.sinks(pins["Q"])
            bad = [desc(a, b) for a, b in ss if not (FLOP.match(nl.insts[a][0]) and b == "D")]
            if bad:
                exc.append(f"rst_n: first reset flop {name} output feeds {bad[:3]} (not only a second flop)")
            entry["feeds"] = [nl.insts[a][1] for a, _b in ss]
        chain.append(entry)
    res["rst_n"] = {"buffers": via, "async_reset_sinks": chain}
    return res


def report(res) -> str:
    n = len(res["inputs"])
    ok = sum(1 for v in res["inputs"].values() if v["ok"] and v["stage1"])
    lines = [f"asynchronous inputs checked: {n}; with a clean 2-flop synchroniser: {ok}"]
    for net, v in res["inputs"].items():
        lines.append(f"  {net:12s} {'OK ' if v['ok'] and v['stage1'] else 'EXC'} via {len(v['buffers'])} buf -> "
                     f"{','.join(v['stage1']) or '-'} -> {','.join(v['stage2']) or '-'}  {' | '.join(v['notes'])}")
    r = res["rst_n"]
    lines.append(f"rst_n: {len(r['async_reset_sinks'])} async-reset sinks; "
                 + "; ".join(f"{c['flop']}[D {c['D']}]" for c in r["async_reset_sinks"][:6])
                 + (" ..." if len(r["async_reset_sinks"]) > 6 else ""))
    lines.append(f"ena sinks: {res['ena'] or 'none'}")
    lines.append(f"waivers (reported): {len(res.get('waivers', []))}" + ("; e.g. " + res["waivers"][0] if res.get("waivers") else ""))
    lines.append(f"exceptions: {len(res['exceptions'])}")
    lines += ["  " + e for e in res["exceptions"]]
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("netlist")
    ap.add_argument("--json")
    ap.add_argument("--clk", default="clk")
    a = ap.parse_args(argv)
    nl = Netlist(open(a.netlist, encoding="utf-8", errors="replace").read())
    res = check(nl, a.clk)
    res["netlist"] = a.netlist
    res["instances"] = len(nl.insts)
    print(report(res))
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=1)
    return 1 if res["exceptions"] else 0


if __name__ == "__main__":
    sys.exit(main())
