r"""Rewrite an OpenSTA SDF (and the matching netlist) so Icarus Verilog 13 annotates all of it.

    python sdf_for_icarus.py IN.sdf OUT.sdf NETLIST NETLIST_OUT

Found on the v2 skeleton (run v2pnr_r4_20261112T0921), 2026-11-12:
  - Icarus's SDF reader cannot resolve flattened instance names that contain '.' or '[' (`u_cfg\.g_byte\[0\]\.u_cg`):
    with DIVIDER '.' it splits at the escaped dots ("Cannot find ... in scope"), and with brackets it reports
    "Invalid/malformed INSTANCE argument". Those cells keep zero delay: the configuration latches, their clock gates
    and the gated-clock buffers among them. This script renames every escaped instance to a plain identifier
    (`.` -> `__`, `[`/`]` -> `_`) in a copy of the netlist and in the SDF, and sets DIVIDER '/'. Net names are not
    changed, so hierarchical references to nets (cfg_probe.vh) still work.
  - INTERCONNECT entries between two cells crash vvp 13.0 ("NULL handle passed to vpi_scan") with -ginterconnect;
    entries at top-level ports work. Cell-to-cell INTERCONNECT entries are dropped and their largest delay is
    reported, which bounds what the simulation leaves out (cell IOPATH delays already include the load).
  - Header triples with an empty typical value ("1.080::1.080") are filled in.
Prints a one-line summary.
"""
import re
import sys

PIN = re.compile(r"^(.*[^\\])\.([A-Za-z_][\w\[\]]*)$")       # instance.pin in the SDF, split at the last plain dot
INST = re.compile(r"^(\s*)(sg13cmos5l_\w+|RM_IHPSG13_\w+)(\s+)\\(\S+)(\s)", re.M)   # escaped instance in netlist


def plain_name(name: str) -> str:
    """Escaped instance name (without backslash, unescaped) -> plain identifier."""
    return name.replace(".", "__").replace("[", "_").replace("]", "_")


def sdf_unescape(x: str) -> str:
    return x.replace("\\.", ".").replace("\\[", "[").replace("\\]", "]")


def is_top_port(x: str) -> bool:
    return "." not in x.replace("\\.", "")


def main() -> int:
    src, dst, nl_in, nl_out = sys.argv[1:5]

    text = open(nl_in).read()
    renamed = {}

    def sub(m):
        new = plain_name(m[4])
        renamed[m[4]] = new
        return f"{m[1]}{m[2]}{m[3]}{new}{m[5]}"

    text = INST.sub(sub, text)
    assert len(set(renamed.values())) == len(renamed), "renaming collided"
    open(nl_out, "w").write(text)

    # Drop the SRAM macro CELL blocks: Icarus cannot parse bit-indexed IOPATH ports (`A_DOUT[0]`) and stops reading
    # the file there, and the behavioural SRAM models have no specify paths to annotate anyway. Their clock-to-output
    # delay (about 6.5 ns slow) is therefore not simulated.
    lines, keep, macros, i = open(src).readlines(), [], 0, 0
    while i < len(lines):
        if lines[i].strip() == "(CELL" and i + 1 < len(lines) and '"RM_IHPSG13_' in lines[i + 1]:
            depth = 0
            while True:
                depth += lines[i].count("(") - lines[i].count(")")
                i += 1
                if depth == 0:
                    break
            macros += 1
            continue
        keep.append(lines[i])
        i += 1

    out, dropped, kept, worst, inst = [], 0, 0, 0.0, 0
    for line in keep:
        s = line.strip()
        if s.startswith("(DIVIDER"):
            line = line.replace("(DIVIDER .)", "(DIVIDER /)")
        elif s.startswith(("(VOLTAGE", "(PROCESS", "(TEMPERATURE")):
            line = re.sub(r"(-?[\d.]+)::(-?[\d.]+)", r"\1:\1:\2", line)
        elif s.startswith("(INSTANCE") and s != "(INSTANCE)":
            name = sdf_unescape(s[len("(INSTANCE "):-1])
            line = line.replace(s, f"(INSTANCE {renamed.get(name, name)})")
            inst += 1
        elif s.startswith("(INTERCONNECT"):
            a, b = s.split()[1:3]
            if not is_top_port(a) and not is_top_port(b):
                dropped += 1
                worst = max([worst] + [float(v) for v in re.findall(r"\d+\.\d+", s.split(b, 1)[1])])
                continue
            kept += 1
            for x in (a, b):
                m = PIN.match(x)
                if not is_top_port(x) and m:
                    name = sdf_unescape(m[1])
                    line = line.replace(x, f"{renamed.get(name, name)}/{m[2]}", 1)
        out.append(line)
    open(dst, "w").writelines(out)
    print(f"renamed {len(renamed)} escaped instances; {inst} SDF cells kept, {macros} SRAM macro cells dropped; "
          f"INTERCONNECT kept {kept} (top-level ports), dropped {dropped} (cell to cell, largest {worst:.3f} ns)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
