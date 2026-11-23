"""Yield a complete, fail-closed inventory of storage in the elaborated v2 RTL.

    python code/tests/xinit/inventory_flops.py [--json OUT] [--paths OUT] [--yosys-json OUT]

The 6.5 MB Yosys JSON is a generated intermediate: by default it is written to a temporary directory and deleted,
so only `inventory.json` (the classified report) and `storage_paths.json` (the bench's deposit list) are source
artifacts.  Pass `--yosys-json` to keep the raw elaboration for debugging.

Yosys (`proc; opt; opt_dff; opt_clean`) lowers every always block to explicit storage cells.  Cells that carry a
reset ($adff/$adffe/$aldff/$aldffe/$sdff/$sdffe/$adlatch/$dffsr/$sr/$dlatchsr) are resettable; $dff/$dffe/$dlatch
are not.  Every non-resettable cell must appear in CLASSIFICATION below with a reason, otherwise the script fails:
a new flop must be argued, not silently accepted.  Unknown storage cell types also fail.

The same JSON is used to emit `storage_paths`: the simulator paths of every storage net (aliases included).  The
random-init bench sets exactly those, so it never deposits on a combinational net whose driver would not change.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = ROOT / "src"
SRAM_MODEL = ROOT / "test/sram_model"

RESET_TYPES = {
    "$adff", "$adffe", "$aldff", "$aldffe", "$sdff", "$sdffe", "$adlatch", "$dffsr", "$sr", "$dlatchsr",
}
NO_RESET_TYPES = {"$dff", "$dffe", "$dlatch"}
# Current Yosys lowering primitives with no persistent state. New primitives
# require explicit review, including ones whose name does not resemble a flop.
STATELESS_TYPES = {
    "$add", "$and", "$eq", "$ge", "$gt", "$le", "$logic_and", "$logic_not",
    "$logic_or", "$lt", "$mul", "$mux", "$ne", "$neg", "$not", "$or", "$pmux",
    "$print", "$reduce_and", "$reduce_bool", "$reduce_or", "$shift", "$shiftx",
    "$shl", "$sub", "$xor",
}
MEMORY_TYPES = {"$mem_v2", "$mem", "$memrd", "$memwr_v2"}

# Every non-reset storage site in the elaborated design, keyed by (module basename, src attribute).  The reason is
# the argument for why the power-up value cannot be observed after reset + program load.  A new site fails the test.
CLASSIFICATION = {
    ("md2_core", "src/md2_core.v:199.5-218.8"): (
        "harmless", "ir (64-bit instruction register): overwritten by the same fetch that sets xv, and only consumed "
        "while xv=1; reset clears xv, and the first dispatched instruction comes from a completed fetch."),
    ("SRAM_1P_behavioral_bm_bist", "test/sram_model/RM_IHPSG13_1P_core_behavioral_bm_bist.v:86.1-96.4"): (
        "harmless", "SRAM read output register dr_r: loaded by the read that a consumer has already issued; no design "
        "flop samples the SRAM output before its own read request.  Memory contents are a host-contract item."),
    ("cfg_lgcp_beh", "src/cells_behav.v:23.5-23.41"): (
        "harmless", "integrated clock-gate latch int_gate: transparent while CLK is low, so it takes GATE before the "
        "first rising edge following a low phase; hold reset through startup before allowing config writes."),
    ("md2_cfg_arb", "src/md2_cfg_bank.v:81.5-88.8"): (
        "harmless", "held_addr/held_data: selected only while host_held=1, and host_held is reset; they are written "
        "in the same edge that sets host_held."),
    ("md2_cfg_stage", "src/md2_cfg_bank.v:105.5-108.8"): (
        "harmless", "addr1/data1: gated by we1, which is reset; addr/data are captured on the same edge that "
        "asserts we1, so the bank never sees a stale address with a live write."),
}


def _run(cmd, cwd):
    return subprocess.run(cmd, cwd=str(cwd), check=False, capture_output=True, text=True)


def yosys_json(out: Path) -> dict:
    """Elaborate the v2 RTL with the IHP behavioural SRAM models and return the Yosys JSON."""
    files = [SRAM_MODEL / "RM_IHPSG13_1P_256x64_c2_bm_bist.v",
             SRAM_MODEL / "RM_IHPSG13_1P_512x32_c2_bm_bist.v",
             SRAM_MODEL / "RM_IHPSG13_1P_core_behavioral_bm_bist.v"]
    files += sorted(SRC.glob("*.v"))
    # Yosys on Windows splits -p on spaces, so use relative paths from the repo root.
    rel = [str(f.relative_to(ROOT)).replace("\\", "/") for f in files]
    script = (f"read_verilog -sv -I src -DSIM=1 -DCOCOTB_SIM=1 -DFUNCTIONAL=1 -DUSE_IHP_SRAM=1 {' '.join(rel)}; "
              f"hierarchy -top tt_um_brentius_metronome; proc; opt; opt_dff; opt_clean; "
              f'write_json "{out.resolve().as_posix()}"')
    r = _run(["yosys", "-q", "-p", script], ROOT)
    if r.returncode or not out.is_file():
        raise RuntimeError(f"yosys failed (rc={r.returncode}):\n{r.stdout}\n{r.stderr}")
    return json.loads(out.read_text())


def module_basename(name: str) -> str:
    # `$paramod\md2_line\CFGW=...` and `$paramod$hash\md2_core` both name the base module second.
    if name.startswith("$paramod"):
        parts = name.split("\\")
        return parts[1] if len(parts) > 1 else name
    return name.rsplit("\\", 1)[-1]


def _balanced(s: str, start: int) -> tuple[str, int]:
    """`(inside, index after the closing paren)` for the parenthesised group at s[start]."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                return s[start + 1:i], i + 1
    return "", len(s)


def _split_commas(s: str) -> list[str]:
    """Split on top-level commas, respecting brackets, braces and parentheses."""
    items, depth, cur = [], 0, []
    for ch in s:
        if ch in "[{(":
            depth += 1
        elif ch in "]})":
            depth -= 1
        if ch == "," and depth == 0:
            items.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    items.append("".join(cur))
    return [item.strip() for item in items if item.strip()]


def _decl_name(item: str) -> str | None:
    """Identifier declared by one declaration item, or None for a non-reg item."""
    item = item.strip()
    saw_reg = False
    while True:
        m = re.match(r"(input|output|inout|reg|wire|logic|signed|unsigned)\b\s*", item)
        if not m:
            break
        saw_reg |= m.group(1) == "reg"
        item = item[m.end():]
        m = re.match(r"\[[^\]]*\]\s*", item)
        if m:
            item = item[m.end():]
    if not saw_reg:
        return None
    m = re.match(r"([A-Za-z_]\w*)", item)
    return m.group(1) if m else None


def declared_regs(path: Path) -> dict[str, set[str]]:
    """Module name -> declared `reg` identifiers, parsed from the RTL source.

    Yosys loses the reg/net distinction after `proc`, so the simulator whitelist must come from the source.  Two
    traps, both found by the seed-5 divergence: an ANSI port list must be parsed item by item (`output reg` counts,
    `output wire` does not), and a `reg` assigned in a combinational `always @*` is not storage even though it shares
    Yosys bit names with a flop after `opt_clean`.  Array declarations are skipped: SRAM word arrays are randomised
    separately.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"//[^\n]*", "", text)
    out = {}
    for m in re.finditer(r"\bmodule\s+(\w+)\b(.*?)\bendmodule", text, flags=re.S):
        name, body = m.group(1), m.group(2).lstrip()
        regs = set()
        if body.startswith("#"):                       # parameter list before the port list
            _params, end = _balanced(body, body.index("("))
            body = body[end:].lstrip()
        if body.startswith("("):                       # ANSI port list: one declaration per item
            header, end = _balanced(body, 0)
            for item in _split_commas(header):
                n = _decl_name(item)
                if n:
                    regs.add(n)
            body = body[end:]
        for d in re.finditer(r"\breg\b([^;()]*);", body):
            for item in d.group(1).split(","):
                n = _decl_name("reg " + item)
                if n:
                    regs.add(n)
        out[name] = regs
    return out


def _module_sources(j: dict) -> dict[str, Path]:
    """Module key -> source file, from the `src` attribute of any cell in it."""
    sources = {}
    for mkey, module in j["modules"].items():
        for cell in module["cells"].values():
            src = cell.get("attributes", {}).get("src")
            if src:
                sources[mkey] = ROOT / src.split(":")[0]
                break
    return sources


def _bit_names(module: dict) -> dict[int, list[str]]:
    bybit: dict[int, list[str]] = defaultdict(list)
    for name, nd in module["netnames"].items():
        for b in nd["bits"]:
            if isinstance(b, int):
                bybit[b].append(name)
    return bybit


def _storage_cells(module: dict):
    for name, cell in module["cells"].items():
        if cell["type"] in RESET_TYPES | NO_RESET_TYPES | MEMORY_TYPES:
            yield name, cell


def _storage_bits(module: dict) -> set[int]:
    bits = set()
    for _cname, cell in _storage_cells(module):
        if cell["type"] in MEMORY_TYPES:
            continue
        for b in cell["connections"].get("Q") or []:
            if isinstance(b, int):
                bits.add(b)
    return bits


def _all_storage(module: dict, name: str, qbits: set[int]) -> bool:
    """True when every bit of `name` is a storage Q bit or a constant.

    `opt_clean` merges combinational nets into flop bits, so a declared `reg` assigned in an `always @*` (e.g.
    md2_core's 512-bit `src`) can name a few storage bits plus hundreds of pure mux bits.  Depositing that handle
    sets the mux bits to values no driver will refresh.
    """
    for b in module["netnames"][name]["bits"]:
        if isinstance(b, int) and b not in qbits:
            return False
    return True


def _num(v, default=1) -> int:
    """Yosys JSON parameters are binary bit-strings; widths need int(v, 2)."""
    if isinstance(v, int):
        return v
    if isinstance(v, str) and v and set(v) <= set("01"):
        return int(v, 2)
    try:
        return int(v)
    except (TypeError, ValueError):
        return default


def classify(j: dict) -> dict:
    """Walk every module, count storage instances and require a reason for each non-reset site."""
    modules = j["modules"]
    # Instance multiplicity from the top, so the report counts the elaborated design, not just module definitions.
    mult: Counter[str] = Counter()

    def walk(mkey: str, n: int):
        module = modules[mkey]
        if _num(module.get("attributes", {}).get("blackbox", 0)):
            raise SystemExit(f"unexpanded black box: {mkey}")
        mult[mkey] += n
        known = STATELESS_TYPES | RESET_TYPES | NO_RESET_TYPES | MEMORY_TYPES
        for name, cell in module["cells"].items():
            kind = cell["type"]
            if kind in modules:
                walk(kind, n)
            elif kind not in known:
                raise SystemExit(f"unknown cell {kind} in {mkey} ({name})")

    walk("tt_um_brentius_metronome", 1)

    counts = Counter()
    bits = Counter()
    no_reset = []
    for mkey, n_inst in mult.items():
        module = modules[mkey]
        bybit = _bit_names(module)
        for cname, cell in _storage_cells(module):
            t = cell["type"]
            width = _num(cell.get("parameters", {}).get("WIDTH", 1))
            key = module_basename(mkey)
            src = cell.get("attributes", {}).get("src")
            if t in RESET_TYPES:
                counts["reset"] += 1
                bits["reset"] += width * n_inst
            elif t in NO_RESET_TYPES:
                counts["no_reset"] += 1
                bits["no_reset"] += width * n_inst
                if n_inst:
                    cls = CLASSIFICATION.get((key, src))
                    no_reset.append({"module": key, "cell": cname, "type": t, "width": width,
                                     "instances": n_inst, "src": src,
                                     "class": cls[0] if cls else "unclassified",
                                     "reason": cls[1] if cls else None,
                                     "q": [bybit.get(b, []) for b in (cell["connections"].get("Q") or [])]})
            elif t in MEMORY_TYPES:
                counts["memory_cell"] += 1
            else:
                raise SystemExit(f"unknown storage cell {t} in {key} ({cname}); inventory is fail-closed")

        # Arrays are module-level `memories`, not cells; count their bits once per elaborated instance.
        for mem in module.get("memories", {}).values():
            counts["memory_array"] += 1
            bits["memory"] += mem["width"] * mem["size"] * n_inst

    for site in no_reset:
        if site["class"] == "unclassified":
            raise SystemExit(
                f"unclassified non-reset storage in {site['module']} {site['cell']} ({site['src']}, "
                f"{site['width']} bits x {site['instances']}): add it to CLASSIFICATION with a reason")

    return {"modules": dict(Counter(module_basename(k) for k in mult.elements())),
            "cell_counts": dict(counts), "bit_counts": dict(bits), "no_reset": no_reset}


def storage_paths(j: dict) -> tuple[list[str], list[str]]:
    """Simulator paths of every declared `reg` holding storage, for the random-init bench.

    A net that merely aliases a storage bit must not be deposited: a VPI deposit on a combinational net sticks while
    that net's driver does not change, which can corrupt control (e.g. A_WEN).  Only source-declared regs are used.
    """
    modules = j["modules"]
    sources = _module_sources(j)
    regs_cache = {}
    paths = []
    fallback = []

    def regs_for(mkey: str) -> set[str]:
        src = sources.get(mkey)
        if src is None:
            return set()
        if src not in regs_cache:
            regs_cache[src] = declared_regs(src)
        return regs_cache[src].get(module_basename(mkey), set())

    def walk(mkey: str, prefix: str):
        module = modules[mkey]
        bybit = _bit_names(module)
        qbits = _storage_bits(module)
        declared = regs_for(mkey)
        names = set()
        for _cname, cell in _storage_cells(module):
            if cell["type"] in MEMORY_TYPES:
                continue
            q = cell["connections"].get("Q") or []
            for b in q:
                hit = {n for n in bybit.get(b, []) if n in declared and _all_storage(module, n, qbits)}
                if hit:
                    names.update(hit)
                else:
                    fallback.append(f"{prefix or '<top>'}:{_cname}:Q[{b}]")
        paths.extend(f"{prefix}.{n}" if prefix else n for n in sorted(names))
        for cname, cell in module["cells"].items():
            if cell["type"] in modules:
                child = cname.lstrip("\\")
                walk(cell["type"], f"{prefix}.{child}" if prefix else child)

    walk("tt_um_brentius_metronome", "")
    return sorted(set(paths)), sorted(set(fallback))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=str(HERE / "inventory.json"))
    ap.add_argument("--paths", default=str(HERE / "storage_paths.json"))
    ap.add_argument("--yosys-json", default=None,
                    help="keep the raw Yosys JSON here (default: temporary file, deleted)")
    args = ap.parse_args()
    out = Path(args.json)
    out.parent.mkdir(parents=True, exist_ok=True)
    tmpdir = None
    if args.yosys_json:
        tmp = Path(args.yosys_json)
    else:
        tmpdir = tempfile.TemporaryDirectory(prefix="xinit_inventory_")
        tmp = Path(tmpdir.name) / "design.json"
    try:
        j = yosys_json(tmp)
        inv = classify(j)
        inv["storage_paths"], inv["storage_fallback_paths"] = storage_paths(j)
        if inv["storage_fallback_paths"]:
            raise SystemExit(f"storage Q bits lack declared-reg paths: {inv['storage_fallback_paths'][:10]}")
        out.write_text(json.dumps(inv, indent=1), encoding="utf-8", newline="\n")
        Path(args.paths).write_text(json.dumps(inv["storage_paths"], indent=1), encoding="utf-8",
                                    newline="\n")
    finally:
        if tmpdir is not None:
            tmpdir.cleanup()
    print(f"storage cells: {inv['cell_counts']}")
    print(f"storage bits:  {inv['bit_counts']}")
    print(f"no-reset sites: {len(inv['no_reset'])} (all classified)")
    for site in inv["no_reset"]:
        print(f"  {site['module']:28s} {site['width']:3d}b x {site['instances']:3d}  {site['class']:11s} "
              f"{site['src']}")
    print(f"storage paths: {len(inv['storage_paths'])} "
          f"(auto-named fallback alias paths: {len(inv['storage_fallback_paths'])})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
