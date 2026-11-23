#!/bin/bash
# Gate-level run of the CDC jitter bench against a routed netlist (RunPod / LibreLane image, or locally).
#
#   gl_cdc.sh NETLIST [options]          netlist = routed *.nl.v (unpowered)
#   gl_cdc.sh --rtl [options]            dry run: the same bench on the RTL, no netlist needed
#
# Options
#   --out DIR         output directory for JSON/log/XML evidence (default: <netlist dir>/cdc_gl)
#   --stdcell DIR     IHP std-cell Verilog models (default: $PDK_ROOT/$PDK/libs.ref/sg13cmos5l_stdcell/verilog)
#   --top NAME        top module in the netlist (default: tt_um_brentius_metronome)
#   --scenarios LIST  comma-separated scenario names (default: spi_host,uart_example)
#   --seeds LIST      jitter seeds, each pass adds one simulation (default: 1,2)
#   --jitter P        probability that an input edge resolves one cycle late (default: 0.5)
#   --force           delete an existing --out directory first
#   -h, --help        this text
#
# Exit status: 0 only if every scenario decoded identically to its unperturbed control AND the negative control
# diverged as required.  Any mismatch, build error or missing input is non-zero.
#
# Jitter in gate level.  The bench drives the raw pads and samples them only through the chip's own pins; the
# injection is the stimulus-side you would get from a late first-stage resolution: an input edge that arrives at a
# clock boundary is presented to the chip one cycle later (probability --jitter, per pin, per edge, seeded).  The
# netlist's s1 flip-flop is a real sg13cmos5l std cell and is *not* forced from the testbench, so the injected edge
# is captured by the actual gate-level synchroniser and propagates through the real netlist.  Metastability itself
# (a cell that resolves to either rail) is not modelled, and the std-cell models are unit-delay functional Verilog,
# so this does not add timing/SDF evidence.
set -uo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
PODENV=$REPO/code/flow/runpod/podenv.sh
[ -f "$PODENV" ] && source "$PODENV"

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; }

NETLIST=""
OUT=""
STDCELL=""
TOP="tt_um_brentius_metronome"
SCENARIOS="spi_host,uart_example"
SEEDS="1,2"
JITTER="0.5"
FORCE=0
RTL=0

while [ $# -gt 0 ]; do
    case "$1" in
        --rtl)       RTL=1 ;;
        --rtl=*)     RTL=1 ;;
        --out)       OUT=${2:-}; shift ;;
        --stdcell)   STDCELL=${2:-}; shift ;;
        --top)       TOP=${2:-}; shift ;;
        --scenarios) SCENARIOS=${2:-}; shift ;;
        --seeds)     SEEDS=${2:-}; shift ;;
        --jitter)    JITTER=${2:-}; shift ;;
        --force)     FORCE=1 ;;
        -h|--help)   usage; exit 0 ;;
        --*)         echo "unknown option $1" >&2; usage >&2; exit 2 ;;
        *)           if [ -n "$NETLIST" ]; then echo "unexpected extra argument $1" >&2; exit 2; fi
                     NETLIST=$1 ;;
    esac
    shift
done

PY=""
for cand in "${CDC_PYTHON:-}" /root/ttvenv/bin/python python python3; do
    [ -n "$cand" ] || continue
    if command -v "$cand" >/dev/null 2>&1 && "$cand" -c 'import cocotb' >/dev/null 2>&1; then
        PY=$cand
        break
    fi
done
[ -n "$PY" ] || { echo "no python with cocotb (set CDC_PYTHON)" >&2; exit 2; }
command -v iverilog >/dev/null 2>&1 || { echo "iverilog not on PATH (source code/flow/runpod/podenv.sh)" >&2; exit 2; }

if [ "$RTL" = "1" ]; then
    unset CDC_GL_NETLIST CDC_STDCELL_DIR CDC_GL_TOP
    if [ -z "$OUT" ]; then
        OUT=${CDC_OUTDIR:-$REPO/build/cdc_rtl_dryrun}
    fi
    KIND=rtl
else
    [ -n "$NETLIST" ] || { echo "no netlist given (or use --rtl)" >&2; usage >&2; exit 2; }
    [ -f "$NETLIST" ] || { echo "netlist not found: $NETLIST" >&2; exit 2; }
    NETLIST=$(cd "$(dirname "$NETLIST")" && pwd)/$(basename "$NETLIST")
    if [ -z "$STDCELL" ]; then
        STDCELL=${PDK_ROOT:-/root/pdk}/${PDK:-ihp-sg13cmos5l}/libs.ref/sg13cmos5l_stdcell/verilog
    fi
    [ -f "$STDCELL/sg13cmos5l_stdcell.v" ] || { echo "no sg13cmos5l_stdcell.v in $STDCELL" >&2; exit 2; }
    ls "$STDCELL"/*_udp.v >/dev/null 2>&1 || { echo "no *_udp.v models in $STDCELL" >&2; exit 2; }
    if [ -z "$OUT" ]; then
        OUT=$(dirname "$NETLIST")/cdc_gl
    fi
    KIND=gl
    export CDC_GL_NETLIST=$NETLIST CDC_STDCELL_DIR=$STDCELL CDC_GL_TOP=$TOP
fi

if [ -e "$OUT" ] && [ -n "$(ls -A "$OUT" 2>/dev/null)" ]; then
    if [ "$FORCE" = "1" ]; then rm -rf "$OUT" || exit 2; else
        echo "refusing to overwrite non-empty $OUT (use --force)" >&2; exit 2
    fi
fi
mkdir -p "$OUT" || exit 2
OUT=$(cd "$OUT" && pwd) || exit 2
export CDC_OUTDIR=$OUT CDC_SCENARIOS=$SCENARIOS CDC_SEEDS=$SEEDS CDC_JITTER=$JITTER

echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) cdc $KIND netlist=${NETLIST:-RTL} top=$TOP scenarios=$SCENARIOS seeds=$SEEDS" \
    | tee "$OUT/run.txt"
echo "cd $REPO && CDC_SCENARIOS=$SCENARIOS CDC_SEEDS=$SEEDS CDC_JITTER=$JITTER pytest code/tests/cdc -q -k 'jitter or negative_control'" \
    | tee -a "$OUT/run.txt"

cd "$REPO" || exit 2
t0=$(date +%s)
"$PY" -m pytest code/tests/cdc -q -k "jitter or negative_control" -p no:cacheprovider \
    > "$OUT/pytest.log" 2>&1
rc=$?
t1=$(date +%s)
wall=$((t1 - t0))

tail -3 "$OUT/pytest.log"
"$PY" - "$OUT" "$rc" "$wall" "$KIND" "$NETLIST" "$STDCELL" "$TOP" "$SCENARIOS" "$SEEDS" "$JITTER" <<'PY'
import hashlib, json, os, subprocess, sys
from datetime import datetime, timezone
out, rc, wall, kind, netlist, stdcell, top, scenarios, seeds, jitter = sys.argv[1:11]

def first(cmd):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    except OSError:
        return "unavailable"
    lines = (p.stdout or p.stderr).strip().splitlines()
    return lines[0].strip() if lines else "no output"

meta = {
    "date_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "kind": kind,
    "rc": int(rc),
    "wall_s": int(wall),
    "netlist": netlist or None,
    "netlist_sha256": hashlib.sha256(open(netlist, "rb").read()).hexdigest() if netlist else None,
    "stdcell_dir": stdcell or None,
    "top": top,
    "scenarios": scenarios.split(","),
    "seeds": seeds.split(","),
    "jitter_probability": float(jitter),
    "iverilog": first(["iverilog", "-V"]),
    "python": first([sys.executable, "-c", "import sys; print(sys.version.split()[0])"]),
    "cocotb": first([sys.executable, "-c", "import cocotb; print(cocotb.__version__)"]),
    "results": (sorted(f for f in os.listdir(out) if f.endswith(".json") and f != "environment.json")
                + sorted("sim/" + f for f in (os.listdir(os.path.join(out, "sim")) if os.path.isdir(os.path.join(out, "sim")) else [])
                         if f.startswith("results_") and f.endswith(".xml"))),
}
with open(os.path.join(out, "run_meta.json"), "w") as fh:
    json.dump(meta, fh, indent=2)
    fh.write("\n")
print(f"wrote {os.path.join(out, 'run_meta.json')} (rc={rc})")
PY

if [ -n "${CDC_GL_NETLIST:-}" ] && [ -d /workspace/results ]; then
    echo "$(date -u +%Y%m%dT%H%M%SZ) cdc gl rc=$rc wall_s=$wall netlist=$NETLIST" >> /workspace/results/runs.log
fi
echo "CDC_GL_END rc=$rc"
exit "$rc"
