#!/bin/bash
# Back-annotated (SDF) gate-level runs of the v2 skeleton on a completed harden result (pod).
#   sdf_v2.sh TAG PROJECT_TGZ RUN...      RUN = name:corner:test[:clk_ps], e.g. cfg_slow:slow:test_cfg
# PROJECT_TGZ holds the tt_v2_pnr project (test/ with run_local.py, test_cfg.py, gen_cfg_probe.py, cfg_latch_chk.v).
# Netlist and SDF come from /workspace/results/TAG/final. Each run writes /workspace/results/TAG/sdf/<name>/ and
# appends a line to /workspace/results/runs.log.
set -uo pipefail
TAG=$1; TGZ=$2; shift 2
source "$(dirname "$0")/podenv.sh"
RES=/workspace/results/$TAG
NL=$(ls "$RES"/final/nl/*.nl.v | head -1)
W=/root/sdf_${TAG}_$(date -u +%H%M%S)
mkdir -p "$W" && tar -xzf "$TGZ" -C "$W" || exit 2
CELLS=$PDK_ROOT/$PDK/libs.ref/sg13cmos5l_stdcell/verilog
cd "$W/test"
for run in "$@"; do
  IFS=: read -r name corner test clk <<< "$run"
  SDF=$(ls "$RES"/final/sdf/*${corner}*/*.sdf | head -1)
  OUT=$RES/sdf/$name; mkdir -p "$OUT"
  t0=$(date +%s)
  /root/ttvenv/bin/python run_local.py --gl "$NL" --pdk-stdcell "$CELLS" --sdf "$SDF" --test "$test" --name "$name" \
      ${clk:+--clk-ps $clk} > "$OUT/sim.log" 2>&1
  rc=$?
  t1=$(date +%s)
  cp sim_build/$name/results.xml sim_build/$name/cfg_probe.json "$OUT/" 2>/dev/null || true
  cp sim_build/$name/icarus.sdf "$OUT/" 2>/dev/null || true
  errs=$(grep -c "SDF ERROR" "$OUT/sim.log"); warns=$(grep "SDF WARNING" "$OUT/sim.log" | grep -vc "TIMINGCHECK not supported")
  tchk=$(grep -c "TIMINGCHECK not supported" "$OUT/sim.log")
  echo "sdf_errors=$errs other_sdf_warnings=$warns timingcheck_unsupported=$tchk" > "$OUT/sdf_summary.txt"
  grep -h "renamed .* escaped instances" "$OUT/sim.log" >> "$OUT/sdf_summary.txt"
  [ "$errs" -eq 0 ] || rc=99   # an SDF error means part of the file was not annotated
  echo "$(date -u +%Y%m%dT%H%M%SZ) $TAG sdf $name corner=$corner test=$test clk_ps=${clk:-16666} rc=$rc sdf_errors=$errs wall_s=$((t1-t0))" | tee -a /workspace/results/runs.log
done
echo SDF_END
