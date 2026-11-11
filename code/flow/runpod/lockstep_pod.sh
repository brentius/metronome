#!/bin/bash
# Run the lockstep harness (RTL or gate level vs the reference model) on the pod, where the PDK models live.
#   lockstep_pod.sh REPO_TGZ MODE [HARDEN_TAG] [-k EXPR]
#     MODE rtl       code/rtl with behavioural memories (same as on the laptop)
#     MODE ihp_sram  code/rtl with USE_IHP_SRAM and the PDK's SRAM behavioural models
#     MODE gl        the harden result's final/nl netlist + IHP stdcell and SRAM models (needs HARDEN_TAG)
# REPO_TGZ: `podctl pack` of code/rtl code/md code/tests/lockstep code/tests/checkers code/host/metronome_tools code/host/examples
# sim/reference. Results: /workspace/results/lockstep/<stamp>_<MODE>[_TAG]/ (junit xml, pytest log).
set -uo pipefail
TGZ=$1; MODE=$2; shift 2
TAG=""
if [ "$MODE" = gl ]; then TAG=$1; shift; fi
source "$(dirname "$0")/podenv.sh"
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
OUT=/workspace/results/lockstep/${STAMP}_${MODE}${TAG:+_$TAG}
mkdir -p "$OUT"
W=/root/lockstep_${STAMP}
mkdir -p "$W" && tar -xzf "$TGZ" -C "$W" || exit 2
LIB=$PDK_ROOT/$PDK/libs.ref
SR=$LIB/sg13cmos5l_sram/verilog
SRAM_MODELS="$SR/RM_IHPSG13_1P_256x64_c2_bm_bist.v:$SR/RM_IHPSG13_1P_512x32_c2_bm_bist.v:$SR/RM_IHPSG13_1P_core_behavioral_bm_bist.v"
case "$MODE" in
  rtl)      export LOCKSTEP_TAG=rtl ;;
  ihp_sram) export LOCKSTEP_TAG=ihp LOCKSTEP_DEFINES=USE_IHP_SRAM,FUNCTIONAL,SIM LOCKSTEP_EXTRA=$SRAM_MODELS ;;
  gl)       NL=$(ls /workspace/results/$TAG/final/nl/*.nl.v | head -1)
            [ -f "$NL" ] || { echo "no netlist for $TAG"; exit 2; }
            export LOCKSTEP_TAG=gl LOCKSTEP_NETLIST=$NL LOCKSTEP_DEFINES=FUNCTIONAL,SIM,GL_TEST
            export LOCKSTEP_EXTRA="$LIB/sg13cmos5l_stdcell/verilog/sg13cmos5l_udp.v:$LIB/sg13cmos5l_stdcell/verilog/sg13cmos5l_stdcell.v:$SRAM_MODELS"
            cp "$NL" "$OUT/" ;;
  *) echo "bad mode $MODE"; exit 2 ;;
esac
cd "$W"
t0=$(date +%s)
/root/ttvenv/bin/python -m pytest code/tests/lockstep -q -p no:cacheprovider "$@" > "$OUT/pytest.log" 2>&1
rc=$?
t1=$(date +%s)
cp code/tests/lockstep/sim_build_*/results_*.xml "$OUT/" 2>/dev/null || true
tail -3 "$OUT/pytest.log"
echo "$STAMP lockstep $MODE ${TAG} rc=$rc wall_s=$((t1-t0)) args=$*" | tee -a /workspace/results/runs.log
echo "LOCKSTEP_END rc=$rc"
exit $rc
