#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=4
python3 /workspace/jsc/flow/ll_variant.py metronome_r3_d17 sta_grt_mc --from OpenROAD.STAMidPNR --to OpenROAD.STAMidPNR --state pnr_area0/28-openroad-globalrouting --set 'SYNTH_STRATEGY="AREA 0"' --set 'PNR_CORNERS=["nom_slow_1p08V_125C","nom_fast_1p32V_m40C","nom_typ_1p20V_25C"]' --set OPENROAD_THREADS=4 --set STA_THREADS=4
