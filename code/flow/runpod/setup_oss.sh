#!/bin/bash
# Install YosysHQ OSS CAD Suite (sby, smtbmc, bitwuzla, yosys-slang) on container disk for the v3 formal checks.
#   setup_oss.sh [RELEASE_DATE]   default 2026-11-15
set -euo pipefail
D=${1:-2026-11-15}; F=oss-cad-suite-linux-x64-${D//-/}.tgz
cd /root
[ -x /root/oss-cad-suite/bin/sby ] && { echo "already installed"; exit 0; }
curl -fsSL -o "$F" "https://github.com/YosysHQ/oss-cad-suite-build/releases/download/$D/$F"
sha256sum "$F" | tee /root/oss-cad-suite.sha256
tar -xzf "$F" && rm -f "$F"
/root/oss-cad-suite/bin/yosys -V; /root/oss-cad-suite/bin/sby --help >/dev/null && echo SBY_OK
ls /root/oss-cad-suite/bin/bitwuzla && echo BITWUZLA_OK
