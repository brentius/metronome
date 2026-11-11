#!/bin/bash
# One-time (per pod) setup of the Tiny Tapeout flow inside the LibreLane image.
# Everything installs on the container disk (/root); only results go to the network volume (/workspace).
# Lesson carried from ns-accel: never install tools on the MooseFS volume (40+ min, pip hangs).
set -euo pipefail
TT_TOOLS_REF=${TT_TOOLS_REF:-9d13ff3e3e6202090740110438c6a10c1d62ca0f}   # tt-support-tools main, 2026-11-05
PDK_FAMILY=ihp-sg13cmos5l
PDK_VERSION=${PDK_VERSION:-89d42ee6d2fd9b50b86a1aada6fee6673c3e6008}    # pinned by tt-gds-action precheck @ttihp27a
export PDK_ROOT=${PDK_ROOT:-/root/pdk}
LOG=/workspace/results/setup_flow_$(date -u +%Y%m%d-%H%M%S).log
mkdir -p /workspace/results
exec > >(tee "$LOG") 2>&1
echo "setup_flow start $(date -u)"

# libstdc++ for pip wheels on the Nix image
source "$(dirname "$0")/podenv.sh"

# tt-support-tools at a pinned commit
if [ ! -d /root/tt/.git ]; then
  git clone -q https://github.com/TinyTapeout/tt-support-tools.git /root/tt
fi
git -C /root/tt fetch -q origin "$TT_TOOLS_REF" || true
git -C /root/tt checkout -q "$TT_TOOLS_REF"

# Python env that sees LibreLane (system site packages) plus tt-support-tools' lighter deps
if [ ! -x /root/ttvenv/bin/python ]; then
  python3 -m venv --system-site-packages /root/ttvenv
fi
/root/ttvenv/bin/python -m pip install -q chevron configupdater gdstk gitpython mistune python-frontmatter \
  pyyaml requests cairosvg matplotlib pytest cocotb==2.1.0 find_libpython
/root/ttvenv/bin/python -c "import librelane, yaml, gdstk, cocotb; print('PY_OK librelane', librelane.__file__)"

# tt-support-tools invokes `yowasp-yosys` (WebAssembly Yosys); use the image's native Yosys with the same CLI.
mkdir -p /root/bin
printf '#!/bin/sh\nexec yosys "$@"\n' > /root/bin/yowasp-yosys
chmod +x /root/bin/yowasp-yosys

# PDK via ciel (bundled in the image)
if [ ! -d "$PDK_ROOT/$PDK_FAMILY" ]; then
  mkdir -p "$PDK_ROOT"
  ciel enable --pdk-root "$PDK_ROOT" --pdk-family "$PDK_FAMILY" "$PDK_VERSION" || \
  ciel enable --pdk-root "$PDK_ROOT" --pdk-family ihp-sg13g2 "$PDK_VERSION"
fi
[ -d "$PDK_ROOT/$PDK_FAMILY" ] || { echo "PDK $PDK_FAMILY missing under $PDK_ROOT"; exit 3; }
ls "$PDK_ROOT"
ls "$PDK_ROOT/$PDK_FAMILY/libs.ref" || true

{
  echo "date $(date -u)"
  echo "tt-support-tools $(git -C /root/tt rev-parse HEAD)"
  echo "pdk $PDK_FAMILY $PDK_VERSION"
  echo "librelane $(python3 -c 'import librelane;print(getattr(librelane,"__version__","?"))')"
  for t in openroad yosys magic klayout netgen iverilog verilator; do echo "$t $(command -v $t)"; done
} > /root/flow_versions.txt
cat /root/flow_versions.txt
echo "SETUP_FLOW_DONE"
