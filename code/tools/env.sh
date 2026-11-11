# Source from Git Bash: puts the local OSS CAD Suite (2026-10-22) on PATH.
# Override the location with OSS_CAD_SUITE=/path/to/oss-cad-suite.
OSS_CAD_SUITE="${OSS_CAD_SUITE:-/c/Users/b_yee23/tools/oss-cad-suite}"
export PATH="$OSS_CAD_SUITE/bin:$OSS_CAD_SUITE/lib:$PATH"
# Verilator's Windows build looks for its include files under a Linux path unless this is set.
export VERILATOR_ROOT="$(cygpath -w "$OSS_CAD_SUITE/share/verilator" 2>/dev/null || echo "$OSS_CAD_SUITE/share/verilator")"
