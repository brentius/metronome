"""pytest configuration for code/tests/cdc: imports and tool discovery."""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

# pyramid: this directory, the lockstep scenarios/decoders, the reference model tables, the v4 firmware sources
for _p in (HERE, ROOT / "code/tests/lockstep_v2", ROOT / "sim/reference", ROOT / "code/host2"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from _tools import ensure_tools  # noqa: E402

ensure_tools()
