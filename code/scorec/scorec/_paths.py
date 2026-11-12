"""Make the score front end, the v2 toolchain and the model importable (repo layout, no installation)."""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in (ROOT / "code" / "score", ROOT / "code" / "host2", ROOT / "sim" / "reference"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
