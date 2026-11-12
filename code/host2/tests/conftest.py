import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (HERE.parent, ROOT / "sim" / "reference", HERE):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
