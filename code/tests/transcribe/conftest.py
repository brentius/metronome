import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (HERE, ROOT / "code" / "tests" / "scorec", ROOT / "code" / "host2", ROOT / "code" / "scorec",
          ROOT / "code" / "score", ROOT / "sim" / "reference"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
