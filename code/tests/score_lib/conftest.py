import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (HERE, ROOT / "code/score", ROOT / "code/scorec", ROOT / "code/host2", ROOT / "sim/reference",
          ROOT / "code/tests/scorec", ROOT / "code/tests/checkers"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
