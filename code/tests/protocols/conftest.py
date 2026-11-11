import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(HERE), str(ROOT / "code/tests/lockstep"), str(ROOT / "code/tests/checkers"),
                str(ROOT / "code/host"), str(ROOT / "code/md"), str(ROOT / "sim/reference")]
