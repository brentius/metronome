import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
# board/ loader core, the metronome2 cycle model, and the lockstep_v2 RTL source list (reused, not copied)
sys.path[:0] = [str(HERE), str(ROOT / "sim/reference"), str(ROOT / "code/host2"),
                str(ROOT / "code/tests/lockstep_v2")]
