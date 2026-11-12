"""Load code/md2/machine.py (the single source of v2 names and numbers) under the private name `md2_machine`.

The same name is used by the v2 model (sim/reference/metronome2/md.py), so tools and model share one module object
and can run in one process next to the v1 tools.  Nothing in this package hard-codes an encoding.
"""
import importlib.util
import sys
from pathlib import Path

_PATH = Path(__file__).resolve().parents[2] / "md2" / "machine.py"

if "md2_machine" in sys.modules:
    M = sys.modules["md2_machine"]
else:
    _spec = importlib.util.spec_from_file_location("md2_machine", _PATH)
    M = importlib.util.module_from_spec(_spec)
    sys.modules["md2_machine"] = M
    _spec.loader.exec_module(M)
