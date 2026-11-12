"""Load code/md2/machine.py under a private module name.

v1's model imports code/md/machine.py as `machine`; loading v2's tables under `md2_machine` lets both models run in
one Python process.
"""
import importlib.util
import sys
from pathlib import Path

_PATH = Path(__file__).resolve().parents[3] / "code" / "md2" / "machine.py"

if "md2_machine" in sys.modules:
    m = sys.modules["md2_machine"]
else:
    _spec = importlib.util.spec_from_file_location("md2_machine", _PATH)
    m = importlib.util.module_from_spec(_spec)
    sys.modules["md2_machine"] = m
    _spec.loader.exec_module(m)
