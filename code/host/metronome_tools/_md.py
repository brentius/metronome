"""Make the machine description (code/md) importable. All encodings come from there; nothing is hard-coded here."""
import sys
from pathlib import Path

_MD = Path(__file__).resolve().parents[2] / "md"
if str(_MD) not in sys.path:
    sys.path.append(str(_MD))

import machine as M  # noqa: E402,F401
from encode import Insn, Move, decode, encode  # noqa: E402,F401
