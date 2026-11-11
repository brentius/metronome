"""Metronome v1 cycle-level reference model (oracle for the RTL). Normative source: wiki/SPEC.md."""
import sys
from pathlib import Path

_MD = Path(__file__).resolve().parents[3] / "code" / "md"
if str(_MD) not in sys.path:
    sys.path.insert(0, str(_MD))

from .chip import Chip  # noqa: E402,F401
from . import spi  # noqa: E402,F401
