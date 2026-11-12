"""scorec: score compiler for Metronome v2 (SPEC_V2_SCORE.md part A section 12 onto SPEC_V2.md part B)."""
from . import _paths  # noqa: F401
from .api import CompileError, Compiled, compile_score  # noqa: F401
