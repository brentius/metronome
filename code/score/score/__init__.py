"""Score language (SPEC_V2_SCORE.md part A): parser, static checks, role projection and reference codec."""
from .ast import Diag, Score, ScoreError  # noqa: F401
from .checks import assert_ok, check, check_binding, errors, parse_bind  # noqa: F401
from .codec import Codec, DecodeResult, EncodeError, Encoded, FrameError, Waveform, resolve  # noqa: F401
from .crc import STD, crc_bytes  # noqa: F401
from .parser import parse, parse_file  # noqa: F401
from .project import project  # noqa: F401
