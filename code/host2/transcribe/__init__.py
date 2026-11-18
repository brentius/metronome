"""Transcription: record a wire, emit a score (host-side, zero chip area)."""
from .crc_search import CrcMatch, search_crc  # noqa: F401
from .infer import (Classification, InferenceError, Transcription, UartInference, classify,  # noqa: F401
                    emit_uart_score, infer_uart, transcribe)
