"""Locate the OSS CAD Suite the same way code/tools/env.sh does, without requiring a sourced shell."""
from __future__ import annotations

import os
import shutil
from pathlib import Path


def suite_dir() -> Path | None:
    candidates = [os.environ.get("OSS_CAD_SUITE"),
                  r"C:\Users\b_yee23\tools\oss-cad-suite",
                  "/opt/oss-cad-suite", "/usr/local/oss-cad-suite", "/c/Users/b_yee23/tools/oss-cad-suite"]
    for candidate in candidates:
        if candidate and (Path(candidate) / "bin").is_dir():
            return Path(candidate)
    return None


def ensure_tools() -> Path | None:
    """Prepend <suite>/bin and <suite>/lib to PATH (Windows yosys needs the DLLs in lib)."""
    suite = suite_dir()
    if suite is None:
        return None
    for sub in ("lib", "bin"):
        d = str(suite / sub)
        if d not in os.environ.get("PATH", "").split(os.pathsep):
            os.environ["PATH"] = d + os.pathsep + os.environ.get("PATH", "")
    os.environ.setdefault("VERILATOR_ROOT", str(suite / "share/verilator"))
    return suite


def have(tool: str) -> bool:
    return shutil.which(tool) is not None
