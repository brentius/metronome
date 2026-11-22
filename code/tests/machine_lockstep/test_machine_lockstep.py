"""pytest: Lean machine-sim versus the metronome2 model, per cycle, on the lockstep_v2 scenarios.

    python -m pytest code/tests/machine_lockstep -q            # real exe (skips if missing)
    MACHINE_LOCKSTEP_SEEDS=10 python -m pytest ...             # random seeds 1..10 (default 4)
    MACHINE_LOCKSTEP_FAKE=1 python -m pytest ...               # harness self-test with fake_sim.py
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE)]

import run_lockstep  # noqa: E402
from lean_proc import default_exe, exe_available, fake_cmd  # noqa: E402

SEEDS = int(os.environ.get("MACHINE_LOCKSTEP_SEEDS", "4"))
SEEDS_V3 = int(os.environ.get("MACHINE_LOCKSTEP_V3_SEEDS", "2"))
FAKE = os.environ.get("MACHINE_LOCKSTEP_FAKE") == "1"
DIRECTED = ["smoke", "eth_loopback", "follower", "hold", "taps", "units", "reset_mid", "spi_target", "shifter_parallel"]
DIRECTED_V3 = ["v3_live_misr", "v3_freeze", "v3_ecap", "v3_freeze2"]
DIRECTED_V4 = ["v4_config_write", "v4_replay", "v4_stage1", "v4_stage2", "v4_uart_reply", "v4_crc_reply"]
ALL = (DIRECTED + [f"random_{s}" for s in range(1, SEEDS + 1)] + DIRECTED_V3
       + [f"random3_{s}" for s in range(1, SEEDS_V3 + 1)] + DIRECTED_V4)


@pytest.mark.skipif(not FAKE and not exe_available(),
                    reason=f"Lean exe not built: {default_exe()} (lake build machine-sim, or set MACHINE_SIM)")
@pytest.mark.parametrize("scenario", ALL)
def test_machine_lockstep(scenario):
    rep = run_lockstep.run(scenario, fake_cmd() if FAKE else None, verbose=False)
    assert rep["ok"], (f"{scenario}: {rep['mismatching_keys']} mismatching keys, first cycle {rep['first_mismatch_cycle']}: "
                       + "; ".join(f"{m['key']}@{m['cycle']} py={m['python']} lean={m['lean']}" for m in rep["mismatches"][:8]))
    assert rep["check"] in (None, "pass"), rep["check"]
