"""Negative tests run the real lockstep loop with one deliberately faulty probe."""
import os
from types import SimpleNamespace

from cocotb.types import LogicArray

import lockstep_tb

original_probe = lockstep_tb.probe


def faulty_probe(dut, model, *args, **kwargs):
    fault = os.environ["PROBE_FAULT"]
    if fault == "missing_handle":
        class MissingAccumulator:
            def __getattr__(self, name):
                if name == "u_acc":
                    raise AttributeError(name)
                return getattr(dut, name)
        return original_probe(MissingAccumulator(), model, *args, **kwargs)
    if fault == "unresolved_value":
        handles = args[0] if args else kwargs["handles"]
        handles["u_acc.a"] = SimpleNamespace(value=LogicArray("XXXXXXXX"))
        return original_probe(dut, model, *args, **kwargs)
    state = original_probe(dut, model, *args, **kwargs)
    actual, expected = state["acc.A"]
    state["acc.A"] = (None if fault == "unavailable" else actual ^ 1, expected)
    return state


lockstep_tb.probe = faulty_probe
lockstep = lockstep_tb.lockstep
