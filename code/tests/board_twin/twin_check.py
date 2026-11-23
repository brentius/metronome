"""The host-link verdict, derived from the raw bytes a trial returns (never from a stored boolean).

`trial_flags()` is what the sweep table shows and `link_problems()` is the whole PASS/FAIL decision, so every test
that uses it -- the smoke test, the sweep and the negative control -- is checking the same thing, and the negative
control can corrupt one raw field to prove the decision is not vacuous.

Evidence class: host-side check logic, exercised RTL-simulated by `board_twin_tb.py`; no hardware.
"""

ID_VALUE = 0xA2                 # CTRL.ID = 0xA0 | machine version 2 (SPEC v2 9)

#: (raw field, expectation field, description) for the four byte-level comparisons.
COMPARISONS = (
    ("readback", "expect_data", "data RAM read back at the trial timing"),
    ("phase_readback", "expect_reg", "runtime register read back at the trial timing"),
    ("data_via_spec", "expect_data", "data RAM content read back at clk/16"),
    ("phase_via_spec", "expect_reg", "runtime register content read back at clk/16"),
)

#: The four comparisons plus the ID read, as the five booleans in the sweep table.
FLAG_NAMES = {
    "readback": "read_data_ok",
    "phase_readback": "read_reg_ok",
    "data_via_spec": "write_data_ok",
    "phase_via_spec": "write_reg_ok",
}


def trial_flags(row):
    """The five pass/fail booleans, recomputed from the raw hex bytes and the ID."""
    flags = {"id_ok": row["id"] == ID_VALUE}
    for raw, expect, _why in COMPARISONS:
        flags[FLAG_NAMES[raw]] = row[raw] == row[expect]
    return flags


def link_problems(row):
    """Every reason this trial is not a working host link.  Empty means the link worked at that timing."""
    problems = []
    if row["id"] != ID_VALUE:
        problems.append("CTRL.ID read 0x%02X, not 0x%02X" % (row["id"], ID_VALUE))
    for raw, expect, why in COMPARISONS:
        if row[raw] != row[expect]:
            problems.append("%s: got %s, expected %s" % (why, row[raw], row[expect]))
    if row.get("mismatches"):
        problems.append("%d LSB cycle(s) differ between the RTL and the cycle model" % row["mismatches"])
    return problems


def link_ok(row):
    return not link_problems(row)
