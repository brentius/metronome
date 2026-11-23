"""Render a board-twin sweep result file as a Markdown table (the tables in SWEEP_RESULTS.md come from this).

    python code/tests/board_twin/sweep_table.py sim_build_twin/sweep_results.json
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def head(data):
    return ("clock period %s ps (%.4g MHz); %d points; %d pin-change nudges away from clock edges"
            % (data.get("clock_period_ps"), 1e6 / float(data.get("clock_period_ps")), len(data["grid"]),
               data.get("nudges", 0)))


def table(rows):
    out = ["| SCK | period (chip cycles) | phase | jitter | sample lead | ID | read RAM | read reg | write RAM | "
           "write reg | model mismatches | verdict |",
           "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        out.append("| clk/%.3g | %.3g | %.2f | %.2f | %.2f | %s | %s | %s | %s | %s | %d | %s |" % (
            r["period"], r["period"], r["phase"], r["jitter"], r.get("sample_lead", 0.25),
            "ok" if r["id_ok"] else "**fail**",
            "ok" if r["read_data_ok"] else "**fail**",
            "ok" if r["read_reg_ok"] else "**fail**",
            "ok" if r["write_data_ok"] else "**fail**",
            "ok" if r["write_reg_ok"] else "**fail**",
            r["mismatches"], "PASS" if r["pass"] else "FAIL"))
    return "\n".join(out)


def summary(rows):
    periods = sorted({r["period"] for r in rows})
    full = [p for p in periods if all(x["pass"] for x in rows if x["period"] == p)]
    read_ok = [p for p in periods if all(x["read_data_ok"] and x["read_reg_ok"] and x["id_ok"]
                                         for x in rows if x["period"] == p)]
    write_ok = [p for p in periods if all(x["write_data_ok"] and x["write_reg_ok"]
                                          for x in rows if x["period"] == p)]
    mism = sum(r["mismatches"] for r in rows)
    lines = [
        "- full link (ID read + RAM read + register read + writes) at every tested phase: " +
        (", ".join("clk/%.3g" % p for p in full) or "none"),
        "- reads at every tested phase: " + (", ".join("clk/%.3g" % p for p in read_ok) or "none"),
        "- writes at every tested phase: " + (", ".join("clk/%.3g" % p for p in write_ok) or "none"),
        "- model mismatches over all points: %d" % mism,
    ]
    return "\n".join(lines)


METRICS = (
    ("ID read", "id_ok"),
    ("RAM read", "read_data_ok"),
    ("register read", "read_reg_ok"),
    ("RAM write", "write_data_ok"),
    ("register write", "write_reg_ok"),
)


def fine_table(rows):
    """A period x phase grid of one metric per row, for the fine-phase runs (two-field TWIN_GRID points)."""
    periods = sorted({r["period"] for r in rows})
    phases = sorted({round(r["phase"], 4) for r in rows})
    out = ["| SCK | " + " | ".join("phase %.2f" % p for p in phases) + " |",
           "|---|" + "---|" * len(phases)]
    for period in periods:
        group = {round(r["phase"], 4): r for r in rows if r["period"] == period}
        for label, key in METRICS:
            cells = []
            for phase in phases:
                row = group.get(phase)
                cells.append("n/a" if row is None else ("ok" if row[key] else "**fail**"))
            out.append("| clk/%.3g %s | %s |" % (period, label, " | ".join(cells)))
    return "\n".join(out)


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    path = Path(args[0]) if args else HERE / "sim_build_twin" / "sweep_results.json"
    data = load(path)
    print(head(data))
    print()
    print(fine_table(data["grid"]) if "--fine" in argv else table(data["grid"]))
    print()
    print(summary(data["grid"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
