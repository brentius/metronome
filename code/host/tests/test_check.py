import pytest

from metronome_tools.asm import assemble_text
from metronome_tools.check import check

HDR = """
.beatgen 0
    period 100
    taps 30 60 -
    ctl run
.end
"""


def eng(trigger="BG0.BEAT", start="s", core=0, n=0, extra=""):
    return f".engine {n}\n core {core}\n trigger {trigger}\n start {start}\n{extra}.end\n"


def rep(src):
    return check(assemble_text(src))


def test_self_loop_without_pause_rejected():
    r = rep(HDR + eng() + "s: ZERO -> R0\n goto s\n")
    assert len(r.errors) == 1
    assert "burst rule" in r.errors[0] and "s(0x00)" in r.errors[0] and "pause" in r.errors[0]


def test_two_instruction_loop_names_path():
    r = rep(HDR + eng() + "s: nop\nt: when F0  goto s if\n pause\n")
    assert any("s(0x00) -> t(0x01) -> s(0x00)" in e for e in r.errors)


def test_loop_through_pause_is_fine():
    r = rep(HDR + eng() + "s: nop\n pause goto s\n")
    assert r.ok, r.errors


def test_conditional_back_edge_without_pause():
    r = rep(HDR + eng() + "s: when SH0.DONE  goto s ifnot\n pause\n")
    assert not r.ok and "loop" in r.errors[0]


def test_fall_into_unprogrammed_memory():
    r = rep(HDR + eng() + "s: nop\n")
    assert any("holds no instruction" in e for e in r.errors)


def test_loop_in_unreachable_code_still_rejected():
    r = rep("s: pause goto s\n.org 8\nx: nop\n goto x\n")
    assert any("burst rule" in e for e in r.errors)


def test_cycle_in_second_core_named():
    r = rep(".core 1\nq: goto q\n")
    assert any("core 1" in e and "q(0x00)" in e for e in r.errors)


def diamond():
    # s -> a(2 insns) | b(1 insn) -> join -> pause : longest path s,a1,a2,j = 4
    return """
s:      when F0  goto b if
a1:     nop
a2:     goto j
b:      nop
j:      pause goto s
"""


def test_worst_case_length_on_branching_cfg():
    r = rep(HDR + eng() + diamond())
    er = r.engines[0]
    assert r.ok, r.errors
    assert er.bursts[0].n == 4
    assert [a for a in er.bursts[0].path] == [0, 1, 2, 4]      # s, a1, a2, j
    assert er.n_max == 4 and er.resp_last == 4 + 1             # first insn at trigger+2, last at trigger+n+1


def test_resume_points_after_pause_are_bursts_too():
    r = rep(HDR + eng() + "s: pause\n nop\n nop\n pause goto s\n")
    er = r.engines[0]
    assert sorted((b.entry, b.n) for b in er.bursts) == [(0, 1), (1, 3)]
    assert er.n_max == 3


def test_watcher_handler_is_an_entry():
    src = HDR + eng(extra=" watch0 F1 -> h\n") + "s: pause goto s\nh: nop\n nop\n pause goto s\n"
    er = rep(src).engines[0]
    assert {b.kind for b in er.bursts} >= {"start", "watch0"}
    assert er.n_max == 3


def test_sym_write_position_and_budget_error():
    # BG0.BEAT every 100 cycles but a window of 100: put the E.SYM write at instruction 100 -> too late
    body = "s:\n" + "  nop\n" * 99 + "  ZERO -> E.SYM\n pause goto s\n"
    r = rep(HDR + eng() + body)
    assert any("LATE" in e and "E.SYM" in e for e in r.errors), r.errors


def test_budget_ok_and_sym_window_from_beatgen():
    r = rep(HDR + eng("BG0.TAP1") + "s: ZERO -> E.SYM\n pause goto s\n")
    er = r.engines[0]
    assert r.ok, r.errors
    # tap 1 at phase 60 of 100 (inc 1): 40 cycles to the beat; window = 1 + (100-1-60)  = 40
    assert er.budget_sym == 40 and er.period_min == 100


def test_sym_write_too_late_for_tap_window():
    body = "s:\n" + "  nop\n" * 40 + "  ZERO -> E.SYM\n pause goto s\n"
    r = rep(HDR + eng("BG0.TAP1") + body)
    assert any("LATE" in e for e in r.errors)


def test_overrun_against_trigger_spacing():
    body = "s:\n" + "  nop\n" * 100 + "  pause goto s\n"
    r = rep(HDR + eng() + body)
    assert any("OVR" in e and "100-cycle minimum spacing" in e for e in r.errors)


def test_declared_budget():
    ok = rep(HDR + eng() + ".budget engine 0 cycles 5\ns: nop\n nop\n nop\n pause goto s\n")
    assert ok.ok, ok.errors
    bad = rep(HDR + eng() + ".budget engine 0 cycles 4\ns: nop\n nop\n nop\n pause goto s\n")
    assert len(bad.errors) == 1 and "exceeds declared budget of 4 cycles" in bad.errors[0]
    assert "s(0x00)" in bad.errors[0] and "->" in bad.errors[0]
    ins = rep(HDR + eng() + ".budget engine 0 insns 3\ns: nop\n nop\n nop\n pause goto s\n")
    assert any("instructions" in e for e in ins.errors)


def test_shared_core_response_bound():
    src = HDR + eng(start="s0") + eng(trigger="BG0.TAP0", start="s1", n=1) + \
        ".budget engine 0 cycles 12\n.core 0\ns0: nop\n nop\n pause goto s0\ns1: nop\n nop\n nop\n nop\n pause goto s1\n"
    r = rep(src)
    e0, e1 = r.engines[0], r.engines[1]
    assert (e0.n_max, e1.n_max) == (3, 5)
    assert e0.others == 5 and e0.resp_last == 3 + 1 + 5      # own + 1 + the other engine's longest burst
    assert e1.others == 3
    assert r.ok, r.errors
    tight = rep(src.replace("cycles 12", "cycles 8"))
    assert any("conservative" in e and "8 cycles" in e for e in tight.errors)


def test_engines_on_different_cores_do_not_add():
    src = HDR + eng(start="s0") + eng(trigger="BG0.TAP0", start="s1", n=1, core=1) + \
        "s0: nop\n pause goto s0\n.core 1\ns1: nop\n nop\n pause goto s1\n"
    r = rep(src)
    assert r.engines[0].others == 0 and r.engines[1].others == 0


def test_disabled_engine_ignored_in_sharing():
    src = HDR + eng(start="s0") + eng(trigger="BG0.TAP0", start="s1", n=1, extra=" disable\n") + \
        "s0: nop\n pause goto s0\ns1: nop\n nop\n pause goto s1\n"
    assert rep(src).engines[0].others == 0


def test_shared_unit_warning():
    src = HDR + eng(start="s0") + eng(trigger="BG0.TAP0", start="s1", n=1, core=1) + \
        "s0: #1 -> R0\n pause goto s0\n.core 1\ns1: #2 -> R0\n pause goto s1\n"
    assert any("R0" in w and "different cores" in w for w in rep(src).warnings)


def test_missing_bg_and_none_trigger_warn():
    r = rep(eng("BG2.BEAT") + "s: pause goto s\n")
    assert any("BG2" in w for w in r.warnings)


def test_missing_start_warns():
    r = rep(".engine 0\n trigger ALWAYS\n.end\ns: pause goto s\n")
    assert any("no 'start'" in w for w in r.warnings)
