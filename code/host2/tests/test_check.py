"""Static check of SPEC v2 10.4: accepts and rejects, and the response arithmetic compared with the model."""
from common import *
from metronome2_tools.asm import assemble_text
from metronome2_tools.check import check
from metronome2_tools.timing import LineTiming


def line_thread(period=6, body="", extra_line="", extra=""):
    return f"""
.line 0
    period {period}
    {extra_line}
    ctl run
.end
.thread 0
    core 0
    trigger L0.BEAT
    start t
.end
{extra}
.core 0
{body}
"""


def seq(n, sym_at=None, read_at=None):
    """n-instruction burst: instruction k writes the symbol if k == sym_at, reads L.IN if k == read_at."""
    out = []
    for k in range(1, n + 1):
        mv = "nop"
        if k == sym_at:
            mv = "R0 -> L.SYM"
        if k == read_at:
            mv = "L.IN -> R1"
        tail = " pause goto t" if k == n else ""
        out.append(("t: " if k == 1 else "") + mv + tail)
    return "\n".join(out)


def errs(src):
    return check(assemble_text(src)).errors


def test_burst_rule_rejects_loops_without_a_pause():
    e = errs(line_thread(body="t: nop\n   nop goto t"))
    assert any("burst rule violated" in x for x in e)
    assert not errs(line_thread(body="t: nop\n   nop pause goto t"))


def test_a_conditional_back_edge_without_a_pause_is_rejected():
    e = errs(line_thread(body="t: when F0 nop goto t if\n   nop pause goto t"))
    assert any("burst rule violated" in x for x in e)


def test_continuing_into_unprogrammed_memory_is_an_error():
    e = errs(line_thread(body="t: nop\n   nop"))
    assert any("holds no instruction" in x for x in e)


def test_burst_length_counts_the_bubble_of_a_taken_jump():
    p = assemble_text(line_thread(period=40, body="t: nop\n   nop goto a\na: nop pause goto t"))
    assert check(p).threads[0].n_max == 4     # t, nop, bubble, a
    p = assemble_text(line_thread(period=40, body="t: nop\n   nop pause goto t"))
    assert check(p).threads[0].n_max == 2     # a pausing jump has no bubble
    p = assemble_text(line_thread(period=40, body="t: nop goto a\n   nop\na: nop pause goto t"))
    assert check(p).threads[0].n_max == 3     # t, bubble, a


def test_longest_path_wins_over_the_cheap_branch():
    body = "t: when F1 nop goto far if F1\n   nop pause goto t\nfar: nop\n   nop\n   nop pause goto t"
    assert check(assemble_text(line_thread(period=40, body=body))).threads[0].n_max == 1 + 1 + 3


def test_commit_deadline_exact_for_a_sole_thread():
    # trigger t, instruction k executes in t + k + 2; the next boundary is t + 6
    assert not any("LATE" in x for x in errs(line_thread(6, seq(8, sym_at=4))))          # 4 + 2 = 6 <= 6
    e = errs(line_thread(6, seq(8, sym_at=5)))
    assert any("LATE" in x and "burst-cycle 5" in x for x in e)
    assert not errs(line_thread(9, seq(6, sym_at=6)))                                    # 6 + 2 <= 9 and 6 + 3 <= 9


def test_sigma_of_other_threads_on_the_core_shortens_the_deadline():
    other = """
.thread 1
    core 0
    trigger L0.TAP0
    start u
.end
"""

    def prog(L):
        body = seq(3, sym_at=3) + "\nu: " + "\n".join(["nop"] * (L - 1) + ["nop pause goto u"])
        return line_thread(12, body, extra_line="taps 3 - -", extra=other)

    assert not errs(prog(5))                  # Sigma = 6: commit 3+2+6 = 11 <= 12, overrun 11 + 1 <= 12
    e = errs(prog(6))                         # Sigma = 7: commit 12 <= 12 still fits but the trigger spacing does not
    assert any("OVR" in x for x in e) and not any("LATE" in x for x in e)
    e = errs(prog(8))                         # Sigma = 9: commit 14 > 12
    assert any("LATE" in x for x in e)


def test_snapshot_read_must_come_before_the_next_snapshot():
    ok = errs(line_thread(6, seq(8, read_at=3), extra_line="snap beat"))               # 3 + 2 = 5 < 6
    assert not any("next snapshot" in x for x in ok)
    bad = errs(line_thread(6, seq(8, read_at=4), extra_line="snap beat"))              # 4 + 2 = 6 is not < 6
    assert any("next snapshot" in x for x in bad)


def test_overrun_of_the_trigger_spacing():
    e = errs(line_thread(4, seq(3)))                                                    # resp 5, +1 > 4
    assert any("OVR" in x for x in e)
    assert not errs(line_thread(6, seq(3)))


def test_inc_must_be_below_mod():
    for inc, mod in ((6, 6), (7, 6)):
        e = errs(f".line 0\n inc {inc}\n mod {mod}\n.end")
        assert any("INC" in x and "below MOD" in x for x in e), (inc, mod)
    assert not errs(".line 0\n inc 5\n mod 6\n.end")


def test_window_and_tap_rule_for_realigning_lines():
    base = "period 100\n edge P0 rise\n ctl run ren\n window 40 60\n preset 10\n"

    def src(taps):
        return f".line 0\n {base} taps {taps}\n snap tap0\n.end\n"

    assert not errs(src("5 - -"))                       # T < WLO and T <= PRE
    assert not errs(src("80 - -"))                      # T > WHI + INC and T > PRE
    for taps in ("30 - -", "50 - -", "61 - -", "20 - -"):
        e = errs(src(taps))
        assert any("window rule" in x for x in e), taps
    wrap = errs(".line 0\n period 100\n edge P0 rise\n ctl run ren\n window 60 40\n taps 5 - -\n.end\n")
    assert any("wrapping window" in x for x in wrap)
    no_ren = errs(".line 0\n period 100\n edge P0 rise\n ctl run\n window 60 40\n taps 50 - -\n.end\n")
    assert not no_ren                                   # REN never used: the generator never re-aligns
    via_move = assemble_text(".line 0\n period 100\n edge P0 rise\n window 60 40\n taps 5 - -\n.end\n"
                             ".thread 0\n trigger NONE\n start t\n.end\n.core 0\nt: #7 -> L0.CTL\n pause goto t\n")
    assert any("wrapping window" in x for x in check(via_move).errors)


def test_hold_rules():
    e = errs(".line 0\n period 10\n taps 3 - -\n hold none high tap0\n.end")
    assert any("forever" in x for x in e)
    assert not errs(".line 0\n period 10\n taps 3 - -\n hold P4 high tap0\n.end")
    rep = check(assemble_text(".line 0\n period 10\n taps 3 - -\n hold P4 high tap2\n.end"))
    assert any("no effect" in w for w in rep.warnings)


FOLLOW = """
.line 0
    follow
    period 40
    edge P0 rise
    {extra}
    ctl run ren
.end
.thread 0
    core 0
    trigger L0.BEAT
    start t
.end
.core 0
t: R0 -> L.SYM pause goto t
"""


def test_follower_needs_declared_assumptions_for_a_bound():
    rep = check(assemble_text(FOLLOW.format(extra="")))
    assert any("minperiod" in w for w in rep.warnings) and rep.ok
    assert check(assemble_text(FOLLOW.format(extra="minperiod 5"))).ok     # write at t+3 <= 5, resp 3 + 1 <= 5
    rep = check(assemble_text(FOLLOW.format(extra="minperiod 3")))               # write at t+3 fits, spacing does not
    assert any("OVR" in x for x in rep.errors) and not any("LATE" in x for x in rep.errors)
    rep = check(assemble_text(FOLLOW.format(extra="minperiod 2")))
    assert any("LATE" in x for x in rep.errors)


def test_line_timing_gaps():
    p = assemble_text(".line 0\n period 6\n taps - 3 -\n.end\n.line 1\n baud 115200\n.end\n"
                      ".line 2\n inc 3\n mod 10\n taps 4 - -\n.end")
    t = LineTiming(p.lines[0])
    assert (t.gap("BEAT", "BEAT"), t.gap("BEAT", "TAP1"), t.gap("TAP1", "BEAT"), t.gap("TAP1", "TAP1")) == (6, 3, 3, 6)
    assert t.gap("BEAT", "TAP0") == float("inf") and t.gap("TAP0", "BEAT") is None
    assert LineTiming(p.lines[1]).gap("BEAT", "BEAT") == 520          # floor(3125 / 6)
    t = LineTiming(p.lines[2])                                        # phase 0,3,6,9,2,5,8,1,4,7: wraps every 3 or 4
    assert t.gap("BEAT", "BEAT") == 3 and t.gap("TAP0", "TAP0") == 3 and t.gap("BEAT", "TAP0") >= 1
    assert not t.tapmiss_free


def test_budget_directive():
    body = seq(3)
    assert not errs(line_thread(20, body) + "\n.budget thread 0 cycles 5\n")
    assert any("budget" in x for x in errs(line_thread(20, body) + "\n.budget thread 0 cycles 4\n"))
    assert any("not defined" in x for x in errs(line_thread(20, body) + "\n.budget thread 3 cycles 4\n"))


def test_response_bound_arithmetic_matches_the_model_for_two_threads_on_one_core():
    """Two threads, both triggered by L0.BEAT in the same cycle.  The tool's bound must hold on the model, and the
    thread dispatched second must meet it exactly."""
    src = line_thread(40, seq(3), extra="""
.thread 1
    core 0
    trigger L0.BEAT
    start u
.end""") + "\nu: nop\n nop\n nop\n nop pause goto u\n"
    prog = assemble_text(src)
    rep = check(prog)
    assert rep.ok
    chip = Chip()
    load(chip, prog)
    beat_cycles = []
    for _ in range(200):
        chip.step(IDLE)
        if chip.lines[0].beat:
            beat_cycles.append(chip.cycle - 1)
    assert len(beat_cycles) >= 4
    worst = 0
    for b in beat_cycles[1:4]:
        last = {}
        for (cy, c, t, pc) in chip.trace:
            if b < cy <= b + 20:
                last[t] = max(last.get(t, 0), cy)
        for t in (0, 1):
            assert last[t] - b <= rep.threads[t].resp_last, (t, last[t] - b, rep.threads[t].resp_last)
            worst = max(worst, last[t] - b - rep.threads[t].resp_last)
        assert max(last[t] - b - rep.threads[t].resp_last for t in (0, 1)) == 0
    assert worst == 0
