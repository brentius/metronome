"""SPEC v2 sections 4-6: threads, pipelined cores, moves, write groups, symbol ports."""
import random

from helpers_v2 import *     # noqa: F401,F403

I = asm.insn
CTRL = m.HOST_MAP["CTRL_BASE"]


def go(chip):
    blk(chip, "CTRL", RUN=1)


def ring(chip, t):
    blk(chip, "CTRL", DOORBELL=chip.DB | (1 << t))
    return chip.cycle                   # the trigger event happens in the next stepped cycle


def execs(chip, core=None, thread=None):
    return [x for x in chip.trace if (core is None or x[1] == core) and (thread is None or x[2] == thread)]


def test_trigger_to_first_instruction_is_three_cycles_and_sequential():
    chip = Chip()
    chip.load_program(0, [I(("IMM", "R0"), imm=1), I(("IMM", "R1"), imm=2), I(pause=1)])
    thread(chip, 0)
    go(chip)
    t = ring(chip, 0)
    steps(chip, 10)
    ex = execs(chip, thread=0)
    assert [(c - t, pc) for c, _, _, pc in ex] == [(3, 0), (4, 1), (5, 2)]
    assert chip.acc.R[:2] == [1, 2]
    assert chip.threads[0].PC == 3 and not chip.threads[0].RUNNING


def test_taken_jump_one_idle_cycle_and_wrong_path_never_executes():
    chip = Chip()
    chip.load_program(0, [
        I(("IMM", "R0"), jmode="always", imm=4),
        I(("IMM", "R1"), imm=0xEE),                 # fetched ahead, must never execute
        I(("IMM", "R1"), imm=0xEE),
        I(("IMM", "R1"), imm=0xEE),
        I(("IMM", "R2"), imm=0x22, pause=1),
    ])
    thread(chip, 0)
    go(chip)
    t = ring(chip, 0)
    steps(chip, 10)
    assert [(c - t, pc) for c, _, _, pc in execs(chip)] == [(3, 0), (5, 4)]
    assert chip.acc.R[1] == 0 and chip.acc.R[0] == 4 and chip.acc.R[2] == 0x22


def test_jump_condition_is_independent_of_move_condition():
    chip = Chip()
    blk(chip, "CTRL")
    chip.flags.F = 0b10                             # F1 set, F0 clear
    chip.load_program(0, [
        I(("IMM", "R0", "if"), ("IMM", "R1", "ifnot"), cond="F0", jmode="if", jcond="F1", imm=7),
        I(pause=1), *[0] * 5, I(("IMM", "R2"), imm=9, pause=1)])
    thread(chip, 0)
    go(chip)
    ring(chip, 0)
    steps(chip, 10)
    assert chip.acc.R[0] == 0 and chip.acc.R[1] == 7 and chip.acc.R[2] == 9


def test_pause_then_dispatch_has_one_idle_cycle_and_round_robin():
    chip = Chip()
    chip.load_program(0, [I(("IMM", "R0"), imm=1, pause=1), I(("IMM", "R1"), imm=2, pause=1)])
    thread(chip, 0, pc=0)
    thread(chip, 1, pc=1)
    go(chip)
    blk(chip, "CTRL", DOORBELL=0b11)
    t = chip.cycle
    steps(chip, 10)
    ex = execs(chip)
    assert [(c - t, th) for c, _, th, _ in ex] == [(3, 0), (5, 1)]


def test_watcher_selects_handler_on_dispatch_line_guard():
    chip = Chip()
    chip.load_program(0, [I(("IMM", "R0"), imm=1, pause=1)] + [0] * 9 + [I(("IMM", "R0"), imm=0x55, pause=1)])
    thread(chip, 0, W0C=m.GUARD_ID["F3"], W0H=10)
    chip.flags.F = 1 << 3
    go(chip)
    ring(chip, 0)
    steps(chip, 8)
    assert chip.acc.R[0] == 0x55


def test_overrun_when_triggered_while_running():
    chip = Chip()
    chip.load_program(0, [I(), I(), I(), I(pause=1)])
    thread(chip, 0)
    go(chip)
    ring(chip, 0)
    steps(chip, 2)
    ring(chip, 0)
    steps(chip, 8)
    assert chip.threads[0].OVR == 1


def test_symbol_ports_commit_and_late():
    """L.SYM / L.DBIT / L.XOR on line 0, committed at the boundary; a write after the disarm is LATE."""
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=8, T0=0, T1=0xFFFF, T2=0xFFFF)
    chip.load_program(0, [
        I(("IMM", "L.SYM"), imm=0b1010), I(("IMM", "L.DBIT"), imm=1), I(("IMM", "L.XOR"), imm=0b0110, pause=1)])
    thread(chip, 0, trig="L0.BEAT")
    go(chip)
    run_line(chip, 0)
    steps(chip, 30)
    ln = chip.lines[0]
    assert ln.STAGED == (0b1011 ^ 0b0110) or ln.STAGED == 0b1101
    assert ln.COMMITTED in (0, 0b1101)
    assert chip.threads[0].LATE == 0
    # now a burst too long for the beat: the write lands after the next boundary
    chip2 = Chip()
    blk(chip2, "LINE", 0, INC=1, MOD=4, T0=0, T1=0xFFFF, T2=0xFFFF)
    chip2.load_program(0, [I(), I(), I(), I(("IMM", "L.SYM"), imm=3, pause=1)])
    thread(chip2, 0, trig="L0.BEAT")
    go(chip2)
    run_line(chip2, 0)
    steps(chip2, 12)
    assert chip2.threads[0].LATE == 1


def test_write_in_boundary_cycle_is_committed():
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=6, T0=0, T1=0xFFFF, T2=0xFFFF)
    chip.load_program(0, [I(), I(), I(("IMM", "L.SYM"), imm=9, pause=1)])     # executes at trigger + 5
    thread(chip, 0, trig="L0.TAP0")                                           # tap 0 fires in the boundary cycle
    go(chip)
    run_line(chip, 0)
    beats = []
    for _ in range(40):
        chip.step(IDLE)
        if chip.lines[0].beat:
            beats.append(chip.cycle - 1)
    hits = [c for c, *_ in execs(chip) if c in beats]
    assert hits, "the write never fell in a boundary cycle"
    assert chip.lines[0].COMMITTED == 9 and chip.threads[0].LATE == 0


def test_conflict_between_cores_on_one_line():
    chip = Chip()
    for c in (0, 1):
        chip.load_program(c, [I(("IMM", "L.SYM"), imm=c + 1, pause=1)])
    thread(chip, 0, core=0)
    thread(chip, 1, core=1)
    go(chip)
    blk(chip, "CTRL", DOORBELL=0b11)
    steps(chip, 6)
    assert chip.ctrl.CONFLICT == 1 and chip.lines[0].STAGED == 1      # core 0 wins


def test_t_stop_disables_thread_after_burst():
    chip = Chip()
    chip.load_program(0, [I(("ZERO", "T.STOP"), ("IMM", "R0"), imm=5, pause=1)])
    thread(chip, 0, trig="ALWAYS")
    go(chip)
    steps(chip, 20)
    assert chip.threads[0].EN == 0 and len(execs(chip)) == 1


def test_response_bound_two_threads_on_one_core():
    """SPEC 5: last instruction <= t + n + 2 + (L_peer + 1), bursts counted in cycles (taken jumps add one)."""
    rnd = random.Random(11)
    prog = [I(), I(jmode="always", imm=2), I(), I(pause=1),        # thread 0 at 0: 4 insns + 1 taken jump = 5
            I(), I(), I(pause=1)]                                    # thread 1 at 4: 3 cycles
    L = {0: 5, 1: 3}
    pcs = {0: 0, 1: 4}
    for trial in range(200):
        chip = Chip()
        chip.load_program(0, prog)
        thread(chip, 0, pc=0)
        thread(chip, 1, pc=4)
        go(chip)
        trig_at = {}
        for _ in range(rnd.randint(0, 6)):
            chip.step(IDLE)
        order = [0, 1] if rnd.random() < 0.5 else [1, 0]
        for t in order:
            for _ in range(rnd.randint(0, 3)):
                chip.step(IDLE)
            trig_at[t] = ring(chip, t)
            # ring sets PC back for the next burst: each thread pauses at its last instruction then would run on
            chip.threads[t].PC = pcs[t]
        steps(chip, 30)
        for t in (0, 1):
            last = max(c for c, _, th, _ in execs(chip, thread=t))
            assert last <= trig_at[t] + L[t] + 2 + (L[1 - t] + 1), (trial, t)
