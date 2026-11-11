from helpers import *     # noqa: F401,F403

DIS = 0xFFFF


def beat_chip(inc=1, mod=20, trig="BG0.BEAT", taps=(DIS, DIS, DIS), engines=(0,)):
    chip = Chip()
    bg_cfg(chip, 0, INC=inc, MOD=mod, T0=taps[0], T1=taps[1], T2=taps[2], CTL=1)
    for e in engines:
        eng_cfg(chip, e, TRIG=m.TRIG_ID[trig], CFG=eng_cfgbyte(1, 0, 0))
    ctrl(chip, "RUN", 1)
    return chip


def to_beat(chip):
    """Step until a beat cycle t has been executed; returns t."""
    while True:
        chip.step(IDLE, 0)
        if chip.bg[0].beat:
            return chip.cycle - 1


def test_trigger_ready_dispatch_first_insn_timing():
    chip = beat_chip()
    load(chip, [I(("IMM", "R0"), imm=5), I(("IMM", "R1"), imm=6), I(("IMM", "R2"), imm=7, pause=True, jmode="always")])
    to_beat(chip)                                        # cycle t = beat, trigger
    e = chip.eng[0]
    assert (e.READY, e.RUNNING, chip.cores[0].XV) == (1, 0, 0)       # READY visible in t+1
    chip.step(IDLE, 0)                                              # t+1: dispatch
    assert (e.READY, e.RUNNING, chip.cores[0].XV, chip.cores[0].XE) == (0, 1, 1, 0)
    assert chip.acc.R[0] == 0
    chip.step(IDLE, 0)                                              # t+2: first instruction executes
    assert chip.acc.R == [5, 0, 0, 0]
    chip.step(IDLE, 0)                                              # t+3
    assert chip.acc.R == [5, 6, 0, 0]
    chip.step(IDLE, 0)                                              # t+4: last instruction (pause)
    assert chip.acc.R == [5, 6, 7, 0]
    assert (e.RUNNING, chip.cores[0].XV, e.PC) == (0, 0, 7)         # pause with jump to imm=7


def test_pause_without_jump_saves_next_pc():
    chip = Chip()
    n = oneshot(chip, [I(("IMM", "R0"), imm=1), I(("IMM", "R0"), imm=2, pause=True)])
    assert n == 3 and chip.eng[0].PC == 2 and chip.acc.R[0] == 2    # dispatch + 2 instructions


def test_back_to_back_bursts_on_one_core():
    chip = beat_chip(engines=(0, 1))
    load(chip, [I(("IMM", "R0"), imm=1), I(("IMM", "R1"), imm=2, pause=True, jmode="always")])
    load(chip, [I(("IMM", "R2"), imm=3), I(("IMM", "R3"), imm=4, pause=True, jmode="always")], at=4)
    eng_cfg(chip, 1, PC=4)
    to_beat(chip)
    assert (chip.eng[0].READY, chip.eng[1].READY) == (1, 1)
    chip.step(IDLE, 0)                                    # t+1: engine 0 dispatched (lowest wins)
    assert (chip.cores[0].XE, chip.eng[1].READY) == (0, 1)
    chip.step(IDLE, 0)                                    # t+2
    assert chip.acc.R == [1, 0, 0, 0]
    chip.step(IDLE, 0)                                    # t+3: engine 0 last insn, engine 1 dispatched in the same cycle
    assert chip.acc.R == [1, 2, 0, 0] and chip.cores[0].XE == 1 and chip.cores[0].XV == 1
    chip.step(IDLE, 0)                                    # t+4: no gap
    assert chip.acc.R == [1, 2, 3, 0]
    chip.step(IDLE, 0)                                    # t+5
    assert chip.acc.R == [1, 2, 3, 4] and chip.eng[1].RUNNING == 0


def test_round_robin_prevents_always_trigger_starvation():
    chip = Chip()
    # Engines 0 and 1 continuously rearm; engine 2 is a one-shot doorbell request.
    for e in (0, 1):
        eng_cfg(chip, e, CFG=eng_cfgbyte(1), TRIG=m.TRIG_ID["ALWAYS"], PC=e * 4)
    eng_cfg(chip, 2, CFG=eng_cfgbyte(1), TRIG=m.TRIG_ID["NONE"], PC=8)
    load(chip, [I(), I(pause=True, jmode="always", imm=0)], at=0)
    load(chip, [I(), I(pause=True, jmode="always", imm=4)], at=4)
    load(chip, [I(("IMM", "HOST.OUT"), imm=0xA5), I(pause=True)], at=8)
    ctrl(chip, "RUN", 1)
    chip.eng[2].fire_now()  # same READY transition as a completed host doorbell write
    step(chip, 7)
    assert chip.eng[2].RUNNING or chip.host.OUTV
    assert chip.host.OUTB == 0xA5


def test_round_robin_cursor_wrap_skips_unready_and_other_core():
    chip = Chip()
    core = chip.cores[0]
    # Starting at ID 1 must skip a wrong-core READY engine and wrap to ID 5.
    core.RR = 1
    eng_cfg(chip, 0, CFG=eng_cfgbyte(1, 0), PC=0)
    eng_cfg(chip, 1, CFG=eng_cfgbyte(1, 1), PC=0)
    eng_cfg(chip, 5, CFG=eng_cfgbyte(1, 0), PC=0)
    eng_cfg(chip, 0, TRIG=m.TRIG_ID["NONE"])
    eng_cfg(chip, 1, TRIG=m.TRIG_ID["NONE"])
    eng_cfg(chip, 5, TRIG=m.TRIG_ID["NONE"])
    load(chip, [I(pause=True)], core=0, at=0)
    load(chip, [I(pause=True)], core=1, at=0)
    ctrl(chip, "RUN", 1)
    chip.eng[0].READY = 1
    chip.eng[1].READY = 1
    chip.eng[5].READY = 1
    core.plan(chip)
    assert core.dispatch == 5
    assert core.RR == 1  # plan must preserve cycle-t state until commit
    core.commit()
    assert core.RR == 0
    # The next scan wraps from 0 and selects engine 0 ahead of engine 5.
    core.XV = 0
    chip.eng[5].READY = 0
    core.plan(chip)
    assert core.dispatch == 0
    core.commit()
    assert core.RR == 1
    core.reset()
    assert core.RR == 0


def test_round_robin_watchers_use_selected_engine_and_cursor_holds():
    chip = Chip()
    core = chip.cores[0]
    eng_cfg(chip, 0, CFG=eng_cfgbyte(1), PC=0x10, TRIG=m.TRIG_ID["NONE"])
    eng_cfg(chip, 1, CFG=eng_cfgbyte(1), PC=0x20, TRIG=m.TRIG_ID["NONE"],
            W0C=m.GUARD_ID["F3"], W0H=0x30)
    load(chip, [I(pause=True)], at=0x10)
    load(chip, [I(pause=True)], at=0x20)
    load(chip, [I(pause=True)], at=0x30)
    ctrl(chip, "RUN", 1)
    core.RR = 1
    chip.flags.F = 1 << 3
    chip.eng[0].READY = chip.eng[1].READY = 1
    core.plan(chip)
    assert core.dispatch == 1 and core.next[1] == 0x30
    core.commit()
    assert core.RR == 2

    # No dispatch while globally stopped or while busy must leave the cursor unchanged.
    chip.ctrl.RUN = 0
    core.XV = 0
    core.plan(chip)
    assert core.dispatch is None and core.RR == 2
    core.commit()
    chip.ctrl.RUN = 1
    core.XV = 1
    core.mem[core.iaddr] = enc.encode(I())
    core.plan(chip)
    assert core.dispatch is None and core.RR == 2


def test_overrun_while_running_and_while_ready():
    chip = beat_chip(inc=1, mod=2)                        # beats in cycles 1, 3, 5, ...
    load(chip, [I(), I(), I(), I(), I(pause=True, jmode="always", imm=0)])
    step(chip, 3)                                         # cycles 0..2
    assert chip.eng[0].OVR == 0
    step(chip, 1)                                         # cycle 3: beat while the engine runs
    assert chip.eng[0].OVR == 1
    chip = beat_chip(inc=1, mod=2)
    ctrl(chip, "RUN", 0)                                  # never dispatched: READY stays up
    step(chip, 3)
    assert chip.eng[0].READY == 1 and chip.eng[0].OVR == 0
    step(chip, 1)
    assert chip.eng[0].OVR == 1


def test_stat_register_and_w1c():
    chip = Chip()
    chip.eng[2].LATE = chip.eng[2].OVR = chip.eng[2].ARMED = 1
    a = m.HOST_MAP["ENG_BASE"] + 2 * 0x20 + 0x0D
    assert chip.backdoor_read(a) == 0b110100
    chip.backdoor_write(a, bytes([0x10]))
    assert chip.backdoor_read(a) == 0b100100
    chip.backdoor_write(a, bytes([0x20]))
    assert chip.backdoor_read(a) == 0b000100


def tap_chip():
    # MOD 10, INC 1, tap 0 at phase 2: cycle k has PH = k mod 10 -> tap in cycle 1, beat in cycle 9
    return beat_chip(inc=1, mod=10, trig="BG0.TAP0", taps=(2, DIS, DIS))


def test_commit_write_through_on_time():
    chip = tap_chip()
    load(chip, [I()] * 6 + [I(("IMM", "E.SYM"), imm=2, pause=True, jmode="always")])   # executes in cycle 9
    e = chip.eng[0]
    step(chip, 9)                                         # cycles 0..8
    assert e.COMMITTED == 0 and e.ARMED == 1
    step(chip, 1)                                         # cycle 9: the SYM move executes in the beat cycle
    assert chip.bg[0].beat == 1
    assert (e.COMMITTED, e.STAGED, e.LATE, e.ARMED) == (2, 2, 0, 0)


def test_late_symbol_write():
    chip = tap_chip()
    load(chip, [I()] * 7 + [I(("IMM", "E.SYM"), imm=2, pause=True, jmode="always")])   # executes in cycle 10
    e = chip.eng[0]
    step(chip, 11)                                        # through cycle 10
    assert (e.LATE, e.STAGED, e.COMMITTED, e.ARMED) == (1, 2, 0, 0)
    step(chip, 9)                                         # through cycle 19: the next beat commits the staged symbol
    assert e.COMMITTED == 2


def test_stop_disables_after_burst():
    chip = Chip()
    oneshot(chip, [I(("ZERO", "E.STOP")), I(pause=True)])
    assert chip.eng[0].EN == 0


def test_trigger_wins_over_beat_clear_of_armed():
    chip = beat_chip(inc=1, mod=6)                        # trigger on every beat: ARMED stays set
    load(chip, [I(pause=True, jmode="always", imm=0)])
    to_beat(chip)
    assert chip.eng[0].ARMED == 1
    to_beat(chip)
    assert chip.eng[0].ARMED == 1


def test_watchers_priority_and_default():
    def run(flags):
        chip = Chip()
        chip.flags.F = flags
        load(chip, [I(("IMM", "R0"), imm=1, pause=True)], at=0x10)
        load(chip, [I(("IMM", "R0"), imm=2, pause=True)], at=0x20)
        load(chip, [I(("IMM", "R0"), imm=3, pause=True)], at=0x30)
        eng_cfg(chip, 0, W0C=m.GUARD_ID["F3"], W0H=0x20, W1C=m.GUARD_ID["F4"], W1H=0x30)
        eng_cfg(chip, 0, PC=0x10, CFG=1)
        ctrl(chip, "RUN", 1)
        chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, b"\x01")
        step(chip, 4)
        return chip.acc.R[0]
    assert run(0) == 1
    assert run(1 << 4) == 3
    assert run(1 << 3) == 2
    assert run((1 << 3) | (1 << 4)) == 2


def test_run_global_gates_dispatch():
    chip = Chip()
    load(chip, [I(("IMM", "R0"), imm=9, pause=True)])
    eng_cfg(chip, 0, CFG=1)
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, b"\x01")
    step(chip, 5)
    assert chip.eng[0].READY == 1 and chip.acc.R[0] == 0
    ctrl(chip, "RUN", 1)
    step(chip, 3)
    assert chip.acc.R[0] == 9


def test_guarded_moves_and_conditional_jump():
    chip = Chip()
    chip.flags.F = 0b100                                  # F2 true
    n = oneshot(chip, [
        I(("IMM", "R0", "if"), ("IMM", "R1", "ifnot"), ("IMM", "R2", "never"), cond="F2", imm=3, jmode="if"),
        I(("IMM", "R3"), imm=99, pause=True),            # skipped by the jump
        I(),
        I(("IMM", "R3"), imm=7, pause=True)])
    assert chip.acc.R == [3, 0, 0, 7]                     # imm doubles as the IMM source and the jump target
    assert n == 3


def first_ready(trig, seq):
    chip = Chip()
    eng_cfg(chip, 0, TRIG=m.TRIG_ID[trig], CFG=1, PINS=0x00)      # PINA = P0 (uio_in[0])
    for i, v in enumerate(seq):
        chip.step(IDLE, v)
        if chip.eng[0].READY:
            return i
    return None


def test_pin_triggers():
    rise = [0, 0, 0, 1, 1, 1, 1, 1]
    fall = [1, 1, 1, 0, 0, 0, 0, 0]
    # raw change in cycle 3 -> s1 (3), s2 (4), edge evaluated in cycle 5 -> READY visible after step 5
    assert first_ready("PINA.RISE", rise) == 5
    assert first_ready("PINA.FALL", fall) == 5
    assert first_ready("PINA.EDGE", rise) == 5
    assert first_ready("PINA.FALL", [0, 0, 0] + [1] * 5) is None
    assert first_ready("PINA.RISE", [0, 0, 1, 0, 0, 0, 0, 0]) == 4


def test_flag_inv_always_doorbell_triggers():
    chip = Chip()
    eng_cfg(chip, 0, TRIG=m.TRIG_ID["FLAG0.RISE"], CFG=1)
    step(chip, 2)
    assert chip.eng[0].READY == 0
    chip.flags.F = 1
    step(chip, 1)
    assert chip.eng[0].READY == 1
    chip = Chip()
    eng_cfg(chip, 0, TRIG=m.TRIG_ID["HOST.INV"], CFG=1)
    step(chip, 2)
    assert chip.eng[0].READY == 0
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 4, b"\x55")
    step(chip, 1)
    assert chip.eng[0].READY == 1
    chip = Chip()
    eng_cfg(chip, 0, TRIG=m.TRIG_ID["ALWAYS"], CFG=1)
    step(chip, 1)
    assert chip.eng[0].READY == 1
    chip = Chip()                                         # doorbell needs EN
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, b"\x01")
    assert chip.eng[0].READY == 0
