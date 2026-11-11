from helpers import *     # noqa: F401,F403


def arm(chip, insns):
    """Load a burst and make it READY without stepping: cycle 0 dispatch, cycle 1 first instruction."""
    load(chip, insns)
    eng_cfg(chip, 0, CFG=1)
    ctrl(chip, "RUN", 1)
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, b"\x01")


def test_pointer_fetch_timing():
    chip = Chip()
    chip.mem.data[0x10] = 0xAB
    arm(chip, [I(("IMM", "P0.AL"), imm=0x10), I(), I(), I(), I(pause=True)])
    p = chip.mem.ptrs[0]
    step(chip, 1)                                         # cycle 0: dispatch
    step(chip, 1)                                         # cycle 1: AL executes
    assert (p.PTR, p.req, p.RDY) == (0x10, ("F",), 0)
    step(chip, 1)                                         # cycle 2: served (fetch reads mem[PTR])
    assert (p.req, p.pipe, p.RDY) == (None, 0xAB, 0)
    step(chip, 1)                                         # cycle 3: D loaded at the end of t+1
    assert (p.D, p.RDY) == (0xAB, 1)


def test_pointer_write_and_autoincrement_without_hazard():
    chip = Chip()
    arm(chip, [I(("IMM", "P0.AL"), imm=0x20), I(("IMM", "P0.W"), imm=0x77), I(("IMM", "P0.W"), imm=0x88), I(), I(pause=True)])
    step(chip, 3)                                         # cycles 0..2
    assert chip.mem.ptrs[0].PTR == 0x21
    step(chip, 1)                                         # cycle 3: first write served
    assert chip.mem.data[0x20] == 0x77
    step(chip, 1)
    assert chip.mem.data[0x21] == 0x88 and chip.mem.ptrs[0].PTR == 0x22
    assert chip.ctrl.MEMHAZ == 0                          # a request served in the cycle a new one is issued is not a hazard


def test_pointer_ah_and_r():
    chip = Chip()
    chip.mem.data[0x305] = 0x5C
    chip.mem.data[0x306] = 0x6D
    arm(chip, [I(("IMM", "P0.AL"), ("IMM", "P1.AH"), imm=0x05), I(("IMM", "P0.AH"), imm=3), I(), I(), I(("IMM", "P0.R"), imm=0), I(), I(), I(pause=True)])
    step(chip, 8)
    p = chip.mem.ptrs[0]
    assert p.PTR == 0x306 and chip.mem.ptrs[1].PTR == 0x500
    step(chip, 4)
    assert (p.D, p.RDY) == (0x6D, 1)


def test_arbiter_priority_and_memhaz_on_overwrite():
    chip = Chip()
    chip.mem.data[1] = 0x11
    chip.mem.data[2] = 0x22
    arm(chip, [I(("IMM", "P0.AL"), ("IMM", "P1.AL"), imm=1), I(), I(), I(), I(pause=True)])
    step(chip, 2)                                         # cycles 0,1
    assert chip.mem.ptrs[0].req and chip.mem.ptrs[1].req
    step(chip, 1)                                         # cycle 2: P0 served, P1 waits
    assert chip.mem.ptrs[0].req is None and chip.mem.ptrs[1].req == ("F",)
    step(chip, 1)                                         # cycle 3: P1 served; P0.D lands
    assert chip.mem.ptrs[1].req is None and chip.mem.ptrs[0].D == 0x11
    assert chip.ctrl.MEMHAZ == 0
    chip = Chip()
    arm(chip, [I(("IMM", "P0.AL"), ("IMM", "P1.AL"), imm=1), I(("ZERO", "P1.R")), I(), I(pause=True)])
    step(chip, 3)
    assert chip.ctrl.MEMHAZ == 1                          # P1 request overwritten while P0 held the memory


def test_memhaz_on_reading_stale_pd():
    chip = Chip()
    chip.mem.ptrs[0].D = 0x42
    oneshot(chip, [I(("P0.D", "R0"), pause=True)])
    assert chip.acc.R[0] == 0x42 and chip.ctrl.MEMHAZ == 1
    chip = Chip()
    chip.mem.ptrs[0].D = 0x42
    chip.mem.ptrs[0].RDY = 1
    oneshot(chip, [I(("P0.D", "R0"), pause=True)])
    assert chip.acc.R[0] == 0x42 and chip.ctrl.MEMHAZ == 0


def test_host_has_lowest_priority():
    chip = Chip()
    chip.mem.ptrs[0].req = ("F",)
    chip.mem.host_req = ("W", 5, 0x99)
    step(chip, 1)
    assert chip.mem.data[5] == 0 and chip.mem.host_req is not None
    step(chip, 1)
    assert chip.mem.data[5] == 0x99


def test_stale_landing_does_not_set_rdy():
    """SPEC 9a.3: P0.AL at t, P0.AH at t+1 (the AL fetch is served at t+1 with the old high byte). That landing
    must not raise RDY; only the AH fetch's landing does, with the byte from the new address."""
    chip = Chip()
    chip.mem.data[0x010] = 0xAA          # old high byte 0, new low byte
    chip.mem.data[0x310] = 0xBB          # final address
    arm(chip, [I(("IMM", "P0.AL"), imm=0x10), I(("IMM", "P0.AH"), imm=3), I(), I(), I(), I(pause=True)])
    p = chip.mem.ptrs[0]
    step(chip, 2)                        # cycle 0 dispatch, cycle 1 AL
    step(chip, 1)                        # cycle 2: AL fetch served (reads 0x010), AH executes
    assert p.pipe == 0xAA and p.PTR == 0x310
    step(chip, 1)                        # cycle 3: stale landing; AH fetch served
    assert (p.D, p.RDY) == (0xAA, 0)
    step(chip, 1)                        # cycle 4: AH landing
    assert (p.D, p.RDY) == (0xBB, 1)
    assert chip.ctrl.MEMHAZ == 0
