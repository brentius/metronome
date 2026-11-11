from helpers import *     # noqa: F401,F403
from metronome import spi

CB = m.HOST_MAP["CTRL_BASE"]


def test_spi_register_roundtrip():
    chip = Chip()
    bgb = m.HOST_MAP["BG_BASE"] + 0x20 * 2
    spi.spi_write(chip, bgb, bytes([6, 0, 0x25, 0x0C, 1, 2, 3, 4]))
    assert chip.bg[2].INC == 6 and chip.bg[2].MOD == 3109 and chip.bg[2].T0 == 0x0201
    assert spi.spi_read(chip, bgb, 8) == [0] * 8                 # D14: configuration is write-only
    spi.spi_write(chip, bgb + 0x12, bytes([0b1111, 0x2B]))
    assert spi.spi_read(chip, bgb + 0x12, 2) == [0b1111, 0]      # CTL readable, EDGE write-only
    assert (chip.bg[2].EDGE_PIN, chip.bg[2].EDGE_POL) == (0xB, 2)
    ob = m.HOST_MAP["OUT_BASE"] + 8 * 3
    spi.spi_write(chip, ob, bytes([5, 0, 0xCD, 0xAB, 0x34, 0x12]))
    assert spi.spi_read(chip, ob, 6) == [0] * 6
    assert (chip.out[3].ENG, chip.out[3].LUT, chip.out[3].OE) == (5, 0xABCD, 0x1234)
    ub = m.HOST_MAP["UNIT_BASE"] + 8
    spi.spi_write(chip, ub, bytes([0x20, 0x83, 0xB8, 0xED]))
    assert chip.lf[1].POLY == 0xEDB88320
    assert spi.spi_read(chip, CB + 7, 1) == [0xA0 | m.VERSION]
    assert spi.spi_read(chip, 0x3000, 2) == [0, 0]        # unmapped


def test_engine_registers_mask_and_cfg():
    chip = Chip()
    eb = m.HOST_MAP["ENG_BASE"] + 0x20 * 4
    spi.spi_write(chip, eb + 1, bytes([0xFF, 0xFF, 0xA7]))      # CFG, TRIG (5 bit), PINS
    assert chip.eng[4].EN == 1 and chip.eng[4].CORE == 1 and chip.eng[4].BG == 3
    assert spi.spi_read(chip, eb + 1, 3) == [0, 0, 0]            # D14: write-only
    assert (chip.eng[4].TRIG, chip.eng[4].PINA, chip.eng[4].PINB) == (0x1F, 7, 0xA)
    spi.spi_write(chip, eb + 8, bytes([0xFF]))
    assert chip.eng[4].W0C == 0x3F                               # W0C is 6 bits


def test_miso_idle_low_and_no_spurious_write_on_bad_command():
    chip = Chip()
    fr = spi._bytes_frames([0x05, 0x20, 0x00, 0x77], 8)         # unknown command: whole transaction ignored
    outs = chip.run(fr)
    assert all(o[0] & 1 == 0 for o in outs)
    assert chip.bg[0].INC == 0


def test_program_memory_byte_lanes():
    chip = Chip()
    data = bytes(range(1, 9))
    spi.spi_write(chip, 0x0800 + 3 * 8, data[:7])
    assert chip.cores[1].mem[3] == int.from_bytes(data[:7], "little")   # each byte lands in its lane at once
    spi.spi_write(chip, 0x0800 + 3 * 8 + 7, data[7:])
    assert chip.cores[1].mem[3] == int.from_bytes(data[:7] + data[7:], "little")
    assert spi.spi_read(chip, 0x0800 + 3 * 8, 4) == [0, 0, 0, 0]       # program memory reads 0


def test_data_ram_spi_and_backdoor():
    chip = Chip()
    spi.spi_write(chip, 0x1000 + 0x40, bytes([9, 8, 7, 6]))
    assert list(chip.mem.data[0x40:0x44]) == [9, 8, 7, 6]
    assert spi.spi_read(chip, 0x1000 + 0x40, 4) == [9, 8, 7, 6]
    chip.backdoor_write(0x1000 + 0x7FF, b"\x5A")
    assert chip.backdoor_read(0x1000 + 0x7FF) == 0x5A


def test_data_ram_read_contends_with_core_pointer():
    chip = Chip()
    chip.mem.data[0x10] = 0x31
    chip.mem.data[0x11] = 0x32
    for _ in range(5):
        chip.mem.ptrs[0].req = ("F",)                     # P0 keeps the memory busy for a while; host waits
        chip.step(IDLE, 0)
    chip.mem.host_req = ("R", 0x10)
    chip.step(IDLE, 0)
    assert chip.mem.hpipe == 0x31 and chip.mem.host_req is None


def test_mailbox_irq_and_read_ahead():
    chip = Chip()
    ctrl(chip, "IRQEN", 1)
    oneshot(chip, [I(("IMM", "HOST.OUT"), imm=0x5A, pause=True)])
    assert (chip.host.OUTV, chip.host.OUTB) == (1, 0x5A)
    assert chip.step(IDLE, 0)[0] & 2                      # IRQ is a register: high one cycle after OUTV
    assert spi.spi_read(chip, CB + 6, 1) == [0b10]        # HOSTSTAT
    assert spi.spi_read(chip, CB + 5, 1) == [0x5A]        # HOSTOUT read has no side effect (SPEC 9, D11)
    assert chip.host.OUTV == 1
    spi.spi_read(chip, CB + 4, 1)                         # read-ahead into HOSTOUT must not clear OUTV either
    assert chip.host.OUTV == 1
    spi.spi_write(chip, CB + 6, b"")                 # acknowledge: HOSTSTAT bit 1 is write-1-to-clear
    assert chip.host.OUTV == 0
    chip.step(IDLE, 0)
    assert not chip.step(IDLE, 0)[0] & 2


def test_hostin_and_doorbell_over_spi():
    chip = Chip()
    spi.spi_write(chip, CB + 4, b"\xC7")
    assert (chip.host.INV, chip.host.INB) == (1, 0xC7)
    oneshot(chip, [I(("HOST.IN", "R2"), pause=True)])
    assert chip.acc.R[2] == 0xC7 and chip.host.INV == 0
    chip = Chip()
    eng_cfg(chip, 3, CFG=1)
    fr = spi.write_frames(CB + 3, b"\x08")
    seen = None
    for i, f in enumerate(fr):
        chip.step(f, 0)
        if chip.eng[3].READY and seen is None:
            seen = i
    assert seen is not None and chip.eng[3].OVR == 0


def test_err_irq_and_sticky():
    chip = Chip()
    ctrl(chip, "IRQEN", 2)
    chip.ctrl.MEMHAZ = 1
    chip.step(IDLE, 0)
    assert chip.step(IDLE, 0)[0] & 2


def test_reset_clears_registers_keeps_memories():
    chip = Chip()
    bg_cfg(chip, 0, INC=5, MOD=9, CTL=1)
    load(chip, [I(("IMM", "R0"), imm=3, pause=True)])
    chip.mem.data[7] = 7
    chip.acc.R[1] = 4
    step(chip, 3)
    uo = chip.step(IDLE, 0, rst_n=0)
    assert uo == (0, 0, 0)
    assert chip.bg[0].INC == 0 and chip.bg[0].RUN == 0 and chip.acc.R[1] == 0 and chip.pins.s1 == 0
    assert chip.cores[0].mem[0] != 0 and chip.mem.data[7] == 7


def test_end_to_end_toggle_output_each_beat():
    chip = Chip()
    DIS = 0xFFFF
    bg_cfg(chip, 0, INC=1, MOD=8, T0=DIS, T1=DIS, T2=DIS, CTL=1)        # beats at cycles 7, 15, ...; seg = 0
    eng_cfg(chip, 0, TRIG=m.TRIG_ID["BG0.BEAT"], CFG=1)
    out_cfg(chip, 0, ENG=0, LUT=0b0010, OE=0xFFFF)                       # idx = committed symbol; sym 1 -> pin high
    out_cfg(chip, 9, ENG=0, LUT=0b0100, OE=0)                            # O9 = uo_out[3] high when symbol == 2
    load(chip, [
        I(("IMM", "ACC.XOR"), imm=1),
        I(("ACC", "E.SYM"), pause=True, jmode="always", imm=0),
    ])
    ctrl(chip, "RUN", 1)
    wave = []
    for s in range(70):
        uo, uio, oe = chip.step(IDLE, 0)
        wave.append((uio & 1, oe & 1, (uo >> 3) & 1))
    # independent expectation: beat k in cycle 7+8k; burst of beat k writes sym (k even: 1, k odd: 0) committed at beat k+1;
    # OUT visible after step s reflects the symbol committed by beats in cycles <= s-1.
    expect = []
    for s in range(70):
        nbeats = len([b for b in range(7, s, 8)])                        # beats in cycles 7, 15, ... <= s-1
        sym = 0 if nbeats <= 1 else (1 if (nbeats - 1) % 2 == 1 else 0)  # committed after beat j (j>=1): j odd -> 1
        expect.append((1 if sym == 1 else 0, 1 if sym else 0, 0))
    # OE table is 0xFFFF for all idx; OUT[0] = LUT[sym]; OE always 1
    expect = [(o, 1, 0) for (o, _, _) in expect]
    assert wave == expect
    assert chip.ctrl.CONFLICT == chip.ctrl.MEMHAZ == 0 and chip.eng[0].OVR == chip.eng[0].LATE == 0
    assert any(w[0] for w in wave) and not all(w[0] for w in wave)


def test_output_enable_and_seg_index():
    chip = Chip()
    bg_cfg(chip, 0, INC=1, MOD=20, T0=5, T1=10, T2=15, CTL=1)
    out_cfg(chip, 1, ENG=0, LUT=0b1010_0110_0011_1100, OE=0b0000_1111_0000_0000)
    seen = {}
    for s in range(40):
        uo, uio, oe = chip.step(IDLE, 0)
        seen[chip.cycle - 1] = (chip.bg[0].seg, (uio >> 1) & 1, (oe >> 1) & 1)
    # symbol is always 0, so idx = seg << 2; LUT bit for seg s: bits 0,4,8,12 ; OE likewise
    lut = 0b1010_0110_0011_1100
    oe = 0b0000_1111_0000_0000
    for c in range(1, 40):
        seg_prev = seen[c - 1][0]
        assert seen[c - 1][1] == (lut >> (seg_prev << 2)) & 1
        assert seen[c - 1][2] == (oe >> (seg_prev << 2)) & 1
    assert {v[0] for v in seen.values()} == {0, 1, 2, 3}


def test_unbound_output_cell_uses_idx_zero():
    chip = Chip()
    out_cfg(chip, 2, ENG=7, LUT=0b0001, OE=0b0001)
    chip.eng[0].COMMITTED = 3
    assert chip.step(IDLE, 0)[1] >> 2 & 1 == 1
