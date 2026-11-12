"""Assemble the examples and run them on the v2 cycle-level model; check the pin traces.

Evidence class: model simulation (the model and the tools share SPEC v2 and an author; this checks the toolchain end
to end, not the silicon)."""
from common import *
from metronome2_tools.check import check

HM = m.HOST_MAP
UART_BIT = 3125 / 6          # cycles per bit at 115200 baud, 60 MHz


def test_examples_pass_the_static_check():
    for name in ("uart_tx", "eth_tx", "spi_target"):
        rep = check(example(name))
        assert rep.ok, (name, rep.format(True))
        assert not rep.warnings, (name, rep.warnings)


def test_uart_tx_frames_on_O8():
    chip = Chip()
    load(chip, example("uart_tx"))
    pin = lambda uo, a, b: (uo >> 2) & 1
    tr = pin_trace(chip, 3, pin)
    assert tr[-1] == 1                                              # idles high once the table is written
    sent = [0xA5, 0x3C]
    for byte in sent:
        chip.backdoor_write(HM["CTRL_BASE"] + 4, bytes([byte]))
        tr += pin_trace(chip, 6000, pin)
    falls = [i for i in range(1, len(tr)) if tr[i - 1] == 1 and tr[i] == 0]
    start0 = falls[0]
    start1 = next(i for i in falls if i > start0 + 9 * UART_BIT)
    got = []
    for s0 in (start0, start1):
        bits = [tr[int(s0 + (i + 0.5) * UART_BIT)] for i in range(10)]
        assert bits[0] == 0 and bits[9] == 1, bits                  # start and stop bits
        got.append(sum(bits[1 + i] << i for i in range(8)))
    assert got == sent
    for lvl, s, n in runs(tr[start0:start0 + int(9 * UART_BIT)])[:-1]:   # every run is whole bit times, +-2 cycles
        assert abs(n - round(n / UART_BIT) * UART_BIT) <= 2, (s, n)
    assert [t.LATE for t in chip.threads] == [0] * 6 and [t.OVR for t in chip.threads] == [0] * 6
    assert chip.ctrl.CONFLICT == 0 and all(ln.TAPMISS == 0 for ln in chip.lines)


def test_ethernet_rate_manchester_tx_on_O0():
    chip = Chip()
    load(chip, example("eth_tx"))
    data = [0x55] * 7 + [0xD5]
    tr = pin_trace(chip, 6 * 72 + 30, lambda uo, a, b: a & 1)
    cells = 66                                                      # two leading cells (before and at the first beat), then 64 data bits
    ok = []
    for off in range(6):                                            # the unique alignment where every cell is valid
        halves = [(tr[off + 6 * i + 1], tr[off + 6 * i + 4]) for i in range(cells)]
        steady = all(len(set(tr[off + 6 * i:off + 6 * i + 3])) == 1 and len(set(tr[off + 6 * i + 3:off + 6 * i + 6])) == 1
                     for i in range(cells))
        if steady and all(a != b for a, b in halves):
            ok.append((off, halves))
    assert len(ok) == 1, [o for o, _ in ok]
    bits = [a for a, _ in ok[0][1]]                                 # the first half of a cell shows the bit
    want = [0, 0] + [(b >> i) & 1 for b in data for i in range(8)]  # two dummy cells, then data LSB first
    assert bits == want
    assert chip.threads[0].EN == 0                                  # stopped itself at the end of the stream
    assert chip.threads[0].LATE == 0 and chip.threads[0].OVR == 0 and chip.lines[0].TAPMISS == 0
    assert chip.mem.streams[0].STARVED == 0 and chip.ctrl.CONFLICT == 0


def spi_session(half, mosi_bytes):
    """Mode-1 controller against the spi_target example.  SCK = P0, MOSI = P1, MISO = O8 (uo_out[2]); MOSI changes on
    the SCK rise, MISO is sampled just before the fall.  Returns (chip, sampled MISO bits)."""
    chip = Chip()
    load(chip, example("spi_target"))
    for _ in range(12):                                             # the stream prefetches its first byte (SPI is slower)
        chip.step(IDLE, 0)
    chip.backdoor_write(HM["CTRL_BASE"] + 3, b"\x01")               # doorbell thread 0: stage the first MISO bit
    for _ in range(30):
        chip.step(IDLE, 0)
    miso = []
    chip.first_tapmiss = None
    for bit in [(b >> (7 - i)) & 1 for b in mosi_bytes for i in range(8)]:
        for _ in range(half):
            uo, _, _ = chip.step(IDLE, 1 | (bit << 1))
        miso.append((uo >> 2) & 1)
        if chip.first_tapmiss is None:                              # the first boundary has no earlier tap-0 edge:
            chip.first_tapmiss = chip.lines[0].TAPMISS              # exempt since D28 (SPEC v2 3.4 FIRST)
        for _ in range(half):
            chip.step(IDLE, bit << 1)
    for _ in range(40):
        chip.step(IDLE, 0)
    return chip, miso


def test_spi_target_follower_mode1_at_three_clock_rates():
    want = [(b >> (7 - i)) & 1 for b in (0xA5, 0x3C, 0xE1, 0x07) for i in range(8)]
    for half, mosi_bytes in ((10, [0x96, 0x4B, 0xF0, 0x0D]), (14, [0x12, 0x34, 0x56, 0x78]),
                             (19, [0xFF, 0x00, 0xAA, 0x55])):
        chip, miso = spi_session(half, mosi_bytes)
        assert miso == want, half
        assert bytes(chip.mem.data[0x100:0x104]) == bytes(mosi_bytes), half
        assert chip.mem.streams[1].POS == 4
        assert [t.LATE for t in chip.threads] == [0] * 6 and [t.OVR for t in chip.threads] == [0] * 6
        assert chip.first_tapmiss == 0 and chip.lines[0].TAPMISS == 0       # D28: none at all
        assert chip.ctrl.CONFLICT == 0
        assert not any(s.STARVED for s in chip.mem.streams)


def test_uart_tx_loaded_over_spi_has_no_consecutive_config_writes():
    """D24 evidence on the cycle-accurate link: load the whole UART image at clk/16 and inspect every cycle."""
    chip = Chip()
    prog = example("uart_tx")
    for _ in range(8):
        chip.step(IDLE)
    n, cfg_cycles = spi_load(chip, prog)
    assert len(cfg_cycles) > 20
    assert min(b - a for a, b in zip(cfg_cycles, cfg_cycles[1:])) >= 128      # 8 SCK periods of 16 cycles per byte
    ref = Chip()
    load(ref, prog)
    assert [bytes(l.cfg) for l in chip.lines] == [bytes(l.cfg) for l in ref.lines]
    assert [bytes(t.cfg) for t in chip.threads] == [bytes(t.cfg) for t in ref.threads]
    assert [bytes(o.cfg) for o in chip.out] == [bytes(o.cfg) for o in ref.out]
    assert chip.cores[0].prog[:8] == ref.cores[0].prog[:8]
    assert chip.ctrl.RUN == 1 and chip.threads[0].EN == 1 and chip.lines[0].RUN == 1
