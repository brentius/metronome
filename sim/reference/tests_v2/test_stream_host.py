"""SPEC v2 6.2-6.3 (data RAM, streams), 8 (output pins) and 9 (host link, host map)."""
from helpers_v2 import *     # noqa: F401,F403
from metronome2 import spi

I = asm.insn
HM = m.HOST_MAP


def rewind(chip, k):
    blk(chip, "SRT", k, CTL=1)


def tx_bits(data, msb):
    return [(b >> (7 - i if msb else i)) & 1 for b in data for i in range(8)]


def stream_tx(chip, k, data, start, msb, gap):
    """Advance stream k directly (as a move would) every `gap` cycles; return (bits, starved)."""
    for i, b in enumerate(data):
        chip.mem.data[(start + i) % m.DATA_BYTES] = b
    blk(chip, "STREAM", k, MODE=msb << 1, START=start, LEN=len(data), MARK=2)
    rewind(chip, k)
    s = chip.mem.streams[k]
    steps(chip, 8)
    bits, marks = [], []
    while not s.END:
        bits.append(s.BIT)
        marks.append(s.G_MARK)
        g = chip.mem.served == ("S", k)
        # one advance, then idle cycles; the model's per-cycle path is exercised through Chip.step
        chip.mem.arbitrate()
        s.commit(chip.mem.served == ("S", k), chip.mem.word(s.BA) if chip.mem.served == ("S", k) else 0, True,
                 None, None)
        for _ in range(gap - 1):
            chip.step(IDLE)
    return bits, marks, s.STARVED


def test_stream_transmit_lsb_and_msb_first_without_starving():
    for msb in (0, 1):
        for start in (5, 6, 0x7FC):
            for gap in (6, 2):
                chip = Chip()
                data = [0xA5, 0x3C, 0x01, 0x80, 0xFF]
                bits, marks, starved = stream_tx(chip, 0, data, start, msb, gap)
                assert bits == tx_bits(data, msb), (msb, start, gap)
                assert starved == 0
                assert marks.index(1) == 16


def program_tx(chip, data, msb=0):
    """Line 0 at 6 cycles per bit; thread 0 on core 0: S0.BIT -> L.DBIT, advance; O0 shows symbol bit 0."""
    chip.mem.data[0:len(data)] = bytes(data)
    blk(chip, "STREAM", 0, MODE=msb << 1, START=0, LEN=len(data))
    rewind(chip, 0)
    blk(chip, "LINE", 0, INC=1, MOD=6, T0=0, T1=3, T2=0xFFFF)
    blk(chip, "OUT", 0, BIND=0b100, SEL=0, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)
    chip.load_program(0, [I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1, jmode="always", imm=0)])
    thread(chip, 0, core=0, line=0, trig="L0.BEAT")
    blk(chip, "CTRL", RUN=1)


def test_ethernet_rate_transmit_and_receive_in_loopback_on_two_cores():
    """10 Mbit at 60 MHz: one bit per 6 cycles, TX on core 0, RX on core 1, O0 looped to P0."""
    chip = Chip()
    data = [0x55, 0xD5, 0x12, 0xF0, 0x0F, 0xC3]
    program_tx(chip, data)
    nrx = len(data) + 1
    blk(chip, "STREAM", 1, MODE=1, START=0x400, LEN=nrx)
    rewind(chip, 1)
    blk(chip, "LINE", 1, INC=1, MOD=6, T0=5, T1=0xFFFF, T2=0xFFFF, PINS=0, SNAP=0, LUT0=lut(lambda i: i & 1))
    chip.load_program(1, [I(("L.IN", "S1.RX"), pause=1, jmode="always", imm=0)])
    thread(chip, 1, core=1, line=1, trig="L1.TAP0")
    chip.backdoor_write(HM["LRT_BASE"] + 2, b"\x01")
    chip.backdoor_write(HM["LRT_BASE"] + 8 + 2, b"\x01")       # both lines start in the same cycle
    uio = 0
    for _ in range(6 * 8 * nrx + 40):
        _, uio_out, _ = chip.step(IDLE, uio)
        uio = uio_out & 1
    bits = [0, 0] + tx_bits(data, 0) + [0] * 8                  # two taps sample the idle symbol first
    expect = bytes(sum(bits[8 * j + i] << i for i in range(8)) for j in range(nrx))
    assert bytes(chip.mem.data[0x400:0x400 + nrx]) == expect
    assert chip.mem.streams[1].POS == nrx
    assert [t.LATE for t in chip.threads] == [0] * 6 and [t.OVR for t in chip.threads] == [0] * 6
    assert [s.STARVED for s in chip.mem.streams] == [0, 0] and chip.ctrl.CONFLICT == 0
    assert all(ln.TAPMISS == 0 for ln in chip.lines)


def test_receive_flush_partial_byte_and_starve_on_early_advance():
    chip = Chip()
    s = chip.mem.streams[0]
    blk(chip, "STREAM", 0, MODE=1, START=0x10, LEN=8)
    rewind(chip, 0)
    chip.mem.data[0x10:0x14] = b"\xEE\xEE\xEE\xEE"
    for b in tx_bits([0x5A], 0) + [1, 0, 1]:
        s.commit(False, 0, False, b, None)              # as an S0.RX move would
        chip.step(IDLE)                                 # lets the arbiter serve the pending byte
    s.commit(False, 0, False, None, 2)                  # flush the 3-bit tail
    steps(chip, 6)
    assert bytes(chip.mem.data[0x10:0x13]) == b"\x5A\x05\xEE" and s.POS == 2 and s.STARVED == 0
    chip2 = Chip()
    blk(chip2, "STREAM", 0, MODE=0, START=0, LEN=4)
    rewind(chip2, 0)
    chip2.mem.streams[0].commit(False, 0, True, None, None)    # advance before the first byte arrives
    assert chip2.mem.streams[0].STARVED == 1
    blk(chip2, "SRT", 0, CTL=0x80)
    assert chip2.mem.streams[0].STARVED == 0


def test_output_pin_table_index_and_oe():
    chip = Chip()
    ln = chip.lines[2]
    ln.COMMITTED = 0b0110
    ln.FIRED = 0b011                                   # SEG = 2
    blk(chip, "OUT", 3, BIND=0b100 | 2, SEL=(1 << 0) | (2 << 2) | (3 << 4), LUT=1 << ((2 << 3) | 0b011),
        OE=1 << ((2 << 3) | 0b011))
    chip.step(IDLE)
    o = chip.out[3]
    assert (o.OUT, o.OEN) == (1, 1)
    _, uio_out, uio_oe = chip.outputs()
    assert uio_out == 0b1000 and uio_oe == 0b1000


# ------------------------------------------------------------------------------------------------ host link
def test_spi_id_data_ram_and_write_only_config():
    chip = Chip()
    steps(chip, 4)
    assert spi.spi_read(chip, HM["CTRL_BASE"] + 7, 1) == [0xA2]
    spi.spi_write(chip, HM["DATA_BASE"] + 0x123, [1, 2, 3, 4, 5])
    steps(chip, 4)
    assert bytes(chip.mem.data[0x123:0x128]) == bytes([1, 2, 3, 4, 5])
    assert spi.spi_read(chip, HM["DATA_BASE"] + 0x123, 5) == [1, 2, 3, 4, 5]
    spi.spi_write(chip, HM["LINE_BASE"] + 2, [0x34, 0x12])          # line 0 MOD
    steps(chip, 4)
    assert chip.lines[0].MOD == 0x1234
    assert spi.spi_read(chip, HM["LINE_BASE"] + 2, 2) == [0, 0]   # write-only, reads 0


def test_configuration_visible_two_cycles_after_the_write_strobe():
    chip = Chip()
    steps(chip, 4)
    frames = spi.write_frames(HM["LINE_BASE"] + 0x0A, [0x77])       # line 0 PRE
    w = None
    seen = []
    for f in frames:
        chip.step(f)
        if chip.host.wr_now is not None:
            w = chip.cycle - 1
        seen.append((chip.cycle, chip.lines[0].PRE))
    vis = min(c for c, v in seen if v == 0x77)       # PRE as seen at the start of cycle `vis`
    assert vis == w + 2


def test_program_load_by_byte_lane_and_doorbell():
    chip = Chip()
    steps(chip, 4)
    word = I(("IMM", "R3"), imm=0x5C, pause=1)
    spi.spi_write(chip, HM["PROG_BASE"] + 0x800 + 8 * 3, list(word.to_bytes(8, "little")))
    assert chip.cores[1].prog[3] == word
    spi.spi_write(chip, HM["THREAD_BASE"] + 8 * 2, [tcfg(core=1)])
    spi.spi_write(chip, HM["TRT_BASE"] + 2 * 2, [3, 0x08])          # PC 3, EN
    spi.spi_write(chip, HM["CTRL_BASE"], [1])
    spi.spi_write(chip, HM["CTRL_BASE"] + 3, [1 << 2])
    steps(chip, 10)
    assert chip.acc.R[3] == 0x5C


def test_host_reads_have_no_side_effects_and_mailbox():
    chip = Chip()
    chip.load_program(0, [I(("IMM", "HOST.OUT"), imm=0x42, pause=1)])
    thread(chip, 0)
    blk(chip, "CTRL", RUN=1, IRQEN=1, DOORBELL=1)
    steps(chip, 8)
    assert chip.host.OUTV == 1 and chip.host.IRQ == 1
    assert spi.spi_read(chip, HM["CTRL_BASE"] + 5, 3) == [0x42, 0x02, 0xA2]
    assert chip.host.OUTV == 1
    spi.spi_write(chip, HM["CTRL_BASE"] + 6, [0x02])
    steps(chip, 3)
    assert chip.host.OUTV == 0 and chip.host.IRQ == 0


def test_stream_advanced_every_cycle_by_a_program_never_starves():
    """SPEC 10.5 (calculated): a transmit stream advanced at most once per cycle does not starve."""
    for msb in (0, 1):
        for start in (0, 3):
            chip = Chip()
            data = [0x96, 0x0F, 0xF0, 0x81, 0x7E, 0x33]
            for i, b in enumerate(data):
                chip.mem.data[start + i] = b
            blk(chip, "STREAM", 0, MODE=msb << 1, START=start, LEN=len(data))
            rewind(chip, 0)
            steps(chip, 8)
            chip.load_program(0, [I(("ZERO", "S0.ADV"))] * (8 * len(data)) + [I(pause=1)])
            thread(chip, 0)
            blk(chip, "CTRL", RUN=1, DOORBELL=1)
            s, bits = chip.mem.streams[0], []
            for _ in range(8 * len(data) + 10):
                if chip.cores[0].XV and not s.END:
                    bits.append(s.BIT)
                chip.step(IDLE)
            assert bits == tx_bits(data, msb) and s.STARVED == 0 and s.END


def test_reset_clears_configuration_and_releases_two_cycles_later():
    chip = Chip()
    blk(chip, "LINE", 1, MOD=99)
    chip.mem.data[5] = 7
    chip.step(IDLE, rst_n=0)
    assert chip.lines[1].MOD == 0 and chip.mem.data[5] == 7
    blk(chip, "CTRL", RUN=1)
    chip.step(IDLE)
    chip.step(IDLE)                       # rst_q still low for two cycles after rst_n rises
    assert chip.ctrl.RUN == 0
    blk(chip, "CTRL", RUN=1)
    chip.step(IDLE)
    assert chip.ctrl.RUN == 1
