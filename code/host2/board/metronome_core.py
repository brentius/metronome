"""Metronome host loader core: SPI host link for the tt_um_brentius_metronome host map.

Pure Python with no machine imports, no CPython-only syntax and no floating-point formatting, so the *same* file runs
under CPython (the board twin in `code/tests/board_twin/`) and under MicroPython on the RP2350 demo board
(`code/host2/board/ttboard_adapter.py`).  Everything that touches hardware is behind an "edge bus" protocol:

    the core is a generator.  It yields operations and the bus performs them:

        ("pins", sck, cs_n, mosi)   drive the three host-link input pins (1 = high)
        ("wait", cycles)            advance by `cycles` chip clock periods (float)
        ("sample",)                 yields back one MISO bit (0/1): uo_out[0] now
        ("reset_n", level)          drive the chip's rst_n pin (1 = out of reset)
        ("log", text)               optional progress note

The bus is free to implement `wait` as busy-wait microseconds (hardware) or as simulator time (the RTL twin).  The
core never reads a clock: all timing is expressed in chip clock cycles, and `clock_hz` is only used to convert for
the reader's benefit.

Protocol, quoted from `wiki/SPEC_V2.md` section 9 (the text, not this code, is the authority):

  * "SPI target, mode 0, MSB first."  "While CS_N is high: the byte state returns to the command byte, the bit count
    clears and `TX' = 0`. `MISO = TX[7]`."
  * "On each `SR`: `RX' = {RX[6:0], MOSI}` ... On the 1st..7th `SR` of a byte, `TX' = {TX[6:0], 0}`.  The 8th `SR`
    in cycle c completes the byte".
  * "Byte 0: command. `0x02` write, `0x03` read; any other value ignores the rest of the transaction."  "Byte 1:
    `ADDR[15:8]`. Byte 2: `ADDR[7:0]`" -- a 16-bit big-endian address.
  * "Write, bytes 3 onward: a host write of the byte to `ADDR` in cycle W = c+1; `ADDR' = ADDR + 1`".
  * "Read, bytes 3 onward: completing a data byte issues a read request at `ADDR` in cycle c+1."  "A register read
    issued in cycle R loads `TX` at the end of R+1" / a data RAM read "loads `TX` at the end of s+1", so the response
    to address A is on MISO during the byte *after* the one that requested it.  The first three MISO bytes of a read
    are therefore the command/address phase and carry no data; n dummy MOSI bytes return n data bytes.
  * "No host read has a side effect. Reads prefetch one address past the last byte the host clocks out."
  * "Keep SCK at or below clk/16 (3.75 MHz at 60 MHz)."  `Timing.period_cycles >= 16` and `MetronomeHost(enforce_spec=
    True)` (the default) refuses faster traffic.  The RTL twin sets `enforce_spec=False` on purpose to find where the
    link actually breaks.

Pins: MISO is `uo_out[0]`, IRQ is `uo_out[1]`; host inputs are `ui_in[0]`=SCK, `ui_in[1]`=CS_N, `ui_in[2]`=MOSI.

MicroPython compatibility is a static property here, not a measured one: no CPython-only syntax, no `json`, `time`,
`typing` or `dataclasses` imports, no f-strings, and no `%` format codes for floats (only `%d`/`%s`/`%r`/`%x` and
explicit `str()`/`round()`).  `code/tests/board_twin/test_core.py` enforces that by reading this file.  Nothing in
`code/host2/board/` has been run on an RP2350.

Evidence class: the frame layout and the high-level sequence are exercised against a spec-level fake target and
against the full-chip RTL in `code/tests/board_twin/` (RTL-simulated, not hardware-measured).
"""

CMD_WRITE = 0x02
CMD_READ = 0x03

HOST_MAP_ID = 0x2407            # CTRL.ID, reads 0xA0 | machine version
HOST_MAP_CTRL = 0x2400          # RUN, STICKY, IRQEN, DOORBELL, HOSTIN, HOSTOUT, HOSTSTAT, ID, ERRSUM
HOST_MAP_LRT = 0x2410           # line runtime, stride 0x08: PHASE (2), CTL, SYM, INS, STAT
HOST_MAP_TRT = 0x2440           # thread runtime, stride 0x02: PC, STAT
HOST_MAP_DATARAM = 0x1000       # 2 KB data RAM
HOST_DATARAM_BYTES = 0x800
IMAGE_FORMAT = "metronome-image"
IMAGE_MACHINE_VERSION = 2
ID_VALUE = 0xA2                 # 0xA0 | 2
SPEC_MIN_PERIOD_CYCLES = 16.0   # SCK <= clk/16


# ------------------------------------------------------------------------------------------------------------------
# operations (the edge bus protocol)


def op_pins(sck, cs_n, mosi):
    return ("pins", int(sck) & 1, int(cs_n) & 1, int(mosi) & 1)


def op_wait(cycles):
    return ("wait", float(cycles))


def op_sample():
    return ("sample",)


def op_reset_n(level):
    return ("reset_n", int(level) & 1)


def op_log(text):
    return ("log", text)


class Rng:
    """Tiny LCG: `random.Random` does not exist in MicroPython and the twin needs reproducibility."""

    def __init__(self, seed=1):
        self.state = (int(seed) * 2 + 1) & 0x7FFFFFFF or 0x1234567

    def _next(self):
        self.state = (self.state * 1103515245 + 12345) & 0x7FFFFFFF
        return self.state

    def uniform(self, lo, hi):
        return lo + (hi - lo) * (self._next() / 2147483648.0)


class Timing:
    """Host-link timing in chip clock cycles.

    period_cycles     full SCK period (SCK frequency = clock_hz / period_cycles).  >= 16 is the SPEC v2 9 limit.
    phase_cycles      phase, inside a chip clock period, at which the *first* SCK rising edge of every transaction
                      lands (exact: the CS_N-low wait is computed so that this holds for any period, and the
                      sub-cycle remainder is given back in the CS_N-high gap, so the chip-clock phase the next
                      transaction starts from is the same one this one started from).
    jitter_cycles     +/- uniform jitter added to every SCK half period (RP2350 GPIO scheduling jitter model).
    sample_lead_fraction  where MISO is sampled, as a fraction of the SCK half period *before* the rising edge
                      (0.25 = a quarter of the low phase before the edge).  The target updates TX two to three
                      chip clocks after the synchronised rising edge (SPEC v2 2, 9), so the value that belongs to
                      bit k must be sampled at or before the edge; mid-high sampling reads bit k+1.
    """

    def __init__(self, period_cycles=SPEC_MIN_PERIOD_CYCLES, phase_cycles=0.5, jitter_cycles=0.0, seed=1,
                 sample_lead_fraction=0.25, cs_setup_cycles=None, cs_gap_cycles=None, cs_hold_cycles=None):
        if period_cycles <= 0:
            raise ValueError("period_cycles must be positive")
        if not 0.0 <= phase_cycles < 1.0:
            raise ValueError("phase_cycles is a fraction of a clock period, 0 <= phase < 1")
        if jitter_cycles < 0:
            raise ValueError("jitter_cycles must be >= 0")
        if not 0.0 <= sample_lead_fraction < 1.0:
            raise ValueError("sample_lead_fraction is a fraction of the SCK half period, 0 <= lead < 1")
        self.period_cycles = float(period_cycles)
        self.phase_cycles = float(phase_cycles)
        self.jitter_cycles = float(jitter_cycles)
        self.seed = int(seed)
        self.sample_lead_fraction = float(sample_lead_fraction)
        # CS_N low before the first edge and between transactions: enough for the two-flop synchroniser (SPEC 2).
        self.cs_setup_cycles = max(8.0, 2.0 * self.period_cycles) if cs_setup_cycles is None else float(cs_setup_cycles)
        self.cs_gap_cycles = max(8.0, 2.0 * self.period_cycles) if cs_gap_cycles is None else float(cs_gap_cycles)
        self.cs_hold_cycles = max(4.0, 0.5 * self.period_cycles) if cs_hold_cycles is None else float(cs_hold_cycles)

    @property
    def half_cycles(self):
        return self.period_cycles / 2.0

    @property
    def sample_lead_cycles(self):
        return self.sample_lead_fraction * self.half_cycles

    @property
    def phase_setup_cycles(self):
        """CS_N-low wait that puts the first rising edge at `phase_cycles` of a chip clock period.

        The transaction begins with `cs_gap_cycles` of CS_N high, then CS_N falls, then this wait, then the first
        bit's low phase.  The first rising edge is `half_cycles` after the start of that low phase, so the wait has
        to absorb `phase - half - cs_gap` cycles modulo one: that is the only sub-cycle quantity in a transaction.
        """
        return self.cs_setup_cycles + ((self.phase_cycles - self.half_cycles - self.cs_gap_cycles) % 1.0)

    def phase_return(self, nbytes):
        """CS_N-high wait that makes a transaction of `nbytes` bytes a whole number of chip cycles.

        A transaction costs `cs_gap + phase_setup + 8*nbytes*period + cs_hold` plus this wait; `phase_setup` has
        already absorbed the sub-cycle part of `phase - half - cs_gap`, so the leftover is whatever fraction the rest
        of the transaction has (from `half`, and from a fractional `cs_hold`).  Returning it keeps the chip-clock
        phase the next transaction starts from equal to the one this transaction started from, which is what makes
        `phase_cycles` reproducible instead of accumulating.  With the jitter on, the phase legitimately walks.
        """
        total = (self.cs_gap_cycles + self.phase_setup_cycles + self.byte_cycles() * int(nbytes)
                 + self.cs_hold_cycles)
        return (-total) % 1.0

    def byte_cycles(self):
        """Chip cycles per completed SPI byte at this timing (D24 spacing argument, SPEC v2 1 and image.py)."""
        return 8.0 * self.period_cycles

    def sck_hz(self, clock_hz=60000000.0):
        return clock_hz / self.period_cycles

    def describe(self, clock_hz=60000000.0):
        # No %g/%e/%f: only integer/str formatting, which every MicroPython build supports.
        return ("SCK %d Hz (period %s chip cycles = clk/%s), phase %s, jitter +/-%s cycles"
                % (int(self.sck_hz(clock_hz) + 0.5), _number(self.period_cycles), _number(self.period_cycles),
                   str(round(self.phase_cycles, 3)), str(round(self.jitter_cycles, 3))))


def _number(value):
    """A cycle count as a compact string: 16 for 16.0, 15.5 for 15.5."""
    value = float(value)
    whole = int(value)
    if whole == value:
        return "%d" % whole
    return str(round(value, 3))


# ------------------------------------------------------------------------------------------------------------------
# SPI host link


class SpiLink:
    """Mode-0 MSB-first transactions over the operation protocol; decodes the read byte stream."""

    def __init__(self, timing):
        self.timing = timing

    def transaction(self, mosi, n_read=0):
        """Clock out `mosi` bytes; return the `n_read` data bytes that follow the 3 command/address bytes."""
        t = self.timing
        rng = Rng(t.seed + len(mosi) * 7 + n_read)
        jitter = t.jitter_cycles
        half = t.half_cycles
        lead = t.sample_lead_cycles

        yield op_pins(0, 1, 0)                          # idle: SCK low, CS_N high (SPEC v2 9: byte state = command)
        yield op_wait(t.cs_gap_cycles)
        yield op_pins(0, 0, 0)                          # CS_N falls with SCK low (mode 0)
        # The wait that puts the first rising edge at Timing.phase_cycles of a chip clock period.
        yield op_wait(t.phase_setup_cycles)
        bits = []
        for byte in mosi:
            value = int(byte) & 0xFF
            for i in range(7, -1, -1):
                mosi_bit = (value >> i) & 1
                yield op_pins(0, 0, mosi_bit)           # data set up while SCK is low
                yield op_wait(half - lead + rng.uniform(-jitter, jitter))
                bits.append((yield op_sample()))        # MISO belongs to this bit until the edge shifts it
                yield op_wait(lead)
                yield op_pins(1, 0, mosi_bit)           # rising edge: the target samples MOSI
                yield op_wait(half + rng.uniform(-jitter, jitter))
        yield op_pins(0, 0, 0)                          # final falling edge
        yield op_wait(t.cs_hold_cycles)
        yield op_pins(0, 1, 0)                          # CS_N high: the target returns to the command byte
        # Give the sub-cycle part of the phase back, so the transaction spans a whole number of chip cycles and
        # the next transaction starts from the phase this one started from (with jitter off).  Without this the
        # requested phase would accumulate from transaction to transaction and "phase" would mean nothing.
        yield op_wait(t.phase_return(len(mosi)))
        return _bits_to_bytes(bits[24:])[:n_read]

    def write(self, addr, data):
        data = bytes(data)
        if not data:
            return
        frame = bytes((CMD_WRITE, (addr >> 8) & 0xFF, addr & 0xFF)) + data
        yield from self.transaction(frame, 0)

    def read(self, addr, n=1):
        frame = bytes((CMD_READ, (addr >> 8) & 0xFF, addr & 0xFF)) + bytes(n)
        return (yield from self.transaction(frame, n))


def _bits_to_bytes(bits):
    out = bytearray()
    for i in range(0, len(bits) - 7, 8):
        value = 0
        for b in bits[i:i + 8]:
            value = (value << 1) | (b & 1)
        out.append(value)
    return bytes(out)


# ------------------------------------------------------------------------------------------------------------------
# the loader


class ImageError(Exception):
    pass


class MetronomeHost:
    """Host-side sequence for one chip: reset, load an image, read status.

    `enforce_spec` (default) refuses any transaction faster than clk/16 (SPEC v2 9).  Set it False only for a sweep
    that is deliberately measuring where the link breaks; the failure is then the point of the exercise.
    """

    def __init__(self, timing=None, clock_hz=60000000.0, enforce_spec=True):
        self.timing = timing or Timing()
        self.clock_hz = float(clock_hz)
        self.enforce_spec = bool(enforce_spec)
        self.link = SpiLink(self.timing)
        self.bytes_written = 0
        self.frames = 0
        self.max_frame = 32

    # -- guards ----------------------------------------------------------------------------------------------------
    def _require_spec(self):
        if self.enforce_spec and self.timing.period_cycles < SPEC_MIN_PERIOD_CYCLES:
            raise ValueError(
                "SCK period %s chip cycles is below clk/16, so SCK is faster than the SPEC v2 9 limit of clk/16; "
                "construct MetronomeHost(enforce_spec=False) only for a deliberate violation sweep"
                % str(round(self.timing.period_cycles, 3)))

    def min_write_gap_cycles(self):
        """D24 spacing between host writes at this timing: one write per completed SPI byte (SPEC v2 1, image.py)."""
        return self.timing.byte_cycles()

    # -- basic link operations -------------------------------------------------------------------------------------
    def read(self, addr, n=1):
        self._require_spec()
        return (yield from self.link.read(addr, n))

    def write(self, addr, data):
        self._require_spec()
        yield from self.link.write(addr, data)
        self.bytes_written += len(bytes(data))
        self.frames += 1

    def transaction(self, mosi, n_read=0):
        return (yield from self.link.transaction(mosi, n_read))

    # -- reset -----------------------------------------------------------------------------------------------------
    def reset_sequence(self, hold_cycles=64, settle_cycles=64):
        """Assert rst_n, hold, release, and stay idle long enough that no configuration write lands in the two
        cycles after rst_q rises (SPEC v2 1)."""
        yield op_log("reset: assert")
        yield op_reset_n(0)
        yield op_pins(0, 1, 0)
        yield op_wait(hold_cycles)
        yield op_reset_n(1)
        yield op_log("reset: release, %d cycle settle" % int(settle_cycles))
        yield op_wait(settle_cycles)

    # -- status ----------------------------------------------------------------------------------------------------
    def read_id(self):
        value = yield from self.read(HOST_MAP_ID, 1)
        return value[0]

    def read_ctrl(self):
        """CTRL block 0x2400..0x2408: RUN, STICKY, IRQEN, DOORBELL, HOSTIN, HOSTOUT, HOSTSTAT, ID, ERRSUM."""
        raw = yield from self.read(HOST_MAP_CTRL, 9)
        return {"RUN": raw[0], "STICKY": raw[1], "IRQEN": raw[2], "DOORBELL": raw[3], "HOSTIN": raw[4],
                "HOSTOUT": raw[5], "HOSTSTAT": raw[6], "ID": raw[7], "ERRSUM": raw[8]}

    def read_lines(self):
        """All four line runtime blocks (0x2410 + 8*l, 8 bytes each): PHASE, CTL, SYM, INS, STAT."""
        raw = yield from self.read(HOST_MAP_LRT, 0x20)
        out = []
        for l in range(4):
            b = raw[8 * l:8 * l + 8]
            out.append({"PHASE": b[0] | (b[1] << 8), "CTL": b[2], "SYM": b[3], "INS": b[4], "STAT": b[5],
                        "SYNC": (b[2] >> 3) & 1, "FIRED": (b[2] >> 4) & 7, "HELD": (b[2] >> 7) & 1,
                        "RUN": b[2] & 1, "ARM": (b[2] >> 1) & 1, "REN": (b[2] >> 2) & 1,
                        "TAPMISS": b[5] & 1})
        return out

    def read_threads(self):
        """All six thread runtime blocks (0x2440 + 2*t, 2 bytes each): PC, STAT."""
        raw = yield from self.read(HOST_MAP_TRT, 0x0C)
        out = []
        for t in range(6):
            st = raw[2 * t + 1]
            out.append({"PC": raw[2 * t], "STAT": st, "READY": st & 1, "RUNNING": (st >> 1) & 1,
                        "ARMED": (st >> 2) & 1, "EN": (st >> 3) & 1, "LATE": (st >> 4) & 1, "OVR": (st >> 5) & 1})
        return out

    def hostin(self, byte):
        """Write CTRL.HOSTIN: sets INB and INV (SPEC v2 9)."""
        yield from self.write(0x2404, bytes((byte & 0xFF,)))

    def hoststat(self):
        value = yield from self.read(0x2406, 1)
        return value[0]

    def hostout(self):
        value = yield from self.read(0x2405, 1)
        return value[0]

    def start(self):
        """CTRL.RUN = 1 (RUN_global).  Images that enable execution already do this themselves."""
        yield from self.write(HOST_MAP_CTRL, b"\x01")

    def delay(self, cycles):
        """Idle for `cycles` chip clock periods with the link deselected (no traffic)."""
        yield op_pins(0, 1, 0)
        yield op_wait(cycles)

    def probe(self):
        """The read-back the loader can check after a load: ID, CTRL block, line and thread runtime."""
        idv = yield from self.read_id()
        ctrl = yield from self.read_ctrl()
        lines = yield from self.read_lines()
        threads = yield from self.read_threads()
        return {"id": idv, "ctrl": ctrl, "lines": lines, "threads": threads}

    # -- images ----------------------------------------------------------------------------------------------------
    def load_image(self, image):
        """Apply a `metronome_image` JSON object (metronome2_tools.image.build_image) in order."""
        if image.get("format") != IMAGE_FORMAT:
            raise ImageError("not a %s file (format=%r)" % (IMAGE_FORMAT, image.get("format")))
        version = image.get("machine_version")
        if version != IMAGE_MACHINE_VERSION:
            raise ImageError("image is for machine version %r, this loader implements %d"
                             % (version, IMAGE_MACHINE_VERSION))
        writes = image.get("writes")
        if not isinstance(writes, list) or not writes:
            raise ImageError("image has no 'writes' list")
        items = []
        for w in writes:
            try:
                addr = int(w["addr"])
                data = bytes.fromhex(w["data"])
            except (KeyError, TypeError, ValueError):
                raise ImageError("malformed write entry %r" % (w,))
            items.append((addr, data))
        return (yield from self.load_writes(items))

    def load_writes(self, writes, coalesce=True, max_frame=None, progress=None):
        """Write ((addr, bytes), ...) in order, merging address-contiguous neighbours into one frame.

        Returns the number of bytes written.  The order is the image's order: program memory first, then
        configuration, then CTRL.RUN, then line CTL (image.py explains why).
        """
        limit = self.max_frame if max_frame is None else int(max_frame)
        frames = _coalesce(writes, coalesce, limit)
        total = 0
        for i, (addr, data) in enumerate(frames):
            if progress is not None and i % 8 == 0:
                yield op_log("load: frame %d/%d @0x%04X (%d bytes)" % (i + 1, len(frames), addr, len(data)))
            yield from self.write(addr, data)
            total += len(data)
        yield op_log("load: %d bytes in %d frames" % (total, len(frames)))
        return total


def _coalesce(writes, coalesce=True, max_frame=32):
    frames = []
    for item in writes:
        addr, data = int(item[0]), bytes(item[1])
        if not 0 <= addr <= 0xFFFF:
            raise ImageError("address 0x%X out of the 16-bit host map" % addr)
        if not data:
            continue
        if coalesce:
            pos = 0
            while pos < len(data):
                if frames and frames[-1][0] + len(frames[-1][1]) == addr + pos and \
                        len(frames[-1][1]) < max_frame:
                    room = max_frame - len(frames[-1][1])
                    chunk = data[pos:pos + room]
                    frames[-1] = (frames[-1][0], frames[-1][1] + chunk)
                    pos += len(chunk)
                else:
                    chunk = data[pos:pos + max_frame]
                    frames.append((addr + pos, chunk))
                    pos += len(chunk)
        else:
            for pos in range(0, len(data), max_frame):
                frames.append((addr + pos, data[pos:pos + max_frame]))
    return frames
