"""RP2350 demo-board adapter for the Metronome host loader (Tiny Tapeout `ttboard` SDK).

The protocol logic lives in `metronome_core.py`, which has no machine imports and runs under CPython in
`code/tests/board_twin/`.  This file is the thin hardware layer: project selection, clock, reset, `ui_in` writes and
`uo_out` reads, plus the ops interpreter that drives the core generator.

Typical session (REPL or `board_cli.py`):

    from board.ttboard_adapter import connect, load_image_file
    board = connect()                     # project enabled, 60 MHz project clock, chip in reset
    host = board.host(Timing())           # the pure core + this bus
    board.run(host.reset_sequence())
    load_image_file(host, "uart_tx.json") # generator, driven by board.run
    board.run(host.read_id())             # -> 0xA2

Nothing here has been run on an RP2350 or a demo board: the SDK calls below were checked by reading the pinned
source, not by calling it.  Evidence class: host software, API names verified against the pinned source, behaviour
RTL-simulated in `code/tests/board_twin/` and not measured on hardware.
"""
import time

try:                                    # imported as a package (`import board.ttboard_adapter`)
    from .metronome_core import (MetronomeHost, Timing, ID_VALUE, HOST_MAP_CTRL, HOST_MAP_ID, HOST_MAP_DATARAM,
                                 op_pins)
except ImportError:                     # run as a plain script (`mpremote run ttboard_adapter.py`)
    import sys as _sys
    _here = __file__.replace("\\", "/").rsplit("/", 1)
    if len(_here) == 2:
        _sys.path.insert(0, _here[0])
    from metronome_core import (MetronomeHost, Timing, ID_VALUE, HOST_MAP_CTRL, HOST_MAP_ID, HOST_MAP_DATARAM,  # noqa: F401
                                op_pins)

#: The shuttle name of this design (info.yaml top_module).  It must be present in the board's shuttle JSON.
PROJECT_NAME = "tt_um_brentius_metronome"
DEFAULT_CLOCK_HZ = 60000000

#: The Tiny Tapeout MicroPython SDK revision this adapter is written against (README.md pins the same hash).
SDK_REPO = "https://github.com/TinyTapeout/tt-micropython-firmware"
SDK_COMMIT = "15ba5ced7aae7746ea2f9004cb412109c9fe9c83"
SDK_COMMIT_DATE = "2026-11-12"
SDK_LICENSE = "LGPL-2.1"               # LICENSE at that commit; pyproject classifier "LGPLv2+"
SDK_VERSION = "2.0.0"                  # pyproject.toml [project] version at that commit

#: Every SDK name this module uses, checked against the pinned source tree (test_core.py re-checks when the pinned
#: checkout is present under build/board_sdk/).  None of these names was confirmed by running the SDK.
SDK_API = (
    ("src/ttboard/boot/demoboard_detect.py", "def probe(cls)"),
    ("src/ttboard/demoboard.py", "def get(cls)"),
    ("src/ttboard/mode.py", "ASIC_RP_CONTROL"),
    ("src/ttboard/demoboard.py", "def clock_project_PWM"),
    ("src/ttboard/demoboard.py", "def clock_project_stop"),
    ("src/ttboard/demoboard.py", "def reset_project"),
    ("src/ttboard/demoboard.py", "def rst_n"),
    ("src/ttboard/demoboard.py", "def is_auto_clocking"),
    ("src/ttboard/demoboard.py", "def auto_clocking_freq"),
    ("src/ttboard/demoboard.py", "def mode_str"),
    ("src/ttboard/project_mux.py", "def find"),
    ("src/ttboard/project_mux.py", "self.enabled = None"),
    ("src/ttboard/project_design.py", "def enable"),
    ("src/ttboard/project_design.py", "self.name = projname"),
    ("src/ttboard/pins/pins.py", "platform.write_ui_in_byte"),
    ("src/ttboard/pins/pins.py", "platform.read_uo_out_byte"),
)


def _ticks_us():
    """MicroPython's time.ticks_us, or a CPython equivalent so this module can be import-checked on a PC."""
    fn = getattr(time, "ticks_us", None)
    if fn is not None:
        return fn()
    return int(time.perf_counter() * 1000000)


def _ticks_diff(a, b):
    fn = getattr(time, "ticks_diff", None)
    if fn is not None:
        return fn(a, b)
    return a - b


def _sleep_us(us):
    fn = getattr(time, "sleep_us", None)
    if fn is not None:
        fn(us)
    else:
        time.sleep(us / 1000000.0)


class TtBoardBus:
    """The edge bus for the core: `ui_in`/`uo_out`/`rst_n` through the ttboard SDK.

    Input pins:  ui_in[0] = SCK, ui_in[1] = CS_N, ui_in[2] = MOSI.  The loader owns those three; `ui_high` keeps
    whatever the caller put on P8..P12 (ui_in[3..7]) so a test can inject a protocol signal on a spare pin.
    Output pins: uo_out[0] = MISO (sampled), uo_out[1] = IRQ (readable via `irq()`).

    `cycles_to_us` converts the core's chip-clock-cycle timing to wall-clock microseconds.  A MicroPython bit-bang
    cannot hold clk/16 (see README); `sck_half_us` may be raised to slow the link down, and every wait is at least
    one bus call long, so the achieved SCK period is the maximum of the requested timing and the interpreter cost.
    A wait shorter than the microsecond timer's granularity is rounded to zero: the timing is only as good as
    `time.ticks_us()`, which is why the honest description of the bit-bang rate is "interpreter-bound" (README).
    """

    def __init__(self, tt, clock_hz=DEFAULT_CLOCK_HZ, ui_high=0, trace=None):
        self.tt = tt
        self.clock_hz = float(clock_hz)
        self.us_per_cycle = 1000000.0 / float(clock_hz)
        self.ui_high = (int(ui_high) & 0xF8)
        self.trace = trace
        self.ops = 0
        self.waits = 0

    # -- pins ------------------------------------------------------------------------------------------------------
    def set_pins(self, sck, cs_n, mosi):
        self.ops += 1
        if self.trace is not None:
            self.trace.append(("pins", sck, cs_n, mosi, _ticks_us()))
        self.tt.ui_in.value = self.ui_high | (sck & 1) | ((cs_n & 1) << 1) | ((mosi & 1) << 2)

    def sample_miso(self):
        self.ops += 1
        return self.tt.uo_out.value & 1

    def irq(self):
        return (self.tt.uo_out.value >> 1) & 1

    def set_reset_n(self, level):
        self.ops += 1
        if self.trace is not None:
            self.trace.append(("reset_n", level, _ticks_us()))
        # ttboard wants the inverse: True means "hold the project in reset".
        self.tt.reset_project(not level)

    # -- time ------------------------------------------------------------------------------------------------------
    def wait_cycles(self, cycles):
        self.waits += 1
        us = cycles * self.us_per_cycle
        if us <= 0:
            return
        # Busy-wait for short intervals (the common case), sleep for the long ones.
        if us >= 2000.0:
            _sleep_us(int(us) - 500)
            us = 500.0
        deadline = _ticks_us() + int(us + 0.5)
        while _ticks_diff(deadline, _ticks_us()) > 0:
            pass


class Board:
    """Project selection, project clock and reset for the Metronome chip on a TT demo board."""

    def __init__(self, tt, clock_hz=DEFAULT_CLOCK_HZ):
        self.tt = tt
        self.clock_hz = clock_hz

    # -- bring-up --------------------------------------------------------------------------------------------------
    @classmethod
    def connect(cls, clock_hz=DEFAULT_CLOCK_HZ, project=PROJECT_NAME, probe=True):
        """Probe the board, select the project, set the mode, start the project clock and assert reset."""
        from ttboard.boot.demoboard_detect import DemoboardDetect
        from ttboard.demoboard import DemoBoard
        from ttboard.mode import RPMode

        if probe:
            DemoboardDetect.probe()
        tt = DemoBoard.get()
        tt.mode = RPMode.ASIC_RP_CONTROL           # RP2 drives ui_in/uio_in, reads uo_out/uio_out
        design = _select_project(tt, project)
        design.enable()                           # also applies config.ini for this project, if any
        tt.clock_project_stop()
        tt.clock_project_PWM(clock_hz)            # 60 MHz: the SDK's PWM path, see README limits
        if not tt.is_auto_clocking or abs(tt.auto_clocking_freq - clock_hz) > 1:
            print("WARNING: project clock is %s Hz, requested %s Hz (see board/README.md clock limits)"
                  % (tt.auto_clocking_freq, clock_hz))
        tt.reset_project(True)
        return cls(tt, clock_hz)

    def host(self, timing=None, enforce_spec=True, ui_high=0, trace=None):
        bus = TtBoardBus(self.tt, self.clock_hz, ui_high=ui_high, trace=trace)
        return HostWithBus(MetronomeHost(timing or Timing(), self.clock_hz, enforce_spec=enforce_spec), bus)

    # -- status ----------------------------------------------------------------------------------------------------
    def describe(self):
        tt = self.tt
        enabled = tt.shuttle.enabled
        return ("project %s, mode %s, clock %s Hz (auto=%s), reset asserted=%s"
                % (enabled.name if enabled is not None else None, tt.mode_str,
                   tt.auto_clocking_freq, tt.is_auto_clocking, not tt.rst_n()))

    def stop(self):
        self.tt.clock_project_stop()


def _select_project(tt, name):
    """Resolve the design object: exact attribute, then a fuzzy find (the shuttle JSON may alias it)."""
    shuttle = tt.shuttle
    design = getattr(shuttle, name, None)
    if design is None:
        found = shuttle.find(name)
        if not found:
            raise RuntimeError(
                "project %r is not in this board's shuttle JSON (%s).  Add a [%s] section to config.ini or install "
                "a shuttle build that contains it." % (name, getattr(shuttle, "shuttle_id", "?"), name))
        design = found[0]
    return design


class HostWithBus:
    """A `MetronomeHost` plus the bus that executes its operations (the generator driver)."""

    def __init__(self, host, bus):
        self.host = host
        self.bus = bus
        self.notes = []

    # -- the ops interpreter ---------------------------------------------------------------------------------------
    def run(self, gen):
        """Drive one core generator to completion and return its value."""
        send = None
        started = False
        while True:
            try:
                operation = gen.send(send) if started else next(gen)
            except StopIteration as stop:
                return stop.value
            started = True
            send = None
            kind = operation[0]
            if kind == "pins":
                self.bus.set_pins(operation[1], operation[2], operation[3])
            elif kind == "wait":
                self.bus.wait_cycles(operation[1])
            elif kind == "sample":
                send = self.bus.sample_miso()
            elif kind == "reset_n":
                self.bus.set_reset_n(operation[1])
            elif kind == "log":
                self.notes.append(operation[1])
            else:
                raise ValueError("unknown loader op %r" % (kind,))

    # -- convenience wrappers (all of these are core generators) ---------------------------------------------------
    def reset(self):
        return self.run(self.host.reset_sequence())

    def read(self, addr, n=1):
        return self.run(self.host.read(addr, n))

    def write(self, addr, data):
        return self.run(self.host.write(addr, data))

    def read_id(self):
        return self.run(self.host.read_id())

    def probe(self):
        return self.run(self.host.probe())

    def load_image(self, image):
        return self.run(self.host.load_image(image))

    def hostin(self, byte):
        return self.run(self.host.hostin(byte))

    def hoststat(self):
        return self.run(self.host.hoststat())

    def hostout(self):
        return self.run(self.host.hostout())

    def start(self):
        return self.run(self.host.start())


def load_image_file(host, path):
    """Read a metronome image JSON and load it through a `HostWithBus` from `Board.host()`."""
    import json
    with open(path, "r") as handle:
        image = json.load(handle)
    if hasattr(host, "load_image"):
        return host.load_image(image)
    raise TypeError("expected a HostWithBus from Board.host()")


def benchmark_sck(board, n=200):
    """Measure the actual bit-bang rate on this board (returns SCK Hz).

    Hardware-only; the twin models timing instead.  Each SCK half period costs three pin writes and two bus calls.
    """
    host = board.host()
    bus = host.bus
    t0 = _ticks_us()
    for _ in range(n):
        bus.set_pins(1, 0, 0)
        bus.set_pins(0, 0, 0)
    dt = _ticks_diff(_ticks_us(), t0)
    if dt <= 0:
        return None
    return 1e6 * n / float(dt)
