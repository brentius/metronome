"""CPython tests for the RP2350 loader core: no RTL, no board.

They pin down what the twin and the hardware adapter rely on: the operation protocol, the SPI frame layout of
SPEC v2 9, the image loader, the status read-back and the clk/16 guard.  `FakeTarget` is a mode-0 SPI target built
from the spec's byte rules, not from the RTL, so a frame-ordering mistake in the core shows up here first.

Evidence class: host software tested against a spec-level fake, plus (test_image_*) the repository toolchain's own
image output.  Not RTL and not hardware.
"""
from __future__ import annotations

import json

import pytest

from board.metronome_core import (IMAGE_FORMAT, ImageError, MetronomeHost, Timing, ID_VALUE, _coalesce,
                                  SPEC_MIN_PERIOD_CYCLES)
from board.board_cli import _drive, main as cli_main


class FakeTarget:
    """SPEC v2 9 SPI target over a byte-addressed file: mode 0, MSB first, 0x02/0x03, auto-increment."""

    def __init__(self, read_filter=None):
        self.regs = {}
        self.host_writes = []               # (addr, byte) in the order the target applies them
        self.read_filter = read_filter      # addr -> byte, or None to use regs
        self.read_requests = 0              # TX loads, i.e. read requests the target served (SPEC v2 9)
        self.sck = 0
        self.cs_n = 1
        self.mosi = 0
        self.state = "cmd"
        self.bitc = 0
        self.rx = 0
        self.tx = 0
        self.addr = 0
        self.is_rd = False
        self.edges = 0
        self.cs_falls = 0

    # -- bus protocol ----------------------------------------------------------------------------------------------
    def set_pins(self, sck, cs_n, mosi):
        rising = sck and not self.sck
        falling = self.cs_n and not (cs_n & 1)
        self.sck, self.cs_n, self.mosi = sck & 1, cs_n & 1, mosi & 1
        if falling:
            self.cs_falls += 1
        if self.cs_n:                       # unselected: byte state returns to the command byte
            self.state, self.bitc, self.tx = "cmd", 0, 0
        elif rising:
            self.edges += 1
            self.rx = ((self.rx << 1) | self.mosi) & 0xFF
            self.bitc += 1
            if self.bitc == 8:
                self.bitc = 0
                self._complete(self.rx)
            else:
                self.tx = (self.tx << 1) & 0xFF

    def sample_miso(self):
        return (self.tx >> 7) & 1

    def wait_cycles(self, cycles):
        return None

    def set_reset_n(self, level):
        if not level:
            self.regs.clear()
            self.state, self.bitc, self.tx, self.addr, self.is_rd = "cmd", 0, 0, 0, False

    # -- SPEC v2 9 byte rules --------------------------------------------------------------------------------------
    def _read(self, addr):
        if self.read_filter is not None:
            value = self.read_filter(addr)
            if value is not None:
                return value & 0xFF
        return self.regs.get(addr, 0) & 0xFF

    def _load(self):
        self.read_requests += 1
        self.tx = self._read(self.addr)
        self.addr = (self.addr + 1) & 0xFFFF

    def _complete(self, byte):
        if self.state == "cmd":
            self.is_rd = byte == 0x03
            self.state = "ah" if byte in (0x02, 0x03) else "ign"
        elif self.state == "ah":
            self.addr = (byte << 8) | (self.addr & 0xFF)
            self.state = "al"
        elif self.state == "al":
            self.addr = (self.addr & 0xFF00) | byte
            self.state = "data"
            if self.is_rd:
                self._load()
        elif self.state == "data":
            if self.is_rd:
                self._load()
            else:
                self.host_writes.append((self.addr, byte))
                self.regs[self.addr] = byte
                self.addr = (self.addr + 1) & 0xFFFF
        # "ign" ignores the rest of the transaction


def run(gen, target):
    return _drive(gen, target)


# ------------------------------------------------------------------------------------------------------------------
# protocol and timing


def test_core_imports_and_constants():
    assert ID_VALUE == 0xA2
    timing = Timing()
    assert timing.period_cycles == SPEC_MIN_PERIOD_CYCLES == 16.0
    assert abs(timing.sck_hz(60e6) - 3.75e6) < 1.0
    assert timing.byte_cycles() == 128.0                 # D24: >= 128 cycles between host writes


def test_hardware_adapter_imports_without_ttboard():
    """The RP2350 module must import on CPython: `ttboard` is only imported inside Board.connect()."""
    from board import ttboard_adapter
    assert ttboard_adapter.PROJECT_NAME == "tt_um_brentius_metronome"
    assert ttboard_adapter.DEFAULT_CLOCK_HZ == 60000000
    assert callable(ttboard_adapter.TtBoardBus.set_pins)
    assert callable(ttboard_adapter.TtBoardBus.sample_miso)


def test_pinned_sdk_commit_is_in_the_code_and_the_readme():
    """One commit hash, in the adapter and in board/README.md: the SDK surface was read at that revision."""
    from pathlib import Path
    from board import ttboard_adapter
    assert len(ttboard_adapter.SDK_COMMIT) == 40 and set(ttboard_adapter.SDK_COMMIT) <= set("0123456789abcdef")
    assert ttboard_adapter.SDK_LICENSE == "LGPL-2.1"
    readme = (Path(ttboard_adapter.__file__).parent / "README.md").read_text(encoding="utf-8")
    assert ttboard_adapter.SDK_COMMIT in readme, "README must pin the same commit hash as ttboard_adapter.SDK_COMMIT"
    assert "LGPL-2.1" in readme, "README must record the SDK licence"


def test_pinned_sdk_api_names_exist_in_the_pinned_source():
    """Re-check every SDK name against the read-only checkout at build/board_sdk (fetched, never run).

    Skipped when the checkout is absent: it is a gitignored build artefact, not part of the submission.
    """
    from pathlib import Path
    from board import ttboard_adapter
    tree = Path(__file__).resolve().parents[3] / "build" / "board_sdk"
    if not (tree / "src" / "ttboard").is_dir():
        pytest.skip("no pinned SDK checkout at build/board_sdk (see code/host2/board/README.md)")
    if not (tree / "src" / "ttboard" / "demoboard.py").is_file():
        pytest.skip("build/board_sdk is not a tt-micropython-firmware checkout")
    for rel, needle in ttboard_adapter.SDK_API:
        text = (tree / rel).read_text(encoding="utf-8")
        assert needle in text, "%s is not in %s at the pinned commit" % (needle, rel)


def test_core_is_micropython_friendly():
    """The core must stay importable by MicroPython: no CPython-only imports, no annotations, no f-strings and no
    float `%` format codes (%g/%e), which the RP2 build may not support."""
    import ast
    from pathlib import Path
    import board.metronome_core as core
    source = Path(core.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    docstrings = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            doc = ast.get_docstring(node, clean=False)
            if doc is not None and node.body:
                docstrings.add(id(node.body[0].value))
    bad_imports = {"json", "time", "typing", "dataclasses", "asyncio", "enum", "functools"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            assert not [a for a in node.names if a.name.split(".")[0] in bad_imports], ast.dump(node)
        elif isinstance(node, ast.ImportFrom):
            assert (node.module or "").split(".")[0] not in bad_imports, ast.dump(node)
        elif isinstance(node, (ast.JoinedStr, ast.AnnAssign)):
            raise AssertionError("CPython-only syntax: " + ast.dump(node))
        elif isinstance(node, ast.Constant) and isinstance(node.value, str) and id(node) not in docstrings:
            for code in ("%g", "%G", "%e", "%E"):
                assert code not in node.value, code


def test_enforce_spec_refuses_faster_than_clk16():
    host = MetronomeHost(Timing(8.0), 60e6)
    with pytest.raises(ValueError):
        run(host.read_id(), FakeTarget())
    host = MetronomeHost(Timing(8.0), 60e6, enforce_spec=False)   # the deliberate sweep path
    assert run(host.read_id(), FakeTarget()) == 0


def test_timing_validation():
    with pytest.raises(ValueError):
        Timing(0.0)
    with pytest.raises(ValueError):
        Timing(16.0, phase_cycles=1.0)
    with pytest.raises(ValueError):
        Timing(16.0, jitter_cycles=-0.1)


def test_reset_sequence_ops():
    host = MetronomeHost(Timing(16.0))
    ops = list(host.reset_sequence(hold_cycles=10, settle_cycles=20))
    kinds = [o[0] for o in ops]
    assert kinds[0] == "log" and ("reset_n", 0) in ops and ("reset_n", 1) in ops
    assert ("wait", 10.0) in ops and ("wait", 20.0) in ops
    assert ops.index(("reset_n", 0)) < ops.index(("reset_n", 1))


# ------------------------------------------------------------------------------------------------------------------
# SPI frames


def test_write_then_read_round_trip():
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    run(host.reset_sequence(hold_cycles=4, settle_cycles=4), target)
    run(host.write(0x1000, b"\x12\x34\x56"), target)
    assert run(host.read(0x1000, 3), target) == b"\x12\x34\x56"
    assert target.host_writes == [(0x1000, 0x12), (0x1001, 0x34), (0x1002, 0x56)]


def test_read_auto_increment_and_no_side_effect():
    target = FakeTarget()
    for i in range(9):
        target.regs[0x2400 + i] = 0x40 + i
    host = MetronomeHost(Timing(16.0), 60e6)
    block = run(host.read(0x2400, 9), target)
    assert block == bytes(0x40 + i for i in range(9))
    assert run(host.read(0x2400, 9), target) == block        # no host read has a side effect (SPEC v2 9)
    assert target.host_writes == []


def test_read_skips_three_command_bytes():
    """The first three MISO bytes are the command/address phase; data starts at byte 3 (SPEC v2 9)."""
    target = FakeTarget()
    target.regs[0x2ABC] = 0x99
    host = MetronomeHost(Timing(16.0), 60e6)
    assert run(host.read(0x2ABC, 1), target) == b"\x99"
    assert target.edges == 4 * 8


def test_frame_is_command_address_and_data_bytes():
    """A transaction clocks exactly the MOSI bytes the caller gives: 3 + n for a read, 3 + len for a write."""
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    run(host.read(0x2400, 5), target)
    assert target.edges == (3 + 5) * 8
    assert target.cs_falls == 1
    target = FakeTarget()
    run(host.write(0x1000, b"\x01\x02\x03\x04"), target)
    assert target.edges == (3 + 4) * 8
    assert target.cs_falls == 1


def test_read_prefetches_one_address_past_the_last_byte():
    """SPEC v2 9: "Reads prefetch one address past the last byte the host clocks out" -- n bytes, n+1 requests."""
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    run(host.read(0x2400, 3), target)
    assert target.read_requests == 4
    target = FakeTarget()
    run(host.write(0x2400, b"\x01\x02"), target)
    assert target.read_requests == 0


def test_cs_n_high_returns_the_byte_state_to_the_command_byte():
    """SPEC v2 9: while CS_N is high the target's byte state is the command byte.  Every transaction must therefore
    start from an idle (CS_N high) bus; the core does, and a transaction ends with CS_N high again."""
    host = MetronomeHost(Timing(16.0), 60e6)
    bus = PhaseBus()
    run(host.link.transaction(b"\x03\x24\x00\x00", 1), bus)
    pins = bus.pin_ops
    sck = [p[0] for p in pins]
    cs = [p[1] for p in pins]
    assert cs[0] == 1, "the first pin operation must be CS_N high"
    assert cs[-1] == 1, "the last pin operation must be CS_N high"
    falls = [i for i in range(1, len(cs)) if cs[i - 1] == 1 and cs[i] == 0]
    rises = [i for i in range(1, len(cs)) if cs[i - 1] == 0 and cs[i] == 1]
    assert len(falls) == 1 and len(rises) == 1, (pins[:6], pins[-3:])
    assert sck[falls[0]] == 0, "CS_N falls while SCK is low (mode 0)"
    assert sck[rises[0] - 1] == 0, "SCK is low again before CS_N rises"


class PhaseBus:
    """Records the sub-cycle phase of every SCK rising edge; keeps time in chip clock cycles.

    The core's clock origin is 0, so a `wait` of a whole number of cycles preserves the phase; this bus is how the
    "first edge lands at Timing.phase_cycles" promise is checked without a simulator.
    """

    def __init__(self):
        self.t = 0.0
        self.sck = 0
        self.pin_ops = []
        self.rises = []
        self.cs_falls = 0
        self.cs_n_prev = 1

    def set_pins(self, sck, cs_n, mosi):
        self.pin_ops.append((sck, cs_n, mosi))
        if sck and not self.sck:
            self.rises.append(self.t % 1.0)
        if self.cs_n_prev and not cs_n:
            self.cs_falls += 1
        self.cs_n_prev = cs_n
        self.sck = sck

    def sample_miso(self):
        return 0

    def wait_cycles(self, cycles):
        self.t += cycles

    def set_reset_n(self, level):
        pass


@pytest.mark.parametrize("period", [16.0, 32.0, 8.0, 15.5, 3.5])
@pytest.mark.parametrize("phase", [0.05, 0.37, 0.5, 0.95])
def test_first_sck_edge_lands_at_the_requested_phase(period, phase):
    """Timing.phase_cycles is a promise about the first SCK rising edge of *every* transaction, for any period."""
    bus = PhaseBus()
    host = MetronomeHost(Timing(period, phase, 0.0, 1), 60e6, enforce_spec=False)
    for _ in range(3):                                  # three transactions: the phase must not drift
        run(host.read(0x2400, 2), bus)
    per_transaction = len(bus.rises) // 3
    firsts = bus.rises[0::per_transaction]
    assert len(firsts) == 3
    for value in firsts:
        assert abs(value - phase) < 1e-9, (period, phase, bus.rises[:per_transaction])
    # an integer period keeps every edge at the same phase; a fractional one walks through the period
    if period == int(period):
        assert all(abs(v - phase) < 1e-9 for v in bus.rises)


def test_transaction_spans_whole_chip_cycles():
    """The sub-cycle part of the phase is given back in the CS_N-high gap, so the origin does not wander."""
    bus = PhaseBus()
    host = MetronomeHost(Timing(15.5, 0.37, 0.0, 1), 60e6, enforce_spec=False)
    before = bus.t
    run(host.read(0x2400, 1), bus)
    elapsed = bus.t - before
    assert abs(elapsed - round(elapsed)) < 1e-9, elapsed


def test_jitter_moves_the_edges_but_keeps_the_frame_intact():
    """The jitter model perturbs every half period; the frame still decodes (it is a phase/period model, not noise
    that can reorder bits)."""
    target = FakeTarget()
    target.regs[0x2400] = 0x5A
    host = MetronomeHost(Timing(16.0, 0.5, 0.45, 7), 60e6)
    assert run(host.read(0x2400, 1), target) == b"\x5a"


def test_bad_command_ignores_transaction():
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    run(host.transaction(bytes((0x07, 0x10, 0x00, 0xAA)), 0), target)
    assert target.host_writes == []
    assert target.regs == {}


def test_start_and_mailbox_helpers():
    """CTRL.RUN, HOSTIN, HOSTOUT and HOSTSTAT at the addresses the loader uses (SPEC v2 9 host map)."""
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    run(host.start(), target)
    assert target.regs[0x2400] == 1                              # CTRL.RUN
    run(host.hostin(0x5A), target)
    assert target.regs[0x2404] == 0x5A                           # CTRL.HOSTIN
    assert run(host.hostout(), target) == 0                      # CTRL.HOSTOUT (nothing written back)
    assert run(host.hoststat(), target) == 0                     # CTRL.HOSTSTAT


def test_unknown_address_reads_zero():
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0), 60e6)
    assert run(host.read(0xFFF0, 2), target) == b"\x00\x00"


def test_probe_layout():
    target = FakeTarget()

    def read_filter(addr):
        table = {0x2407: ID_VALUE, 0x2400: 0x01, 0x2406: 0x02, 0x2408: 0x00}
        if addr in table:
            return table[addr]
        if 0x2410 <= addr < 0x2430:                        # LRT: PHASE low/high, CTL, ...
            line = (addr - 0x2410) // 8
            offset = (addr - 0x2410) % 8
            return {0: 0x10 * (line + 1), 1: 0, 2: 0x05 if line == 1 else 0x00}.get(offset, 0)
        if 0x2440 <= addr < 0x244C:                        # TRT: PC, STAT
            thread = (addr - 0x2440) // 2
            offset = (addr - 0x2440) % 2
            return {0: 0x20 + thread, 1: 0x08 if thread == 2 else 0x00}[offset]
        return None

    target.read_filter = read_filter
    host = MetronomeHost(Timing(16.0), 60e6)
    state = run(host.probe(), target)
    assert state["id"] == ID_VALUE
    assert state["ctrl"]["RUN"] == 1 and state["ctrl"]["HOSTSTAT"] == 0x02
    assert state["lines"][1]["CTL"] == 0x05 and state["lines"][1]["RUN"] == 1 and state["lines"][1]["REN"] == 1
    assert state["lines"][0]["PHASE"] == 0x10 and state["lines"][3]["PHASE"] == 0x40
    assert state["threads"][2]["PC"] == 0x22 and state["threads"][2]["EN"] == 1
    assert state["threads"][3]["EN"] == 0


# ------------------------------------------------------------------------------------------------------------------
# images


def test_coalesce_merges_contiguous_writes():
    frames = _coalesce([(0x2000, b"\x01\x02"), (0x2002, b"\x03"), (0x2010, b"\x04\x05")], True, 32)
    assert frames == [(0x2000, b"\x01\x02\x03"), (0x2010, b"\x04\x05")]
    frames = _coalesce([(0x2000, bytes(range(40)))], True, 32)
    assert [len(d) for _a, d in frames] == [32, 8]
    assert frames[1][0] == 0x2020


def test_image_validation():
    host = MetronomeHost(Timing(16.0), 60e6)
    with pytest.raises(ImageError):
        list(host.load_image({"format": "nope"}))
    with pytest.raises(ImageError):
        list(host.load_image({"format": IMAGE_FORMAT, "machine_version": 99, "writes": []}))
    with pytest.raises(ImageError):
        list(host.load_image({"format": IMAGE_FORMAT, "machine_version": 2, "writes": []}))


def _uart_tx_image():
    from pathlib import Path
    from metronome2_tools.asm import assemble_file
    from metronome2_tools.image import build_image
    root = Path(__file__).resolve().parents[3]
    return build_image(assemble_file(str(root / "code/host2/examples/uart_tx.mas")))


def test_toolchain_image_loads_byte_for_byte():
    """The core must reproduce `metronome2_tools.image.image_writes` exactly, in order, over real SPI framing."""
    image = _uart_tx_image()
    target = FakeTarget()
    host = MetronomeHost(Timing(16.0, phase_cycles=0.25), 60e6)
    written = run(host.load_image(image), target)
    expected = {}
    for item in image["writes"]:
        addr = int(item["addr"])
        data = bytes.fromhex(item["data"])
        for i, byte in enumerate(data):
            expected[addr + i] = byte
    assert target.regs == expected
    assert written == sum(len(bytes.fromhex(w["data"])) for w in image["writes"])
    # the image ends with CTRL.RUN and then L0.CTL: the image decides when execution starts
    assert target.regs[0x2400] == 1
    assert target.regs[0x2412] == 1


def test_image_load_is_refused_at_fast_sck():
    image = _uart_tx_image()
    host = MetronomeHost(Timing(12.0), 60e6)
    with pytest.raises(ValueError):
        run(host.load_image(image), FakeTarget())


def test_cli_plan_accepts_a_toolchain_image(tmp_path, capsys):
    image = _uart_tx_image()
    path = tmp_path / "uart_tx.json"
    path.write_text(json.dumps(image), encoding="utf-8")
    assert cli_main(["plan", str(path)]) == 0
    out = capsys.readouterr().out
    assert "image" in out and "bus operations" in out
