"""Command-line entry for the Metronome host loader.

Runs on the RP2350 (MicroPython) and, for the `plan` command, on a PC:

    mpremote run board_cli.py selftest
    mpremote run board_cli.py load uart_tx.json
    mpremote run board_cli.py status
    mpremote run board_cli.py read 0x2400 9
    mpremote run board_cli.py hostin 0x41
    python board_cli.py plan uart_tx.json          # offline: validates the image and counts bus operations
"""
import sys

try:                                    # imported as a package (`import board.board_cli`)
    from .metronome_core import MetronomeHost, Timing, ID_VALUE, _coalesce
    from . import metronome_core
    from . import ttboard_adapter
except ImportError:                     # run as a plain script (`mpremote run board_cli.py`)
    import metronome_core
    import ttboard_adapter
    from metronome_core import MetronomeHost, Timing, ID_VALUE, _coalesce


class NullBus:
    """Offline bus: no time, MISO reads 0.  Used by `plan` to validate an image under CPython."""

    def __init__(self):
        self.ops = 0
        self.notes = []

    def set_pins(self, sck, cs_n, mosi):
        self.ops += 1

    def sample_miso(self):
        self.ops += 1
        return 0

    def wait_cycles(self, cycles):
        self.ops += 1

    def set_reset_n(self, level):
        self.ops += 1


def _drive(gen, bus):
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
            bus.set_pins(operation[1], operation[2], operation[3])
        elif kind == "wait":
            bus.wait_cycles(operation[1])
        elif kind == "sample":
            send = bus.sample_miso()
        elif kind == "reset_n":
            bus.set_reset_n(operation[1])
        elif kind == "log":
            if hasattr(bus, "notes"):
                bus.notes.append(operation[1])
        else:
            raise ValueError("unknown loader op %r" % (kind,))


def _plan(path):
    import json
    with open(path) as handle:
        image = json.load(handle)
    writes = [(int(w["addr"]), bytes.fromhex(w["data"])) for w in image["writes"]]
    frames = _coalesce(writes, True, 32)
    host = MetronomeHost(Timing(16.0), 60000000.0)
    bus = NullBus()
    _drive(host.load_image(image), bus)
    clock_hz = image.get("clock_hz", 60000000.0)
    bits = sum(len(data) + 3 for _addr, data in frames) * 8
    print("image %s: %d writes, %d frames, %d data bytes" % (path, len(writes), len(frames),
                                                             sum(len(d) for _a, d in frames)))
    print("bus operations: %d (pins/waits/samples); %d SCK bits" % (bus.ops, bits))
    ms = 1e3 * bits * 16.0 / clock_hz
    print("load time at SCK = clk/16 and %d Hz: %s ms (calculated from the bit count)"
          % (int(clock_hz), str(round(ms, 3))))
    return 0


def _connect():
    board = ttboard_adapter.Board.connect()
    print(board.describe())
    return board


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    command = argv[0] if argv else "selftest"

    if command == "plan":
        if len(argv) < 2:
            print("usage: plan <image.json>")
            return 2
        return _plan(argv[1])

    benchmark_sck = ttboard_adapter.benchmark_sck
    load_image_file = ttboard_adapter.load_image_file

    if command == "selftest":
        board = _connect()
        host = board.host()
        host.reset()
        idv = host.read_id()
        print("ID = 0x%02X (expected 0x%02X) %s" % (idv, ID_VALUE, "ok" if idv == ID_VALUE else "MISMATCH"))
        state = host.probe()
        print("ctrl RUN=%d IRQEN=%d HOSTSTAT=0x%02X ERRSUM=0x%02X"
              % (state["ctrl"]["RUN"], state["ctrl"]["IRQEN"], state["ctrl"]["HOSTSTAT"], state["ctrl"]["ERRSUM"]))
        return 0 if idv == ID_VALUE else 1

    if command == "load":
        if len(argv) < 2:
            print("usage: load <image.json>")
            return 2
        board = _connect()
        host = board.host()
        host.reset()
        bytes_written = load_image_file(host, argv[1])
        idv = host.read_id()
        state = host.probe()
        print("loaded %d bytes; ID=0x%02X; RUN=%d; line0 CTL=0x%02X; thread0 STAT=0x%02X; ERRSUM=0x%02X"
              % (bytes_written, idv, state["ctrl"]["RUN"], state["lines"][0]["CTL"],
                 state["threads"][0]["STAT"], state["ctrl"]["ERRSUM"]))
        return 0 if idv == ID_VALUE else 1

    if command == "status":
        board = _connect()
        host = board.host()
        state = host.probe()
        print("ID=0x%02X RUN=%d IRQEN=%d STICKY=0x%02X ERRSUM=0x%02X HOSTSTAT=0x%02X"
              % (state["id"], state["ctrl"]["RUN"], state["ctrl"]["IRQEN"], state["ctrl"]["STICKY"],
                 state["ctrl"]["ERRSUM"], state["ctrl"]["HOSTSTAT"]))
        for i, line in enumerate(state["lines"]):
            print("L%d PHASE=%5d CTL=0x%02X FIRED=%d HELD=%d TAPMISS=%d" % (i, line["PHASE"], line["CTL"],
                                                                          line["FIRED"], line["HELD"],
                                                                          line["TAPMISS"]))
        for i, thread in enumerate(state["threads"]):
            print("T%d PC=0x%02X STAT=0x%02X READY=%d RUNNING=%d ARMED=%d EN=%d LATE=%d OVR=%d"
                  % (i, thread["PC"], thread["STAT"], thread["READY"], thread["RUNNING"], thread["ARMED"],
                     thread["EN"], thread["LATE"], thread["OVR"]))
        return 0

    if command == "read":
        if len(argv) < 2:
            print("usage: read <addr> [n]")
            return 2
        addr = int(argv[1], 0)
        n = int(argv[2], 0) if len(argv) > 2 else 1
        board = _connect()
        print(bytes(board.host().read(addr, n)).hex())
        return 0

    if command == "write":
        if len(argv) < 3:
            print("usage: write <addr> <hex bytes>")
            return 2
        board = _connect()
        board.host().write(int(argv[1], 0), bytes.fromhex(argv[2]))
        return 0

    if command == "hostin":
        if len(argv) < 2:
            print("usage: hostin <byte>")
            return 2
        board = _connect()
        host = board.host()
        host.hostin(int(argv[1], 0))
        print("HOSTSTAT=0x%02X" % host.hoststat())
        return 0

    if command == "bench":
        board = _connect()
        hz = benchmark_sck(board)
        print("bit-bang toggle rate: %s Hz (SCK is at most half of this, and slower in practice)"
              % ("?" if hz is None else "%d" % int(hz + 0.5)))
        return 0

    print("unknown command %r; try: selftest | load | status | read | write | hostin | bench | plan" % command)
    return 2


if __name__ == "__main__":
    sys.exit(main())
