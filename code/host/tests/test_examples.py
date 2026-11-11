from pathlib import Path

import pytest
from funcsim import FuncSim

from metronome_tools.asm import assemble_file
from metronome_tools.check import check

EX = Path(__file__).resolve().parents[1] / "examples"
ALL = sorted(p.name for p in EX.glob("*.mas"))


@pytest.mark.parametrize("name", ALL)
def test_example_assembles_and_passes_checks(name):
    prog = assemble_file(EX / name)
    rep = check(prog)
    assert rep.ok, rep.errors
    assert not any("burst rule" in w for w in rep.warnings)


def test_all_expected_examples_present():
    assert {"blink.mas", "uart_tx.mas", "uart_rx.mas", "spi_controller.mas", "eth_tx.mas"} <= set(ALL)


def test_blink_toggles_every_beat():
    prog = assemble_file(EX / "blink.mas")
    assert (prog.bgs[0].inc, prog.bgs[0].mod) == (1, 60000)
    sim = FuncSim(prog)
    levels = []
    for _ in range(8):
        sim.commit()
        levels.append(sim.level(8))
        sim.burst()
    # staged symbol alternates 0,1,0,1 from the first burst; commits lag by one beat
    assert levels[1:] == [0, 1, 0, 1, 0, 1, 0]


def uart_frame(byte):
    return [0] + [(byte >> i) & 1 for i in range(8)] + [1]


def decode_uart(levels):
    out, i = [], 0
    while i < len(levels) - 9:
        if levels[i] == 0:
            frame = levels[i:i + 10]
            assert frame[9] == 1, f"framing error at beat {i}"
            out.append(sum(b << k for k, b in enumerate(frame[1:9])))
            i += 10
        else:
            i += 1
    return out


def test_uart_tx_sends_mailbox_bytes_back_to_back():
    prog = assemble_file(EX / "uart_tx.mas")
    assert (prog.bgs[0].inc, prog.bgs[0].mod) == (6, 3125)
    sim = FuncSim(prog)
    data = [0x41, 0x00, 0xFF, 0x55, 0xA5]
    queue = list(data)
    levels, bursts = [], []
    for beat in range(120):
        sim.commit()
        levels.append(sim.level(8))
        if queue and not sim.inv and beat >= 3:          # the host feeds the mailbox when INV is clear
            sim.inb, sim.inv = queue.pop(0), 1
        bursts.append(sim.burst())
    assert levels[:4] == [1, 1, 1, 1]                    # idle high from reset (symbol 0 = high)
    assert decode_uart(levels) == data
    assert max(bursts) <= 2
    # back-to-back: no idle beats between consecutive frames once the mailbox is kept full
    first = levels.index(0)
    assert levels[first:first + 20] == uart_frame(0x41) + uart_frame(0x00)


def test_uart_tx_idle_stays_high():
    sim = FuncSim(assemble_file(EX / "uart_tx.mas"))
    for _ in range(30):
        sim.commit()
        assert sim.level(8) == 1
        sim.burst()


def run_rx(sim, bits):
    for b in bits:
        sim.burst(ein=b)


def test_uart_rx_receives_bytes_and_rearms():
    prog = assemble_file(EX / "uart_rx.mas")
    sim = FuncSim(prog)
    for byte in (0x41, 0x00, 0xFF, 0x96):
        sim.ctl_writes.clear()
        run_rx(sim, uart_frame(byte))
        assert sim.outq[-1] == byte
        assert sim.ctl_writes == [(0, 2)]                # BG0.CTL = ARM only: stop and wait for the next start edge
        assert not sim.flags & 4
    assert len(sim.outq) == 4


def test_uart_rx_flags_framing_error():
    sim = FuncSim(assemble_file(EX / "uart_rx.mas"))
    run_rx(sim, [0] + [1, 0, 1, 0, 1, 0, 1, 0] + [0])   # stop bit low
    assert sim.flags & 4 and sim.outq == []          # byte dropped, F2 = framing error


def test_uart_rx_rejects_false_start():
    sim = FuncSim(assemble_file(EX / "uart_rx.mas"))
    sim.burst(ein=1)                                      # the "start bit" sample is high: a glitch
    assert sim.ctl_writes == [(0, 2)] and sim.pc == prog_start(sim)
    run_rx(sim, uart_frame(0x3C))
    assert sim.outq == [0x3C]


def prog_start(sim):
    return sim.eng.start_addr
