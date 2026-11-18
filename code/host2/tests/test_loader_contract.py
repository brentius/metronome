"""Host-loader contract (loader_contract.py) against the v2 cycle-level model.

Evidence class: host software tested on the cycle model (model-verified), not RTL or hardware.
"""
import pytest
from common import *
from metronome2_tools.asm import assemble_text
from metronome2_tools.loader_contract import ContractLoader, ContractViolation, classify
from metronome2_tools._md import M

HMAP = M.HOST_MAP
SRC = """
.clock 60e6
.line 0
    inc 1
    mod 6
    taps - - -
    ctl run
.end
.out O8
    line 0
    sel 0 1 2
    lutraw 0xFBFBFBFB
.end
.thread 0
    core 0
    line 0
    trigger L0.BEAT
    start idle
.end
.core 0
idle:
    pause goto idle
"""


class ModelLink:
    """The cycle model through its host backdoor; reads see the registers exactly as the SPI read path does."""
    min_gap = 128

    def __init__(self, chip):
        self.chip = chip
        self.writes = []

    def write(self, addr, data):
        self.writes.append((addr, bytes(data)))
        self.chip.backdoor_write(addr, data)

    def read(self, addr, n=1):
        return bytes(self.chip.backdoor_read(addr + i) & 0xFF for i in range(n))

    def settle(self, cycles=40):
        for _ in range(cycles):
            self.chip.step(IDLE, 0)


def fresh():
    chip = Chip()
    link = ModelLink(chip)
    return chip, link, ContractLoader(link)


def run_chip(cycles=200):
    prog = assemble_text(SRC)
    chip, link, ld = fresh()
    n = ld.load(host_writes(prog))
    assert n == len(host_writes(prog))
    link.settle(cycles)
    return chip, link, ld, prog


def line_addr(l, off):
    return HMAP["LINE_BASE"] + M.HOST_STRIDE["LINE"] * l + off


def test_image_loads_on_a_fresh_chip_and_runs():
    chip, link, ld, prog = run_chip()
    assert ld.refused == 0
    assert chip.lines[0].RUN == 1 and chip.ctrl.RUN == 1
    assert ld.line_active(0) and ld.run_global()


def test_classify_matches_host_map():
    assert classify(HMAP["PROG_BASE"] + 5) == ("prog",)
    assert classify(HMAP["DATA_BASE"]) == ("data",)
    assert classify(line_addr(2, 4)) == ("LINE", 2, 4)
    assert classify(HMAP["CTRL_BASE"]) == ("CTRL", 0, 0)
    assert classify(0xFFFF) is None


@pytest.mark.parametrize("off,name", [(0, "INC"), (2, "MOD"), (3, "MOD hi byte"), (16, "EDGE"), (20, "LUT0")])
def test_running_line_configuration_is_refused(off, name):
    chip, link, ld, _ = run_chip()
    before = len(link.writes)
    with pytest.raises(ContractViolation) as e:
        ld.write(line_addr(0, off), bytes([7]))
    assert e.value.rule == "C1"
    assert len(link.writes) == before                      # nothing reached the link
    assert chip.lines[0].RUN == 1


def test_idle_line_configuration_is_accepted_while_another_line_runs():
    chip, link, ld, _ = run_chip()
    ld.write(line_addr(1, 0), (3).to_bytes(2, "little"))   # line 1 is stopped
    assert chip.lines[1].MOD == 0 and chip.lines[1].INC == 3 or chip.lines[1].INC == 3
    assert link.writes[-1][0] == line_addr(1, 0)


def test_armed_line_counts_as_in_use():
    chip, link, ld = fresh()
    link.write(HMAP["LRT_BASE"] + 2, bytes([0b10]))        # CTL.ARM
    with pytest.raises(ContractViolation):
        ld.write(line_addr(0, 2), bytes([9, 0]))


def test_enabled_thread_configuration_and_pc_refused():
    chip, link, ld, _ = run_chip()
    tcfg = HMAP["THREAD_BASE"]
    with pytest.raises(ContractViolation) as e:
        ld.write(tcfg, bytes([0]))
    assert e.value.rule == "C2"
    with pytest.raises(ContractViolation) as e:
        ld.write(HMAP["TRT_BASE"], bytes([3]))              # T0.PC
    assert e.value.rule == "C6"
    ld.write(HMAP["THREAD_BASE"] + M.HOST_STRIDE["THREAD"] * 5, bytes([0]))   # thread 5 is not enabled: allowed


def test_program_memory_refused_while_run_global_set_allowed_when_stopped():
    chip, link, ld, _ = run_chip()
    with pytest.raises(ContractViolation) as e:
        ld.write(HMAP["PROG_BASE"], bytes(8))
    assert e.value.rule == "C5"
    link.write(HMAP["CTRL_BASE"], bytes([0]))               # RUN_global = 0 (runtime register, always writable)
    ld.write(HMAP["PROG_BASE"], bytes(8))


def test_lfsr_and_stream_config_refused_while_running():
    chip, link, ld, _ = run_chip()
    for addr in (HMAP["LFSR_BASE"], HMAP["STREAM_BASE"]):
        with pytest.raises(ContractViolation) as e:
            ld.write(addr, bytes([1]))
        assert e.value.rule == "C4"


def test_output_cell_config_uses_shadow_binding_and_is_conservative_otherwise():
    chip, link, ld, _ = run_chip()
    out8 = HMAP["OUT_BASE"] + M.HOST_STRIDE["OUT"] * 8
    with pytest.raises(ContractViolation) as e:             # O8 bound to running line 0 (shadow from the image load)
        ld.write(out8 + 4, bytes(4))
    assert e.value.rule == "C3"
    chip2, link2, ld2 = fresh()                             # unknown binding, but nothing active: allowed
    ld2.write(out8 + 4, bytes(4))
    link2.write(HMAP["LRT_BASE"] + 2, bytes([1]))           # a line becomes active; binding unknown -> refuse
    with pytest.raises(ContractViolation):
        ld2.write(out8 + 4, bytes(4))


def test_data_ram_allowed_unless_strict():
    chip, link, ld, _ = run_chip()
    ld.write(HMAP["DATA_BASE"] + 4, bytes([1, 2, 3]))
    strict = ContractLoader(link, strict_data=True)
    with pytest.raises(ContractViolation) as e:
        strict.write(HMAP["DATA_BASE"] + 4, bytes([1]))
    assert e.value.rule == "C7"


def test_runtime_registers_stay_writable():
    chip, link, ld, _ = run_chip()
    ld.write(HMAP["LRT_BASE"] + 2, bytes([0]))              # stop line 0
    ld.write(HMAP["CTRL_BASE"], bytes([0]))
    assert not ld.line_active(0) and not ld.run_global()


def test_stopped_chip_accepts_reconfiguration():
    chip, link, ld, _ = run_chip()
    link.write(HMAP["LRT_BASE"] + 2, bytes([0]))
    link.write(HMAP["TRT_BASE"] + 1, bytes([0]))
    link.settle()
    ld.write(line_addr(0, 2), (12).to_bytes(2, "little"))
    ld.write(HMAP["THREAD_BASE"], bytes([8]))


def test_atomic_replace_stops_touched_state_and_reaches_the_new_value():
    chip, link, ld, _ = run_chip()
    ld.atomic_replace([(line_addr(0, 2), (12).to_bytes(2, "little")), (HMAP["THREAD_BASE"], bytes([8]))])
    assert chip.lines[0].RUN == 0                          # left stopped for the caller to restart
    assert chip.lines[0].MOD == 12
    # a program write also stops RUN_global
    ld.atomic_replace([(HMAP["PROG_BASE"], bytes(8))])
    assert chip.ctrl.RUN == 0


def test_unprotected_write_to_a_running_line_is_the_hazard_the_contract_prevents():
    """Without the loader, a two-byte field written while in use is visible half-written (SPEC 1)."""
    chip, link, ld, _ = run_chip()
    link.write(line_addr(0, 3), bytes([0x01]))              # high byte of MOD first: MOD = 0x0106 for a while
    assert chip.lines[0].MOD == 0x0106
    with pytest.raises(ContractViolation):                   # the same write through the loader is refused
        ld.write(line_addr(0, 3), bytes([0x01]))


def test_link_that_can_write_in_consecutive_cycles_is_rejected():
    class Fast(ModelLink):
        min_gap = 1
    with pytest.raises(ValueError):
        ContractLoader(Fast(Chip()))
