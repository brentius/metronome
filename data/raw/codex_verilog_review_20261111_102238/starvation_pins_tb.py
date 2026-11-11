"""Reach starvation through ordinary SPI loading and a host doorbell; no backdoor writes."""
import sys
from pathlib import Path
import cocotb

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(ROOT / 'code/tests/rtl'), str(ROOT / 'code/host'), str(ROOT / 'code/md')]
from tb_metronome import TB, a_ctrl, a_eng
from metronome_tools.asm import assemble_file
from metronome_tools.image import host_writes
from metronome_tools.check import check

@cocotb.test()
async def starvation_via_spi(dut):
    tb = TB(dut)
    await tb.start()
    program = assemble_file(HERE / 'starvation_v2.mas')
    assert check(program).ok
    for addr, data, _ in host_writes(program):
        await tb.write(addr, data)
    await tb.write(a_ctrl('DOORBELL'), [4])
    dispatches = [0] * 6
    for _ in range(200):
        await tb.cycles(1)
        if int(dut.c0_disp.value):
            dispatches[int(dut.c0_de.value)] += 1
    status = (await tb.read(a_eng(2, 'STAT')))[0]
    hoststat = (await tb.read(a_ctrl('HOSTSTAT')))[0]
    dut._log.info(f'200 cycles after SPI doorbell: dispatches={dispatches}; E2.STAT={status:#04x}; HOSTSTAT={hoststat:#04x}')
    assert dispatches[:3] == [50, 50, 0]
    assert status & 1, 'E2 should still be READY'
    assert not hoststat & 2, 'E2 should never have written HOST.OUT'
