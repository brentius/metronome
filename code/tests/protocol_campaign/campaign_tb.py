"""Pin-only protocol campaign bench; RTL and routed netlists share this checker."""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge, Timer

REPO = Path(os.environ['CAMPAIGN_REPO'])
sys.path[:0] = [str(REPO/'code/tests/protocol_campaign'), str(REPO/'code/tests/lockstep_v2'),
               str(REPO/'sim/reference')]
import campaign
from protocol_decode import validate as decode_protocol
from metronome2.chip import Chip


async def clock(dut):
    """60 MHz nominal: exact 16667 ps period at 1 ps simulator precision."""
    dut.clk.value = 0
    while True:
        await Timer(8333, unit='ps')
        dut.clk.value = 1
        await Timer(8334, unit='ps')
        dut.clk.value = 0


def value(signal):
    return int(signal.value) if signal.value.is_resolvable else None


def initialize_sram(dut):
    mapping = json.loads(os.environ.get('CAMPAIGN_SRAM_MAP', '{}'))
    for name, size in (('u_pmem0',256),('u_pmem1',256),('u_dmem',512)):
        if mapping:
            macro = getattr(dut.user_project, mapping[name])
            memory = macro.i_SRAM_1P_behavioral_bm_bist.memory
        else:
            macro = getattr(dut,name)
            memory = macro.u_sram.i_SRAM_1P_behavioral_bm_bist.memory
        for i in range(size): memory[i].value = 0


def locate_waveform(trace: bytes, expected: bytes, name: str) -> int:
    if not expected:
        raise AssertionError(f'{name}: empty protocol expectation')
    index = trace.find(expected)
    assert index >= 0, f'{name}: complete expected wire waveform absent from {len(trace)} sampled cycles'
    return index


@cocotb.test()
async def protocol(dut):
    name = os.environ['CAMPAIGN_CASE']
    out = Path(os.environ['CAMPAIGN_OUTPUT'])
    scenario = campaign.build(name)
    metadata = dict(scenario.campaign)
    words = metadata['expected_words']
    period = metadata['cell_cycles']
    mask = metadata.get('pins_mask',15)
    pulls = metadata.get('pullups',0)
    capture_start = metadata.get('capture_start',0)
    capture_end = metadata.get('capture_end',len(scenario.steps))
    expected_wave = bytes((word & mask) for word in words for _ in range(period))
    assert period > 0 and len(words) > 1
    model = Chip()
    dut.ena.value = 1
    dut.ui_in.value = 1
    dut.uio_in.value = 0
    dut.rst_n.value = 1
    initialize_sram(dut)
    cocotb.start_soon(clock(dut))
    previous = (0,0,0)
    mismatches = []
    trace = bytearray()
    enables = bytearray()
    pins = bytearray()
    stimulus = bytearray()
    for cycle,(ui,hi,uio,rst) in enumerate(scenario.steps):
        await FallingEdge(dut.clk)
        uio = uio(cycle,previous) if callable(uio) else uio
        hi = hi(cycle,previous) if callable(hi) else hi
        ui = (ui & 7) | (hi & 248)
        dut.ui_in.value = ui
        dut.uio_in.value = uio & 255
        dut.rst_n.value = rst
        expected = tuple(model.step(ui,uio & 255,rst))
        await RisingEdge(dut.clk)
        await Timer(8000,unit='ps')
        observed = tuple(value(getattr(dut,n)) for n in ('uo_out','uio_out','uio_oe'))
        if cycle >= scenario.compare_from and observed != expected:
            if len(mismatches) < 10:
                mismatches.append({'cycle':cycle,'observed':observed,'expected':expected})
        previous = expected
        stimulus.extend((ui,uio & 255,rst))
        pins.extend(255 if x is None else x for x in observed)
        if capture_start <= cycle < capture_end:
            assert observed[1] is not None and observed[2] is not None, f'{name}: unresolved GPIO at cycle {cycle}'
            wire = (observed[1] & observed[2]) | (pulls & ~observed[2])
            trace.append(wire & mask)
            enables.append(observed[2] & 15)
    (out/f'{name}.stimulus.bin').write_bytes(stimulus)
    (out/f'{name}.pins.bin').write_bytes(pins)
    (out/f'{name}.wire.bin').write_bytes(trace)
    (out/f'{name}.expectation.json').write_text(json.dumps(metadata,indent=2)+'\n')
    assert not mismatches, f'{name}: pin/reference mismatches: {mismatches}'
    offset = locate_waveform(bytes(trace),expected_wave,name)
    expected_oe = metadata.get('oe_expected')
    if expected_oe is not None:
        assert len(expected_oe) == len(words), 'OE and wire vectors have different lengths'
        oe_mask = metadata.get('oe_mask',mask)
        wanted = bytes(v & oe_mask for v in expected_oe for _ in range(period))
        actual = bytes(v & oe_mask for v in enables[offset:offset+len(wanted)])
        assert actual == wanted, f'{name}: output-enable waveform mismatch'
    # Reject a corrupted observed pin sample; matching model behavior alone is
    # insufficient evidence that the wire expectation is actually enforced.
    changed = bytearray(trace)
    position = offset + len(expected_wave)//2
    changed[position] ^= mask & -mask
    try:
        locate_waveform(bytes(changed),expected_wave,name)
    except AssertionError:
        negative_rejected = True
    else:
        negative_rejected = False
    assert negative_rejected, f'{name}: corrupt-pin negative control was not rejected'
    if hasattr(campaign,'validate_case'):
        actual_words = [trace[offset+i*period+period//2] for i in range(len(words))]
        campaign.validate_case(name,actual_words)
    else:
        actual_words = [trace[offset+i*period+period//2] for i in range(len(words))]
    decoded = decode_protocol(name,actual_words)
    warnings = {'tapmiss':sum(line.TAPMISS for line in model.lines),
                'late':sum(thread.LATE for thread in model.threads),
                'overrun':sum(thread.OVR for thread in model.threads),
                'starved':sum(stream.STARVED for stream in model.mem.streams),
                'conflict':model.ctrl.CONFLICT,'memory_hazard':model.ctrl.MEMHAZ}
    for key,wanted in metadata.get('warning_assert',{}).items():
        assert warnings[key] == wanted, f'{name}: unexpected {key}: {warnings[key]}'
    assert warnings['conflict']==warnings['memory_hazard']==0, f'{name}: {warnings}'
    if getattr(scenario,'check',None):
        scenario.check(model)
    details={'name':name,'cycles':len(scenario.steps),'wire_cells':len(words),
             'cell_cycles':period,'clock_period_ps':16667,'sampling_after_rise_ps':8000,
             'match_start_cycle':capture_start+offset,'negative_control_rejected':negative_rejected,
             'pin_reference_mismatches':0,'metadata':metadata}
    details['independent_protocol_decode'] = decoded
    details['runtime_warnings'] = warnings
    (out/f'{name}.checked.json').write_text(json.dumps(details,indent=2)+'\n')
    dut._log.info('%s: %d wire cells, %d cycles/cell, pin/reference agreement and negative control passed',
                  name,len(words),period)
