"""Compare real SPI-loaded Score programs against the cycle model and wire oracles."""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys

import cocotb
from cocotb.triggers import FallingEdge,RisingEdge,Timer

ROOT=Path(os.environ['SCORE_RTL_REPO'])
sys.path.insert(0,str(ROOT/'code/tests/score_rtl'))
import scenarios_score as scenarios
from metronome2.chip import Chip


async def clock(dut):
    dut.clk.value=0
    while True:
        await Timer(8333,unit='ps');dut.clk.value=1
        await Timer(8334,unit='ps');dut.clk.value=0


def sample(signal):return int(signal.value) if signal.value.is_resolvable else None


def zero_memory(dut):
    names=json.loads(os.environ.get('SCORE_SRAM_MAP','{}'))
    for name,size in (('u_pmem0',256),('u_pmem1',256),('u_dmem',512)):
        if names:mem=getattr(dut.user_project,names[name]).i_SRAM_1P_behavioral_bm_bist.memory
        else:mem=getattr(dut,name).u_sram.i_SRAM_1P_behavioral_bm_bist.memory
        for i in range(size):mem[i].value=0


def read_bytes(frames,outputs,size):
    bits=[]
    for i in range(1,len(frames)):
        if frames[i]&1 and not frames[i-1]&1:
            bits.append((outputs[i-2][0] if i>=2 else 0)&1)
    data=bits[24:24+size*8]
    assert len(data)==size*8,'truncated SPI readback'
    return bytes(sum(data[j+k]<<(7-k) for k in range(8)) for j in range(0,len(data),8))


@cocotb.test()
async def compiled_score(dut):
    out=Path(os.environ['SCORE_OUTPUT']);name=os.environ['SCORE_CASE']
    s=scenarios.build(name);model=Chip()
    (out/(name+'.mas')).write_text(s.compiled.mas,encoding='utf-8')
    (out/(name+'.image.json')).write_text(json.dumps(s.compiled.image,indent=2)+'\n')
    (out/(name+'.metadata.json')).write_text(json.dumps(s.metadata,indent=2)+'\n')
    dut.ena.value=1;dut.ui_in.value=2;dut.uio_in.value=0;dut.rst_n.value=1
    zero_memory(dut);cocotb.start_soon(clock(dut))
    trace=[];inputs=[];frames=[];previous=(0,0,0);bad=[]
    for cycle,(ui,hi,uio,rst) in enumerate(s.steps):
        await FallingEdge(dut.clk)
        uio=uio(cycle,previous) if callable(uio) else uio
        hi=hi(cycle,previous) if callable(hi) else hi
        ui=(ui&7)|(hi&248)
        dut.ui_in.value=ui;dut.uio_in.value=uio&255;dut.rst_n.value=rst
        expected=tuple(model.step(ui,uio&255,rst))
        await RisingEdge(dut.clk);await Timer(8000,unit='ps')
        actual=tuple(sample(getattr(dut,k)) for k in ('uo_out','uio_out','uio_oe'))
        if cycle>=s.compare_from and actual!=expected and len(bad)<12:
            bad.append({'cycle':cycle,'rtl':actual,'model':expected})
        trace.append(actual);inputs.append(uio&255);frames.append(ui)
        previous=expected
    (out/(name+'.pins.bin')).write_bytes(bytes(255 if v is None else v for row in trace for v in row))
    (out/(name+'.stimulus.bin')).write_bytes(bytes(v for ui,io in zip(frames,inputs) for v in (ui,io)))
    assert not bad,f'pin/model mismatch: {bad}'
    readbacks=[]
    for read in s.read_expectations:
        start,end=read['start'],read['end']
        actual=read_bytes(frames[start:end],trace[start:end],len(read['data']))
        assert actual==bytes(read['data']),(hex(read['addr']),actual,bytes(read['data']))
        readbacks.append({'addr':read['addr'],'data_hex':actual.hex()})
    checked=scenarios.validate(s,trace,inputs,model)
    checked.update(case=name,cycles=len(s.steps),clock_period_ps=16667,pin_reference_mismatches=0,
                   spi_readbacks=readbacks,host_image_loaded_through_spi=True,
                   sram_preinitialized_to_zero=True)
    (out/(name+'.checked.json')).write_text(json.dumps(checked,indent=2,default=lambda x:x.hex() if isinstance(x,bytes) else str(x))+'\n')
