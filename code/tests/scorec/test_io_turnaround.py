"""A generated request edge must allow returned data through the input pipeline."""
import pytest
from harness import *
import test_spi

BIND='sck=O8 cs_n=O9 mosi=O10 miso=P1'


@pytest.mark.parametrize('rate',[9e6,10e6])
def test_generated_edge_sample_rejects_insufficient_pin_turnaround(rate):
    with pytest.raises(scorec.CompileError,match='E-TIME-IO'):
        scorec.compile_score(spec_block(2),'controller',BIND,rate_hz=rate)


@pytest.mark.parametrize('rate,late',[(7.5e6,False),(8e6,False),(60e6/7,False),(10e6,True)])
def test_spi_turnaround_exact_received_data(monkeypatch,rate,late):
    original=scorec.compile_score
    def compile_at_rate(source,*args,**kwargs):
        if late:source=(ROOT/'code/score/examples/spi_mode0_late_sample.score').read_text()
        return original(source,*args,**kwargs,rate_hz=rate)
    monkeypatch.setattr(scorec,'compile_score',compile_at_rate)
    monkeypatch.setattr(test_spi,'CPU',round(60e6/rate))
    outgoing=list(range(16));incoming=[(i*73+0xa5)&255 for i in range(16)]
    c,chip,bus=test_spi.run_controller(outgoing,incoming)
    assert bytes(chip.mem.data[0x400:0x410])==bytes(incoming)
    result=Codec(parse(spec_block(2)),rate=rate).decode('peripheral',bus)
    want=[('select',)]+[e for a,b in zip(outgoing,incoming) for e in (('out',a),('in',b))]+[('deselect',)]
    assert result.ok and result.events==want,(result.events,result.notes)
    assert not any(t.LATE or t.OVR for t in chip.threads)
    assert not any(l.TAPMISS for l in chip.lines)
    assert not any(s.STARVED for s in chip.mem.streams)
    assert not chip.ctrl.CONFLICT and not chip.ctrl.MEMHAZ
    if late:
        assert 'sample miso at 75%' in c.score.source
