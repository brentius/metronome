"""Loading a checked image over the real SPI protocol must not create startup faults."""
import pytest
from harness import Chip,IDLE,scorec,spec_block
from metronome2.spi import write_frames
from metronome2_tools.image import host_writes


@pytest.mark.parametrize('index,role,bind,kwargs,idle',[
    (0,'sender','tx=O8',{'rate_hz':1e6},0),
    (3,'sender','td=O0 tdn=O1',{'skip_periodic':True},0),
])
def test_spi_image_load_activates_dispatch_before_generated_line(index,role,bind,kwargs,idle):
    compiled=scorec.compile_score(spec_block(index),role,bind,**kwargs)
    chip=Chip()
    for _ in range(10):chip.step(IDLE,idle,0)
    for _ in range(8):chip.step(IDLE,idle,1)
    for address,data,_ in host_writes(compiled.program):
        for ui in write_frames(address,data,half_period=8):chip.step(ui,idle)
    for _ in range(80):chip.step(IDLE,idle)
    assert not any(t.LATE or t.OVR for t in chip.threads),[(t.LATE,t.OVR) for t in chip.threads]
    assert not chip.ctrl.CONFLICT and not chip.ctrl.MEMHAZ
