"""Actual Score -> assembler -> SPI-loaded program scenarios, with independent peers.

These programs execute protocol decisions and CRCs; they are not unrolled GPIO
waveform tables. Images and readback use the SPI pins. The bench initializes
SRAM to zero for reproducibility; it does not prove unknown-memory startup.
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import sys
import zlib

ROOT=Path(os.environ.get('SCORE_RTL_REPO',Path(__file__).resolve().parents[3]))
for path in ('code/scorec','code/score','code/host2','sim/reference','code/tests/lockstep_v2',
             'code/tests/scorec','code/tests/checkers'):
    sys.path.insert(0,str(ROOT/path))
import scenarios as base
import scorec
from score import Codec,parse
from metronome2_tools.image import host_writes
from test_i2c import PyTarget,controller_tx,controller_rx,target_rx,checker_view,want_records
import protocols as independent

HM=base.HM


def spec_block(index):
    text=(ROOT/'wiki/SPEC_V2_SCORE.md').read_text(encoding='utf-8')
    section=text.split('## 16. Examples')[1].split('## 17.')[0]
    return re.findall(r'```\n(.*?)```',section,re.S)[index]


def flags(chip):
    return {'late':sum(t.LATE for t in chip.threads),'overrun':sum(t.OVR for t in chip.threads),
            'tapmiss':sum(l.TAPMISS for l in chip.lines),'starved':sum(s.STARVED for s in chip.mem.streams),
            'conflict':chip.ctrl.CONFLICT,'memory_hazard':chip.ctrl.MEMHAZ}


class Scenario(base.Scn):
    def __init__(self,name,compiled,idle=0):
        super().__init__(name,half=8) # documented host SCK=clk/16; no fast/backdoor loader
        self.compiled=compiled; self.uio=idle; self.reset()
        for addr,data,_ in host_writes(compiled.program): self.write(addr,data)
        self.idle(80)
        self.capture_start=len(self.steps)
        self.read_expectations=[]
        self.expected_status=None

    def expect_read(self,addr,data):
        start=len(self.steps); self.read(addr,len(data))
        self.read_expectations.append({'start':start,'end':len(self.steps),'data':list(data),'addr':addr})

    def finish(self):
        self.capture_end=len(self.steps)
        self.readback_all()
        if self.expected_status is not None:
            self.expect_read(HM['CTRL_BASE']+5,bytes([self.expected_status]))
        self.metadata={'name':self.name,'capture_start':self.capture_start,'capture_end':self.capture_end,
                       'expected_status':self.expected_status,'reads':self.read_expectations,
                       'compiled_report':self.compiled.report,'host':self.compiled.host}
        return self


def prep_tx(s,data):
    s.data(0,data);s.blk('STREAM',0,LEN=len(data));s.blk('SRT',0,CTL=1);s.idle(40)


def uart_tx(rate):
    c=scorec.compile_score(spec_block(0),'sender','tx=O8',rate_hz=rate)
    s=Scenario(f'uart_tx_{int(rate)}',c)
    s.rate=rate;s.payload=b'\xa5\x3c'
    for value in s.payload:
        s.blk('CTRL',HOSTIN=value)
        s.idle(int(14*60e6/rate)+80)
    return s.finish()


def mixed_mailbox():
    from test_mailbox_widths import mailbox_score
    # The single-byte mailbox is not a FIFO. SPI must supply the second
    # field after the first is consumed and before that field is needed.
    text=mailbox_score('lsb');rate=100e3;period=int(60e6/rate)
    c=scorec.compile_score(text,'sender','tx=O8',rate_hz=rate)
    s=Scenario('mixed_mailbox',c)
    s.score_text=text;s.rate=rate;s.pairs=[(0x15,0xa6),(3,0x5b),(0x1c,0xe1)]
    for a,b in s.pairs:
        s.blk('CTRL',HOSTIN=a);s.idle(3*period)
        s.blk('CTRL',HOSTIN=b);s.idle(16*period)
    s.idle(period)
    return s.finish()


def uart_rx(rate,fault=None):
    text=spec_block(0)
    c=scorec.compile_score(text,'receiver','tx=P5',rate_hz=rate)
    s=Scenario(f'uart_rx_{int(rate)}'+('_'+fault if fault else ''),c,idle=1<<5)
    s.rate=rate;s.payload=b'\x00\xff\xa5' if not fault else b'\x12'
    peer_rate=rate*(1.12 if fault=='tempo' else 1)
    waveform=list(Codec(parse(text),rate=peer_rate).encode_all([('data',v) for v in s.payload]).bus['tx'])
    if fault=='stop':
        period=60e6/rate
        start=next(i for i in range(1,len(waveform)) if waveform[i-1]==1 and waveform[i]==0)
        for i in range(int(start+9*period)+2,min(int(start+10*period)-1,len(waveform))):waveform[i]=0
    for level in waveform:
        s.uio=(level&1)<<5;s.idle(1)
    s.uio=1<<5;s.idle(int(5*60e6/rate)+150)
    s.expected_status=2 if fault=='stop' else None if fault=='tempo' else 0
    if fault!='tempo':s.expect_read(HM['DATA_BASE']+0x400,s.payload)
    s.fault=fault
    return s.finish()


def ethernet_tx():
    text=spec_block(3)
    c=scorec.compile_score(text,'sender','td=O0 tdn=O1',skip_periodic=True)
    s=Scenario('ethernet_tx',c)
    # One complete minimum-length MAC body, including header and46 payloadbytes.
    s.payload=bytes.fromhex('0123456789abfedcba9876540800')+bytes(range(46))
    prep_tx(s,s.payload);s.capture_start=len(s.steps)
    s.blk('CTRL',HOSTIN=1)
    s.idle((64+8*len(s.payload)+32+120)*6+500)
    return s.finish()


def ethernet_rx(corrupt=False):
    text=spec_block(3)
    c=scorec.compile_score(text,'receiver','td=P2 tdn=P3',skip_periodic=True)
    s=Scenario('ethernet_rx_bad_crc' if corrupt else 'ethernet_rx',c)
    s.payload=bytes(range(20))
    crc=zlib.crc32(s.payload)
    events=[('body',s.payload)]+([('fcs',crc^1)] if corrupt else [])
    wave=Codec(parse(text)).encode_all(events).bus['td']
    for level in wave:
        s.uio=((level&1)<<2)|((1-(level&1))<<3);s.idle(1)
    s.uio=0;s.idle(2500)
    s.expected_status=4 if corrupt else 0
    s.expect_read(HM['DATA_BASE']+0x400,s.payload+(crc^int(corrupt)).to_bytes(4,'little'))
    return s.finish()


def spi_controller(rate,late=False):
    text=(ROOT/'code/score/examples/spi_mode0_late_sample.score').read_text() if late else spec_block(2)
    c=scorec.compile_score(text,'controller','sck=O8 cs_n=O9 mosi=O10 miso=P1',rate_hz=rate)
    s=Scenario(f'spi_controller_{int(rate)}'+('_late' if late else ''),c)
    s.payload=b'\x96\x2d';s.peer_payload=b'\xa5\x3c';s.rate=rate
    prep_tx(s,s.payload);s.blk('STREAM',1,LEN=64);s.blk('SRT',1,CTL=1)
    state={'sck':0,'cs':1,'bit':0,'level':0}
    bits=[(v>>i)&1 for v in s.peer_payload for i in range(7,-1,-1)]
    def peer(t,outs):
        clock=(outs[0]>>2)&1;cs=(outs[0]>>3)&1
        if state['cs'] and not cs:state['bit']=0;state['level']=bits[0]
        elif not cs and state['sck'] and not clock:
            state['bit']+=1;state['level']=bits[state['bit']] if state['bit']<len(bits) else 0
        state['sck']=clock;state['cs']=cs
        return state['level']<<1
    s.uio=peer;s.capture_start=len(s.steps);s.blk('CTRL',HOSTIN=1)
    s.idle(int((len(s.payload)*8+10)*60e6/rate)+300)
    s.expect_read(HM['DATA_BASE']+0x400,s.peer_payload)
    return s.finish()


def i2c_controller(rate,nack=False,stretch=False):
    c=scorec.compile_score(spec_block(1),'controller','scl=P0/O0 sda=P1/O1',rate_hz=rate)
    s=Scenario(f'i2c_controller_{int(rate)}'+('_nack' if nack else '_stretch' if stretch else ''),c,idle=3)
    my=0x42
    s.requests=[(my^int(nack),'w',b'\xa5\x3c')]
    peer=PyTarget(my,rbytes=b'\x96\x0f',stretch=int(3*60e6/rate) if stretch else 0)
    tx=controller_tx(s.requests);prep_tx(s,tx);s.blk('SRT',1,CTL=1)
    def drive(t,outs):
        oe,out=outs[2],outs[1]
        scl=int(not(oe&1 and not out&1) and peer.scl!=0)
        sda=int(not(oe&2 and not out&2) and peer.sda!=0)
        peer.step(scl,sda)
        return scl|(sda<<1)
    s.uio=drive;s.rate=rate;s.capture_start=len(s.steps);s.blk('CTRL',HOSTIN=1)
    s.idle(int((40+(4 if stretch else 0))*60e6/rate)+200)
    s.expected_status=int(nack)
    s.nack=nack;s.peer=peer
    return s.finish()


def i2c_target(rate):
    my=0x33;text=spec_block(1)
    c=scorec.compile_score(text,'target','scl=P0 sda=P1/O1',follow_period=2400,rate_hz=rate,params={'my_addr':my})
    s=Scenario(f'i2c_target_{int(rate)}',c,idle=3)
    s.payload=b'\xa5\x5a';prep_tx(s,s.payload);s.blk('SRT',1,CTL=1)
    s.events=[('start',),('addr',my),('rw',1),('ack',0),('data',0xa5),('more',0),
              ('data',0x5a),('more',1),('stop',)]
    enc=Codec(parse(text),params={'my_addr':my},rate=rate).encode_all(s.events)
    peer=enc.drives['controller'];start=len(s.steps)
    def drive(t,outs):
        i=min(t-start,peer.n-1)
        scl=int(peer['scl'][i]!=0)
        sda=int(peer['sda'][i]!=0 and not(outs[2]&2 and not outs[1]&2))
        return scl|(sda<<1)
    s.uio=drive;s.rate=rate;s.capture_start=start;s.idle(peer.n)
    s.uio=3;s.idle(int(4*60e6/rate))
    return s.finish()


BUILDERS={
    'mixed_mailbox':mixed_mailbox,
    'uart_tx_1000000':lambda:uart_tx(1e6),'uart_tx_10000000':lambda:uart_tx(10e6),
    'uart_rx_1000000':lambda:uart_rx(1e6),'uart_rx_3000000':lambda:uart_rx(3e6),
    'uart_rx_1000000_stop':lambda:uart_rx(1e6,'stop'),
    'ethernet_tx':ethernet_tx,'ethernet_rx':ethernet_rx,'ethernet_rx_bad_crc':lambda:ethernet_rx(True),
    'spi_controller_1000000':lambda:spi_controller(1e6),'spi_controller_5000000':lambda:spi_controller(5e6),
    'spi_controller_8571428':lambda:spi_controller(60e6/7),
    'spi_controller_10000000_late':lambda:spi_controller(10e6,late=True),
    'i2c_controller_100000':lambda:i2c_controller(100e3),
    'i2c_controller_3750000':lambda:i2c_controller(3.75e6),
    'i2c_controller_3750000_stretch':lambda:i2c_controller(3.75e6,stretch=True),
    'i2c_controller_400000_stretch':lambda:i2c_controller(400e3,stretch=True),
    'i2c_controller_100000_nack':lambda:i2c_controller(100e3,nack=True),
    'i2c_target_100000':lambda:i2c_target(100e3),'i2c_target_400000':lambda:i2c_target(400e3)}


def build(name):return BUILDERS[name]()


def validate(s,trace,inputs,model):
    a,b=s.capture_start,s.capture_end
    observed=trace[a:b];driven=inputs[a:b]
    name=s.name;details={}
    if name=='mixed_mailbox':
        result=Codec(parse(s.score_text),rate=s.rate).decode('receiver',{'tx':[(o[0]>>2)&1 for o in observed]})
        want=[e for a,b in s.pairs for e in (('narrow',a),('wide',b))]
        assert result.ok and [e for e in result.events if e[0] in ('narrow','wide')]==want,(result.events,result.notes)
        details['events']=result.events
    elif name.startswith('uart_tx'):
        wire=[(o[0]>>2)&1 for o in observed]
        result=Codec(parse(spec_block(0)),rate=s.rate).decode('receiver',{'tx':wire})
        assert result.ok and result.events==[('data',v) for v in s.payload],(result.events,result.notes)
        details['events']=result.events
    elif name=='ethernet_tx':
        wire=[o[1]&1 for o in observed]
        result=Codec(parse(spec_block(3))).decode('receiver',{'td':wire})
        assert result.ok,result.notes
        fields={e[0]:e[1] for e in result.events if len(e)>1}
        assert fields['body']==s.payload and fields['fcs']==zlib.crc32(s.payload)
        assert all((o[1]&1)!=((o[1]>>1)&1) for o in observed)
        details['body_hex']=s.payload.hex();details['crc32']=fields['fcs']
    elif name.startswith('spi_controller'):
        bus={'sck':[(o[0]>>2)&1 for o in observed],'cs_n':[(o[0]>>3)&1 for o in observed],
             'mosi':[(o[0]>>4)&1 for o in observed],'miso':[(i>>1)&1 for i in driven]}
        result=Codec(parse(spec_block(2)),rate=s.rate).decode('peripheral',bus)
        want=[('select',)]+[e for x,y in zip(s.payload,s.peer_payload) for e in (('out',x),('in',y))]+[('deselect',)]
        assert result.ok and result.events==want,(result.events,result.notes)
        details['events']=result.events
    elif name.startswith('i2c_'):
        assert not any(o[1]&o[2]&3 for o in observed),'open-drain output drives high'
        bus={'scl':[i&1 for i in driven],'sda':[(i>>1)&1 for i in driven]}
        decoded=independent.i2c_decode(bus['scl'],bus['sda'])
        assert len(decoded)==1,decoded
        if name.startswith('i2c_controller'):
            address=s.requests[0][0]
            want=[('S',),('B',address<<1,not s.nack)]
            if not s.nack:want += [('B',v,True) for v in s.requests[0][2]]
            want += [('P',)]
        else:
            want=checker_view(s.events)
            fall=None;holds=[]
            for i in range(1,len(observed)):
                if bus['scl'][i-1] and not bus['scl'][i]:fall=i
                if (observed[i][2]^observed[i-1][2])&2:
                    assert not bus['scl'][i] and fall is not None,'target drive changes while SCL high'
                    holds.append(i-fall)
            assert holds and min(holds)>=18,holds
            details['minimum_target_oe_hold_cycles']=min(holds)
        assert decoded[0].events==want,(decoded[0].events,want)
        details['events']=decoded[0].events
    else:
        details['receive_checked_via_spi']=True
    if s.expected_status is not None:
        assert model.host.OUTB==s.expected_status,(model.host.OUTB,s.expected_status)
    state=flags(model)
    assert not any(state.values()),state
    details['runtime_flags']=state
    return details
