"""Independent wire-level decoders for the campaign's documented bounded frames.

No imports from the assembler, DUT model, or waveform builders. These establish
framing/data validity separately from the exact waveform playback comparison.
They deliberately do not implement complete endpoints or analog PHY behavior.
"""
from __future__ import annotations

import binascii


def packed(bits, lsb=False):
    assert len(bits)%8==0, f'non-byte-aligned data: {len(bits)} bits'
    return bytes(sum(b << (i if lsb else 7-i) for i,b in enumerate(bits[j:j+8]))
                 for j in range(0,len(bits),8))


def edges(words,clock=0,data=1,rising=True):
    result=[]
    for a,b in zip(words,words[1:]):
        old=(a>>clock)&1; new=(b>>clock)&1
        if old!=new and new==int(rising): result.append((b>>data)&1)
    return result


def crc_usb(data):
    reg=0xffff
    for value in data:
        for bit in range(8):
            feedback=(reg^(value>>bit))&1
            reg>>=1
            if feedback: reg^=0xa001
    return reg^0xffff


def validate(name,words):
    """Decode actual observed pin cells and enforce this case's fixed payload."""
    assert words, 'empty wire trace'
    if name=='uart':
        b=[w&1 for w in words]
        assert b[:2]==[1,1]
        frames=b[2:]
        assert len(frames)==20
        got=[]
        for i in (0,10):
            assert frames[i]==0 and frames[i+9]==1, 'UART framing error'
            got.append(sum(frames[i+1+k]<<k for k in range(8)))
        assert got==[0xa6,0x39], got
        return {'bytes_hex':bytes(got).hex(),'framing':'8N1'}
    if name.startswith('spi_mode'):
        mode=int(name[-1]); cpol=mode>>1; cpha=mode&1
        assert words[0]&4 and words[-1]&4, 'SPI CS must frame transaction'
        assert words[0]&1==cpol and words[-1]&1==cpol, 'SPI CPOL idle incorrect'
        active=[w for w in words if not w&4]
        samples=[]; previous=words[0]
        for word in active:
            old=previous&1; new=word&1
            sampling=(new!=old and new==(cpol if cpha else 1-cpol))
            if sampling: samples.append((word>>1)&1)
            previous=word
        data=packed(samples)
        assert data==bytes.fromhex('962d'), f'SPI mode{mode} decoded {data.hex()}'
        return {'bytes_hex':data.hex(),'mode':mode}
    if name.startswith('i2c_'):
        starts=[]; stops=[]
        for i,(a,b) in enumerate(zip(words,words[1:]),1):
            if (a&1) and (b&1) and ((a^b)&2):
                (starts if (a&2) else stops).append(i)
        assert len(starts)==len(stops)==1 and starts[0]<stops[0], 'I2C START/STOP invalid'
        samples=[]
        for a,b in zip(words[starts[0]:stops[0]],words[starts[0]+1:stops[0]+1]):
            if not a&1 and b&1: samples.append((b>>1)&1)
        # A low-to-high SCL used to prepare STOP is not a data clock.
        if len(samples)==19: samples=samples[:-1]
        assert len(samples)==18, f'I2C expected two nine-clock groups, got {len(samples)}'
        data=packed(samples[:8]+samples[9:17])
        assert data==bytes.fromhex('a0a5') and samples[8]==samples[17]==0, 'I2C address/data/ACK mismatch'
        return {'address':0x50,'write_data_hex':'a5','ack_bits':[samples[8],samples[17]],
                'scope':'precomputed combined bus waveform; ACK is replayed, not a target response'}
    if name=='usb_ls':
        assert words[:2] in ([2,2],[1,1]), 'USB idle missing'
        idle=words[0]
        eop=next((i for i in range(2,len(words)-2) if words[i]==words[i+1]==0),None)
        assert eop is not None and words[eop+2]==idle, 'USB SE0 EOP/J invalid'
        level=idle; stuffed=[]
        for state in words[2:eop]:
            assert state in (1,2), 'USB illegal differential state'
            stuffed.append(int(state==level)); level=state
        raw=[]; ones=0; i=0
        while i<len(stuffed):
            bit=stuffed[i]; raw.append(bit); i+=1
            ones=ones+1 if bit else 0
            if ones==6:
                assert i<len(stuffed) and stuffed[i]==0, 'USB stuffing error'
                i+=1; ones=0
        data=packed(raw,lsb=True)
        assert data[:3]==bytes.fromhex('80c35a'), f'USB SYNC/PID/payload {data.hex()}'
        assert (data[1]>>4)==((data[1]&15)^15), 'USB PID complement error'
        assert len(data)==5, 'USB DATA0 waveform must include its CRC16'
        assert int.from_bytes(data[-2:],'little')==crc_usb(data[2:-2]), 'USB DATA CRC16 mismatch'
        scope='DATA0 packet waveform with host-generated CRC16'
        return {'decoded_hex':data.hex(),'scope':scope}
    if name=='ethernet_10baset':
        assert len(words)%2==0
        bits=[]
        for a,b in zip(words[::2],words[1::2]):
            assert a in (1,2) and b in (1,2) and a!=b, 'Manchester coding error'
            bits.append(1-(a&1))
        data=packed(bits,lsb=True)
        assert data==b'\x55'*7+bytes.fromhex('d512a6'), f'Ethernet decoded {data.hex()}'
        return {'decoded_hex':data.hex(),'scope':'10M Manchester/preamble/SFD/pattern; no full MAC frame/FCS'}
    if name=='jtag':
        # IEEE1149.1 TAP transitions, indexed by sampled TMS.
        transitions={'RESET':('IDLE','RESET'),'IDLE':('IDLE','SELECT_DR'),
                     'SELECT_DR':('CAPTURE_DR','SELECT_IR'),'CAPTURE_DR':('SHIFT_DR','EXIT1_DR'),
                     'SHIFT_DR':('SHIFT_DR','EXIT1_DR'),'EXIT1_DR':('PAUSE_DR','UPDATE_DR'),
                     'PAUSE_DR':('PAUSE_DR','EXIT2_DR'),'EXIT2_DR':('SHIFT_DR','UPDATE_DR'),
                     'UPDATE_DR':('IDLE','SELECT_DR'),'SELECT_IR':('CAPTURE_IR','RESET'),
                     'CAPTURE_IR':('SHIFT_IR','EXIT1_IR'),'SHIFT_IR':('SHIFT_IR','EXIT1_IR'),
                     'EXIT1_IR':('PAUSE_IR','UPDATE_IR'),'PAUSE_IR':('PAUSE_IR','EXIT2_IR'),
                     'EXIT2_IR':('SHIFT_IR','UPDATE_IR'),'UPDATE_IR':('IDLE','SELECT_DR')}
        state='RESET'; scan=[]; sampled_tms=[]
        for a,b in zip(words,words[1:]):
            if not a&1 and b&1:
                tms=(b>>1)&1; sampled_tms.append(tms)
                if state=='SHIFT_DR': scan.append((b>>2)&1)
                state=transitions[state][tms]
        assert sampled_tms[:5]==[1]*5 and state=='IDLE' and scan==[0]*32, (state,len(scan))
        return {'dr_shift_bits':len(scan),'final_tap_state':state,'scope':'TCK/TMS/TDI playback; no TDO target'}
    if name=='swd':
        samples=edges(words)
        # This bounded request follows four idle clocks.
        assert samples[:4]==[1]*4 and len(samples)>=12
        req=samples[4:12]
        assert req[0]==1 and req[6:]==[0,1], 'SWD start/stop/park error'
        assert (sum(req[1:5])&1)==req[5], 'SWD request parity error'
        assert req[1:5]==[1,0,1,0], 'SWD AP/write/address fields incorrect'
        return {'request_bits':req,'scope':'host request only; no target ACK/data phase'}
    if name=='ps2':
        samples=edges(words,rising=False)
        # The first low cell begins the two-clock idle preamble; it has no prior
        # clock edge inside the capture window.
        frame=samples[-11:]
        assert len(frame)==11 and frame[0]==0 and frame[-1]==1, 'PS/2 framing error'
        assert sum(frame[1:10])%2==1, 'PS/2 odd parity error'
        data=sum(frame[1+i]<<i for i in range(8))
        assert data==0x5a, f'PS/2 data {data:#x}'
        return {'byte_hex':f'{data:02x}'}
    if name=='can':
        raw=[]; previous=None; run=0; i=0
        while len(raw)<42:
            assert i<len(words), 'truncated CAN frame'
            b=words[i]&1; i+=1; raw.append(b)
            run=run+1 if b==previous else 1; previous=b
            if run==5:
                assert i<len(words) and (words[i]&1)!=b, 'CAN stuffing error'
                previous=words[i]&1; run=1; i+=1
        value=lambda b: int(''.join(str(x) for x in b),2)
        assert raw[0]==0 and value(raw[1:12])==0x123 and raw[12:15]==[0,0,0]
        assert value(raw[15:19])==1 and value(raw[19:27])==0xa5
        # Polynomial long division of message*x^15; independent of the encoder's
        # running register implementation.
        dividend=value(raw[:27])<<15; polynomial=(1<<15)|0x4599
        while dividend.bit_length()>=polynomial.bit_length():
            dividend^=polynomial<<(dividend.bit_length()-polynomial.bit_length())
        assert value(raw[27:42])==dividend, 'CAN CRC15 mismatch'
        tail=[x&1 for x in words[i:]]
        assert len(tail)>=10 and tail[0]==1 and tail[2:10]==[1]*8, 'CAN delimiters/EOF error'
        return {'id_hex':'123','data_hex':'a5','acknowledged':tail[1]==0,
                'scope':'single frame waveform; no arbitration/error/retransmission engine'}
    if name=='custom_hdlc':
        flag=[0,1,1,1,1,1,1,0]
        b=[w&1 for w in words]
        assert b[:2]==[1,1] and b[2:10]==flag and b[-10:-2]==flag
        stuffed=b[10:-10]; raw=[]; ones=0; i=0
        while i<len(stuffed):
            bit=stuffed[i]; raw.append(bit); i+=1; ones=ones+1 if bit else 0
            if ones==5:
                assert i<len(stuffed) and stuffed[i]==0, 'custom HDLC stuffing error'
                i+=1; ones=0
        data=packed(raw)
        assert data[:-2]==bytes.fromhex('7e7da5')
        assert int.from_bytes(data[-2:],'big')==binascii.crc_hqx(data[:-2],0xffff), 'custom CRC16 error'
        return {'payload_hex':data[:-2].hex(),'crc_hex':data[-2:].hex()}
    if name=='custom_diffman':
        body=words[:-2]; level=1; raw=[]
        assert len(body)==48
        for a,b in zip(body[::2],body[1::2]):
            assert a in (1,2) and b in (1,2) and a!=b, 'differential Manchester mid-cell error'
            first=a&1; raw.append(int(first==level)); level=b&1
        data=packed(raw,lsb=True)
        assert data==bytes.fromhex('55d53c'), data.hex()
        return {'payload_hex':data.hex()}
    raise AssertionError(f'No independent decoder for {name}')
