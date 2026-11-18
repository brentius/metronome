"""Deterministic compiled Score rate sweep against the pure Python cycle model.

Direct configuration is used for the program image; host SPI loading time is not part of these rates.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time, traceback
from pathlib import Path

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True,help='source tree whose compiler/model is exercised')
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args(); repo=a.repo.resolve(); out=a.out.resolve()
    if out.exists(): ap.error('refusing existing output directory')
    out.mkdir(parents=True)
    # Import every package from the selected tree, never the active workspace by accident.
    paths=[repo/'code/tests/scorec',repo/'code/scorec',repo/'code/score',repo/'code/host2',repo/'sim/reference',repo/'code/tests/checkers']
    sys.path[:0]=[str(p) for p in paths]
    from harness import IDLE, HM, new_chip, hostin, stream_reg, stream_rewind, host_writes
    from score import Codec, parse
    import scorec, test_uart, test_spi, test_i2c
    rows=[]
    # Keep representative points small but bracket the practically interesting clocks.
    cases=[('uart_tx',r) for r in (1e6,3e6,6e6,7.5e6,10e6,12e6)] + \
          [('uart_rx',r) for r in (1e6,3e6,3.5e6,4e6,4.5e6,6e6,7.5e6,10e6)] + \
          [('spi_controller',r) for r in (1e6,2e6,5e6,7.5e6,8e6,60e6/7,9e6,10e6,11e6)] + \
          [('i2c_controller',r) for r in (100e3,400e3,500e3,1e6,2e6,2.1e6,2.5e6,3e6,3.4e6,3.5e6,3.6e6,3.75e6,3.8e6,4e6)] + \
          [('ethernet_tx',10e6)] + [('mailbox_lsb',7.5e6),('mailbox_msb',6e6),('mailbox_wide_first',1e6),('spi_controller_late',10e6)]
    spec_u=test_uart.spec_block(0); spec_s=test_spi.spec_block(2); spec_i=test_i2c.spec_block(1)
    source_hashes={str(p.relative_to(repo)):sha(p) for top in paths for p in top.rglob('*') if p.is_file() and p.suffix in ('.py','.score','.md') and '__pycache__' not in p.parts}
    for proto,rate in cases:
        row={'protocol':proto,'rate_hz':int(rate),'clock_hz':60000000,'mode':'reference_model_direct_configuration','status':'ERROR'}
        c=None; score_text=''
        started=time.perf_counter()
        try:
            if proto.startswith('uart'):
                text=score_text=spec_u; role='sender' if proto=='uart_tx' else 'receiver'; bind='tx=O8' if role=='sender' else 'tx=P5'
                c=scorec.compile_score(text,role,bind,rate_hz=rate); row['compile_seconds']=time.perf_counter()-started
                chip=new_chip(c); payload=bytes([0xA5,0x3C]); trace=[]
                if role=='sender':
                    pending=list(payload); n=int(len(payload)*10*60e6/rate+4*60e6/rate)
                    for _ in range(n):
                        if pending and chip.host.INV==0: hostin(chip,pending.pop(0))
                        uo,_,_=chip.step(IDLE,0); trace.append((uo>>2)&1)
                    decoded=Codec(parse(text),rate=rate).decode('receiver',{'tx':trace})
                    assert not pending and decoded.ok and decoded.events==[('data',x) for x in payload],(pending,decoded.notes,decoded.events)
                else:
                    wave=Codec(parse(text),rate=rate).encode_all([('data',x) for x in payload]).bus['tx']
                    for _ in range(40): chip.step(IDLE,1<<5)
                    for lvl in list(wave)+[1]*int(4*60e6/rate): chip.step(IDLE,(lvl&1)<<5)
                    n=chip.mem.streams[0].POS; assert bytes(chip.mem.data[0x400:0x400+n])==payload,(n,chip.mem.data[0x400:0x400+n])
                row['decoded_bytes']=payload.hex()
            elif proto in ('spi_controller','spi_controller_late'):
                # Adapt the established independent codec peer bench to this requested rate.
                score_text=spec_s.replace('sample miso at sck rise','sample miso at 75%') if proto.endswith('_late') else spec_s
                row.update(tx_payload='962d',peer_payload='a53c',bit_order='MSB-first')
                period=max(2,round(60e6/rate)); test_spi.CPU=period
                orig=scorec.compile_score
                def comp(source,*args,**kwargs): kwargs['rate_hz']=rate; return orig(score_text,*args,**kwargs)
                scorec.compile_score=comp
                try: c,chip,bus=test_spi.run_controller([0x96,0x2D],[0xA5,0x3C])
                finally: scorec.compile_score=orig
                want=[('select',),('out',0x96),('in',0xA5),('out',0x2D),('in',0x3C),('deselect',)]
                decoded=Codec(parse(spec_s),rate=rate).decode('peripheral',bus)
                assert decoded.ok and decoded.events==want,(decoded.notes,decoded.events)
                n=chip.mem.streams[1].POS; assert bytes(chip.mem.data[0x400:0x400+n])[:2]==b'\xa5\x3c'
                row['decoded_events']=len(decoded.events)
            elif proto=='i2c_controller':
                score_text=spec_i; row.update(address=0x42,tx_payload='a53c',peer='ACK-write')
                period=max(2,round(60e6/rate)); test_i2c.BEAT=period
                orig=scorec.compile_score
                def comp(*args,**kwargs): kwargs['rate_hz']=rate; return orig(*args,**kwargs)
                scorec.compile_score=comp
                try: c=scorec.compile_score(spec_i,'controller','scl=P0/O0 sda=P1/O1')
                finally: scorec.compile_score=orig
                peer=test_i2c.PyTarget(0x42)
                chip,bus=test_i2c.run_controller(c,[(0x42,'w',b'\xa5\x3c')],peer,extra=4*period)
                decoded=Codec(parse(spec_i),params={'my_addr':0x42},rate=rate).decode('target',test_i2c.ideal(bus))
                assert decoded.ok,(decoded.notes,decoded.events)
                want=test_i2c.expected_events([(0x42,'w',b'\xa5\x3c')],0x42,peer.reads)
                assert decoded.events==want,(decoded.events,want)
                independent=test_i2c.ind.i2c_decode(bus['scl'],bus['sda'])
                assert len(independent)==1 and independent[0].events==test_i2c.checker_view(want)
                assert peer.writes==[0xa5,0x3c] and chip.host.OUTV and chip.host.OUTB==0
                row['decoded_events']=len(decoded.events)
            elif proto=='ethernet_tx':
                import zlib
                text=score_text=__import__('test_ethernet').spec_block(3); body=bytes.fromhex('0123456789abfedcba9876540800')+bytes(range(46))
                c=scorec.compile_score(text,'sender','td=O0 tdn=O1',skip_periodic=True);row['compile_seconds']=time.perf_counter()-started
                chip=new_chip(c);chip.backdoor_write(HM['DATA_BASE'],body)
                stream_reg(chip,0,'LEN',len(body),2);stream_rewind(chip,0)
                for _ in range(80):chip.step(IDLE,0)
                hostin(chip,1);td=[];tdn=[]
                for _ in range((64+8*len(body)+32+2+110)*6+300):
                    uo,uio,_=chip.step(IDLE,0);td.append(uio&1);tdn.append((uio>>1)&1)
                decoded=Codec(parse(text)).decode('receiver',{'td':td});fields={e[0]:e[1] for e in decoded.events if len(e)>1}
                assert decoded.ok and fields.get('body')==body and fields.get('fcs')==zlib.crc32(body),(decoded.notes,fields)
                assert all(x+y==1 for x,y in zip(td,tdn));row['payload_bytes']=len(body);row['crc32']=fields['fcs']
            else:
                from score import Codec,parse
                wide_first=proto=='mailbox_wide_first'
                order='lsb' if proto.endswith('lsb') or wide_first else 'msb'
                fields='wide:u8 narrow:u5' if wide_first else 'narrow:u5 wide:u8'
                text=f'''protocol mailbox_widths\nroles sender, receiver\nwire tx out push-pull idle high by sender\nclock 1 MHz\n  sender: generated\n  receiver: started by tx fall\n  tolerance 3%\nsymbols\n  bit(d) tx "d" sample tx at 50%\nbits {order} first\ngrammar\n  line = frame*\n  frame = bit(0) narrow:u5 wide:u8 bit(1) gap 0 beats\n'''
                text=text.replace('narrow:u5 wide:u8',fields)
                score_text=text
                pairs=[(0x15,0xa6),(0x03,0x5b),(0x1c,0xe1)]
                c=scorec.compile_score(text,'sender','tx=O8',rate_hz=rate);row['compile_seconds']=time.perf_counter()-started
                chip=new_chip(c);pending=[v for a,b in pairs for v in ((b,a) if wide_first else (a,b))];trace=[]
                for _ in range(int(3*20*60e6/rate)+500):
                    if pending and chip.host.INV==0:hostin(chip,pending.pop(0))
                    uo,_,_=chip.step(IDLE,0);trace.append((uo>>2)&1)
                decoded=Codec(parse(text),rate=rate).decode('receiver',{'tx':trace})
                got=[e for e in decoded.events if e[0] in ('narrow','wide')]
                want=[e for a,b in pairs for e in ((('wide',b),('narrow',a)) if wide_first else (('narrow',a),('wide',b)))]
                assert not pending and decoded.ok and got==want,(pending,decoded.notes,got,want)
                row['payload_bytes']=len(pairs)*2;row['decoded_events']=len(got)
            if proto.startswith('spi_controller') or proto=='i2c_controller':
                from collections import Counter
                wire=bus['sck'] if proto.startswith('spi_controller') else bus['scl']
                falls=[i for i in range(1,len(wire)) if wire[i-1] and not wire[i]]
                periods=Counter(b-a for a,b in zip(falls,falls[1:]))
                row['clock_fall_period_cycles']=dict(sorted(periods.items()))
                row['observed_cycles']=len(wire)
                if periods:row['modal_wire_clock_hz']=60e6/periods.most_common(1)[0][0]
            flags={'late':sum(t.LATE for t in chip.threads),'overrun':sum(t.OVR for t in chip.threads),
                   'tapmiss':sum(l.TAPMISS for l in chip.lines),'starved':sum(s.STARVED for s in chip.mem.streams),
                   'conflict':chip.ctrl.CONFLICT,'memory_hazard':chip.ctrl.MEMHAZ}
            assert not any(flags.values()),flags
            row['program_words']=sum(len(words) for words in c.program.code.values())
            row.update(status='PASS',runtime_flags=flags)
        except Exception as e:
            msg=str(e)
            if e.__class__.__name__=='CompileError': row.update(status='COMPILE_REJECT',diagnostic=msg,compile_seconds=time.perf_counter()-started)
            else: row.update(status='RUNTIME_FAIL',error=repr(e),traceback=traceback.format_exc())
        row['total_seconds']=time.perf_counter()-started; rows.append(row)
        case_dir=out/'cases'/f"{proto}_{int(rate)}";case_dir.mkdir(parents=True,exist_ok=True)
        if score_text: (case_dir/'source.score').write_text(score_text,encoding='utf-8')
        if c is not None:
            (case_dir/'program.mas').write_text(c.mas,encoding='utf-8')
            (case_dir/'fit_report.txt').write_text(c.report,encoding='utf-8')
            (case_dir/'image.json').write_text(json.dumps(c.image,indent=2)+'\n',encoding='utf-8')
            (case_dir/'host_writes.json').write_text(json.dumps([{'addr':addr,'data_hex':data.hex(),'note':note} for addr,data,note in host_writes(c.program)],indent=2)+'\n',encoding='utf-8')
        (case_dir/'result.json').write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
        (out/f"{proto}_{int(rate)}.json").write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
    result={'repo':str(repo),'benchmark_sha256':sha(Path(__file__)),'source_hashes':source_hashes,'clock_hz':60000000,'results':rows,
            'summary':{s:sum(r['status']==s for r in rows) for s in ('PASS','COMPILE_REJECT','RUNTIME_FAIL','ERROR')},
            'limitations':['Pure reference-model configuration; no RTL, gates, hardware or host-link throughput. Highest tested passing point is not a validated maximum. I2C values above 1 MHz are arbitrary compiler/model stress points, not standard-mode claims.']}
    current_hashes={name:sha(repo/name) for name in source_hashes}
    changed=[name for name,wanted in source_hashes.items() if current_hashes[name]!=wanted]
    result['changed_sources_during_run']=changed
    if changed:
        for r in rows:
            if r['status']=='PASS': r.update(status='ERROR',error='source changed during benchmark: '+', '.join(changed))
        result['summary']={s:sum(r['status']==s for r in rows) for s in ('PASS','COMPILE_REJECT','RUNTIME_FAIL','ERROR')}
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    (out/'benchmark.py').write_bytes(Path(__file__).read_bytes())
    print(json.dumps(result['summary'],sort_keys=True))
    return int(any(r['status'] in ('RUNTIME_FAIL','ERROR') for r in rows))
if __name__=='__main__': raise SystemExit(main())
