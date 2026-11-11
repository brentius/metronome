"""Read-only review reproductions; no production RTL or tests are modified."""
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(ROOT / 'code/host'), str(ROOT / 'code/md')]
from metronome_tools.asm import assemble_text
from metronome_tools.check import check
from metronome_tools.image import host_writes
from encode import Insn, encode

os.environ['PATH'] = os.pathsep.join([
    'C:/Users/b_yee23/tools/oss-cad-suite/bin',
    'C:/Users/b_yee23/tools/oss-cad-suite/lib', os.environ['PATH']])
program = '''
.engine 0
 core 0
 trigger ALWAYS
 start high0
.end
.engine 1
 core 0
 trigger ALWAYS
 start high1
.end
.engine 2
 core 0
 trigger NONE
 start low
.end
.budget engine 2 cycles 7
.core 0
high0: nop
 pause goto high0
high1: nop
 pause goto high1
low: #165 -> HOST.OUT
 pause goto low
'''
(HERE / 'starvation_v2.mas').write_text(program)
p = assemble_text(program)
report = check(p)
print(report.format(verbose=True), flush=True)
assert report.ok
words = p.words(0)
assignments = '\n'.join(f"dut.u_pmem0.mem[{a}] = 64'h{w:016x};" for a, w in words.items())
pcs = [p.engines[e].start_addr for e in range(3)]
tb = '''
`timescale 1ns/1ps
module review_tb;
reg clk=0, rst_n=0;
wire [7:0] uo, uio, oe;
tt_um_metronome dut(.clk(clk), .rst_n(rst_n), .ena(1'b1), .ui_in(8'd2), .uio_in(8'd0),
 .uo_out(uo), .uio_out(uio), .uio_oe(oe));
always #5 clk=~clk;
integer t, d0=0, d1=0, d2=0;
initial begin
 repeat(3) @(negedge clk);
 rst_n=1;
 ASSIGNMENTS
 dut.u_ctrl.run_g=1;
 dut.g_eng[0].u.en=1; dut.g_eng[0].u.trig=29; dut.g_eng[0].u.pc=PC0; dut.g_eng[0].u.ready=1;
 dut.g_eng[1].u.en=1; dut.g_eng[1].u.trig=29; dut.g_eng[1].u.pc=PC1; dut.g_eng[1].u.ready=1;
 dut.g_eng[2].u.en=1; dut.g_eng[2].u.trig=0; dut.g_eng[2].u.pc=PC2; dut.g_eng[2].u.ready=1;
 for(t=0;t<200;t=t+1) begin
  #1;
  if(dut.c0_disp) begin
   if(t<15) $display("cycle %0d dispatch %0d",t,dut.c0_de);
   case(dut.c0_de) 0:d0=d0+1; 1:d1=d1+1; 2:d2=d2+1; endcase
  end
  @(negedge clk);
 end
 $display("dispatch counts: E0=%0d E1=%0d E2=%0d; E2.READY=%b HOST.OUTV=%b",d0,d1,d2,dut.e_ready[2],dut.outv);
 if(d2 != 0 || !dut.e_ready[2] || dut.outv) $fatal(1,"starvation not reproduced");
 $finish;
end
endmodule
'''.replace('ASSIGNMENTS', assignments)
for e, pc in enumerate(pcs):
    tb = tb.replace(f'PC{e}', str(pc))
(HERE / 'starvation_v2_tb.v').write_text(tb)
args = ['iverilog', '-g2005', '-s', 'review_tb', '-I', str(ROOT / 'code/rtl/gen'),
        '-o', str(HERE / 'starvation_v2.vvp'), *map(str, sorted((ROOT / 'code/rtl').glob('*.v'))),
        str(HERE / 'starvation_v2_tb.v')]
subprocess.run(args, check=True)
subprocess.run(['vvp', str(HERE / 'starvation_v2.vvp')], check=True)

