
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
 dut.u_pmem0.mem[0] = 64'h0000000000000000;
dut.u_pmem0.mem[1] = 64'h0000000000000003;
dut.u_pmem0.mem[2] = 64'h0000000000000000;
dut.u_pmem0.mem[3] = 64'h0000000000000013;
dut.u_pmem0.mem[4] = 64'h000000007c080528;
dut.u_pmem0.mem[5] = 64'h0000000000000023;
 dut.u_ctrl.run_g=1;
 dut.g_eng[0].u.en=1; dut.g_eng[0].u.trig=29; dut.g_eng[0].u.pc=0; dut.g_eng[0].u.ready=1;
 dut.g_eng[1].u.en=1; dut.g_eng[1].u.trig=29; dut.g_eng[1].u.pc=2; dut.g_eng[1].u.ready=1;
 dut.g_eng[2].u.en=1; dut.g_eng[2].u.trig=0; dut.g_eng[2].u.pc=4; dut.g_eng[2].u.ready=1;
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
