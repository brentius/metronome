`ifndef VERILATOR
module testbench;
  reg [4095:0] vcdfile;
  reg clock;
`else
module testbench(input clock, output reg genclock);
  initial genclock = 1;
`endif
  reg genclock = 1;
  reg [31:0] cycle = 0;
  reg [0:0] PI_mv_we;
  reg [4:0] PI_h_roff;
  reg [15:0] PI_pin_fall;
  reg [15:0] PI_pin_rise;
  reg [0:0] PI_rst_n;
  reg [0:0] PI_h_we;
  reg [7:0] PI_h_wd;
  reg [4:0] PI_h_off;
  wire [0:0] PI_clk = clock;
  reg [2:0] PI_mv_d;
  md_beatgen UUT (
    .mv_we(PI_mv_we),
    .h_roff(PI_h_roff),
    .pin_fall(PI_pin_fall),
    .pin_rise(PI_pin_rise),
    .rst_n(PI_rst_n),
    .h_we(PI_h_we),
    .h_wd(PI_h_wd),
    .h_off(PI_h_off),
    .clk(PI_clk),
    .mv_d(PI_mv_d)
  );
`ifndef VERILATOR
  initial begin
    if ($value$plusargs("vcd=%s", vcdfile)) begin
      $dumpfile(vcdfile);
      $dumpvars(0, testbench);
    end
    #5 clock = 0;
    while (genclock) begin
      #5 clock = 0;
      #5 clock = 1;
    end
  end
`endif
  initial begin
`ifndef VERILATOR
    #1;
`endif
    // UUT.$auto$async2sync.\cc:116:execute$567  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$573  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$579  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$585  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$591  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$597  = 1'b1;
    UUT.arm = 1'b0;
    UUT.edg = 6'b110000;
    UUT.fv_props.p_accept = 1'b0;
    UUT.fv_props.p_beat = 1'b0;
    UUT.fv_props.p_rstn = 1'b0;
    UUT.fv_props.p_start = 1'b0;
    UUT.fv_props.pv = 1'b0;
    UUT.inc = 16'b1111111111111110;
    UUT.mod = 16'b1111111111111111;
    UUT.ph = 16'b0000000000000001;
    UUT.pre = 16'b0000000000000000;
    UUT.ren = 1'b1;
    UUT.run = 1'b1;
    UUT.sc = 1'b0;
    UUT.sp = 1'b0;
    UUT.t0 = 16'b0000000000000000;
    UUT.t1 = 16'b0000000000000000;
    UUT.t2 = 16'b0000000000000000;
    UUT.wen = 1'b1;
    UUT.whi = 16'b1111111111111111;
    UUT.wlo = 16'b0000000000000011;

    // state 0
    PI_mv_we = 1'b0;
    PI_h_roff = 5'b00000;
    PI_pin_fall = 16'b1010101010101011;
    PI_pin_rise = 16'b1010101010101011;
    PI_rst_n = 1'b0;
    PI_h_we = 1'b0;
    PI_h_wd = 8'b00000000;
    PI_h_off = 5'b00000;
    PI_mv_d = 3'b000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_mv_we <= 1'b1;
      PI_h_roff <= 5'b00000;
      PI_pin_fall <= 16'b0000000000000000;
      PI_pin_rise <= 16'b0000000000000000;
      PI_rst_n <= 1'b1;
      PI_h_we <= 1'b1;
      PI_h_wd <= 8'b11100000;
      PI_h_off <= 5'b10011;
      PI_mv_d <= 3'b110;
    end

    // state 2
    if (cycle == 1) begin
      PI_mv_we <= 1'b0;
      PI_h_roff <= 5'b00000;
      PI_pin_fall <= 16'b1010101010101011;
      PI_pin_rise <= 16'b1010101010101011;
      PI_rst_n <= 1'b1;
      PI_h_we <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_h_off <= 5'b00000;
      PI_mv_d <= 3'b000;
    end

    // state 3
    if (cycle == 2) begin
      PI_mv_we <= 1'b0;
      PI_h_roff <= 5'b00000;
      PI_pin_fall <= 16'b0000000000000000;
      PI_pin_rise <= 16'b0000000000000000;
      PI_rst_n <= 1'b0;
      PI_h_we <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_h_off <= 5'b00000;
      PI_mv_d <= 3'b000;
    end

    // state 4
    if (cycle == 3) begin
      PI_mv_we <= 1'b0;
      PI_h_roff <= 5'b00000;
      PI_pin_fall <= 16'b0000000000000000;
      PI_pin_rise <= 16'b0000000000000000;
      PI_rst_n <= 1'b0;
      PI_h_we <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_h_off <= 5'b00000;
      PI_mv_d <= 3'b000;
    end

    genclock <= cycle < 4;
    cycle <= cycle + 1;
  end
endmodule
