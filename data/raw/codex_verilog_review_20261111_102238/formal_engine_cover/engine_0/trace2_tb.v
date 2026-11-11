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
  reg [7:0] PI_bg_seg;
  reg [0:0] PI_stop_we;
  wire [0:0] PI_clk = clock;
  reg [11:0] PI_bg_tap;
  reg [15:0] PI_pin_fall;
  reg [0:0] PI_pause;
  reg [0:0] PI_hostinv_rise;
  reg [0:0] PI_doorbell;
  reg [7:0] PI_pause_pc;
  reg [15:0] PI_pin_lvl;
  reg [1:0] PI_sym_d;
  reg [7:0] PI_flag_rise;
  reg [4:0] PI_h_off;
  reg [0:0] PI_h_we;
  reg [7:0] PI_h_wd;
  reg [0:0] PI_sym_we;
  reg [4:0] PI_h_roff;
  reg [15:0] PI_pin_rise;
  reg [0:0] PI_rst_n;
  reg [0:0] PI_disp;
  reg [3:0] PI_bg_sp;
  reg [3:0] PI_bg_beat;
  md_engine UUT (
    .bg_seg(PI_bg_seg),
    .stop_we(PI_stop_we),
    .clk(PI_clk),
    .bg_tap(PI_bg_tap),
    .pin_fall(PI_pin_fall),
    .pause(PI_pause),
    .hostinv_rise(PI_hostinv_rise),
    .doorbell(PI_doorbell),
    .pause_pc(PI_pause_pc),
    .pin_lvl(PI_pin_lvl),
    .sym_d(PI_sym_d),
    .flag_rise(PI_flag_rise),
    .h_off(PI_h_off),
    .h_we(PI_h_we),
    .h_wd(PI_h_wd),
    .sym_we(PI_sym_we),
    .h_roff(PI_h_roff),
    .pin_rise(PI_pin_rise),
    .rst_n(PI_rst_n),
    .disp(PI_disp),
    .bg_sp(PI_bg_sp),
    .bg_beat(PI_bg_beat)
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
    // UUT.$auto$async2sync.\cc:116:execute$618  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$624  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$630  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$636  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$642  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$648  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$654  = 1'b1;
    UUT.armed = 1'b0;
    UUT.bg = 2'b00;
    UUT.cap = 4'b0000;
    UUT.committed = 2'b00;
    UUT.core = 1'b0;
    UUT.en = 1'b0;
    UUT.fv_props.p_acc = 1'b0;
    UUT.fv_props.p_armed = 1'b0;
    UUT.fv_props.p_beat = 1'b0;
    UUT.fv_props.p_busy = 1'b0;
    UUT.fv_props.p_cap = 4'b0000;
    UUT.fv_props.p_en = 1'b0;
    UUT.fv_props.p_late = 1'b0;
    UUT.fv_props.p_ovr = 1'b0;
    UUT.fv_props.p_rstn = 1'b0;
    UUT.fv_props.p_staged = 2'b00;
    UUT.fv_props.p_stop_we = 1'b0;
    UUT.fv_props.p_sym_d = 2'b00;
    UUT.fv_props.p_sym_we = 1'b0;
    UUT.fv_props.p_tap = 3'b000;
    UUT.fv_props.p_trig = 1'b0;
    UUT.fv_props.pv = 1'b0;
    UUT.late = 1'b0;
    UUT.lut0 = 16'b0000000000000000;
    UUT.lut1 = 16'b0000000000000000;
    UUT.ovr = 1'b0;
    UUT.pa_sel = 4'b0000;
    UUT.pb_sel = 4'b0000;
    UUT.pc = 8'b00000000;
    UUT.ready = 1'b1;
    UUT.running = 1'b0;
    UUT.staged = 2'b00;
    UUT.trig = 5'b00000;
    UUT.w0c = 6'b000000;
    UUT.w0h = 8'b00000000;
    UUT.w1c = 6'b000000;
    UUT.w1h = 8'b00000000;

    // state 0
    PI_bg_seg = 8'b00000000;
    PI_stop_we = 1'b0;
    PI_bg_tap = 12'b000000000000;
    PI_pin_fall = 16'b0000000000000000;
    PI_pause = 1'b0;
    PI_hostinv_rise = 1'b0;
    PI_doorbell = 1'b0;
    PI_pause_pc = 8'b00000000;
    PI_pin_lvl = 16'b0000000000000000;
    PI_sym_d = 2'b00;
    PI_flag_rise = 8'b00000000;
    PI_h_off = 5'b00000;
    PI_h_we = 1'b0;
    PI_h_wd = 8'b00000000;
    PI_sym_we = 1'b0;
    PI_h_roff = 5'b00000;
    PI_pin_rise = 16'b0000000000000000;
    PI_rst_n = 1'b0;
    PI_disp = 1'b1;
    PI_bg_sp = 4'b0000;
    PI_bg_beat = 4'b0000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_bg_seg <= 8'b00000000;
      PI_stop_we <= 1'b0;
      PI_bg_tap <= 12'b000000000010;
      PI_pin_fall <= 16'b0000000000000000;
      PI_pause <= 1'b0;
      PI_hostinv_rise <= 1'b0;
      PI_doorbell <= 1'b0;
      PI_pause_pc <= 8'b00000000;
      PI_pin_lvl <= 16'b0000000000000001;
      PI_sym_d <= 2'b11;
      PI_flag_rise <= 8'b00000000;
      PI_h_off <= 5'b01101;
      PI_h_we <= 1'b1;
      PI_h_wd <= 8'b00001111;
      PI_sym_we <= 1'b1;
      PI_h_roff <= 5'b00000;
      PI_pin_rise <= 16'b0000000000000000;
      PI_rst_n <= 1'b1;
      PI_disp <= 1'b0;
      PI_bg_sp <= 4'b0000;
      PI_bg_beat <= 4'b0001;
    end

    // state 2
    if (cycle == 1) begin
      PI_bg_seg <= 8'b00000000;
      PI_stop_we <= 1'b0;
      PI_bg_tap <= 12'b010010010010;
      PI_pin_fall <= 16'b0001101010101010;
      PI_pause <= 1'b0;
      PI_hostinv_rise <= 1'b1;
      PI_doorbell <= 1'b0;
      PI_pause_pc <= 8'b00000000;
      PI_pin_lvl <= 16'b0000000000000000;
      PI_sym_d <= 2'b00;
      PI_flag_rise <= 8'b01010101;
      PI_h_off <= 5'b00000;
      PI_h_we <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_sym_we <= 1'b0;
      PI_h_roff <= 5'b00000;
      PI_pin_rise <= 16'b0001101010101010;
      PI_rst_n <= 1'b1;
      PI_disp <= 1'b0;
      PI_bg_sp <= 4'b0000;
      PI_bg_beat <= 4'b1111;
    end

    // state 3
    if (cycle == 2) begin
      PI_bg_seg <= 8'b00000000;
      PI_stop_we <= 1'b0;
      PI_bg_tap <= 12'b000000000000;
      PI_pin_fall <= 16'b0000000000000000;
      PI_pause <= 1'b0;
      PI_hostinv_rise <= 1'b0;
      PI_doorbell <= 1'b0;
      PI_pause_pc <= 8'b00000000;
      PI_pin_lvl <= 16'b0000000000000000;
      PI_sym_d <= 2'b00;
      PI_flag_rise <= 8'b00000000;
      PI_h_off <= 5'b00000;
      PI_h_we <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_sym_we <= 1'b0;
      PI_h_roff <= 5'b00000;
      PI_pin_rise <= 16'b0000000000000000;
      PI_rst_n <= 1'b0;
      PI_disp <= 1'b0;
      PI_bg_sp <= 4'b0000;
      PI_bg_beat <= 4'b0000;
    end

    genclock <= cycle < 3;
    cycle <= cycle + 1;
  end
endmodule
