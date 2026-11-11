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
  reg [5:0] PI_e_core;
  reg [63:0] PI_s_lf;
  reg [63:0] PI_insn;
  reg [47:0] PI_e_pc;
  reg [3:0] PI_s_sho;
  reg [31:0] PI_s_shd;
  reg [11:0] PI_e_in;
  reg [5:0] PI_e_sync;
  reg [0:0] PI_run_g;
  reg [0:0] PI_rst_n;
  reg [63:0] PI_grd_g;
  reg [31:0] PI_s_r;
  reg [23:0] PI_e_cap;
  reg [47:0] PI_e_w0h;
  wire [0:0] PI_clk = clock;
  reg [35:0] PI_e_w0c;
  reg [15:0] PI_s_f;
  reg [5:0] PI_e_ready;
  reg [5:0] PI_e_pinb;
  reg [5:0] PI_e_pina;
  reg [7:0] PI_s_inb;
  reg [12:0] PI_s_pin;
  reg [15:0] PI_s_pd;
  reg [63:0] PI_s_cnt;
  reg [47:0] PI_e_w1h;
  reg [35:0] PI_e_w1c;
  reg [7:0] PI_s_acc;
  md_core UUT (
    .e_core(PI_e_core),
    .s_lf(PI_s_lf),
    .insn(PI_insn),
    .e_pc(PI_e_pc),
    .s_sho(PI_s_sho),
    .s_shd(PI_s_shd),
    .e_in(PI_e_in),
    .e_sync(PI_e_sync),
    .run_g(PI_run_g),
    .rst_n(PI_rst_n),
    .grd_g(PI_grd_g),
    .s_r(PI_s_r),
    .e_cap(PI_e_cap),
    .e_w0h(PI_e_w0h),
    .clk(PI_clk),
    .e_w0c(PI_e_w0c),
    .s_f(PI_s_f),
    .e_ready(PI_e_ready),
    .e_pinb(PI_e_pinb),
    .e_pina(PI_e_pina),
    .s_inb(PI_s_inb),
    .s_pin(PI_s_pin),
    .s_pd(PI_s_pd),
    .s_cnt(PI_s_cnt),
    .e_w1h(PI_e_w1h),
    .e_w1c(PI_e_w1c),
    .s_acc(PI_s_acc)
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
    // UUT.$auto$async2sync.\cc:116:execute$336  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$342  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$384  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$402  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$420  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$438  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$456  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$474  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$480  = 1'b1;
    UUT.fv_props.\g_wait[0] .waiting_grants = 4'b0000;
    UUT.fv_props.\g_wait[1] .waiting_grants = 4'b0000;
    UUT.fv_props.\g_wait[2] .waiting_grants = 4'b0000;
    UUT.fv_props.\g_wait[3] .waiting_grants = 4'b0000;
    UUT.fv_props.\g_wait[4] .waiting_grants = 4'b0000;
    UUT.fv_props.\g_wait[5] .waiting_grants = 4'b0000;
    UUT.fv_props.p_disp = 1'b0;
    UUT.fv_props.p_engine = 3'b000;
    UUT.fv_props.p_rstn = 1'b0;
    UUT.fv_props.past_valid = 1'b0;
    UUT.rr = 3'b000;
    UUT.xe = 3'b000;
    UUT.xpc = 8'b00000000;
    UUT.xv = 1'b0;

    // state 0
    PI_e_core = 6'b000000;
    PI_s_lf = 64'b0000000000000000000000000000000000000000000000000000000000000000;
    PI_insn = 64'b0000000000000000000000000000000000000000000000000000000000000000;
    PI_e_pc = 48'b000000000000000000000000000000000000000000000000;
    PI_s_sho = 4'b0000;
    PI_s_shd = 32'b00000000000000000000000000000000;
    PI_e_in = 12'b000000000000;
    PI_e_sync = 6'b000000;
    PI_run_g = 1'b0;
    PI_rst_n = 1'b0;
    PI_grd_g = 64'b0000000000000000000000000000000000000000000000000000000000000000;
    PI_s_r = 32'b00000000000000000000000000000000;
    PI_e_cap = 24'b000000000000000000000000;
    PI_e_w0h = 48'b000000000000000000000000000000000000000000000000;
    PI_e_w0c = 36'b000000000000000000000000000000000000;
    PI_s_f = 16'b0000000000000000;
    PI_e_ready = 6'b000000;
    PI_e_pinb = 6'b000000;
    PI_e_pina = 6'b000000;
    PI_s_inb = 8'b00000000;
    PI_s_pin = 13'b0000000000000;
    PI_s_pd = 16'b0000000000000000;
    PI_s_cnt = 64'b0000000000000000000000000000000000000000000000000000000000000000;
    PI_e_w1h = 48'b000000000000000000000000000000000000000000000000;
    PI_e_w1c = 36'b000000000000000000000000000000000000;
    PI_s_acc = 8'b00000000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_e_core <= 6'b010111;
      PI_s_lf <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_insn <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_e_pc <= 48'b000000000000000000000000000000000000000000000000;
      PI_s_sho <= 4'b0000;
      PI_s_shd <= 32'b00000000000000000000000000000000;
      PI_e_in <= 12'b000000000000;
      PI_e_sync <= 6'b000000;
      PI_run_g <= 1'b1;
      PI_rst_n <= 1'b1;
      PI_grd_g <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_s_r <= 32'b00000000000000000000000000000000;
      PI_e_cap <= 24'b000000000000000000000000;
      PI_e_w0h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w0c <= 36'b000000000000000000000000000000000000;
      PI_s_f <= 16'b0000000000000000;
      PI_e_ready <= 6'b111111;
      PI_e_pinb <= 6'b000000;
      PI_e_pina <= 6'b000000;
      PI_s_inb <= 8'b00000000;
      PI_s_pin <= 13'b0000000000000;
      PI_s_pd <= 16'b0000000000000000;
      PI_s_cnt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_e_w1h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w1c <= 36'b000000000000000000000000000000000000;
      PI_s_acc <= 8'b00000000;
    end

    // state 2
    if (cycle == 1) begin
      PI_e_core <= 6'b011110;
      PI_s_lf <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_insn <= 64'b0000000000000000000000000000000000000000000000000000000000000001;
      PI_e_pc <= 48'b000000000000000000000000000000000000000000000000;
      PI_s_sho <= 4'b0000;
      PI_s_shd <= 32'b00000000000000000000000000000000;
      PI_e_in <= 12'b000000000000;
      PI_e_sync <= 6'b000000;
      PI_run_g <= 1'b1;
      PI_rst_n <= 1'b0;
      PI_grd_g <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_s_r <= 32'b00000000000000000000000000000000;
      PI_e_cap <= 24'b000000000000000000000000;
      PI_e_w0h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w0c <= 36'b000000000000000000000000000000000000;
      PI_s_f <= 16'b0000000000000000;
      PI_e_ready <= 6'b111111;
      PI_e_pinb <= 6'b000000;
      PI_e_pina <= 6'b000000;
      PI_s_inb <= 8'b00000000;
      PI_s_pin <= 13'b0000000000000;
      PI_s_pd <= 16'b0000000000000000;
      PI_s_cnt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_e_w1h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w1c <= 36'b000000000000000000000000000000000000;
      PI_s_acc <= 8'b00000000;
    end

    // state 3
    if (cycle == 2) begin
      PI_e_core <= 6'b000000;
      PI_s_lf <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_insn <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_e_pc <= 48'b000000000000000000000000000000000000000000000000;
      PI_s_sho <= 4'b0000;
      PI_s_shd <= 32'b00000000000000000000000000000000;
      PI_e_in <= 12'b000000000000;
      PI_e_sync <= 6'b000000;
      PI_run_g <= 1'b0;
      PI_rst_n <= 1'b0;
      PI_grd_g <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_s_r <= 32'b00000000000000000000000000000000;
      PI_e_cap <= 24'b000000000000000000000000;
      PI_e_w0h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w0c <= 36'b000000000000000000000000000000000000;
      PI_s_f <= 16'b0000000000000000;
      PI_e_ready <= 6'b000000;
      PI_e_pinb <= 6'b000000;
      PI_e_pina <= 6'b000000;
      PI_s_inb <= 8'b00000000;
      PI_s_pin <= 13'b0000000000000;
      PI_s_pd <= 16'b0000000000000000;
      PI_s_cnt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      PI_e_w1h <= 48'b000000000000000000000000000000000000000000000000;
      PI_e_w1c <= 36'b000000000000000000000000000000000000;
      PI_s_acc <= 8'b00000000;
    end

    genclock <= cycle < 3;
    cycle <= cycle + 1;
  end
endmodule
