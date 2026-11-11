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
  reg [0:0] PI_we;
  reg [7:0] PI_d;
  reg [1:0] PI_h_byte;
  reg [0:0] PI_rst_n;
  wire [0:0] PI_clk = clock;
  reg [7:0] PI_h_wd;
  reg [0:0] PI_h_we;
  reg [2:0] PI_sel;
  fv_lfsr_top UUT (
    .we(PI_we),
    .d(PI_d),
    .h_byte(PI_h_byte),
    .rst_n(PI_rst_n),
    .clk(PI_clk),
    .h_wd(PI_h_wd),
    .h_we(PI_h_we),
    .sel(PI_sel)
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
    // UUT.$auto$async2sync.\cc:116:execute$147  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$81  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$87  = 1'b1;
    UUT.u0.fv_props.p_d = 8'b00000000;
    UUT.u0.fv_props.p_h_we = 1'b0;
    UUT.u0.fv_props.p_rstn = 1'b0;
    UUT.u0.fv_props.p_s = 32'b00000000000000000000000000000000;
    UUT.u0.fv_props.p_sel = 3'b000;
    UUT.u0.fv_props.p_we = 1'b0;
    UUT.u0.fv_props.pv = 1'b0;
    UUT.u0.poly = 32'b00000000000000000000000000000000;
    UUT.u0.s = 32'b00000000000000000000000000000000;

    // state 0
    PI_we = 1'b0;
    PI_d = 8'b00000000;
    PI_h_byte = 2'b00;
    PI_rst_n = 1'b0;
    PI_h_wd = 8'b00000000;
    PI_h_we = 1'b0;
    PI_sel = 3'b000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_we <= 1'b1;
      PI_d <= 8'b00000000;
      PI_h_byte <= 2'b00;
      PI_rst_n <= 1'b1;
      PI_h_wd <= 8'b00000000;
      PI_h_we <= 1'b1;
      PI_sel <= 3'b100;
    end

    // state 2
    if (cycle == 1) begin
      PI_we <= 1'b0;
      PI_d <= 8'b00000000;
      PI_h_byte <= 2'b00;
      PI_rst_n <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_h_we <= 1'b0;
      PI_sel <= 3'b000;
    end

    // state 3
    if (cycle == 2) begin
      PI_we <= 1'b0;
      PI_d <= 8'b00000000;
      PI_h_byte <= 2'b00;
      PI_rst_n <= 1'b0;
      PI_h_wd <= 8'b00000000;
      PI_h_we <= 1'b0;
      PI_sel <= 3'b000;
    end

    genclock <= cycle < 3;
    cycle <= cycle + 1;
  end
endmodule
