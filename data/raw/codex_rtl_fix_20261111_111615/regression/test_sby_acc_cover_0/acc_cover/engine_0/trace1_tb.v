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
  reg [0:0] PI_rst_n;
  reg [2:0] PI_sel;
  reg [3:0] PI_r_we;
  reg [31:0] PI_r_d;
  wire [0:0] PI_clk = clock;
  md_acc UUT (
    .we(PI_we),
    .d(PI_d),
    .rst_n(PI_rst_n),
    .sel(PI_sel),
    .r_we(PI_r_we),
    .r_d(PI_r_d),
    .clk(PI_clk)
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
    // UUT.$auto$async2sync.\cc:116:execute$198  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$204  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$210  = 1'b1;
    UUT.a = 8'b00000000;
    UUT.c = 1'b0;
    UUT.fv_props.p_c = 1'b0;
    UUT.fv_props.p_dst = 3'b000;
    UUT.fv_props.p_rstn = 1'b0;
    UUT.fv_props.p_we = 1'b0;
    UUT.fv_props.pv = 1'b0;
    UUT.n = 1'b0;
    UUT.r = 32'b00000000000000000000000000000000;
    UUT.z = 1'b0;

    // state 0
    PI_we = 1'b0;
    PI_d = 8'b00000000;
    PI_rst_n = 1'b0;
    PI_sel = 3'b111;
    PI_r_we = 4'b0000;
    PI_r_d = 32'b00000000000000000000000000000000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_we <= 1'b1;
      PI_d <= 8'b00000000;
      PI_rst_n <= 1'b1;
      PI_sel <= 3'b010;
      PI_r_we <= 4'b0000;
      PI_r_d <= 32'b00000000000000000000000000000000;
    end

    // state 2
    if (cycle == 1) begin
      PI_we <= 1'b0;
      PI_d <= 8'b00000000;
      PI_rst_n <= 1'b0;
      PI_sel <= 3'b111;
      PI_r_we <= 4'b0000;
      PI_r_d <= 32'b00000000000000000000000000000000;
    end

    // state 3
    if (cycle == 2) begin
      PI_we <= 1'b1;
      PI_d <= 8'b00000000;
      PI_rst_n <= 1'b0;
      PI_sel <= 3'b011;
      PI_r_we <= 4'b0000;
      PI_r_d <= 32'b00000000000000000000000000000000;
    end

    genclock <= cycle < 3;
    cycle <= cycle + 1;
  end
endmodule
