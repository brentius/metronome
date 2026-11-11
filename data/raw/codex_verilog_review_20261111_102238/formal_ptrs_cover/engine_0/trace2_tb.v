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
  reg [15:0] PI_d;
  wire [0:0] PI_clk = clock;
  reg [7:0] PI_m_rd;
  reg [3:0] PI_sel;
  reg [10:0] PI_hreq_addr;
  reg [0:0] PI_rst_n;
  reg [0:0] PI_hreq_wr;
  reg [0:0] PI_hreq_set;
  reg [1:0] PI_we;
  reg [7:0] PI_hreq_d;
  md_ptrs UUT (
    .d(PI_d),
    .clk(PI_clk),
    .m_rd(PI_m_rd),
    .sel(PI_sel),
    .hreq_addr(PI_hreq_addr),
    .rst_n(PI_rst_n),
    .hreq_wr(PI_hreq_wr),
    .hreq_set(PI_hreq_set),
    .we(PI_we),
    .hreq_d(PI_hreq_d)
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
    // UUT.$auto$async2sync.\cc:116:execute$650  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$656  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$662  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$668  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$674  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$680  = 1'b1;
    // UUT.$auto$async2sync.\cc:116:execute$686  = 1'b1;
    UUT.fv_props.p2_fetch_served = 2'b00;
    UUT.fv_props.p2_rstn = 1'b0;
    UUT.fv_props.p_fetch_served = 2'b00;
    UUT.fv_props.p_op_w = 2'b00;
    UUT.fv_props.p_rdy = 2'b00;
    UUT.fv_props.p_rstn = 1'b0;
    UUT.fv_props.p_setrq = 2'b00;
    UUT.fv_props.pv = 1'b0;
    UUT.\g_p[0] .dr = 8'b00000000;
    UUT.\g_p[0] .land = 1'b0;
    UUT.\g_p[0] .lok = 1'b0;
    UUT.\g_p[0] .ptr = 11'b00000000000;
    UUT.\g_p[0] .rdyr = 1'b0;
    UUT.\g_p[0] .rq = 2'b10;
    UUT.\g_p[0] .rqa = 11'b00000000000;
    UUT.\g_p[0] .rqd = 8'b00000000;
    UUT.\g_p[1] .dr = 8'b00000000;
    UUT.\g_p[1] .land = 1'b0;
    UUT.\g_p[1] .lok = 1'b0;
    UUT.\g_p[1] .ptr = 11'b00000000000;
    UUT.\g_p[1] .rdyr = 1'b0;
    UUT.\g_p[1] .rq = 2'b10;
    UUT.\g_p[1] .rqa = 11'b00000000000;
    UUT.\g_p[1] .rqd = 8'b00000000;
    UUT.hland = 1'b0;
    UUT.hq = 1'b1;
    UUT.hqa = 11'b00000000000;
    UUT.hqd = 8'b00000000;
    UUT.hqw = 1'b0;

    // state 0
    PI_d = 16'b0000000000000000;
    PI_m_rd = 8'b00000000;
    PI_sel = 4'b0000;
    PI_hreq_addr = 11'b00000000000;
    PI_rst_n = 1'b0;
    PI_hreq_wr = 1'b0;
    PI_hreq_set = 1'b0;
    PI_we = 2'b10;
    PI_hreq_d = 8'b00000000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_d <= 16'b0000000000000000;
      PI_m_rd <= 8'b00000000;
      PI_sel <= 4'b0000;
      PI_hreq_addr <= 11'b00000000000;
      PI_rst_n <= 1'b0;
      PI_hreq_wr <= 1'b0;
      PI_hreq_set <= 1'b0;
      PI_we <= 2'b00;
      PI_hreq_d <= 8'b00000000;
    end

    genclock <= cycle < 1;
    cycle <= cycle + 1;
  end
endmodule
