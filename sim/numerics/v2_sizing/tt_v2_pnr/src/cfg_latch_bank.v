// cfg_latch_bank: write-only configuration held in resettable latches (IHP sg13cmos5l_dlhrq_1), one clock gate
// (sg13cmos5l_lgcp_1) per byte. See sim/numerics/v2_sizing/LATCH_SIZING.md.
//
// Interface: byte k is q[8k+7:8k]; writes to waddr >= BYTES are ignored.
// Timing (write latency): `we`/`waddr`/`wdata` are sampled on rising edge E1. q changes just after rising edge E2 =
// E1 + 1 cycle (gated-clock high phase), so logic that samples q on E3 (two cycles after E1) sees the new value.
// Pipeline: E1 registers we/addr (we1, addr1) and, only when `we` is high, the data (data1). The byte-select decode
// of we1/addr1 drives the lgcp GATE (its internal latch passes the enable while clk is low, so decode glitches cannot
// reach GCLK). E2 opens GCLK for the selected byte; the latches are transparent in the high phase after E2 and close
// on the falling edge. data1 has been stable since E1, so the latch opens on settled data and does not borrow time.
//
// WRITE SPACING RULE (r3, HARDEN_LEDGER U10): `we` must not be high on two consecutive rising edges. A write sampled
// at E2 would reload data1 while the previous write's latches are still open. md2_host gives one `wr` strobe per SPI
// data byte (at least 8 synchronised SCK edges apart), so the rule holds by construction; the COCOTB_SIM check below
// flags any violation in simulation. The rule is what makes the 2-cycle setup exception on the data1 -> latch D
// paths in src/project.sdc correct: data1 launched at E1 is captured by a gate that opens at E2, never at E1.
// Reset: rst_s (async assert by rst_n, release synchronised to clk through two flops) drives every latch RESET_B,
// so all configuration clears to 0 on reset. A write sampled while rst_s is still low (the two edges after rst_n
// rises) is ignored.
// USE_IHP_CELLS selects the library cells; otherwise the behavioural cells in cells_behav.v (same pins).
// AW is derived from BYTES; do not override it.
module cfg_latch_bank #(parameter BYTES = 8, parameter AW = (BYTES > 2) ? $clog2(BYTES) : 1) (
    input                          clk,
    input                          rst_n,
    input                          we,
    input  [AW-1:0]                waddr,
    input  [7:0]                   wdata,
    output [8*BYTES-1:0]           q
);

    // reset synchroniser: async assert, synchronous release
    reg rst_m, rst_s;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rst_m <= 1'b0;
            rst_s <= 1'b0;
        end else begin
            rst_m <= 1'b1;
            rst_s <= rst_m;
        end
    end

    // write pipeline
    reg          we1;
    reg [AW-1:0] addr1;
    reg [7:0]    data1;
    always @(posedge clk or negedge rst_s) begin
        if (!rst_s) we1 <= 1'b0;
        else        we1 <= we;
    end
    always @(posedge clk) begin
        addr1 <= waddr;
        if (we) data1 <= wdata;
    end

`ifdef COCOTB_SIM
    // simulation check of the write spacing rule (not synthesised; the tests read wr_spacing_err)
    reg wr_spacing_err = 1'b0;
    always @(posedge clk)
        if (rst_s && we && we1) begin
            wr_spacing_err <= 1'b1;
            $display("cfg_latch_bank %m: ERROR write on consecutive cycles at %0t", $time);
        end
`endif

    genvar k, b;
    generate
        for (k = 0; k < BYTES; k = k + 1) begin : g_byte
            wire en   = we1 && (addr1 == k[AW-1:0]);   // decoded; filtered by the clock gate's enable latch
            wire gclk;
`ifdef USE_IHP_CELLS
            sg13cmos5l_lgcp_1 u_cg (.CLK(clk), .GATE(en), .GCLK(gclk));
`else
            cfg_lgcp_beh      u_cg (.CLK(clk), .GATE(en), .GCLK(gclk));
`endif
            for (b = 0; b < 8; b = b + 1) begin : g_bit
`ifdef USE_IHP_CELLS
                sg13cmos5l_dlhrq_1 u_l (.D(data1[b]), .GATE(gclk), .RESET_B(rst_s), .Q(q[8*k+b]));
`else
                cfg_dlhrq_beh      u_l (.D(data1[b]), .GATE(gclk), .RESET_B(rst_s), .Q(q[8*k+b]));
`endif
            end
        end
    endgenerate
endmodule
