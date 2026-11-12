// Metronome v2 configuration: write-only host configuration held in resettable latches (V2_DESIGN 4.7, D24).
// From sim/numerics/v2_sizing/rtl/cfg_latch_bank.v (RTL-simulated, gate-level-verified write path), extended with a
// per-bit MASK so that only the 2,084 used configuration bits get a latch (md2_map.vh CFG_MASK); masked bits read 0
// and bytes without any latch get no clock gate.
//
// Timing (SPEC_V2 1): we/waddr/wdata are sampled on rising edge E1 (the end of host write cycle W); the selected
// byte's gated clock opens after E2 = E1 + 1 cycle, so logic sees the new value from W+2 and the old one through W+1.
// WRITE SPACING RULE: `we` must not be high on two consecutive rising edges (one host write per SPI byte guarantees
// it). Reset: rst_s (async assert by rst_n, release through two flops) clears every latch, so configuration is 0
// while rst_n is low; a write sampled while rst_s is low is ignored.
// USE_IHP_CELLS selects the library latch and clock gate; otherwise the behavioural cells in cells_behav.v.
`timescale 1ns/1ps
`default_nettype none
module md2_cfg_bank #(
    parameter integer      BYTES = 8,
    parameter [8*BYTES-1:0] MASK = {8*BYTES{1'b1}},
    parameter integer      AW    = 9
) (
    input  wire               clk,
    input  wire               rst_n,
    input  wire               we,
    input  wire [AW-1:0]      waddr,
    input  wire [7:0]         wdata,
    output wire [8*BYTES-1:0] q
);
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
    reg wr_spacing_err = 1'b0;
    always @(posedge clk)
        if (rst_s && we && we1) begin
            wr_spacing_err <= 1'b1;
            $display("md2_cfg_bank %m: ERROR write on consecutive cycles at %0t", $time);
        end
`endif

    genvar k, b;
    generate
        for (k = 0; k < BYTES; k = k + 1) begin : g_byte
            if (MASK[8*k +: 8] == 8'd0) begin : g_none
                assign q[8*k +: 8] = 8'd0;
            end else begin : g_used
                wire en = we1 && (addr1 == k[AW-1:0]);
                wire gclk;
`ifdef USE_IHP_CELLS
                sg13cmos5l_lgcp_1 u_cg (.CLK(clk), .GATE(en), .GCLK(gclk));
`else
                cfg_lgcp_beh      u_cg (.CLK(clk), .GATE(en), .GCLK(gclk));
`endif
                for (b = 0; b < 8; b = b + 1) begin : g_bit
                    if (MASK[8*k + b]) begin : g_l
`ifdef USE_IHP_CELLS
                        sg13cmos5l_dlhrq_1 u_l (.D(data1[b]), .GATE(gclk), .RESET_B(rst_s), .Q(q[8*k+b]));
`else
                        cfg_dlhrq_beh      u_l (.D(data1[b]), .GATE(gclk), .RESET_B(rst_s), .Q(q[8*k+b]));
`endif
                    end else begin : g_z
                        assign q[8*k+b] = 1'b0;
                    end
                end
            end
        end
    endgenerate
endmodule
`default_nettype wire
