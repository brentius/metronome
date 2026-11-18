// Metronome v2 configuration: write-only host configuration held in resettable latches (V2_DESIGN 4.7, D24).
// From sim/numerics/v2_sizing/rtl/cfg_latch_bank.v (RTL-simulated, gate-level-verified write path), extended with a
// per-bit MASK so that only the used configuration bits get a latch (md2_map.vh CFG_MASK); masked bits read 0
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

    wire          we1;
    wire [AW-1:0] addr1;
    wire [7:0]    data1;
    md2_cfg_stage #(.AW(AW)) u_stage (
        .clk(clk), .rst_s(rst_s), .we(we), .waddr(waddr), .wdata(wdata),
        .we1(we1), .addr1(addr1), .data1(data1)
    );
    md2_cfg_cells #(.BYTES(BYTES), .MASK(MASK), .AW(AW)) u_cells (
        .clk(clk), .rst_s(rst_s), .we1(we1), .addr1(addr1), .data1(data1), .q(q)
    );
`ifdef COCOTB_SIM
    wire wr_spacing_err = u_stage.wr_spacing_err;
`endif
endmodule

/* verilator lint_off DECLFILENAME */
// Grant a single latch-bank write every other cycle. A host byte that
// follows a core write is held for one cycle. SPI strobes are spaced
// far enough apart that this one slot can never hold two host bytes.
module md2_cfg_arb (
    input  wire        clk,
    input  wire        rst_s,
    input  wire        previous_write,
    input  wire        host_valid,
    input  wire [8:0]  host_addr,
    input  wire [7:0]  host_data,
    input  wire        core_valid,
    input  wire [8:0]  core_addr,
    input  wire [7:0]  core_data,
    output wire        core_issue,
    output wire        bank_write,
    output wire [8:0]  bank_addr,
    output wire [7:0]  bank_data
);
    reg host_held;
    reg [8:0] held_addr;
    reg [7:0] held_data;
    wire hold_host = host_valid & previous_write;
    wire host_issue = host_held | (host_valid & ~previous_write);
    assign core_issue = core_valid & ~previous_write & ~host_issue;
    assign bank_write = host_issue | core_issue;
    assign bank_addr = host_held ? held_addr : host_issue ? host_addr : core_addr;
    assign bank_data = host_held ? held_data : host_issue ? host_data : core_data;

    always @(posedge clk) begin
        if (!rst_s) host_held <= 1'b0;
        else        host_held <= hold_host;
        if (hold_host) begin
            held_addr <= host_addr;
            held_data <= host_data;
        end
    end
endmodule

module md2_cfg_stage #(parameter integer AW = 9) (
    input  wire          clk,
    input  wire          rst_s,
    input  wire          we,
    input  wire [AW-1:0] waddr,
    input  wire [7:0]    wdata,
    output reg           we1,
    output reg  [AW-1:0] addr1,
    output reg  [7:0]    data1
);
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
endmodule

// BASE is the byte offset in the shared configuration window.
module md2_cfg_cells #(
    parameter integer      BYTES = 8,
    parameter [8*BYTES-1:0] MASK = {8*BYTES{1'b1}},
    parameter integer      AW    = 9,
    parameter integer      BASE  = 0
) (
    input  wire                clk,
    input  wire                rst_s,
    input  wire                we1,
    input  wire [AW-1:0]       addr1,
    input  wire [7:0]          data1,
    output wire [8*BYTES-1:0]  q
);

    genvar k, b;
    generate
        for (k = 0; k < BYTES; k = k + 1) begin : g_byte
            if (MASK[8*k +: 8] == 8'd0) begin : g_none
                assign q[8*k +: 8] = 8'd0;
            end else begin : g_used
                localparam integer BYTE_ADDR = BASE + k;
                wire en = we1 && (addr1 == BYTE_ADDR[AW-1:0]);
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
/* verilator lint_on DECLFILENAME */
`default_nettype wire
