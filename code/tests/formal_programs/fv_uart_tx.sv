// Formal top for the compiled UART-transmit program (Score uart_8n1 / sender at 10 Mbaud = 6 clk per bit).
// The DUT is the unmodified tt_um_brentius_metronome except md2_cfg_bank (constant image) and md2_host (write
// sequencer): see rtl_fv/ and README.md for the preload-equivalence assumptions.
//
// Claim (for every payload byte p, every extra HOSTIN delay d in 0..11 except the documented hazard value):
//   P1  O8 stays high until the first low cycle t0 and no low cycle exists before the HOSTIN write
//   P2  for off = 0..59: O8(t0 + off) == frame[off/6], frame = {0, p[0..7] LSB first, 1}
//   P3  O8 is high from t0+60 on (one frame, nothing spurious afterwards, within the horizon)
//   P4  t0 occurs within LAT_MAX cycles after the HOSTIN write cycle (bounded response)
//   P5  at t0 the line-0 phase PH is 1 (the edge lies on the beat grid, 6-cycle beat)
`ifndef HAZARD_DELAY
`define HAZARD_DELAY 8'd2      // delay value for which the HOSTIN write lands in the idle loop's blind cycle
`endif
module fv_uart_tx (input wire clk);
    parameter integer LAT_MAX = 24;
    (* anyseq *) wire [7:0] ui_in;
    (* anyseq *) wire [7:0] uio_in;
    wire [7:0] uo_out, uio_out, uio_oe;
    reg  rst_n = 1'b0;
    reg [2:0] rc = 3'd0;
    always @(posedge clk) begin
        if (rc != 3'd4) rc <= rc + 3'd1;
        rst_n <= (rc >= 3'd2);          // low for the first 3 cycles, then released and never re-asserted
    end
    tt_um_brentius_metronome dut (.ui_in(ui_in), .uo_out(uo_out), .uio_in(uio_in), .uio_out(uio_out),
                                  .uio_oe(uio_oe), .ena(1'b1), .clk(clk), .rst_n(rst_n));
    wire [7:0] payload = dut.u_host.payload;
    wire [7:0] delay   = dut.u_host.delay;
    wire o8 = uo_out[2];

`ifdef SAFE
    always @(*) assume(delay <= 8'd11 && delay != `HAZARD_DELAY);
`else
    always @(*) assume(delay <= 8'd11);
`endif

    reg        hi_seen = 1'b0, fell = 1'b0;
    reg [7:0]  since_hi = 8'd0;       // cycles since the HOSTIN write cycle
    reg [7:0]  off = 8'd0;            // cycles since t0
    reg        past_rst = 1'b0;
    reg        live = 1'b0;                 // output registers have been loaded after reset (O8 reads 0 during reset)
    always @(posedge clk) live <= dut.rst_q;
    wire hi_wr = live && dut.rst_q && dut.h_wr && (dut.ha == 16'h2404);   // reset registers are arbitrary before rst_q
    wire       start_now = live && dut.rst_q && !fell && !o8;
    wire [9:0] frame = {1'b1, payload, 1'b0};
    wire [7:0] off_now = fell ? off : 8'd0;   // at start_now (fell=0) off_now = 0
    wire [3:0] k = (off_now >= 8'd60) ? 4'd9 : off_now / 8'd6;
    always @(posedge clk) begin
        if (hi_wr) hi_seen <= 1'b1;
        if (hi_seen) since_hi <= (since_hi == 8'hFF) ? since_hi : since_hi + 8'd1;
        if (start_now) fell <= 1'b1;
        if (start_now) off <= 8'd1;                                 // off = cycles since t0, valid while fell
        else if (fell) off <= (off == 8'hFF) ? off : off + 8'd1;
    end
    // checks begin once the reset chain has released (rst_q high): the pins are defined from then on
    always @(posedge clk) if (live && dut.rst_q) begin
        if (!hi_seen && !hi_wr) assert (o8);                                   // P1 (nothing before the write)
        if (!fell && !start_now) assert (o8);                                  // P1
        if (start_now) begin
            assert (since_hi <= LAT_MAX && hi_seen);                           // P4 (and not before the write)
            assert (dut.g_ln[0].u.ph == 16'd1);                                // P5
        end
        if (fell || start_now) begin
            assert (o8 == (off_now >= 8'd60 ? 1'b1 : frame[k]));              // P2, P3
        end
        if (hi_seen && since_hi == LAT_MAX + 1) assert (fell);                 // P4: the frame did start
    end
`ifdef COVER
    always @(posedge clk) cover (fell && off == 8'd62);                        // a complete frame is reachable
`endif
endmodule
