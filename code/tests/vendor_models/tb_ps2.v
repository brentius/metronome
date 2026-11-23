/* Co-simulation top: Metronome full-chip RTL listening to a PS/2 keyboard device peer.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Metronome side: program code/host2/examples/vendor/ps2_keyboard_rx.mas.  P0 = PS/2 CLK, P1 = PS/2 DATA,
 * both inputs with pull-ups; the chip never drives either wire (a sticky `bus_fault` records it if it does).
 * Peer: ps2_keyboard_peer.v, written from the IBM PS/2 interface specification (first-party test peer).
 */
`timescale 1ns/1ps
`default_nettype none

module tb_ps2 (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       ena,
    input  wire [7:0] ui_in,
    output wire [7:0] uo_out,
    output wire [7:0] uio_out,
    output wire [7:0] uio_oe,
    input  wire       ps2_go,           // drive under testbench control
    input  wire [7:0] ps2_din,
    input  wire       ps2_bad_parity,
    output wire       ps2_clk,          // observation points
    output wire       ps2_data,
    output wire       ps2_busy,
    output wire       bus_fault         // sticky: the chip ever drove a '1' onto an open-drain wire
);
    wire [7:0] uio_in;

    pullup (ps2_clk);
    pullup (ps2_data);

    // The chip may only pull low or release; a '1' with the enable set would be a protocol error.
    assign ps2_clk  = (uio_oe[0] & ~uio_out[0]) ? 1'b0 : 1'bz;
    assign ps2_data = (uio_oe[1] & ~uio_out[1]) ? 1'b0 : 1'bz;

    reg fault = 1'b0;
    always @(posedge clk)
        if (ena && ((uio_oe[0] & uio_out[0]) || (uio_oe[1] & uio_out[1]))) fault <= 1'b1;
    assign bus_fault = fault;

    assign uio_in = {6'b000000, ps2_data, ps2_clk};      // P1 = DATA, P0 = CLK

    tt_um_brentius_metronome u_chip (
        .ui_in(ui_in), .uo_out(uo_out), .uio_in(uio_in), .uio_out(uio_out), .uio_oe(uio_oe),
        .ena(ena), .clk(clk), .rst_n(rst_n)
    );

    ps2_keyboard_peer u_peer (
        .go(ps2_go), .din(ps2_din), .bad_parity(ps2_bad_parity),
        .ps2_clk(ps2_clk), .ps2_data(ps2_data), .busy(ps2_busy)
    );

    // Wire truth for the test: the data level at every falling clock edge (the PS/2 sampling instant).
    reg [63:0] seen_bits = 64'b0;
    reg [6:0]  seen_n = 7'b0;
    always @(negedge ps2_clk)
        if (ena && seen_n < 64) begin
            seen_bits[seen_n] <= ps2_data;
            seen_n <= seen_n + 1'b1;
        end
endmodule

`default_nettype wire
