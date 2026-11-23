/* Co-simulation top: Metronome full-chip RTL + a third-party SPI NOR flash model, wired on the uio bus.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Metronome side (scorec SPI mode-0 controller, code/score/lib/spi_mode0.score):
 *   O0 = SCK, O1 = CS_N, O2 = MOSI (push-pull uio outputs), P3 = MISO (uio input).
 * Flash side: the unmodified Winbond W25Q128JVxIM behavioural model from build/vendor/w25q128jv
 * (fetched by fetch_vendor.sh).  NUM_PAGES is reduced to 256 (64 KiB) so the model's memory array and
 * its MEM.TXT preload stay small; the test writes a 64 KiB all-0xFF (erased) preload into the run
 * directory, which is the model's own user-preload mechanism.  tPP is shortened so a page program
 * does not cost 700 us of wall-clock simulation.  No other change to the model.
 */
`timescale 1ns/1ps
`default_nettype none

module tb_spi_flash (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       ena,
    input  wire [7:0] ui_in,
    output wire [7:0] uo_out,
    output wire [7:0] uio_out,
    output wire [7:0] uio_oe,
    output wire       flash_sck,       // observation points for the test log
    output wire       flash_cs_n,
    output wire       flash_do
);
    wire [7:0] uio_in;

    wire sck  = uio_out[0];
    wire cs_n = uio_out[1];
    wire mosi = uio_out[2];

    wire do_line;
    wire wp_n = 1'b1;
    wire hold_n = 1'b1;

    assign uio_in = {4'b0000, do_line === 1'b1, 3'b000};      // P3 = MISO (z reads as 0 through the pad)

    tt_um_brentius_metronome u_chip (
        .ui_in(ui_in), .uo_out(uo_out), .uio_in(uio_in), .uio_out(uio_out), .uio_oe(uio_oe),
        .ena(ena), .clk(clk), .rst_n(rst_n)
    );

    W25Q128JVxIM #(.NUM_PAGES(256), .tPP(100000)) u_flash (
        .CSn(cs_n), .CLK(sck), .DIO(mosi), .DO(do_line), .WPn(wp_n), .HOLDn(hold_n)
    );

    assign flash_sck = sck;
    assign flash_cs_n = cs_n;
    assign flash_do = do_line;
endmodule

`default_nettype wire
