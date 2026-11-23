/* Co-simulation top: Metronome full-chip RTL + a third-party 24LC256 I2C EEPROM model.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Metronome side (scorec I2C controller, code/score/lib/i2c.score): P0 = SCL, P1 = SDA, both open drain
 * (the score binds "scl=P0/O0 sda=P1/O1").  The chip is the only clock driver; the EEPROM drives SDA only
 * to acknowledge or to return a data bit.
 *
 * EEPROM side: the unmodified M24LC256 behavioural model (Young Engineering, distributed by Microchip and
 * republished in azonenberg/antikernel; see build/vendor/MANIFEST.md).  Two bench settings, both outside the
 * model's documented behaviour of the wire protocol:
 *   - MemoryBlock is preloaded with 0xFF ("erased") so reads of untouched cells are defined;
 *   - tWC (write cycle time) is shortened from 5 ms to 200 us so the write/busy window is affordable in a
 *     full-chip simulation.  The model still refuses acknowledges for the whole window, which is what the
 *     ack-polling check needs.
 * Both are simulation-time overrides from this testbench; no line of the model is edited.
 */
`timescale 1ns/1ps
`default_nettype none

module tb_i2c_eeprom (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       ena,
    input  wire [7:0] ui_in,
    output wire [7:0] uo_out,
    output wire [7:0] uio_out,
    output wire [7:0] uio_oe,
    output wire       scl_line,        // observation points
    output wire       sda_line,
    output wire       bus_fault        // sticky: the chip ever drove a '1' onto an open-drain wire
);
    wire [7:0] uio_in;

    wire scl_pad;
    wire sda_pad;

    pullup (scl_pad);
    pullup (sda_pad);

    // Open-drain pads: a '0' with the output enable set pulls low, anything else releases.  Driving a '1'
    // with the enable set is an open-drain protocol error; latch it instead of hiding it (the test reads this).
    reg fault = 1'b0;
    always @(posedge clk)
        if (ena && ((uio_oe[0] & uio_out[0]) || (uio_oe[1] & uio_out[1]))) fault <= 1'b1;
    assign bus_fault = fault;

    assign scl_pad = (uio_oe[0] & ~uio_out[0]) ? 1'b0 : 1'bz;
    assign sda_pad = (uio_oe[1] & ~uio_out[1]) ? 1'b0 : 1'bz;

    assign uio_in = {6'b000000, sda_pad, scl_pad};      // P1 = SDA, P0 = SCL

    tt_um_brentius_metronome u_chip (
        .ui_in(ui_in), .uo_out(uo_out), .uio_in(uio_in), .uio_out(uio_out), .uio_oe(uio_oe),
        .ena(ena), .clk(clk), .rst_n(rst_n)
    );

    M24LC256 u_eeprom (
        .A0(1'b0), .A1(1'b0), .A2(1'b0),        // device address 1010_000 = 0x50
        .WP(1'b0),                              // write enabled
        .SDA(sda_pad), .SCL(scl_pad),
        .RESET(1'b0)                            // its timing checks are enabled while RESET is low
    );

    integer i;
    initial begin
        for (i = 0; i < 32768; i = i + 1) u_eeprom.MemoryBlock[i] = 8'hFF;
        #1 u_eeprom.tWC = 200000;               // 200 us (model default 5 ms)
    end

    assign scl_line = scl_pad;
    assign sda_line = sda_pad;
endmodule

`default_nettype wire
