/* PS/2 keyboard device, written from the public interface specification (first-party test peer, not a
 * third-party model and not part of build/vendor/MANIFEST.md).
 *
 * Source of the behaviour (device-to-host frame):
 *   IBM Personal System/2 Hardware Interface Technical Reference (1988), section "Keyboard-to-System
 *   Communication" (scanned copies: https://archive.org/details/bitsavers_ibm), and the mirrored article
 *   "The PS/2 Mouse/Keyboard Protocol" (A. Chapweske, 1999), sections "Communication: General Description"
 *   and "Communication: Device-to-Host": https://www.burtonsys.com/ps2_chapweske.htm
 *   - 11 bits per frame: 1 start bit (0), 8 data bits least significant first, 1 odd parity bit, 1 stop bit (1);
 *   - the device always generates the clock, 10-16.7 kHz (30-50 us per clock phase);
 *   - data is read by the host on the falling clock edge and changes while the clock is high, at least 5 us
 *     after the rising edge and 5-25 us before the next falling edge;
 *   - both lines are open collector with pull-ups.
 *
 * Timing here: 60 us per bit (16.7 kHz, the fast end of the specification), clock low 30 us / high 30 us,
 * data changed 10 us after the rising edge (20 us before the next falling edge).  `bad_parity` inverts
 * the parity bit so the receiver's parity check can be exercised.
 *
 * The peer only drives its two pins low or releases them; the pull-ups are in the testbench.
 */
`timescale 1ns/1ps
`default_nettype none

module ps2_keyboard_peer #(
    parameter integer T_SETUP = 10000,      // data setup before the first clock fall, ns (> 5 us)
    parameter integer T_LOW   = 30000,      // clock low phase, ns (25-50 us)
    parameter integer T_HIGH  = 30000,      // clock high phase, ns
    parameter integer T_STABLE = 10000      // data changed this long after the rise, ns
) (
    input  wire       go,                   // one frame per rising edge while idle
    input  wire [7:0] din,
    input  wire       bad_parity,
    output wire       ps2_clk,
    output wire       ps2_data,
    output wire       busy
);
    reg clk_n = 1'b1;                       // 1 = released (open drain), 0 = driven low
    reg dat_n = 1'b1;
    reg busy_r = 1'b0;
    reg [10:0] frame;
    reg parity;
    integer i;

    assign ps2_clk  = clk_n ? 1'bz : 1'b0;
    assign ps2_data = dat_n ? 1'bz : 1'b0;
    assign busy = busy_r;

    always @(posedge go) begin
        if (!busy_r) begin
            busy_r = 1'b1;
            parity = ~^din ^ bad_parity;      // odd parity over the eight data bits
            frame = {1'b1, parity, din[7:0], 1'b0};   // frame[0] is sent first: start bit
            dat_n = 1'b0;                     // start bit = 0, driven while the clock is high
            #(T_SETUP);
            for (i = 0; i < 11; i = i + 1) begin
                clk_n = 1'b0;                 // falling edge: the receiver samples data here
                #(T_LOW);
                clk_n = 1'b1;                 // rising edge
                #(T_STABLE);
                if (i < 10) dat_n = frame[i + 1] ? 1'b1 : 1'b0;
                #(T_HIGH - T_STABLE);
            end
            dat_n = 1'b1;                     // release the data line after the stop bit
            busy_r = 1'b0;
        end
    end
endmodule

`default_nettype wire
