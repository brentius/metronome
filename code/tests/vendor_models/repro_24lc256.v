/* Minimal reproduction of finding F1: the 24LC256 model starts a spurious write cycle after a
 * write-address-only transaction (the standard acknowledge-polling probe), so the device is busy for another
 * tWC even though nothing was written.  A real 24LC256 performs no write for that transaction and is idle at
 * the STOP (24LC256 datasheet, "Acknowledge Polling": the device responds to its address as soon as the
 * internal write cycle is complete, and a write needs at least one data byte).
 *
 * Runs on the model alone (no Metronome RTL): one second of wall clock.
 *
 *   iverilog -g2012 -o repro.vvp repro_24lc256.v build/vendor/antikernel/models/i2c_eeprom/24LC256.v
 *   vvp repro.vvp
 *
 * Expected output (what the shipped model does):
 *   PAGE  WrCounter=1 WriteActive=1          the write cycle starts at the STOP
 *   IDLE  WriteActive=0                      ... and ends after tWC
 *   POLL  ack=0                              the acknowledge poll succeeds, as on silicon
 *   AFTER_POLL WriteActive=1                 BUG: a second write cycle starts at the poll's STOP
 *   POLL2 ack=1                              BUG: the next poll is refused although the write is done
 *
 * Timing discipline: every SDA change happens while SCL is low (a first version of this bench changed SDA
 * while SCL was high, which the model correctly decoded as a STOP; that was a bench bug).
 */
`timescale 1ns/1ps

module repro_24lc256;
    reg  scl_d = 1'b1, sda_d = 1'b1;                  // 1 = released (open drain)
    wire scl, sda;
    integer ack;

    pullup (scl);
    pullup (sda);
    assign scl = scl_d ? 1'bz : 1'b0;
    assign sda = sda_d ? 1'bz : 1'b0;

    M24LC256 u (.A0(1'b0), .A1(1'b0), .A2(1'b0), .WP(1'b0), .SDA(sda), .SCL(scl), .RESET(1'b0));

    task automatic bit_out(input b);         // entry and exit: SCL low
        begin
            sda_d = b; #2500;
            scl_d = 1'b1; #5000; scl_d = 1'b0; #2500;
        end
    endtask

    task automatic byte_out(input [7:0] b, output a);   // entry and exit: SCL low
        integer i;
        begin
            for (i = 7; i >= 0; i = i - 1) bit_out(b[i]);
            sda_d = 1'b1; #2500;                        // release for the acknowledge, SCL still low
            scl_d = 1'b1; #4000; a = sda; #1000; scl_d = 1'b0; #2500;
        end
    endtask

    task automatic start;                    // entry: idle (both released); exit: SCL low
        begin sda_d = 1'b1; scl_d = 1'b1; #2500; sda_d = 1'b0; #2500; scl_d = 1'b0; #2500; end
    endtask

    task automatic stop;                     // entry: SCL low; exit: idle
        begin sda_d = 1'b0; #2500; scl_d = 1'b1; #2500; sda_d = 1'b1; #2500; end
    endtask

    initial begin
        #1 u.tWC = 200000;
        start;                                                   // page write: 0xA0, word 0x0040, 0xDE
        byte_out(8'hA0, ack); byte_out(8'h00, ack); byte_out(8'h40, ack); byte_out(8'hDE, ack);
        stop;
        $display("PAGE WrCounter=%0d WriteActive=%b", u.WrCounter, u.WriteActive);
        #300000;                                                 // let the write cycle finish
        $display("IDLE WriteActive=%b", u.WriteActive);

        start; byte_out(8'hA0, ack); stop;                        // acknowledge-polling probe
        $display("POLL ack=%0d", ack);
        $display("AFTER_POLL WriteActive=%b WrCounter=%0d", u.WriteActive, u.WrCounter);

        start; byte_out(8'hA0, ack); stop;                        // a second probe ~2 us later
        $display("POLL2 ack=%0d", ack);
        $finish;
    end
endmodule
