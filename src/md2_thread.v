// Metronome v2 thread t state (wiki/SPEC_V2.md section 4): PC, EN, READY, RUNNING, ARMED and sticky LATE, OVR.
// Thread configuration (CORE, LINE, TRIG, watchers) is latch configuration and lives in the top level; the trigger
// event is decoded there. Host writes come last: PC wins over a pause, EN over T.STOP, and a sticky flag set in the
// same cycle as a host clear stays set.
`timescale 1ns/1ps
`default_nettype none
module md2_thread (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       ev,          // event(TRIG) in this cycle
    input  wire       db,          // doorbell pulse
    input  wire       disp,        // a core dispatches this thread
    input  wire       pause,       // the core executing this thread retires a pausing instruction
    input  wire [7:0] npc,
    input  wire       stop,        // winning move to T.STOP of this thread
    input  wire       late_set,    // an enabled symbol move by this thread while ARMED = 0
    input  wire       line_beat,   // BEAT of the thread's line
    input  wire       h_pc_we,
    input  wire       h_stat_we,
    input  wire [7:0] h_d,
    output reg  [7:0] pc,
    output reg        en,
    output reg        ready,
    output reg        running,
    output reg        armed,
    output reg        late,
    output reg        ovr
);
    wire trig = en & (ev | db);
    wire busy = ready | running;
    wire acc  = trig & ~busy;
    always @(posedge clk) begin
        if (!rst_n) begin
            pc <= 8'd0; en <= 1'b0; ready <= 1'b0; running <= 1'b0; armed <= 1'b0; late <= 1'b0; ovr <= 1'b0;
        end else begin
            if (disp)     ready <= 1'b0;
            else if (acc) ready <= 1'b1;
            if (pause)     running <= 1'b0;
            else if (disp) running <= 1'b1;
            if (h_pc_we)    pc <= h_d;
            else if (pause) pc <= npc;
            if (acc)            armed <= 1'b1;
            else if (line_beat) armed <= 1'b0;
            late <= late_set | (late & ~(h_stat_we & h_d[4]));
            ovr  <= (trig & busy) | (ovr & ~(h_stat_we & h_d[5]));
            if (h_stat_we) en <= h_d[3];
            else if (stop) en <= 1'b0;
        end
    end
endmodule
`default_nettype wire
