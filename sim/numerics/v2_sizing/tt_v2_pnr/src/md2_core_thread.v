// Metronome v2 sizing: one thread's state slice (V2_DESIGN 4.1, SPEC v1 section 4 semantics for READY/RUNNING/OVR).
// Holds PC, READY, RUNNING, EN and sticky OVR in flops. Thread configuration (CORE, LINE, watchers) is
// host-written latch configuration in v2 (V2_DESIGN 4.7) and arrives as inputs; it is not stored here.
`timescale 1ns/1ps
`default_nettype none
module md2_core_thread (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       trig,       // trigger event for this thread in this cycle
    input  wire       h_pc_we,    // host write of PC (priority over a pause)
    input  wire [7:0] h_pc_d,
    input  wire       h_en_we,    // host write of EN
    input  wire       h_en_d,
    input  wire       disp,       // a core dispatches this thread in this cycle
    input  wire       pause,      // the core executing this thread retires a pausing instruction
    input  wire [7:0] npc,        // PC written at the pause (sequential or jump target)
    input  wire       stop,       // enabled move to T.STOP by this thread
    output reg        ready,
    output reg        running,
    output reg        en,
    output reg  [7:0] pc,
    output reg        ovr
);
    wire acc = trig & en;
    always @(posedge clk) begin
        if (!rst_n) begin
            ready <= 1'b0; running <= 1'b0; en <= 1'b0; pc <= 8'd0; ovr <= 1'b0;
        end else begin
            if (acc & (ready | running)) ovr <= 1'b1;
            if (disp) begin
                ready   <= 1'b0;
                running <= 1'b1;
            end else if (acc & ~ready & ~running) begin
                ready <= 1'b1;
            end
            if (pause) running <= 1'b0;
            if (h_pc_we)    pc <= h_pc_d;
            else if (pause) pc <= npc;
            if (h_en_we)    en <= h_en_d;
            else if (stop)  en <= 1'b0;
        end
    end
endmodule
`default_nettype wire
