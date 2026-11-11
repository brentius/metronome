// Global control and status block (SPEC 6.1 host mailbox, SPEC 9 CTRL registers and IRQ): RUN_global, sticky
// CONFLICT/MEMHAZ, IRQEN, doorbell, HOSTIN/HOSTOUT mailbox, ID.
`timescale 1ns/1ps
`default_nettype none
module md_ctrl #(
    parameter integer NE = 6
) (
    input  wire          clk,
    input  wire          rst_n,
    input  wire          h_we,          // host write to the CTRL block
    input  wire [2:0]    h_off,
    input  wire [7:0]    h_wd,
    input  wire [2:0]    h_roff,
    output reg  [7:0]    h_rd,
    input  wire          ho_we,         // move to HOST.OUT
    input  wire [7:0]    ho_d,
    input  wire          hin_rd,        // an enabled move read HOST.IN
    input  wire          conflict_set,
    input  wire          memhaz_set,
    input  wire          eng_err,       // OR of every engine's LATE and OVR
    output reg           run_g,
    output wire [NE-1:0] doorbell,
    output reg  [7:0]    inb,
    output reg           inv,
    output reg           outv,
    output wire          hostinv_rise,
    output reg           irq
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    reg       conflict, memhaz, invp;
    reg [1:0] irqen;
    reg [7:0] outb;

    wire hw_run    = h_we && (h_off == HCTRL_RUN[2:0]);
    wire hw_sticky = h_we && (h_off == HCTRL_STICKY[2:0]);
    wire hw_irqen  = h_we && (h_off == HCTRL_IRQEN[2:0]);
    wire hw_door   = h_we && (h_off == HCTRL_DOORBELL[2:0]);
    wire hw_hostin = h_we && (h_off == HCTRL_HOSTIN[2:0]);
    wire hw_hstat  = h_we && (h_off == HCTRL_HOSTSTAT[2:0]);   // bit 1 = 1 clears OUTV

    assign doorbell     = hw_door ? h_wd[NE-1:0] : {NE{1'b0}};
    assign hostinv_rise = inv & ~invp;

    always @(posedge clk) begin
        if (!rst_n) begin
            run_g <= 1'b0; conflict <= 1'b0; memhaz <= 1'b0; irqen <= 2'd0;
            inb <= 8'd0; inv <= 1'b0; invp <= 1'b0; outb <= 8'd0; outv <= 1'b0; irq <= 1'b0;
        end else begin
            invp <= inv;
            irq  <= (irqen[0] & outv) | (irqen[1] & (conflict | memhaz | eng_err));
            if (hw_run)   run_g <= h_wd[0];
            if (hw_irqen) irqen <= h_wd[1:0];
            // sticky W1C. SPEC-AMBIGUITY: a host clear in the same cycle as a set wins (host priority).
            if (hw_sticky && h_wd[0]) conflict <= 1'b0;
            else if (conflict_set)    conflict <= 1'b1;
            if (hw_sticky && h_wd[1]) memhaz <= 1'b0;
            else if (memhaz_set)      memhaz <= 1'b1;
            // host -> chip mailbox: host write beats the move-side clear
            if (hw_hostin) begin
                inb <= h_wd;
                inv <= 1'b1;
            end else if (hin_rd) begin
                inv <= 1'b0;
            end
            // chip -> host mailbox (SPEC 9, 9a.5): host acknowledges by writing 1 to HOSTSTAT bit 1; a HOST.OUT
            // move in the same cycle wins (OUTV' = 1). No host read has a side effect.
            if (ho_we) begin
                outb <= ho_d;
                outv <= 1'b1;
            end else if (hw_hstat && h_wd[1]) begin
                outv <= 1'b0;
            end
        end
    end

    always @* begin
        case (h_roff)
            HCTRL_RUN[2:0]:      h_rd = {7'd0, run_g};
            HCTRL_STICKY[2:0]:   h_rd = {6'd0, memhaz, conflict};
            HCTRL_IRQEN[2:0]:    h_rd = {6'd0, irqen};
            HCTRL_DOORBELL[2:0]: h_rd = 8'd0;
            HCTRL_HOSTIN[2:0]:   h_rd = inb;
            HCTRL_HOSTOUT[2:0]:  h_rd = outb;
            HCTRL_HOSTSTAT[2:0]: h_rd = {6'd0, outv, inv};
            HCTRL_ID[2:0]:       h_rd = 8'hA0 | MD_VERSION[7:0];
            default:             h_rd = 8'd0;
        endcase
    end
endmodule
`default_nettype wire
