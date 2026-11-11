// Shifter unit k (SPEC 6.1): D, CNT, LEN (0 means 8), MSB.
// Write groups: SHk.{LD,SH} and SHk.CFG. Out bit O = MSB ? D[7] : D[0]; DONE = (CNT == 0).
`timescale 1ns/1ps
`default_nettype none
module md_shifter (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       we,
    input  wire       sel,      // 0 LD, 1 SH
    input  wire [7:0] d,
    input  wire       cfg_we,
    input  wire [4:0] cfg_d,
    output reg  [7:0] dr,
    output wire       o,
    output wire       done
);
    reg [3:0] cnt, len;
    reg       msb;
    always @(posedge clk) begin
        if (!rst_n) begin
            dr  <= 8'd0;
            cnt <= 4'd0;
            len <= 4'd0;
            msb <= 1'b0;
        end else begin
            if (we && !sel) begin
                dr  <= d;
                cnt <= (len != 4'd0) ? len : 4'd8;
            end else if (we) begin
                dr  <= msb ? {dr[6:0], d[0]} : {d[0], dr[7:1]};
                cnt <= (cnt != 4'd0) ? cnt - 4'd1 : 4'd0;
            end
            if (cfg_we) begin
                len <= cfg_d[3:0];
                msb <= cfg_d[4];
            end
        end
    end
    assign o    = msb ? dr[7] : dr[0];
    assign done = (cnt == 4'd0);
endmodule
`default_nettype wire
