// LFSR/CRC unit (SPEC 6.1): S (32), POLY (32, host-set, write-only per D14). Write group LFk.{ST,B0..B3}
// (sel 0 ST, 1..4 B0..B3). ST: fb = S[0]^v[0]; S' = (S >> 1) ^ (fb ? POLY : 0). Bb: S[8b+7:8b]' = v. OUT = S[0].
`timescale 1ns/1ps
`default_nettype none
module md_lfsr (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        we,
    input  wire [2:0]  sel,
    input  wire [7:0]  d,
    // host write of POLY (byte lane 0..3)
    input  wire        h_we,
    input  wire [1:0]  h_byte,
    input  wire [7:0]  h_wd,
    output reg  [31:0] s
);
    reg [31:0] poly;
    wire fb = s[0] ^ d[0];
    always @(posedge clk) begin
        if (!rst_n) begin
            s    <= 32'd0;
            poly <= 32'd0;
        end else begin
            if (we) begin
                case (sel)
                    3'd0: s <= {1'b0, s[31:1]} ^ (fb ? poly : 32'd0);
                    3'd1: s[7:0]   <= d;
                    3'd2: s[15:8]  <= d;
                    3'd3: s[23:16] <= d;
                    3'd4: s[31:24] <= d;
                    default: ;
                endcase
            end
            if (h_we) poly[8*h_byte +: 8] <= h_wd;
        end
    end
endmodule
`default_nettype wire
