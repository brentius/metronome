// One write group of the move bus (SPEC 6): picks the enabled move with the lowest (core, move) slot index and
// flags a conflict when two or more slots hit the group in the same cycle. Uniform per-unit write interface:
// we (group selected), sel (the winning slot's port select within the group), data.
// DW / SW size the data and port-select fields so that a group carries only what its unit uses (0 = none).
// The selection is a one-hot priority AND-OR (cheaper than a mux tree for 6 slots).
`timescale 1ns/1ps
`default_nettype none
module md_wgroup #(
    parameter integer N  = 6,
    parameter integer DW = 8,       // data bits carried (>= 1; tie off unused outputs at the instance)
    parameter integer SW = 1        // port-select bits carried (>= 1)
) (
    input  wire [N-1:0]    hit,
    input  wire [SW*N-1:0] sel,
    input  wire [DW*N-1:0] data,
    output wire            we,
    output reg  [SW-1:0]   wsel,
    output reg  [DW-1:0]   wdata,
    output wire            multi
);
    // lower[i] = some slot below i hits
    wire [N-1:0] lower;
    assign lower[0] = 1'b0;
    genvar g;
    generate
        for (g = 1; g < N; g = g + 1) begin : g_low
            assign lower[g] = lower[g-1] | hit[g-1];
        end
    endgenerate
    wire [N-1:0] win = hit & ~lower;

    integer i;
    always @* begin
        wsel  = {SW{1'b0}};
        wdata = {DW{1'b0}};
        for (i = 0; i < N; i = i + 1) begin
            wsel  = wsel  | (sel[SW*i +: SW]  & {SW{win[i]}});
            wdata = wdata | (data[DW*i +: DW] & {DW{win[i]}});
        end
    end
    assign we    = |hit;
    assign multi = |(hit & lower);
endmodule
`default_nettype wire
