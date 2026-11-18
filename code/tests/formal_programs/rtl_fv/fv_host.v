// FORMAL-ONLY replacement for src/md2_host.v: instead of the SPI target it issues the image's non-configuration host
// writes (program bytes, runtime registers) on the same internal write bus (addr, wr, wdata) that md2_host drives,
// then one HOSTIN write of the symbolic payload after a symbolic extra delay. Same module name and ports.
// Table and timing come from the generated fv_seq.vh. Reads, MISO and the SPI pins are not modelled.
`default_nettype none
module md2_host (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        sck,
    input  wire        sck_p,
    input  wire        cs_n,
    input  wire        mosi,
    output reg  [15:0] addr,
    output reg         wr,
    output reg  [7:0]  wdata,
    output reg         rd,
    input  wire        rd_data,
    input  wire [7:0]  rd_val,
    input  wire        hland,
    input  wire [7:0]  hland_d,
    output wire        miso
);
    `include "fv_seq.vh"
    // payload / delay: free constants in the proof (anyconst); fixed by -DFV_PAYLOAD / -DFV_DELAY for the calibration sim
`ifdef FV_PAYLOAD
    wire [7:0] payload = `FV_PAYLOAD;
    wire [7:0] delay   = `FV_DELAY;
`else
    // free constants built from free per-step inputs: sampled once at the first clock, then held (a plain
    // (* anyconst *) wire is not held constant by the slang frontend: it was seen changing every step)
    (* anyseq *) wire [7:0] payload_free;
    (* anyseq *) wire [7:0] delay_free;
    reg        fc_init = 1'b0;
    reg [7:0]  payload_r = 8'd0, delay_r = 8'd0;
    always @(posedge clk) begin
        fc_init <= 1'b1;
        if (!fc_init) begin payload_r <= payload_free; delay_r <= delay_free; end
    end
    wire [7:0] payload = fc_init ? payload_r : payload_free;
    wire [7:0] delay   = fc_init ? delay_r : delay_free;
`endif
    reg [7:0]  idx;
    reg [15:0] gap;
    assign miso = 1'b0;
    wire [15:0] need = SEQ_GAP[idx*16 +: 16] + ((HAS_HI && idx == NSEQ-1) ? {8'd0, delay} : 16'd0);
    always @(posedge clk) begin
        if (!rst_n) begin
            idx <= 8'd0; gap <= 16'd0; wr <= 1'b0; addr <= 16'd0; wdata <= 8'd0; rd <= 1'b0;
        end else begin
            wr <= 1'b0; rd <= 1'b0;
            if (idx < NSEQ) begin
                if (gap == need) begin
                    wr <= 1'b1;
                    addr <= SEQ_ADDR[idx*16 +: 16];
                    wdata <= (HAS_HI && idx == NSEQ-1) ? payload : SEQ_DATA[idx*8 +: 8];
                    idx <= idx + 8'd1;
                    gap <= 16'd0;
                end else gap <= gap + 16'd1;
            end
        end
    end
endmodule
`default_nettype wire
