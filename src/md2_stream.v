// Metronome v2 stream k (wiki/SPEC_V2.md section 6.3). Adapted from sim/numerics/v2_sizing/rtl/md2_stream.v.
// Transmit: CUR (`cur`) holds the current byte, WB (`wb`) one word of lookahead. Receive: `cur` assembles a byte,
// PEND holds one completed byte waiting for a RAM write grant. Configuration is latch configuration (inputs);
// MODE, MSB and START take effect at the next rewind, LEN and MARK are used live.
`timescale 1ns/1ps
`default_nettype none
module md2_stream (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        cfg_mode,      // 0 transmit, 1 receive
    input  wire        cfg_msb,       // 1: most significant bit first
    input  wire [10:0] cfg_start,
    input  wire [11:0] cfg_len,
    input  wire [11:0] cfg_mark,
    // winning move of the stream's write group, and control requests (move and host combined)
    input  wire        adv,           // Sk.ADV
    input  wire        rx_we,         // Sk.RX
    input  wire        rx_bit,
    input  wire        rewind,
    input  wire        flush,
    input  wire        clr_starved,   // host CTL bit 7
    // sources and guards
    output wire        bit_out,       // Sk.BIT
    output wire [7:0]  byte_out,      // Sk.BYTE
    output wire        g_end,
    output wire        g_mark,
    output wire        g_byte,
    output reg         starved,
    output reg  [11:0] pos,
    output reg  [2:0]  bidx,
    // data RAM request (held until served)
    output wire        req,
    output wire        req_we,
    output wire [10:0] req_addr,      // byte address (word = req_addr[10:2])
    output wire [7:0]  req_wdata,
    input  wire        gnt,           // served this cycle
    input  wire [31:0] rdata          // RAM output (word read in the previous cycle)
);
    reg [10:0] ba;
    reg [7:0]  cur;
    reg        cv;
    reg [31:0] wb;
    reg        wv, rq, ld;
    reg [7:0]  pend;
    reg        pv;

    wire       tx    = ~cfg_mode;
    wire       end_c = (pos == cfg_len);
    wire       last  = (bidx == 3'd7);
    wire [1:0] lane  = ba[1:0];
    wire [2:0] bsel  = cfg_msb ? ~bidx : bidx;
    wire [7:0] lb    = wb[8*lane +: 8];

    wire tx_adv = tx & adv & ~end_c;
    wire bitin  = cfg_mode & rx_we & ~end_c;
    wire fl     = cfg_mode & flush & ~end_c;
    wire [7:0] nsh = cur | ({7'd0, bitin & rx_bit} << bsel);
    wire done   = (bitin & last) | (fl & ((bidx != 3'd0) | bitin));

    assign bit_out  = tx & cv & ~end_c & cur[bsel];
    assign byte_out = cfg_mode ? pend : cur;
    assign g_end    = end_c;
    assign g_mark   = (pos == cfg_mark) & (bidx == 3'd0);
    assign g_byte   = (bidx == 3'd0);

    assign req       = cfg_mode ? pv : rq;
    assign req_we    = cfg_mode;
    assign req_addr  = ba;
    assign req_wdata = pend;

    wire starve_tx = tx_adv & (~cv | (last & ~wv));          // advance without a byte, or byte end with no next
    wire starve_rx = cfg_mode & done & pv & ~gnt;

    always @(posedge clk) begin
        if (!rst_n) begin
            pos <= 12'd0; bidx <= 3'd0; ba <= 11'd0; cur <= 8'd0; cv <= 1'b0; wb <= 32'd0; wv <= 1'b0;
            rq <= 1'b0; ld <= 1'b0; pend <= 8'd0; pv <= 1'b0; starved <= 1'b0;
        end else begin
            if (tx) begin
                if (ld) begin wb <= rdata; wv <= 1'b1; ld <= 1'b0; end
                if (rq & gnt) begin rq <= 1'b0; ld <= 1'b1; end
                else if (~wv & ~rq & ~ld) rq <= 1'b1;
                if (~cv & wv) begin
                    cur <= lb; cv <= 1'b1; ba <= ba + 11'd1;
                    if (lane == 2'd3) wv <= 1'b0;
                end else if (tx_adv & cv) begin
                    if (~last) bidx <= bidx + 3'd1;
                    else begin
                        pos <= pos + 12'd1; bidx <= 3'd0;
                        if (wv) begin
                            cur <= lb; ba <= ba + 11'd1;
                            if (lane == 2'd3) wv <= 1'b0;
                        end else begin
                            cv <= 1'b0;
                        end
                    end
                end
            end else begin
                if (pv & gnt) begin pv <= 1'b0; ba <= ba + 11'd1; end
                if (bitin & ~done) begin cur <= nsh; bidx <= bidx + 3'd1; end
                if (done) begin
                    cur <= 8'd0; bidx <= 3'd0; pos <= pos + 12'd1;
                    if (~(pv & ~gnt)) begin pend <= nsh; pv <= 1'b1; end
                end
            end
            starved <= starve_tx | starve_rx | (starved & ~clr_starved);
            if (rewind) begin
                pos <= 12'd0; bidx <= 3'd0; ba <= cfg_start; cur <= 8'd0; cv <= 1'b0; wv <= 1'b0;
                rq <= 1'b0; ld <= 1'b0; pv <= 1'b0;
            end
        end
    end
endmodule
`default_nettype wire
