// Metronome v2 stream unit (sizing model): presents a region of a 2 KB / 512 x 32 data RAM as a bit sequence.
// Transmit: sh holds the current byte, wbuf one word of lookahead. Receive: sh assembles a byte, pend holds one
// completed byte waiting for a RAM write grant. See sim/numerics/v2_sizing/STREAM_SIZING.md for the contract.
module md2_stream (
    input  wire        clk,
    input  wire        rst_n,
    // configuration (constant while running; changing it needs a rewind)
    input  wire        cfg_mode,      // 0 transmit, 1 receive
    input  wire        cfg_msb,       // 1: most significant bit first
    input  wire [10:0] cfg_start,     // byte address of the region
    input  wire [11:0] cfg_len,       // bytes, 0..2048
    input  wire [11:0] cfg_mark,      // byte position for MARK
    // program ports (act at the end of the cycle)
    input  wire        adv,
    input  wire        rx_bit_we,
    input  wire        rx_bit,
    input  wire        ctl_we,
    input  wire [1:0]  ctl,           // [0] rewind, [1] flush
    input  wire        clr_starved,
    // sources and guards
    output wire        bit_out,
    output wire [7:0]  byte_out,
    output wire        g_end,
    output wire        g_mark,
    output wire        g_byte,
    output wire        starved,
    output wire [11:0] pos,
    output wire [2:0]  bitidx,
    // RAM interface
    output wire        req,
    output wire        req_we,
    output wire [8:0]  req_addr,
    output wire [31:0] req_wdata,
    output wire [3:0]  req_wmask,
    input  wire        gnt,
    input  wire [31:0] rdata
);
    reg        inited;
    reg [11:0] pos_r;
    reg [2:0]  bidx;
    reg [10:0] ba;        // tx: address of the next byte to move into sh; rx: address of the pending write
    reg [31:0] wbuf;
    reg        bv;        // wbuf holds the word containing ba
    reg        rq;        // read request outstanding
    reg        rdw;       // read granted last cycle, rdata valid now
    reg [7:0]  sh;
    reg        shv;       // tx: sh holds the current byte
    reg [7:0]  pend;
    reg        pend_v;
    reg        starved_r;

    wire       tx      = ~cfg_mode;
    wire       end_c   = (pos_r == cfg_len);
    wire       rew     = (ctl_we & ctl[0]) | ~inited;
    wire       flush   = ctl_we & ctl[1];
    wire       last    = (bidx == 3'd7);
    wire [1:0] lane    = ba[1:0];
    wire [2:0] bsel    = cfg_msb ? ~bidx : bidx;

    reg [7:0] lane_byte;
    always @(*) begin
        case (lane)
            2'd0:    lane_byte = wbuf[7:0];
            2'd1:    lane_byte = wbuf[15:8];
            2'd2:    lane_byte = wbuf[23:16];
            default: lane_byte = wbuf[31:24];
        endcase
    end

    // transmit
    wire tx_adv = tx & adv & ~end_c;
    // receive: place an incoming bit at its bit-order position, then complete on byte end or flush
    wire rx_act   = cfg_mode & ~end_c;
    wire rx_shift = rx_act & rx_bit_we;
    wire [7:0] nsh = sh | ({7'd0, rx_shift & rx_bit} << bsel);
    wire rx_done  = (rx_shift & last) | (rx_act & flush & ((bidx != 3'd0) | rx_bit_we));

    assign bit_out  = tx & shv & ~end_c & sh[bsel];
    assign byte_out = sh;
    assign g_end    = end_c;
    assign g_mark   = (pos_r == cfg_mark) & (bidx == 3'd0);
    assign g_byte   = (bidx == 3'd0);
    assign starved  = starved_r;
    assign pos      = pos_r;
    assign bitidx   = bidx;

    assign req       = cfg_mode ? pend_v : rq;
    assign req_we    = cfg_mode;
    assign req_addr  = ba[10:2];
    assign req_wdata = {pend, pend, pend, pend};
    assign req_wmask = cfg_mode ? (4'b0001 << lane) : 4'b0000;

    always @(posedge clk) begin
        if (!rst_n) begin
            inited <= 1'b0; pos_r <= 12'd0; bidx <= 3'd0; ba <= 11'd0; wbuf <= 32'd0; bv <= 1'b0;
            rq <= 1'b0; rdw <= 1'b0; sh <= 8'd0; shv <= 1'b0; pend <= 8'd0; pend_v <= 1'b0; starved_r <= 1'b0;
        end else begin
            inited <= 1'b1;
            if (clr_starved) starved_r <= 1'b0;
            // RAM read handshake
            if (rdw) begin wbuf <= rdata; bv <= 1'b1; rdw <= 1'b0; end
            if (rq & gnt) begin rq <= 1'b0; rdw <= 1'b1; end
            else if (tx & ~bv & ~rq & ~rdw) rq <= 1'b1;
            if (tx) begin
                if (tx_adv & ~shv) starved_r <= 1'b1;            // stalled: advance ignored
                if (~shv & bv) begin
                    sh <= lane_byte; shv <= 1'b1; ba <= ba + 11'd1;
                    if (lane == 2'd3) bv <= 1'b0;
                end else if (tx_adv & shv) begin
                    if (~last) bidx <= bidx + 3'd1;
                    else begin
                        pos_r <= pos_r + 12'd1; bidx <= 3'd0;
                        if (bv) begin
                            sh <= lane_byte; ba <= ba + 11'd1;
                            if (lane == 2'd3) bv <= 1'b0;
                        end else begin
                            shv <= 1'b0; starved_r <= 1'b1;
                        end
                    end
                end
            end else begin
                if (gnt & pend_v) begin pend_v <= 1'b0; ba <= ba + 11'd1; end
                if (rx_shift & ~rx_done) begin sh <= nsh; bidx <= bidx + 3'd1; end
                if (rx_done) begin
                    sh <= 8'd0; bidx <= 3'd0; pos_r <= pos_r + 12'd1;
                    if (pend_v & ~gnt) starved_r <= 1'b1;        // overflow: byte dropped
                    else begin pend <= nsh; pend_v <= 1'b1; end
                end
            end
            if (rew) begin
                pos_r <= 12'd0; bidx <= 3'd0; ba <= cfg_start; bv <= 1'b0; shv <= 1'b0; sh <= 8'd0;
                rq <= 1'b0; rdw <= 1'b0; pend_v <= 1'b0;
            end
        end
    end
endmodule
