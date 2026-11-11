// Data-RAM pointers and memory arbiter (SPEC 6.1). Two pointers (PTR, D, RDY, one pending REQ each) and one
// pending host request (SPEC 9a.4: a new one overwrites an unserved one, no flag); the arbiter serves one request per cycle in priority P0, P1, host. A write writes in the
// cycle it is served; a fetch/read served in cycle t addresses the RAM at the end of t and its byte lands at the
// end of t+1.
`timescale 1ns/1ps
`default_nettype none
module md_ptrs (
    input  wire        clk,
    input  wire        rst_n,
    // move write groups P0.*, P1.*
    input  wire [1:0]  we,
    input  wire [3:0]  sel,         // per pointer: 0 AL, 1 AH, 2 W, 3 R (md_movebus)
    input  wire [15:0] d,
    // host request (queued by the SPI link)
    input  wire        hreq_set,
    input  wire        hreq_wr,
    input  wire [10:0] hreq_addr,
    input  wire [7:0]  hreq_d,
    output wire [1:0]  rdy,
    output wire [15:0] pd,          // Pk.D
    output wire        memhaz,      // a request overwrote a pending (unserved) one
    output reg         hland,       // host read byte lands this cycle
    output wire [7:0]  hland_d,
    // data RAM port
    output wire        m_en,
    output wire        m_we,
    output wire [10:0] m_addr,
    output wire [7:0]  m_wd,
    input  wire [7:0]  m_rd
);
    localparam [1:0] RQ_NONE = 2'd0, RQ_FETCH = 2'd1, RQ_WRITE = 2'd2;

    wire [1:0]  rq_w0, rq_w1;   // REQ of P0, P1
    wire [10:0] ptr_w0, ptr_w1, rqa_w0, rqa_w1;
    wire [7:0]  rqd_w0, rqd_w1;
    reg        hq, hqw;
    reg [10:0] hqa;
    reg [7:0]  hqd;

    wire g0 = (rq_w0 != RQ_NONE);
    wire g1 = ~g0 & (rq_w1 != RQ_NONE);
    wire gh = ~g0 & ~g1 & hq;

    assign m_en   = g0 | g1 | gh;
    assign m_we   = (g0 & (rq_w0 == RQ_WRITE)) | (g1 & (rq_w1 == RQ_WRITE)) | (gh & hqw);
    assign m_addr = g0 ? ((rq_w0 == RQ_WRITE) ? rqa_w0 : ptr_w0) :
                    g1 ? ((rq_w1 == RQ_WRITE) ? rqa_w1 : ptr_w1) : hqa;
    assign m_wd   = g0 ? rqd_w0 : (g1 ? rqd_w1 : hqd);
    assign hland_d = m_rd;

    wire [1:0] served = {g1, g0};
    wire [1:0] hz;

    genvar k;
    generate
        for (k = 0; k < 2; k = k + 1) begin : g_p
            wire [1:0] dk = sel[2*k +: 2];
            wire [7:0] vk = d[8*k +: 8];
            wire op_al = we[k] && (dk == 2'd0);
            wire op_ah = we[k] && (dk == 2'd1);
            wire op_w  = we[k] && (dk == 2'd2);
            wire op_r  = we[k] && (dk == 2'd3);
            wire setrq = we[k];
            reg [10:0] ptr, rqa;
            reg [7:0]  dr, rqd;
            reg [1:0]  rq;
            reg        rdyr, land, lok;
            // SPEC 9a.2: MEMHAZ only when an unserved request is replaced; served-this-cycle is not pending.
            assign hz[k] = setrq && (rq != RQ_NONE) && !served[k];
            always @(posedge clk) begin
                if (!rst_n) begin
                    ptr <= 11'd0; dr <= 8'd0; rdyr <= 1'b0; rq <= RQ_NONE;
                    rqa <= 11'd0; rqd <= 8'd0; land <= 1'b0; lok <= 1'b0;
                end else begin
                    land <= served[k] && (rq == RQ_FETCH);
                    lok  <= !setrq;
                    // landing byte (SPEC 9a.3): D always loads it; a request-setting pointer move in the serve
                    // cycle (lok = 0) or in the landing cycle (setrq) keeps RDY at 0.
                    if (land) dr <= m_rd;
                    if (setrq)             rdyr <= 1'b0;
                    else if (land && lok)  rdyr <= 1'b1;
                    if (op_al)             ptr <= {ptr[10:8], vk};
                    else if (op_ah)        ptr <= {vk[2:0], ptr[7:0]};
                    else if (op_w | op_r)  ptr <= ptr + 11'd1;
                    if (op_w) begin
                        rq  <= RQ_WRITE;
                        rqa <= ptr;
                        rqd <= vk;
                    end else if (setrq) begin
                        rq <= RQ_FETCH;
                    end else if (served[k]) begin
                        rq <= RQ_NONE;
                    end
                end
            end
            assign rdy[k] = rdyr;
            assign pd[8*k +: 8] = dr;
            if (k == 0) begin : g_o0
                assign rq_w0 = rq; assign ptr_w0 = ptr; assign rqa_w0 = rqa; assign rqd_w0 = rqd;
            end else begin : g_o1
                assign rq_w1 = rq; assign ptr_w1 = ptr; assign rqa_w1 = rqa; assign rqd_w1 = rqd;
            end
        end
    endgenerate
    assign memhaz = |hz;

    always @(posedge clk) begin
        if (!rst_n) begin
            hq <= 1'b0; hqw <= 1'b0; hqa <= 11'd0; hqd <= 8'd0; hland <= 1'b0;
        end else begin
            hland <= gh & ~hqw;
            if (hreq_set) begin
                hq <= 1'b1; hqw <= hreq_wr; hqa <= hreq_addr; hqd <= hreq_d;
            end else if (gh) begin
                hq <= 1'b0;
            end
        end
    end
endmodule
`default_nettype wire
