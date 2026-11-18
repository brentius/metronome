// Metronome v2 data RAM arbiter, pointer P0 and host request slot (wiki/SPEC_V2.md 6.1-6.2, SPEC v1 6.1 and
// 9a.2-9a.4 for the pointer, adapted from v1 md_ptrs.v). One access per cycle to the 512 x 32 RAM, priority S0, S1,
// P0, host. A write is performed at the end of the cycle it is served; a read served in s has its word at the RAM
// output during s+1 and the requester loads its byte at the end of s+1.
`timescale 1ns/1ps
`default_nettype none
module md2_mem (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        frz,         // v3: frozen cycle: only the host is served, P0 holds (SPEC v2 12.3)
    input  wire        frzd,        // v3: the previous cycle was frozen (P0 landing capture)
    // streams
    input  wire [1:0]  s_req,
    input  wire [1:0]  s_we,
    input  wire [21:0] s_addr,      // 2 x byte address
    input  wire [15:0] s_wd,        // 2 x byte
    output wire [1:0]  s_gnt,
    input  wire        s0_word,     // v3: S0 requests a whole-word write of s0_wword (edge capture)
    input  wire [31:0] s0_wword,
    // pointer P0: winning move of its write group (sel 0 AL, 1 AH, 2 W, 3 R)
    input  wire        p_we,
    input  wire [1:0]  p_sel,
    input  wire [7:0]  p_d,
    output reg         p_rdy,
    output reg  [7:0]  p_dat,
    output wire        p_haz,       // a pointer move replaced an unserved request (MEMHAZ)
    // host request (a new one overwrites an unserved one)
    input  wire        h_set,
    input  wire        h_wr,
    input  wire [10:0] h_addr,
    input  wire [7:0]  h_d,
    output reg         h_land,      // host read byte lands this cycle
    output wire [7:0]  h_land_d,
    // RAM port
    output wire        m_ren,
    output wire        m_we,
    output wire [8:0]  m_addr,
    output wire [3:0]  m_be,
    output wire [31:0] m_wd,
    input  wire [31:0] m_rd
);
    localparam [1:0] RQ_NONE = 2'd0, RQ_FETCH = 2'd1, RQ_WRITE = 2'd2;

    reg [10:0] ptr, rqa;
    reg [7:0]  rqd;
    reg [1:0]  rq;
    reg        land, lok;
    reg [1:0]  plane;
    reg        hq, hqw;
    reg [10:0] hqa;
    reg [7:0]  hqd;
    reg [1:0]  hlane;

    wire gs0 = s_req[0] & ~frz;
    wire gs1 = ~s_req[0] & s_req[1] & ~frz;
    wire gp  = ~(|s_req) & (rq != RQ_NONE) & ~frz;
    wire gh  = (frz | (~(|s_req) & (rq == RQ_NONE))) & hq;
    wire gw  = gs0 & s0_word;
    assign s_gnt = {gs1, gs0};

    wire        pw = (rq == RQ_WRITE);
    wire [10:0] a  = gs0 ? s_addr[10:0] : (gs1 ? s_addr[21:11] : (gp ? (pw ? rqa : ptr) : hqa));
    wire [7:0]  wd = gs0 ? s_wd[7:0] : (gs1 ? s_wd[15:8] : (gp ? rqd : hqd));
    assign m_we   = (gs0 & s_we[0]) | (gs1 & s_we[1]) | (gp & pw) | (gh & hqw);
    assign m_ren  = (gs0 | gs1 | gp | gh) & ~m_we;
    assign m_addr = a[10:2];
    assign m_be   = gw ? 4'hF : (4'd1 << a[1:0]);
    assign m_wd   = gw ? s0_wword : {4{wd}};
    assign h_land_d = m_rd[8*hlane +: 8];

    // pointer (SPEC v1 9a.2/9a.3): every move sets a request and clears RDY; a request-setting move in the serve
    // cycle or the landing cycle keeps RDY at 0; MEMHAZ only when an unserved request is replaced
    wire op_al = p_we & (p_sel == 2'd0);
    wire op_ah = p_we & (p_sel == 2'd1);
    wire op_w  = p_we & (p_sel == 2'd2);
    wire op_r  = p_we & (p_sel == 2'd3);
    assign p_haz = p_we & (rq != RQ_NONE) & ~gp;

    always @(posedge clk) begin
        if (!rst_n) begin
            ptr <= 11'd0; p_dat <= 8'd0; p_rdy <= 1'b0; rq <= RQ_NONE; rqa <= 11'd0; rqd <= 8'd0;
            land <= 1'b0; lok <= 1'b0; plane <= 2'd0;
            hq <= 1'b0; hqw <= 1'b0; hqa <= 11'd0; hqd <= 8'd0; h_land <= 1'b0; hlane <= 2'd0;
        end else begin
            if (!frz) begin
                land  <= gp & (rq == RQ_FETCH);
                plane <= ptr[1:0];
                lok   <= ~p_we;
            end
            if (land & ~frzd) p_dat <= m_rd[8*plane +: 8];      // v3: captured even in a frozen cycle (12.3)
            if (p_we)                   p_rdy <= 1'b0;
            else if (land & lok & ~frz) p_rdy <= 1'b1;
            if (op_al)            ptr <= {ptr[10:8], p_d};
            else if (op_ah)       ptr <= {p_d[2:0], ptr[7:0]};
            else if (op_w | op_r) ptr <= ptr + 11'd1;
            if (op_w) begin
                rq <= RQ_WRITE; rqa <= ptr; rqd <= p_d;
            end else if (p_we) begin
                rq <= RQ_FETCH;
            end else if (gp) begin
                rq <= RQ_NONE;
            end
            h_land <= gh & ~hqw;
            hlane  <= hqa[1:0];
            if (h_set) begin
                hq <= 1'b1; hqw <= h_wr; hqa <= h_addr; hqd <= h_d;
            end else if (gh) begin
                hq <= 1'b0;
            end
        end
    end
endmodule
`default_nettype wire
