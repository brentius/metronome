// v3 formal properties (wiki/SPEC_V2.md 12.3, 12.4) on md2_stream (CAP = 1, the S0 instance) and md2_mem.
// Freeze: a frozen cycle changes no stream or pointer state and grants the RAM only to the host, except the RAM
// landing capture (the stream's WB and the pointer's D in the cycle after a serve, 12.3). Capture: a push writes
// the record, sets PV and adds 4 to POS; a push behind an unserved record sets STARVED and leaves POS.
// Inputs are free except the interface guarantees of the top level: cap_push only when CEN and not frozen.
module fv_v3_stream_props (
    input wire clk, input wire rst_n, input wire frz, input wire frzd, input wire cen, input wire push,
    input wire cap_push, input wire [31:0] cap_rec, input wire rewind, input wire clr_starved, input wire gnt,
    input wire [31:0] rdata, input wire tx, input wire end_c,
    input wire [11:0] pos, input wire [2:0] bidx, input wire [10:0] ba, input wire [7:0] cur, input wire cv,
    input wire [31:0] wb, input wire wv, input wire rq, input wire ld, input wire [7:0] pend, input wire pv,
    input wire starved, input wire cap_en, input wire adv, input wire rx_we
);
    reg init = 1'b0;
    always @(posedge clk) begin init <= 1'b1; if (!init) assume (!rst_n); end
    always @(posedge clk) assume (!cap_push || (cap_en && !frz));
    always @(posedge clk) assume (!frz || (!adv && !rx_we));     // no moves while frozen (cores are frozen)
    reg p_rstn, p_frz, p_frzd, p_rew, p_clr, p_gnt, p_tx, p_ld, p_cen, p_push, p_end, p_pv;
    reg [11:0] p_pos; reg [2:0] p_bidx; reg [10:0] p_ba; reg [7:0] p_cur, p_pend; reg p_cv, p_wv, p_rq, p_st;
    reg [31:0] p_wb, p_rdata, p_rec;
    always @(posedge clk) begin
        p_rstn <= rst_n; p_frz <= frz; p_frzd <= frzd; p_rew <= rewind; p_clr <= clr_starved; p_gnt <= gnt;
        p_tx <= tx; p_ld <= ld; p_cen <= cen; p_push <= push; p_end <= end_c; p_pv <= pv;
        p_pos <= pos; p_bidx <= bidx; p_ba <= ba; p_cur <= cur; p_pend <= pend; p_cv <= cv; p_wv <= wv;
        p_rq <= rq; p_st <= starved; p_wb <= wb; p_rdata <= rdata; p_rec <= cap_rec;
    end
    wire ok = init && p_rstn;
    // 12.3: frozen cycle without a host rewind or STARVED clear: every state bit holds, WB only takes a landing
    always @(posedge clk) if (ok && p_frz && !p_rew && !p_clr) begin
        assert (pos == p_pos && bidx == p_bidx && ba == p_ba && cur == p_cur && cv == p_cv && wv == p_wv);
        assert (rq == p_rq && ld == p_ld && pend == p_pend && pv == p_pv && starved == p_st);
        assert (wb == ((p_tx && p_ld && !p_frzd) ? p_rdata : p_wb));
    end
    // 12.4: an accepted push
    always @(posedge clk) if (ok && !p_rew && p_push && !(p_pv && !p_gnt)) begin
        assert (wb == p_rec && pv && pos == p_pos + 12'd4);
    end
    // 12.4: a push behind an unserved record is dropped and raises STARVED
    always @(posedge clk) if (ok && !p_rew && p_push && p_pv && !p_gnt) begin
        assert (starved && pos == p_pos && wb == p_wb && pv);
    end
    // 12.4: capture mode ignores the transmit path entirely (no read request, no LD)
    always @(posedge clk) if (ok && p_cen && !p_rew && !p_ld) assert (!ld);
    always @(posedge clk) begin
        cover (ok && p_frz && p_tx && p_ld && !p_frzd);
        cover (ok && p_push && p_pv && !p_gnt);
        cover (ok && p_push && p_pv && p_gnt);
    end
endmodule

module fv_v3_mem_props (
    input wire clk, input wire rst_n, input wire frz, input wire frzd, input wire [1:0] s_gnt, input wire gp,
    input wire gh, input wire hq, input wire [10:0] ptr, input wire [1:0] rq, input wire [10:0] rqa,
    input wire [7:0] rqd, input wire land, input wire lok, input wire [1:0] plane, input wire p_rdy,
    input wire [7:0] p_dat, input wire p_we, input wire [31:0] m_rd, input wire m_we, input wire h_wr
);
    reg init = 1'b0;
    always @(posedge clk) begin init <= 1'b1; if (!init) assume (!rst_n); end
    always @(posedge clk) assume (!(frz && p_we));          // no moves while frozen (cores are frozen, 12.3)
    reg p_rstn, p_frz, p_frzd, p_land, p_lok, p_rdy0; reg [10:0] p_ptr, p_rqa; reg [1:0] p_rq, p_plane;
    reg [7:0] p_rqd, p_dat0; reg [31:0] p_mrd;
    always @(posedge clk) begin
        p_rstn <= rst_n; p_frz <= frz; p_frzd <= frzd; p_land <= land; p_lok <= lok; p_rdy0 <= p_rdy;
        p_ptr <= ptr; p_rqa <= rqa; p_rq <= rq; p_plane <= plane; p_rqd <= rqd; p_dat0 <= p_dat; p_mrd <= m_rd;
    end
    wire ok = init && p_rstn;
    // 12.3: while frozen only the host request is served
    always @(posedge clk) if (init && rst_n && frz) assert (s_gnt == 2'b00 && !gp && (gh == hq));
    // 12.3: pointer state holds in a frozen cycle; D takes only the landing of a read served before the freeze
    always @(posedge clk) if (ok && p_frz) begin
        assert (ptr == p_ptr && rq == p_rq && rqa == p_rqa && rqd == p_rqd && land == p_land && lok == p_lok);
        assert (plane == p_plane && p_rdy == p_rdy0);
        assert (p_dat == ((p_land && !p_frzd) ? p_mrd[8*p_plane +: 8] : p_dat0));
    end
    always @(posedge clk) cover (ok && p_frz && p_land && !p_frzd);
endmodule

module fv_v3_top (
    input wire clk, input wire rst_n, input wire frz, input wire frzd,
    // stream
    input wire cfg_mode, input wire cfg_msb, input wire [10:0] cfg_start, input wire [11:0] cfg_len,
    input wire [11:0] cfg_mark, input wire adv, input wire rx_we, input wire rx_bit, input wire rewind,
    input wire flush, input wire clr_starved, input wire gnt, input wire [31:0] rdata, input wire cap_en,
    input wire cap_push, input wire [31:0] cap_rec,
    // mem
    input wire [1:0] s_req, input wire [1:0] s_we, input wire [21:0] s_addr, input wire [15:0] s_wd,
    input wire s0_word, input wire [31:0] s0_wword, input wire p_we, input wire [1:0] p_sel, input wire [7:0] p_d,
    input wire h_set, input wire h_wr, input wire [10:0] h_addr, input wire [7:0] h_d, input wire [31:0] m_rd
);
    wire bo, ge, gm, gb, st, rq_, rqw, rword; wire [7:0] by, rwd; wire [11:0] ps; wire [2:0] bi; wire [10:0] ra;
    wire [31:0] rww;
    md2_stream #(.CAP(1)) us (
        .clk(clk), .rst_n(rst_n), .frz(frz), .frzd(frzd), .cap_en(cap_en), .cap_push(cap_push), .cap_rec(cap_rec),
        .replay_en(1'b0), .replay_apply(1'b0), .replay_late(1'b0),
        .cfg_mode(cfg_mode), .cfg_msb(cfg_msb), .cfg_start(cfg_start), .cfg_len(cfg_len), .cfg_mark(cfg_mark),
        .adv(adv), .rx_we(rx_we), .rx_bit(rx_bit), .rewind(rewind), .flush(flush), .clr_starved(clr_starved),
        .bit_out(bo), .byte_out(by), .g_end(ge), .g_mark(gm), .g_byte(gb), .starved(st), .pos(ps), .bidx(bi),
        .req(rq_), .req_we(rqw), .req_addr(ra), .req_wdata(rwd), .req_word(rword), .req_wword(rww),
        .gnt(gnt), .rdata(rdata));
    wire [1:0] sg; wire prdy, phaz, hl, mren, mwe; wire [7:0] pdat, hld; wire [8:0] madr; wire [3:0] mbe;
    wire [31:0] mwd;
    md2_mem um (
        .clk(clk), .rst_n(rst_n), .frz(frz), .frzd(frzd), .s_req(s_req), .s_we(s_we), .s_addr(s_addr),
        .s_wd(s_wd), .s_gnt(sg), .s0_word(s0_word), .s0_wword(s0_wword), .p_we(p_we), .p_sel(p_sel), .p_d(p_d),
        .p_rdy(prdy), .p_dat(pdat), .p_haz(phaz), .h_set(h_set), .h_wr(h_wr), .h_addr(h_addr), .h_d(h_d),
        .h_land(hl), .h_land_d(hld), .m_ren(mren), .m_we(mwe), .m_addr(madr), .m_be(mbe), .m_wd(mwd), .m_rd(m_rd));
endmodule

bind md2_stream fv_v3_stream_props fv_s (.*);
bind md2_mem fv_v3_mem_props fv_m (.*);
