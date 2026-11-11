// Formal properties for md_ptrs (SPEC 6.1, 9a.2, 9a.3, 9a.4). Bound into the DUT scope.
// MEMORY MODEL: the RAM is abstracted to the free input m_rd (no shadow array). That is sound for the control
// properties and for "the byte that lands in D is the m_rd of the landing cycle"; it does NOT check that m_rd
// equals the byte last written to the address (that is the RAM's contract, covered by lockstep simulation).
// Move inputs: we/sel/d come from md_wgroup/md_movebus: at most one op per pointer per cycle; sel is the port
// within the group (0 AL, 1 AH, 2 W, 3 R) and every we[k] is a request-setting op.
module fv_ptrs_props (
    input wire clk, input wire rst_n,
    input wire [1:0] we, input wire [3:0] sel, input wire [15:0] d,
    input wire hreq_set, input wire hreq_wr, input wire [10:0] hreq_addr, input wire [7:0] hreq_d,
    input wire [1:0] rdy, input wire [15:0] pd, input wire memhaz, input wire hland, input wire [7:0] hland_d,
    input wire m_en, input wire m_we, input wire [10:0] m_addr, input wire [7:0] m_wd, input wire [7:0] m_rd,
    input wire [1:0] rq_w0, input wire [1:0] rq_w1, input wire [10:0] ptr_w0, input wire [10:0] ptr_w1,
    input wire [10:0] rqa_w0, input wire [10:0] rqa_w1, input wire [7:0] rqd_w0, input wire [7:0] rqd_w1,
    input wire hq, input wire hqw, input wire [10:0] hqa, input wire [7:0] hqd,
    input wire g0, input wire g1, input wire gh
);
    localparam [1:0] NONE = 2'd0, FETCH = 2'd1, WRITE = 2'd2;
    reg pv = 1'b0;
    always @(posedge clk) begin pv <= 1'b1; if (!pv) assume(!rst_n); end

    // ---- per-pointer decode, from SPEC 6.1 op list (independent of the RTL's localparams: dst 50..57)
    wire [1:0] rq  [0:1];  assign rq[0] = rq_w0;   assign rq[1] = rq_w1;
    wire [10:0] ptr [0:1]; assign ptr[0] = ptr_w0; assign ptr[1] = ptr_w1;
    wire [10:0] rqa [0:1]; assign rqa[0] = rqa_w0; assign rqa[1] = rqa_w1;
    wire [7:0] rqd [0:1];  assign rqd[0] = rqd_w0; assign rqd[1] = rqd_w1;
    wire [1:0] pend = {rq_w1 != NONE, rq_w0 != NONE};
    wire [1:0] served = {g1, g0};

    // SPEC 6.1 arbiter: one request per cycle, priority P0 > P1 > host.
    always @(*) begin
        assert (g0 == pend[0]);
        assert (g1 == (!pend[0] && pend[1]));
        assert (gh == (!pend[0] && !pend[1] && hq));
        assert (!(g0 && g1) && !(g0 && gh) && !(g1 && gh));          // at most one served
        assert (m_en == (g0 || g1 || gh));
        if (g0) begin
            assert (m_we == (rq_w0 == WRITE));
            assert (m_addr == ((rq_w0 == WRITE) ? rqa_w0 : ptr_w0));
            if (rq_w0 == WRITE) assert (m_wd == rqd_w0);
        end
        if (g1) begin
            assert (m_we == (rq_w1 == WRITE));
            assert (m_addr == ((rq_w1 == WRITE) ? rqa_w1 : ptr_w1));
            if (rq_w1 == WRITE) assert (m_wd == rqd_w1);
        end
        if (gh) begin
            assert (m_we == hqw && m_addr == hqa);
            if (hqw) assert (m_wd == hqd);
        end
        if (!m_en) assert (!m_we);
        // invariant needed for induction: REQ is never the unused encoding 3
        if (pv) assert (rq_w0 != 2'd3 && rq_w1 != 2'd3);
    end

        wire [1:0] op_al, op_ah, op_w, op_r, setrq;
    genvar k;
    generate for (k = 0; k < 2; k = k + 1) begin : g_k
        wire [1:0] dk = sel[2*k +: 2];
        assign op_al[k] = we[k] && dk == 2'd0;
        assign op_ah[k] = we[k] && dk == 2'd1;
        assign op_w[k]  = we[k] && dk == 2'd2;
        assign op_r[k]  = we[k] && dk == 2'd3;
        assign setrq[k] = op_al[k] | op_ah[k] | op_w[k] | op_r[k];
    end endgenerate
    always @(*) assert (setrq == we);    // every pointer-group write sets a request (SPEC 6.1)

    // SPEC 9a.2: MEMHAZ iff a pointer op replaces a request that is still unserved at the end of the cycle.
    // A request served in cycle t may be replaced in t without a hazard; the host never raises it (9a.4).
    always @(*) assert (memhaz == (|(setrq & pend & ~served)));
    always @(*) if (setrq == 2'b00) assert (!memhaz);

    // ---- shadow of previous cycles
    reg p_rstn, p2_rstn, p_hreq_set, p_hreq_wr, p_hland_ok;
    reg [1:0] p_setrq, p2_setrq, p_served, p2_served, p_pend, p_op_w, p_op_r, p_op_al, p_op_ah, p_rdy;
    reg [1:0] p_fetch_served, p2_fetch_served;
    reg [10:0] p_ptr0, p_ptr1, p_hreq_addr; reg [7:0] p_d0, p_d1, p_hreq_d, p_m_rd, p_m_rd2;
    reg [10:0] p_rqa0, p_rqa1; reg [7:0] p_rqd0, p_rqd1; reg [1:0] p_rq0, p_rq1;
    reg p_gh, p_hqw, p_hq;
    always @(posedge clk) begin
        p_rstn <= rst_n; p2_rstn <= p_rstn;
        p_setrq <= setrq; p2_setrq <= p_setrq; p_served <= served; p2_served <= p_served;
        p_pend <= pend; p_op_w <= op_w; p_op_r <= op_r; p_op_al <= op_al; p_op_ah <= op_ah; p_rdy <= rdy;
        p_fetch_served <= {g1 && rq_w1 == FETCH, g0 && rq_w0 == FETCH};
        p2_fetch_served <= p_fetch_served;
        p_ptr0 <= ptr_w0; p_ptr1 <= ptr_w1; p_d0 <= d[7:0]; p_d1 <= d[15:8];
        p_rq0 <= rq_w0; p_rq1 <= rq_w1; p_rqa0 <= rqa_w0; p_rqa1 <= rqa_w1; p_rqd0 <= rqd_w0; p_rqd1 <= rqd_w1;
        p_m_rd <= m_rd; p_m_rd2 <= p_m_rd;
        p_hreq_set <= hreq_set; p_hreq_wr <= hreq_wr; p_hreq_addr <= hreq_addr; p_hreq_d <= hreq_d;
        p_gh <= gh; p_hqw <= hqw; p_hq <= hq;
    end
    wire ok1 = pv && p_rstn;                // previous cycle was a normal cycle
    wire ok2 = ok1 && p2_rstn;              // and the one before it

    // reset values
    always @(posedge clk) if (pv && !p_rstn)
        assert (rq_w0 == NONE && rq_w1 == NONE && ptr_w0 == 0 && ptr_w1 == 0 && rdy == 2'b00 && !hq && !hland);

    // ---- SPEC 6.1 pointer/request update, per pointer
    wire [10:0] pptr [0:1]; assign pptr[0] = p_ptr0; assign pptr[1] = p_ptr1;
    wire [7:0] pdv [0:1]; assign pdv[0] = p_d0; assign pdv[1] = p_d1;
    wire [1:0] prq [0:1]; assign prq[0] = p_rq0; assign prq[1] = p_rq1;
    wire [10:0] prqa [0:1]; assign prqa[0] = p_rqa0; assign prqa[1] = p_rqa1;
    wire [7:0] prqd [0:1]; assign prqd[0] = p_rqd0; assign prqd[1] = p_rqd1;
    generate for (k = 0; k < 2; k = k + 1) begin : g_seq
        wire [10:0] expptr = p_op_al[k] ? {pptr[k][10:8], pdv[k]} : p_op_ah[k] ? {pdv[k][2:0], pptr[k][7:0]} :
                             (p_op_w[k] | p_op_r[k]) ? pptr[k] + 11'd1 : pptr[k];
        // SPEC 6.1: AL/AH replace one part of PTR; W and R post-increment PTR.
        always @(posedge clk) if (ok1) assert (ptr[k] == expptr);
        // SPEC 6.1: W = write(PTR, v) with the PRE-increment PTR; AL/AH/R = fetch; otherwise a served request
        // clears REQ and an unserved one persists unchanged.
        always @(posedge clk) if (ok1) begin
            if (p_op_w[k]) begin
                assert (rq[k] == WRITE && rqa[k] == pptr[k] && rqd[k] == pdv[k]);
            end else if (p_setrq[k]) begin
                assert (rq[k] == FETCH);
            end else if (p_served[k]) begin
                assert (rq[k] == NONE);
            end else begin
                assert (rq[k] == prq[k] && rqa[k] == prqa[k] && rqd[k] == prqd[k]);
            end
        end
        // SPEC 6.1/9a.3: any request-setting op clears RDY in the following cycle.
        always @(posedge clk) if (ok1 && p_setrq[k]) assert (!rdy[k]);
        // SPEC 9a.3: RDY rises only exactly one cycle after the landing (visible t+2), and only if there was
        // no request-setting op in the serve cycle t or the landing cycle t+1; D holds the landing-cycle m_rd.
        always @(posedge clk) if (ok2 && rdy[k] && !p_rdy[k]) begin
            assert (p2_fetch_served[k] && !p2_setrq[k] && !p_setrq[k]);
            assert (pd[8*k +: 8] == p_m_rd);
        end
        // ... and it does rise in exactly that situation (not merely only-if).
        always @(posedge clk) if (ok2 && p2_fetch_served[k] && !p2_setrq[k] && !p_setrq[k]) begin
            assert (rdy[k]);
            assert (pd[8*k +: 8] == p_m_rd);
        end
        // SPEC 9a.3: the landing byte is always loaded into D, even when RDY stays 0.
        always @(posedge clk) if (ok2 && p2_fetch_served[k]) assert (pd[8*k +: 8] == p_m_rd);
        // RDY is sticky until a request-setting op (it cannot fall on its own).
        always @(posedge clk) if (ok1 && p_rdy[k] && !p_setrq[k]) assert (rdy[k]);
    end endgenerate

    // ---- host request slot (SPEC 9a.4): a new request overwrites an unserved one, no flag
    always @(posedge clk) if (ok1) begin
        if (p_hreq_set) begin
            assert (hq && hqw == p_hreq_wr && hqa == p_hreq_addr && hqd == p_hreq_d);
        end else if (p_gh) begin
            assert (!hq);
        end else begin
            assert (hq == p_hq && hqw == p_hqw);
        end
        // host read lands one cycle after it is served; writes produce no landing; byte = m_rd of that cycle
        assert (hland == (p_gh && !p_hqw));
        if (hland) assert (hland_d == m_rd);
    end

    // ---- non-vacuity
    always @(posedge clk) begin
        cover (ok2 && rdy[0] && !p_rdy[0]);
        cover (ok2 && rdy[1] && !p_rdy[1]);
        cover (memhaz);
        cover (ok1 && p_setrq[0] && p2_fetch_served[0] && !rdy[0]);   // stale landing suppressed
        cover (g1);
        cover (gh && !hqw);
        cover (ok1 && p_op_w[0] && g0 && rq_w0 == WRITE);
    end
endmodule

bind md_ptrs fv_ptrs_props fv_props (.*);
