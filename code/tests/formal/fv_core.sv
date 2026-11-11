// D17 / SPEC 5: round-robin selection, cursor state, and bounded overtaking in dispatches.
// Free requests, instruction streams and RUN: liveness is measured in actual dispatches, not clocks.
// A clock bound additionally requires the checker's finite-burst and fixed-configuration obligations.
module fv_core_props #(parameter integer NE = 6) (
    input wire clk, rst_n,
    input wire [2:0] rr, disp_e,
    input wire [NE-1:0] cand, win,
    input wire disp_o, cont
);
    reg past_valid = 1'b0;
    reg p_rstn, p_disp;
    reg [2:0] p_rr, p_engine;
    always @(posedge clk) begin
        past_valid <= 1'b1;
        if (!past_valid) assume (!rst_n);
        p_rstn <= rst_n; p_disp <= disp_o; p_rr <= rr; p_engine <= disp_e;
    end

    // Independent circular scan; the implementation uses a masked priority network.
    reg [NE-1:0] expected;
    reg [2:0] expected_engine;
    reg found;
    integer offset, index;
    always @* begin
        expected = 0; expected_engine = 0; found = 0;
        for (offset = 0; offset < NE; offset = offset + 1) begin
            index = ({29'd0, rr} + offset) % NE;
            if (!found && cand[index]) begin
                expected[index] = 1;
                expected_engine = index[2:0];
                found = 1;
            end
        end
        if (past_valid) begin
            assert (rr < NE);
            assert (win == expected);
            assert (disp_e == expected_engine);
            assert (disp_o == (!cont && (|cand)));
        end
    end

    always @(posedge clk) if (past_valid) begin
        if (!p_rstn) assert (rr == 0);
        else if (p_disp) assert (rr == ((p_engine == NE-1) ? 0 : p_engine + 1));
        else assert (rr == p_rr);
    end

    // Each continuously eligible engine is overtaken by at most NE-1 other dispatches.
    genvar k;
    generate for (k = 0; k < NE; k = k + 1) begin : g_wait
        reg [3:0] waiting_grants;
        always @(posedge clk) begin
            if (!rst_n || !cand[k] || (disp_o && win[k])) waiting_grants <= 0;
            else if (disp_o) waiting_grants <= waiting_grants + 1;
            if (past_valid) assert (waiting_grants < NE);
            // Relate the monitor to the circular cursor for induction through arbitrarily long stalls.
            // Every other dispatch before k reduces its remaining circular distance by at least one.
            if (past_valid && cand[k])
                assert (waiting_grants + ((k + NE - {29'd0, rr}) % NE) < NE);
            cover (past_valid && waiting_grants == NE-1 && disp_o && win[k]);
        end
    end endgenerate

    always @(posedge clk) begin
        cover (past_valid && p_rstn && p_disp && p_engine == NE-1 && rr == 0);
        cover (past_valid && disp_o && disp_e != 0 && cand[0]);
        cover (past_valid && cont && (|cand));
    end
endmodule

bind md_core fv_core_props #(.NE(NE)) fv_props (.*);
