// Formal wrapper for md_wgroup (SPEC 6 write groups). Purely combinational, so the proof is complete for
// every input. Checked for three parameterisations: the instantiated N=6 with (DW=8,SW=3), the narrow
// (DW=5,SW=1) form, and N=3. A generic checker module is instantiated for each.
module fv_wg_check #(parameter integer N = 6, parameter integer DW = 8, parameter integer SW = 1) ();
    (* anyseq *) wire [N-1:0]    hit;
    (* anyseq *) wire [SW*N-1:0] sel;
    (* anyseq *) wire [DW*N-1:0] data;
    wire we, multi; wire [SW-1:0] wsel; wire [DW-1:0] wdata;
    md_wgroup #(.N(N), .DW(DW), .SW(SW)) dut (.hit(hit), .sel(sel), .data(data), .we(we), .wsel(wsel),
                                              .wdata(wdata), .multi(multi));
    // independent reference: lowest set index and population count
    integer i;
    reg [4:0] low; reg [4:0] cnt;
    always @(*) begin
        low = 5'd31; cnt = 5'd0;
        for (i = 0; i < N; i = i + 1) begin
            if (hit[i]) begin
                cnt = cnt + 5'd1;
                if (low == 5'd31) low = i[4:0];
            end
        end
    end
    // SPEC 6: a write reaches the unit iff at least one enabled writer targets the group.
    always @(*) assert (we == (cnt != 0));
    // SPEC 6: only the lowest (core, move) slot takes effect (slot order = index order).
    always @(*) if (cnt != 0) assert (wsel == sel[SW*low +: SW] && wdata == data[DW*low +: DW]);
    // Idle outputs are zero (no stray write data).
    always @(*) if (cnt == 0) assert (wsel == 0 && wdata == 0);
    // SPEC 6: CONFLICT is raised iff two or more enabled writers target the group.
    always @(*) assert (multi == (cnt >= 2));
    always @(*) if (cnt == 1) assert (!multi && hit[low]);
    always @(*) begin cover (cnt == 1); cover (cnt == 2); cover (cnt == N); end
endmodule

module fv_wgroup;
    fv_wg_check #(.N(6), .DW(8), .SW(3)) c0 ();
    fv_wg_check #(.N(6), .DW(5), .SW(1)) c1 ();
    fv_wg_check #(.N(3), .DW(8), .SW(2)) c2 ();
endmodule
