// Formal properties for md_movebus (SPEC 6 write groups), default parameters (NE=6 NB=4 NSH=4 NCN=4 NLF=2
// NR=4 NP=2). Combinational, so the proof is complete over all inputs. The reference model is an independent
// group-id function written directly from the SPEC 6 group list over the numeric destination codes
// (md_defs.vh): it maps (destination, executing engine) to a group number, and the bus is then checked
// against "lowest enabled slot of the same group wins; CONFLICT iff any group has >= 2 enabled writers".
module fv_movebus_props (
    input wire [5:0] en, input wire [35:0] dst, input wire [47:0] data, input wire [2:0] xe0, input wire [2:0] xe1,
    input wire acc_we, input wire [2:0] acc_sel, input wire [7:0] acc_d,
    input wire [3:0] r_we, input wire [31:0] r_d,
    input wire [3:0] sh_we, input wire [3:0] sh_sel, input wire [31:0] sh_d,
    input wire [3:0] shc_we, input wire [19:0] shc_d,
    input wire [3:0] cn_we, input wire [7:0] cn_sel, input wire [31:0] cn_d,
    input wire [1:0] lf_we, input wire [5:0] lf_sel, input wire [15:0] lf_d,
    input wire [1:0] p_we, input wire [3:0] p_sel, input wire [15:0] p_d,
    input wire fl_we, input wire fl_sel, input wire [3:0] fl_d,
    input wire [3:0] bg_we, input wire [11:0] bg_d,
    input wire ho_we, input wire [7:0] ho_d,
    input wire [5:0] sym_we, input wire [11:0] sym_d, input wire [5:0] stop_we,
    input wire conflict
);
    localparam [6:0] NONE = 7'd127;
    // group numbering: 0 ACC | 1-4 Rk | 5-8 SHk.{LD,SH} | 9-12 SHk.CFG | 13-16 CNTk | 17-18 LFk | 19-20 Pk
    //                  21 FLAGS | 22-25 BGk.CTL | 26 HOST.OUT | 27-32 E.SYM e | 33-38 E.STOP e
    function [6:0] gid;
        input [5:0] d; input [2:0] x;
        begin
            gid = NONE;
            if (d >= 6'd5  && d <= 6'd11) gid = 7'd0;                       // ACC.{LD,ADD,SUB,AND,OR,XOR,CMP}
            else if (d >= 6'd12 && d <= 6'd15) gid = 7'd1 + (d - 6'd12);    // R0..R3
            else if (d >= 6'd16 && d <= 6'd19) gid = 7'd5 + (d - 6'd16);    // SHk.LD
            else if (d >= 6'd20 && d <= 6'd23) gid = 7'd5 + (d - 6'd20);    // SHk.SH (same group as LD)
            else if (d >= 6'd24 && d <= 6'd27) gid = 7'd9 + (d - 6'd24);    // SHk.CFG
            else if (d >= 6'd28 && d <= 6'd39) gid = 7'd13 + ((d - 6'd28) & 6'd3); // CNTk.{LO,HI,DEC}
            else if (d == 6'd40 || d == 6'd41) gid = 7'd17 + (d - 6'd40);   // LFk.ST
            else if (d >= 6'd42 && d <= 6'd49) gid = 7'd17 + ((d - 6'd42) >> 2); // LFk.B0..B3
            else if (d >= 6'd50 && d <= 6'd57) gid = 7'd19 + ((d - 6'd50) & 6'd1); // Pk.{AL,AH,W,R}
            else if (d == 6'd3 || d == 6'd4) gid = 7'd21;                   // FLAGS.{SET,CLR}
            else if (d >= 6'd58 && d <= 6'd61) gid = 7'd22 + (d - 6'd58);   // BGk.CTL
            else if (d == 6'd62) gid = 7'd26;                               // HOST.OUT
            else if (d == 6'd1 && x < 3'd6) gid = 7'd27 + x;                // E.SYM of the executing engine
            else if (d == 6'd2 && x < 3'd6) gid = 7'd33 + x;                // E.STOP of the executing engine
        end
    endfunction

    // port index within the group (the `sel` the unit sees; SPEC 6 port order / md_movebus header)
    function [2:0] pidx;
        input [5:0] d;
        begin
            pidx = 3'd0;
            if (d >= 6'd5 && d <= 6'd11) pidx = d - 6'd5;                 // ACC: LD ADD SUB AND OR XOR CMP
            else if (d >= 6'd20 && d <= 6'd23) pidx = 3'd1;               // SHk.SH (LD = 0)
            else if (d >= 6'd28 && d <= 6'd39) pidx = (d - 6'd28) >> 2;   // CNT: LO HI DEC
            else if (d >= 6'd42 && d <= 6'd49) pidx = 3'd1 + ((d - 6'd42) & 6'd3);  // LF: B0..B3 (ST = 0)
            else if (d >= 6'd50 && d <= 6'd57) pidx = (d - 6'd50) >> 1;   // P: AL AH W R
            else if (d == 6'd4) pidx = 3'd1;                              // FLAGS: SET=0 CLR=1
        end
    endfunction
    reg [6:0] g [0:5];
    integer i, j, q;
    reg anyconf;
    reg [3:0] lo [0:38];       // lowest enabled slot per group (15 = none)
    reg [3:0] cn [0:38];
    reg [2:0] pi [0:38];       // port index of the winning slot       // number of enabled writers per group
    always @(*) begin
        for (i = 0; i < 6; i = i + 1)
            g[i] = en[i] ? gid(dst[6*i +: 6], (i < 3) ? xe0 : xe1) : NONE;
        for (q = 0; q < 39; q = q + 1) begin
            lo[q] = 4'd15; cn[q] = 4'd0; pi[q] = 3'd0;
            for (i = 0; i < 6; i = i + 1)
                if (g[i] == q) begin
                    cn[q] = cn[q] + 4'd1;
                    if (lo[q] == 4'd15) begin lo[q] = i[3:0]; pi[q] = pidx(dst[6*i +: 6]); end
                end
        end
        anyconf = 1'b0;
        for (q = 0; q < 39; q = q + 1) if (cn[q] >= 2) anyconf = 1'b1;
    end

    // SPEC 6: CONFLICT iff some group has two or more enabled writers.
    always @(*) assert (conflict == anyconf);
    // SPEC 6: the group receives a write iff >= 1 enabled writer; the lowest (core, move) slot wins.
    always @(*) begin
        assert (acc_we == (cn[0] != 0));
        if (cn[0] != 0) assert (acc_d == data[8*lo[0] +: 8] && acc_sel == pi[0]);
        for (j = 0; j < 4; j = j + 1) begin
            assert (r_we[j] == (cn[1+j] != 0));
            if (cn[1+j] != 0) assert (r_d[8*j +: 8] == data[8*lo[1+j] +: 8]);
            assert (sh_we[j] == (cn[5+j] != 0));
            if (cn[5+j] != 0) assert (sh_d[8*j +: 8] == data[8*lo[5+j] +: 8] && sh_sel[j] == pi[5+j][0]);
            assert (shc_we[j] == (cn[9+j] != 0));
            if (cn[9+j] != 0) assert (shc_d[5*j +: 5] == data[8*lo[9+j] +: 5]);
            assert (cn_we[j] == (cn[13+j] != 0));
            if (cn[13+j] != 0) assert (cn_d[8*j +: 8] == data[8*lo[13+j] +: 8] && cn_sel[2*j +: 2] == pi[13+j][1:0]);
            assert (bg_we[j] == (cn[22+j] != 0));
            if (cn[22+j] != 0) assert (bg_d[3*j +: 3] == data[8*lo[22+j] +: 3]);
        end
        for (j = 0; j < 2; j = j + 1) begin
            assert (lf_we[j] == (cn[17+j] != 0));
            if (cn[17+j] != 0) assert (lf_d[8*j +: 8] == data[8*lo[17+j] +: 8] && lf_sel[3*j +: 3] == pi[17+j]);
            assert (p_we[j] == (cn[19+j] != 0));
            if (cn[19+j] != 0) assert (p_d[8*j +: 8] == data[8*lo[19+j] +: 8] && p_sel[2*j +: 2] == pi[19+j][1:0]);
        end
        assert (fl_we == (cn[21] != 0));
        if (cn[21] != 0) assert (fl_d == data[8*lo[21] +: 4] && fl_sel == pi[21][0]);
        assert (ho_we == (cn[26] != 0));
        if (cn[26] != 0) assert (ho_d == data[8*lo[26] +: 8]);
        for (j = 0; j < 6; j = j + 1) begin
            assert (sym_we[j] == (cn[27+j] != 0));
            if (cn[27+j] != 0) assert (sym_d[2*j +: 2] == data[8*lo[27+j] +: 2]);
            assert (stop_we[j] == (cn[33+j] != 0));
        end
    end
    // Distinct groups never conflict: two moves to different registers (R0 and R1) never raise CONFLICT.
    always @(*) if (en[0] && en[1] && dst[5:0] == 6'd12 && dst[11:6] == 6'd13 && !en[2] && !en[3] && !en[4] && !en[5])
        assert (!conflict);
    // SPEC 6: NULL has no group; a NULL move never raises a write or conflict by itself.
    always @(*) if (en == 6'b000001 && dst[5:0] == 6'd0) assert (!conflict && !acc_we && r_we == 0 && !ho_we);
    // non-vacuity
    always @(*) begin
        cover (conflict);
        cover (!conflict && acc_we);
        cover (sym_we[3] && conflict);
        cover (cn[17] == 2);   // LF ST + B group conflict reachable
    end
endmodule

bind md_movebus fv_movebus_props fv_props (.*);
