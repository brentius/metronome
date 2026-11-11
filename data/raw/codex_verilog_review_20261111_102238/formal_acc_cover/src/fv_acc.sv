// Formal properties for md_acc (SPEC 6.1 accumulator, 9a.7). Reference arithmetic is done in 9 bits.
// Interface assumption (UNIT-LEVEL): `we` is only asserted with sel 0..6 (an ACC.* op). md_acc itself would
// update Z/N from the data for a stray destination; at integration this cannot happen because md_movebus
// raises acc_we only for ACC ops (proven in movebus.sby: acc_sel equals the port index 0..6 of the winning ACC.* destination).
module fv_acc_props (
    input wire clk, input wire rst_n, input wire we, input wire [2:0] sel, input wire [7:0] d,
    input wire [3:0] r_we, input wire [31:0] r_d,
    input wire [7:0] a, input wire z, input wire c, input wire n, input wire [31:0] r
);
    reg pv = 1'b0;
    always @(posedge clk) begin pv <= 1'b1; if (!pv) assume(!rst_n); end
    always @(*) if (we) assume (sel <= 3'd6);
    reg p_rstn, p_we; reg [2:0] p_dst; reg [7:0] p_d, p_a; reg p_z, p_c, p_n; reg [3:0] p_rwe; reg [31:0] p_rd, p_r;
    always @(posedge clk) begin
        p_rstn <= rst_n; p_we <= we; p_dst <= sel; p_d <= d; p_a <= a; p_z <= z; p_c <= c; p_n <= n;
        p_rwe <= r_we; p_rd <= r_d; p_r <= r;
    end
    wire ok1 = pv && p_rstn;
    wire [8:0] add9 = {1'b0, p_a} + {1'b0, p_d};
    wire [8:0] sub9 = {1'b0, p_a} - {1'b0, p_d};
    reg [7:0] res; reg exp_wa, exp_wc, exp_c;
    always @(*) begin
        res = p_d; exp_wa = 1; exp_wc = 0; exp_c = p_c;
        case (p_dst)
            3'd0:  res = p_d;                                            // LD
            3'd1:  begin res = add9[7:0]; exp_wc = 1; exp_c = add9[8]; end    // ADD, C = carry out
            3'd2:  begin res = sub9[7:0]; exp_wc = 1; exp_c = !sub9[8]; end   // SUB, C = !borrow = (A >= v)
            3'd3:  res = p_a & p_d;                                      // AND
            3'd4:  res = p_a | p_d;                                      // OR
            3'd5: res = p_a ^ p_d;                                      // XOR
            3'd6: begin res = sub9[7:0]; exp_wa = 0; exp_wc = 1; exp_c = !sub9[8]; end  // CMP: A unchanged
            default: ;
        endcase
    end
    always @(posedge clk) if (pv && !p_rstn) assert (a == 0 && z == 0 && c == 0 && n == 0 && r == 0);
    always @(posedge clk) if (ok1 && p_we) begin
        assert (a == (exp_wa ? res : p_a));
        assert (c == (exp_wc ? exp_c : p_c));
        assert (z == (res == 8'd0));        // SPEC 9a.7: Z is computed on the 8-bit result (also for ADD/SUB/CMP)
        assert (n == res[7]);
    end
    always @(posedge clk) if (ok1 && !p_we) assert (a == p_a && z == p_z && c == p_c && n == p_n);
    // scratch registers: Rk' = v when written, otherwise hold; independent of the ACC ops
    genvar k;
    generate for (k = 0; k < 4; k = k + 1) begin : g_r
        always @(posedge clk) if (ok1) assert (r[8*k +: 8] == (p_rwe[k] ? p_rd[8*k +: 8] : p_r[8*k +: 8]));
    end endgenerate
    always @(posedge clk) begin
        cover (ok1 && p_we && p_dst == 3'd2 && c && !p_c);
        cover (ok1 && p_we && p_dst == 3'd1 && c && z);
        cover (ok1 && p_we && p_dst == 3'd6 && z);
    end
endmodule

bind md_acc fv_acc_props fv_props (.*);
