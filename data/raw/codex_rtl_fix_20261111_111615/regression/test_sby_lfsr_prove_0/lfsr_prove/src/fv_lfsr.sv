// Formal properties for md_lfsr (SPEC 6.1 LFSR/CRC), single instance. The reference is the reflected Galois
// step written out directly. Interface assumption: nothing beyond the unit's own ports (we/dst free; a
// destination that belongs to the other LFSR or to no LFSR must leave S unchanged, which is checked).
module fv_lfsr_props (
    input wire clk, input wire rst_n, input wire we, input wire [2:0] sel, input wire [7:0] d,
    input wire h_we, input wire [1:0] h_byte, input wire [7:0] h_wd,
    input wire [31:0] s, input wire [31:0] poly
);
    reg pv = 1'b0;
    always @(posedge clk) begin pv <= 1'b1; if (!pv) assume(!rst_n); end
    reg p_rstn, p_we, p_h_we; reg [2:0] p_sel; reg [7:0] p_d, p_h_wd; reg [1:0] p_hb; reg [31:0] p_s, p_poly;
    always @(posedge clk) begin
        p_rstn <= rst_n; p_we <= we; p_sel <= sel; p_d <= d; p_s <= s; p_poly <= poly;
        p_h_we <= h_we; p_hb <= h_byte; p_h_wd <= h_wd;
    end
    wire ok1 = pv && p_rstn;
    wire [31:0] shifted = {1'b0, p_s[31:1]};
    wire [31:0] st_next = ((p_s[0] ^ p_d[0]) ? (shifted ^ p_poly) : shifted);   // SPEC 6.1 ST (reflected Galois)

    always @(posedge clk) if (pv && !p_rstn) assert (s == 0 && poly == 0);
    // SPEC 6.1 ST (sel 0)
    always @(posedge clk) if (ok1 && p_we && p_sel == 3'd0) assert (s == st_next);
    // SPEC 6.1 Bb (sel 1..4): replaces byte b only
    always @(posedge clk) if (ok1 && p_we && p_sel == 3'd1) assert (s == {p_s[31:8],  p_d});
    always @(posedge clk) if (ok1 && p_we && p_sel == 3'd2) assert (s == {p_s[31:16], p_d, p_s[7:0]});
    always @(posedge clk) if (ok1 && p_we && p_sel == 3'd3) assert (s == {p_s[31:24], p_d, p_s[15:0]});
    always @(posedge clk) if (ok1 && p_we && p_sel == 3'd4) assert (s == {p_d, p_s[23:0]});
    // no write (or an unused select 5..7) leaves S alone
    always @(posedge clk) if (ok1 && (!p_we || p_sel > 3'd4)) assert (s == p_s);
    // host POLY byte write; S is never touched by the host (POLY is write-only, D14)
    always @(posedge clk) if (ok1) begin
        assert (poly == (p_h_we ? (p_poly & ~(32'hFF << (8 * p_hb))) | ({24'd0, p_h_wd} << (8 * p_hb)) : p_poly));
    end
    always @(posedge clk) begin
        cover (ok1 && p_we && p_sel == 3'd0 && s != p_s && p_s[0] != p_d[0]);
        cover (ok1 && p_we && p_sel == 3'd4);
        cover (ok1 && p_h_we);
    end
endmodule

module fv_lfsr_top (
    input wire clk, input wire rst_n, input wire we, input wire [2:0] sel, input wire [7:0] d,
    input wire h_we, input wire [1:0] h_byte, input wire [7:0] h_wd
);
    wire [31:0] s0;
    md_lfsr u0 (.clk(clk), .rst_n(rst_n), .we(we), .sel(sel), .d(d), .h_we(h_we), .h_byte(h_byte),
                .h_wd(h_wd), .s(s0));
endmodule

bind md_lfsr fv_lfsr_props fv_props (.*);
