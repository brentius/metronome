// Metronome v2 place-and-route sizing: stand-in for the commons (move bus targets, sources and guards).
// Not the v2 commons. Its purpose is realistic timing and wiring around the two cores: every one of the 58
// destinations of code/md2/machine.py writes a register or a cheap functional stand-in, every source reads a
// register, and the guards come from registers, synchronised pins and the real stream's status.
//
// Move bus: the six move slots (core 0 m0..m2, core 1 m0..m2) are merged per write group by OR (a conflict, which
// v2 flags as CONFLICT, gives the OR of the data here). L.SYM/L.DBIT/L.XOR use the executing core's line.
// Stand-ins (all registers reset to 0):
//   L<k> symbol: 4 bits per line, written directly (no beat commit). L<k>.CTL: 3 bits; bit 0 is the L<k>.RUN guard.
//   ACC: LD/ADD/SUB/AND/OR/XOR/CMP with Z, C, N. R0..R3: 8-bit registers. FLAGS: 16 bits, SET/CLR by bus[3:0].
//   SH<k>: 8-bit data, 4-bit count, CFG {msb, len[3:0]}. CNT<k>: 16 bits, LO/HI loads, DEC saturating.
//   LF<k>: 32-bit Galois LFSR, fixed polynomial 0xEDB88320 (v2 keeps POLY in latches). P0: 11-bit pointer and a data
//   byte register (no RAM access; RDY = pointer nonzero). S1: an 8-bit rotator with a 3-bit position (one real
//   stream, S0, is outside this module). HOST.OUT: mailbox byte, sets OUTV; it also clears INV (stand-in for the
//   read-clears-INV rule, which needs the source codes the core does not export).
`timescale 1ns/1ps
`default_nettype none
module md2_commons_stub (
    input  wire         clk,
    input  wire         rst_n,
    input  wire [5:0]   mv_en,       // {core1 m2..m0, core0 m2..m0}
    input  wire [35:0]  mv_dst,
    input  wire [47:0]  mv_data,
    input  wire [3:0]   x_line,      // {core1 line, core0 line}
    input  wire [12:0]  pins,        // synchronised input pins P12..P0
    // stream S0 (md2_stream)
    output wire         s0_adv,
    output wire         s0_rx_we,
    output wire         s0_rx_bit,
    output wire         s0_ctl_we,
    output wire [1:0]   s0_ctl,
    input  wire         s0_bit,
    input  wire [7:0]   s0_byte,
    input  wire         s0_end,
    input  wire         s0_mark,
    input  wire         s0_bbound,
    // host mailbox
    input  wire         h_in_we,
    input  wire [7:0]   h_in_d,
    input  wire         h_out_rd,    // host read of HOST.OUT clears OUTV
    output reg  [7:0]   host_out,
    output reg          outv,
    output reg          inv,
    // to the cores
    output reg  [63:0]  guards,
    output wire [19:0]  g_line,
    output reg  [511:0] srcs,
    output wire [7:0]   l_in,
    output wire [19:0]  l_cap,
    output wire [7:0]   flags_lo,
    // observation
    output reg  [7:0]   r0,
    output reg  [7:0]   r1,
    output wire [15:0]  sym          // {L3, L2, L1, L0} symbols
);
/* verilator lint_off UNUSEDPARAM */
`undef MD2_DEFS_VH
`include "md2_defs.vh"
/* verilator lint_on UNUSEDPARAM */

    localparam [63:0] ONE = 64'd1;
    localparam [63:0] M_SYM   = (ONE << D_L_SYM) | (ONE << D_L_DBIT) | (ONE << D_L_XOR);
    localparam [63:0] M_FLAGS = (ONE << D_FLAGS_SET) | (ONE << D_FLAGS_CLR);
    localparam [63:0] M_ACC   = (ONE << D_ACC_LD) | (ONE << D_ACC_ADD) | (ONE << D_ACC_SUB) | (ONE << D_ACC_AND) |
                                (ONE << D_ACC_OR) | (ONE << D_ACC_XOR) | (ONE << D_ACC_CMP);
    localparam [63:0] M_SH0   = (ONE << D_SH0_LD) | (ONE << D_SH0_SH) | (ONE << D_SH0_CFG);
    localparam [63:0] M_SH1   = (ONE << D_SH1_LD) | (ONE << D_SH1_SH) | (ONE << D_SH1_CFG);
    localparam [63:0] M_CNT0  = (ONE << D_CNT0_LO) | (ONE << D_CNT0_HI);
    localparam [63:0] M_CNT1  = (ONE << D_CNT1_LO) | (ONE << D_CNT1_HI);
    localparam [63:0] M_CNT2  = (ONE << D_CNT2_LO) | (ONE << D_CNT2_HI);
    localparam [63:0] M_LF0   = (ONE << D_LF0_ST) | (ONE << D_LF0_B0) | (ONE << D_LF0_B1) | (ONE << D_LF0_B2) |
                                (ONE << D_LF0_B3);
    localparam [63:0] M_LF1   = (ONE << D_LF1_ST) | (ONE << D_LF1_B0) | (ONE << D_LF1_B1) | (ONE << D_LF1_B2) |
                                (ONE << D_LF1_B3);
    localparam [63:0] M_P0    = (ONE << D_P0_AL) | (ONE << D_P0_AH) | (ONE << D_P0_W);
    localparam [63:0] M_S0    = (ONE << D_S0_RX) | (ONE << D_S0_CTL);
    localparam [63:0] M_S1    = (ONE << D_S1_RX) | (ONE << D_S1_CTL);
    localparam [63:0] M_LCTL  = (ONE << D_L0_CTL) | (ONE << D_L1_CTL) | (ONE << D_L2_CTL) | (ONE << D_L3_CTL);
    localparam [31:0] POLY    = 32'hEDB88320;

    // ---------------------------------------------------------------- move bus
    // OR of the data of the enabled slots whose destination is in `mask`
    function [7:0] gbus;
        input [5:0]  en;
        input [35:0] dst;
        input [47:0] dat;
        input [63:0] mask;
        integer s;
        begin
            gbus = 8'd0;
            for (s = 0; s < 6; s = s + 1)
                if (en[s] && mask[dst[6*s +: 6]]) gbus = gbus | dat[8*s +: 8];
        end
    endfunction

    reg [63:0] hit;                   // destination d is written by an enabled slot
    integer s;
    always @* begin
        hit = 64'd0;
        for (s = 0; s < 6; s = s + 1)
            if (mv_en[s]) hit[mv_dst[6*s +: 6]] = 1'b1;
    end
    wire _unused_hit = &{1'b0, hit[D_NULL], hit[D_T_STOP], hit[63:58]};


    // per-line slot enables (slots 0..2 run on core 0's line, 3..5 on core 1's)
    wire [5:0] en_l [0:3];
    genvar k;
    generate
        for (k = 0; k < 4; k = k + 1) begin : g_len
            assign en_l[k] = mv_en & {{3{x_line[3:2] == k[1:0]}}, {3{x_line[1:0] == k[1:0]}}};
        end
    endgenerate

    wire [7:0] b_flags = gbus(mv_en, mv_dst, mv_data, M_FLAGS);
    wire [7:0] b_acc   = gbus(mv_en, mv_dst, mv_data, M_ACC);
    wire [7:0] b_sh0   = gbus(mv_en, mv_dst, mv_data, M_SH0);
    wire [7:0] b_sh1   = gbus(mv_en, mv_dst, mv_data, M_SH1);
    wire [7:0] b_cnt0  = gbus(mv_en, mv_dst, mv_data, M_CNT0);
    wire [7:0] b_cnt1  = gbus(mv_en, mv_dst, mv_data, M_CNT1);
    wire [7:0] b_cnt2  = gbus(mv_en, mv_dst, mv_data, M_CNT2);
    wire [7:0] b_lf0   = gbus(mv_en, mv_dst, mv_data, M_LF0);
    wire [7:0] b_lf1   = gbus(mv_en, mv_dst, mv_data, M_LF1);
    wire [7:0] b_p0    = gbus(mv_en, mv_dst, mv_data, M_P0);
    wire [7:0] b_s0    = gbus(mv_en, mv_dst, mv_data, M_S0);
    wire [7:0] b_s1    = gbus(mv_en, mv_dst, mv_data, M_S1);
    wire [7:0] b_lctl  = gbus(mv_en, mv_dst, mv_data, M_LCTL);
    wire [7:0] b_r0    = gbus(mv_en, mv_dst, mv_data, ONE << D_R0);
    wire [7:0] b_r1    = gbus(mv_en, mv_dst, mv_data, ONE << D_R1);
    wire [7:0] b_r2    = gbus(mv_en, mv_dst, mv_data, ONE << D_R2);
    wire [7:0] b_r3    = gbus(mv_en, mv_dst, mv_data, ONE << D_R3);
    wire [7:0] b_hout  = gbus(mv_en, mv_dst, mv_data, ONE << D_HOST_OUT);

    wire _unused_bus = &{1'b0, b_flags[7:4], b_s0[7:2], b_s1[7:1], b_lctl[7:3]};

    // ---------------------------------------------------------------- line symbols and line control
    reg [3:0] sym_r [0:3];
    reg [2:0] lctl  [0:3];
    generate
        for (k = 0; k < 4; k = k + 1) begin : g_ln
            wire [7:0] b = gbus(en_l[k], mv_dst, mv_data, M_SYM);
            wire _unused_b = &{1'b0, b[7:4]};
            reg  h_sym, h_dbit, h_xor;
            integer q;
            always @* begin
                h_sym = 1'b0; h_dbit = 1'b0; h_xor = 1'b0;
                for (q = 0; q < 6; q = q + 1) begin
                    h_sym  = h_sym  | (en_l[k][q] & (mv_dst[6*q +: 6] == D_L_SYM));
                    h_dbit = h_dbit | (en_l[k][q] & (mv_dst[6*q +: 6] == D_L_DBIT));
                    h_xor  = h_xor  | (en_l[k][q] & (mv_dst[6*q +: 6] == D_L_XOR));
                end
            end
            always @(posedge clk) begin
                if (!rst_n) begin
                    sym_r[k] <= 4'd0;
                    lctl[k]  <= 3'd0;
                end else begin
                    if (h_sym)       sym_r[k]    <= b[3:0];
                    else if (h_dbit) sym_r[k][0] <= b[0];
                    else if (h_xor)  sym_r[k]    <= sym_r[k] ^ b[3:0];
                    if (hit[D_L0_CTL + k]) lctl[k] <= b_lctl[2:0];
                end
            end
            assign sym[4*k +: 4] = sym_r[k];
            // line guards {PINB, PINA, SYNC, IN1, IN0}: pins of the line, SYNC stand-in = ARM bit
            assign l_in[2*k +: 2]  = pins[2*k +: 2];
            assign g_line[5*k +: 5] = {pins[2*k + 1], pins[2*k], lctl[k][1] ^ lctl[k][2], pins[2*k + 1], pins[2*k]};
            assign l_cap[5*k +: 5] = {sym_r[k][0], pins[8 + k], pins[2*k + 1], pins[2*k], pins[(2*k + 2) % 8]};
        end
    endgenerate

    // ---------------------------------------------------------------- flags and accumulator
    reg [15:0] flags;
    reg [7:0]  acc, r2, r3;
    reg        acc_z, acc_c, acc_n;
    reg [8:0]  ar;
    always @* begin
        ar = {1'b0, acc};
        if      (hit[D_ACC_LD])  ar = {1'b0, b_acc};
        else if (hit[D_ACC_ADD]) ar = {1'b0, acc} + {1'b0, b_acc};
        else if (hit[D_ACC_SUB] | hit[D_ACC_CMP]) ar = {1'b0, acc} + {1'b0, ~b_acc} + 9'd1;
        else if (hit[D_ACC_AND]) ar = {1'b0, acc & b_acc};
        else if (hit[D_ACC_OR])  ar = {1'b0, acc | b_acc};
        else if (hit[D_ACC_XOR]) ar = {1'b0, acc ^ b_acc};
    end
    wire acc_wr = |(hit & M_ACC);
    always @(posedge clk) begin
        if (!rst_n) begin
            flags <= 16'd0; acc <= 8'd0; acc_z <= 1'b0; acc_c <= 1'b0; acc_n <= 1'b0;
            r0 <= 8'd0; r1 <= 8'd0; r2 <= 8'd0; r3 <= 8'd0;
        end else begin
            if (hit[D_FLAGS_SET]) flags[b_flags[3:0]] <= 1'b1;
            if (hit[D_FLAGS_CLR]) flags[b_flags[3:0]] <= 1'b0;
            if (acc_wr) begin
                if (!hit[D_ACC_CMP]) acc <= ar[7:0];
                acc_z <= (ar[7:0] == 8'd0);
                acc_c <= ar[8];
                acc_n <= ar[7];
            end
            if (hit[D_R0]) r0 <= b_r0;
            if (hit[D_R1]) r1 <= b_r1;
            if (hit[D_R2]) r2 <= b_r2;
            if (hit[D_R3]) r3 <= b_r3;
        end
    end
    assign flags_lo = flags[7:0];

    // ---------------------------------------------------------------- shifters
    reg [7:0] sh_d   [0:1];
    reg [3:0] sh_cnt [0:1];
    reg [4:0] sh_cfg [0:1];
    wire [7:0] b_sh [0:1];
    assign b_sh[0] = b_sh0;
    assign b_sh[1] = b_sh1;
    wire [1:0] sh_out;
    generate
        for (k = 0; k < 2; k = k + 1) begin : g_sh
            wire ld = hit[D_SH0_LD + k];
            wire sf = hit[D_SH0_SH + k];
            wire cf = hit[D_SH0_CFG + k];
            assign sh_out[k] = sh_cfg[k][4] ? sh_d[k][7] : sh_d[k][0];
            always @(posedge clk) begin
                if (!rst_n) begin
                    sh_d[k] <= 8'd0; sh_cnt[k] <= 4'd0; sh_cfg[k] <= 5'd0;
                end else begin
                    if (cf) sh_cfg[k] <= b_sh[k][4:0];
                    if (ld) begin
                        sh_d[k]   <= b_sh[k];
                        sh_cnt[k] <= (sh_cfg[k][3:0] == 4'd0) ? 4'd8 : sh_cfg[k][3:0];
                    end else if (sf) begin
                        sh_d[k] <= sh_cfg[k][4] ? {sh_d[k][6:0], b_sh[k][0]} : {b_sh[k][0], sh_d[k][7:1]};
                        if (sh_cnt[k] != 4'd0) sh_cnt[k] <= sh_cnt[k] - 4'd1;
                    end
                end
            end
        end
    endgenerate

    // ---------------------------------------------------------------- counters
    reg [15:0] cnt [0:2];
    wire [7:0] b_cnt [0:2];
    assign b_cnt[0] = b_cnt0;
    assign b_cnt[1] = b_cnt1;
    assign b_cnt[2] = b_cnt2;
    generate
        for (k = 0; k < 3; k = k + 1) begin : g_cnt
            always @(posedge clk) begin
                if (!rst_n) cnt[k] <= 16'd0;
                else begin
                    if (hit[D_CNT0_LO + k]) cnt[k][7:0]  <= b_cnt[k];
                    if (hit[D_CNT0_HI + k]) cnt[k][15:8] <= b_cnt[k];
                    if (hit[D_CNT0_DEC + k] && (cnt[k] != 16'd0)) cnt[k] <= cnt[k] - 16'd1;
                end
            end
        end
    endgenerate

    // ---------------------------------------------------------------- LFSRs
    reg [31:0] lf [0:1];
    wire [7:0] b_lf [0:1];
    assign b_lf[0] = b_lf0;
    assign b_lf[1] = b_lf1;
    generate
        for (k = 0; k < 2; k = k + 1) begin : g_lf
            wire fb = lf[k][0] ^ b_lf[k][0];
            always @(posedge clk) begin
                if (!rst_n) lf[k] <= 32'd0;
                else if (hit[D_LF0_ST + k]) lf[k] <= {1'b0, lf[k][31:1]} ^ (fb ? POLY : 32'd0);
                else begin
                    if (hit[D_LF0_B0 + 4*k]) lf[k][7:0]   <= b_lf[k];
                    if (hit[D_LF0_B1 + 4*k]) lf[k][15:8]  <= b_lf[k];
                    if (hit[D_LF0_B2 + 4*k]) lf[k][23:16] <= b_lf[k];
                    if (hit[D_LF0_B3 + 4*k]) lf[k][31:24] <= b_lf[k];
                end
            end
        end
    endgenerate

    // ---------------------------------------------------------------- pointer, S1 stand-in, host mailbox
    reg [10:0] ptr;
    reg [7:0]  pdat, s1;
    reg [2:0]  s1pos;
    always @(posedge clk) begin
        if (!rst_n) begin
            ptr <= 11'd0; pdat <= 8'd0; s1 <= 8'd0; s1pos <= 3'd0;
            host_out <= 8'd0; outv <= 1'b0; inv <= 1'b0;
        end else begin
            if (hit[D_P0_AL]) ptr[7:0]  <= b_p0;
            if (hit[D_P0_AH]) ptr[10:8] <= b_p0[2:0];
            if (hit[D_P0_W]) pdat <= b_p0;
            if (hit[D_P0_W] | hit[D_P0_R]) ptr <= ptr + 11'd1;
            if (hit[D_S1_CTL] & b_s1[0]) begin s1 <= 8'd0; s1pos <= 3'd0; end
            else if (hit[D_S1_RX])  begin s1 <= {b_s1[0], s1[7:1]}; s1pos <= s1pos + 3'd1; end
            else if (hit[D_S1_ADV]) begin s1 <= {s1[0], s1[7:1]};   s1pos <= s1pos + 3'd1; end
            if (h_in_we) inv <= 1'b1;
            if (h_out_rd) outv <= 1'b0;
            if (hit[D_HOST_OUT]) begin host_out <= b_hout; outv <= 1'b1; inv <= 1'b0; end
        end
    end
    reg [7:0] host_in;
    always @(posedge clk) begin
        if (!rst_n)       host_in <= 8'd0;
        else if (h_in_we) host_in <= h_in_d;
    end

    // ---------------------------------------------------------------- stream S0 ports
    assign s0_adv    = hit[D_S0_ADV];
    assign s0_rx_we  = hit[D_S0_RX];
    assign s0_rx_bit = b_s0[0];
    assign s0_ctl_we = hit[D_S0_CTL];
    assign s0_ctl    = b_s0[1:0];

    // ---------------------------------------------------------------- sources (IMM, L.IN, L.CAP filled by the core)
    always @* begin
        srcs = 512'd0;
        srcs[8*S_FLAGS_LO +: 8] = flags[7:0];
        srcs[8*S_FLAGS_HI +: 8] = flags[15:8];
        srcs[8*S_PINS_LO  +: 8] = pins[7:0];
        srcs[8*S_PINS_HI  +: 8] = {3'd0, pins[12:8]};
        srcs[8*S_ACC      +: 8] = acc;
        srcs[8*S_R0       +: 8] = r0;
        srcs[8*S_R1       +: 8] = r1;
        srcs[8*S_R2       +: 8] = r2;
        srcs[8*S_R3       +: 8] = r3;
        srcs[8*S_SH0_D    +: 8] = sh_d[0];
        srcs[8*S_SH1_D    +: 8] = sh_d[1];
        srcs[8*S_SH0_O    +: 8] = {7'd0, sh_out[0]};
        srcs[8*S_SH1_O    +: 8] = {7'd0, sh_out[1]};
        srcs[8*S_CNT0_LO  +: 8] = cnt[0][7:0];
        srcs[8*S_CNT1_LO  +: 8] = cnt[1][7:0];
        srcs[8*S_CNT2_LO  +: 8] = cnt[2][7:0];
        srcs[8*S_CNT0_HI  +: 8] = cnt[0][15:8];
        srcs[8*S_CNT1_HI  +: 8] = cnt[1][15:8];
        srcs[8*S_CNT2_HI  +: 8] = cnt[2][15:8];
        srcs[8*S_LF0_B0   +: 32] = lf[0];
        srcs[8*S_LF1_B0   +: 32] = lf[1];
        srcs[8*S_LF0_O    +: 8] = {7'd0, lf[0][0]};
        srcs[8*S_LF1_O    +: 8] = {7'd0, lf[1][0]};
        srcs[8*S_P0_D     +: 8] = pdat;
        srcs[8*S_S0_BIT   +: 8] = {7'd0, s0_bit};
        srcs[8*S_S1_BIT   +: 8] = {7'd0, s1[0]};
        srcs[8*S_S0_BYTE  +: 8] = s0_byte;
        srcs[8*S_S1_BYTE  +: 8] = s1;
        srcs[8*S_HOST_IN  +: 8] = host_in;
    end

    // ---------------------------------------------------------------- guards (TRUE and L.* filled by the core)
    always @* begin
        guards = 64'd0;
        guards[G_F0 +: 16] = flags;
        guards[G_SH0_DONE] = (sh_cnt[0] == 4'd0);
        guards[G_SH1_DONE] = (sh_cnt[1] == 4'd0);
        guards[G_SH0_OUT]  = sh_out[0];
        guards[G_SH1_OUT]  = sh_out[1];
        guards[G_CNT0_Z]   = (cnt[0] == 16'd0);
        guards[G_CNT1_Z]   = (cnt[1] == 16'd0);
        guards[G_CNT2_Z]   = (cnt[2] == 16'd0);
        guards[G_ACC_Z]    = acc_z;
        guards[G_ACC_C]    = acc_c;
        guards[G_ACC_N]    = acc_n;
        guards[G_LF0_OUT]  = lf[0][0];
        guards[G_LF1_OUT]  = lf[1][0];
        guards[G_HOST_INV] = inv;
        guards[G_HOST_OUTE] = ~outv;
        guards[G_P0_RDY]   = |ptr;
        guards[G_S0_END]   = s0_end;
        guards[G_S1_END]   = (s1pos == 3'd7);
        guards[G_S0_MARK]  = s0_mark;
        guards[G_S1_MARK]  = s1[7];
        guards[G_S0_BYTE]  = s0_bbound;
        guards[G_S1_BYTE]  = (s1pos == 3'd0);
        guards[G_S0_BIT]   = s0_bit;
        guards[G_S1_BIT]   = s1[0];
        guards[G_PIN0 +: 13] = pins;
        guards[G_L0_RUN +: 4] = {lctl[3][0], lctl[2][0], lctl[1][0], lctl[0][0]};
    end
endmodule
`default_nettype wire
