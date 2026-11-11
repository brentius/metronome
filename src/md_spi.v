// Host link (SPEC 9): SPI target, mode 0, oversampled in the system clock through the input synchronisers.
// Command byte (0x02 write, 0x03 read), address high, address low, then data bytes with auto-increment.
// Produces a host write strobe and a host read strobe for the register file, queues data-RAM accesses to the
// arbiter, and writes each program-memory byte straight into its byte lane of the program SRAM (byte enable; no
// staging register, coordinator option 3 / D15).
`timescale 1ns/1ps
`default_nettype none
module md_spi (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        sck_r,       // synchronised SCK rise (SR)
    input  wire        sck_f,       // synchronised SCK fall (SF)
    input  wire        cs_n,        // synchronised CS_N level
    input  wire        mosi,        // synchronised MOSI level
    // register-file write (all address ranges; decoded by the top level)
    output wire        h_we,
    output wire [15:0] h_waddr,
    output wire [7:0]  h_wd,
    // register-file read issue (address is valid in the issuing cycle)
    output wire        h_re,
    output wire [15:0] h_raddr,
    input  wire [7:0]  reg_rd,      // register read data for h_raddr (0 for unmapped and program memory)
    // data-RAM host request
    output wire        hreq_set,
    output wire        hreq_wr,
    output wire [10:0] hreq_addr,
    output wire [7:0]  hreq_d,
    input  wire        hland,
    input  wire [7:0]  hland_d,
    // program-memory write
    output wire [1:0]  prog_we,
    output wire [7:0]  prog_waddr,
    output wire [7:0]  prog_be,     // byte lane of the word
    output wire [7:0]  prog_wd,     // the byte (the memory wrapper replicates it across lanes)
    output reg         miso
);
/* verilator lint_off UNUSEDPARAM */
`undef MD_DEFS_VH
`include "md_defs.vh"
/* verilator lint_on UNUSEDPARAM */
    localparam integer PROG_SPAN = MD_PROG_WORDS * 8;        // bytes per core

    reg [2:0]  bitcnt;
    reg [1:0]  bytecnt;         // 0, 1, 2, 3 = "byte 3 onward"
    reg        cmd_wr, cmd_rd;
    reg [6:0]  rx;
    reg [15:0] addr;
    reg [7:0]  tx, hrd;
    reg        ldpend;          // a completed read byte (>= byte 2) still has to load TX

    wire cs        = ~cs_n;
    wire byte_done = cs & sck_r & (bitcnt == 3'd7);
    wire [7:0] rbyte = {rx, mosi};

    // writes: byte 3 onward of a write command
    assign h_we    = byte_done & (bytecnt == 2'd3) & cmd_wr;
    assign h_waddr = addr;
    assign h_wd    = rbyte;

    // reads: completing byte 2 of a read command, or the first SF after a later completed read byte.
    // SPEC 9a.9: the byte-2 read uses ADDR = {byte 1, byte 2}.
    wire re_b2 = byte_done & (bytecnt == 2'd2) & cmd_rd;
    wire re_sf = cs & sck_f & ldpend;
    assign h_re    = re_b2 | re_sf;
    assign h_raddr = re_b2 ? {addr[15:8], rbyte} : addr;

    // range checks as one unsigned compare: (a - base) mod 2^32 < size
    localparam [31:0] DATA_SIZE = MD_DATA_BYTES;
    localparam [31:0] PROG_SIZE = MD_N_CORES * PROG_SPAN;
    function in_data;
        input [15:0] a;
        reg [31:0] o;
        begin
            o = {16'd0, a} - {16'd0, H_DATA_BASE};
            in_data = (o < DATA_SIZE);
        end
    endfunction
    function in_prog;
        input [15:0] a;
        reg [31:0] o;
        begin
            o = {16'd0, a} - {16'd0, H_PROG_BASE};
            in_prog = (o < PROG_SIZE);
        end
    endfunction

    wire [15:0] w_off = h_waddr - H_PROG_BASE;
    wire [15:0] w_doff = h_waddr - H_DATA_BASE;
    wire [15:0] r_doff = h_raddr - H_DATA_BASE;
    wire wr_data = h_we & in_data(h_waddr);
    wire wr_prog = h_we & in_prog(h_waddr);
    wire rd_data = h_re & in_data(h_raddr);

    assign hreq_set  = wr_data | rd_data;
    assign hreq_wr   = wr_data;
    assign hreq_addr = wr_data ? w_doff[10:0] : r_doff[10:0];
    assign hreq_d    = rbyte;

    // program memory: every byte is written to its lane of word w_off[10:3] of core w_off / PROG_SPAN
    wire [31:0] w_core = {16'd0, w_off} / PROG_SPAN;
    assign prog_we    = {wr_prog & (w_core == 32'd1), wr_prog & (w_core == 32'd0)};
    assign prog_waddr = w_off[10:3];
    assign prog_be    = 8'd1 << w_off[2:0];
    assign prog_wd    = rbyte;

    always @(posedge clk) begin
        if (!rst_n) begin
            bitcnt <= 3'd0; bytecnt <= 2'd0; cmd_wr <= 1'b0; cmd_rd <= 1'b0; rx <= 7'd0; addr <= 16'd0;
            tx <= 8'd0; hrd <= 8'd0; ldpend <= 1'b0; miso <= 1'b0;
        end else begin
            // read holding register: register reads at the end of the issuing cycle, data-RAM bytes on landing
            if (h_re && !rd_data) hrd <= reg_rd;
            else if (hland)       hrd <= hland_d;
            if (!cs) begin
                bitcnt <= 3'd0; bytecnt <= 2'd0; tx <= 8'd0; cmd_wr <= 1'b0; cmd_rd <= 1'b0;
                ldpend <= 1'b0; miso <= 1'b0;
            end else begin
                miso <= tx[7];
                if (sck_r) begin
                    rx     <= rbyte[6:0];
                    bitcnt <= bitcnt + 3'd1;
                end
                if (byte_done) begin
                    if (bytecnt != 2'd3) bytecnt <= bytecnt + 2'd1;
                    case (bytecnt)
                        2'd0: begin
                            cmd_wr <= (rbyte == 8'h02);
                            cmd_rd <= (rbyte == 8'h03);
                        end
                        2'd1: if (cmd_wr | cmd_rd) addr[15:8] <= rbyte;
                        2'd2: begin
                            if (cmd_wr) addr[7:0] <= rbyte;
                            if (cmd_rd) begin
                                addr   <= {addr[15:8], rbyte} + 16'd1;
                                ldpend <= 1'b1;
                            end
                        end
                        default: begin
                            if (cmd_wr) addr <= addr + 16'd1;
                            if (cmd_rd) ldpend <= 1'b1;
                        end
                    endcase
                end
                if (sck_f) begin
                    if (ldpend) begin
                        tx     <= hrd;
                        ldpend <= 1'b0;
                        addr   <= addr + 16'd1;
                    end else begin
                        tx <= {tx[6:0], 1'b0};
                    end
                end
            end
        end
    end

    wire unused_ok = &{1'b0, w_off[15:11], w_doff[15:11], r_doff[15:11], w_core[31:2]};
endmodule
`default_nettype wire
