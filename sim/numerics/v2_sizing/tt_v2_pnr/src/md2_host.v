// Metronome v2 host link (sizing version): SPI target, mode 0 (CPOL 0, CPHA 0), MSB first, oversampled by clk.
// SCK, CS_N and MOSI pass through 2-flop synchronisers; MOSI is sampled on the synchronised SCK rising edge.
// A frame (CS_N low) is: command byte, address high byte, address low byte, then data bytes with auto-increment.
//   0x02 write: each data byte gives a one-cycle `wr` strobe at `addr` with `wdata`; `addr` then increments.
//   0x03 read:  at the end of the address and of each data byte a one-cycle `rd` request at `addr`; the bus answers
//               with `rd_ack`/`rd_data` (any later cycle), which loads the MISO shift register and increments `addr`.
//   Other command bytes: the rest of the frame is ignored.
// MISO is the shift register's MSB and changes a few clk cycles after each SCK rising edge, so it is stable at the
// controller's next rising edge. Timing (calculated): synchroniser and edge detect take 3 clk cycles; a read must be
// acknowledged before the next SCK rising edge, so SCK should be at most clk/16 for reads that can wait on the data
// RAM arbiter (one SCK period = 16 clk, of which 3 are synchroniser latency).
// The bus address map belongs to the instantiating top (docs/info.md of the sizing project).
`timescale 1ns/1ps
`default_nettype none
module md2_host (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        sck,
    input  wire        cs_n,
    input  wire        mosi,
    output wire        miso,
    output reg         wr,
    output reg         rd,
    output reg  [15:0] addr,
    output reg  [7:0]  wdata,
    input  wire        rd_ack,
    input  wire [7:0]  rd_data
);
    localparam [2:0] ST_CMD = 3'd0, ST_AH = 3'd1, ST_AL = 3'd2, ST_DATA = 3'd3, ST_IGN = 3'd4;

    reg sck_m, sck_s, sck_d, cs_m, cs_s, mosi_m, mosi_s;
    always @(posedge clk) begin
        if (!rst_n) begin
            sck_m <= 1'b0; sck_s <= 1'b0; sck_d <= 1'b0;
            cs_m <= 1'b1; cs_s <= 1'b1;
            mosi_m <= 1'b0; mosi_s <= 1'b0;
        end else begin
            sck_m <= sck;  sck_s <= sck_m;  sck_d <= sck_s;
            cs_m  <= cs_n; cs_s  <= cs_m;
            mosi_m <= mosi; mosi_s <= mosi_m;
        end
    end
    wire rise = sck_s & ~sck_d & ~cs_s;

    reg [2:0] st;
    reg [2:0] bitc;
    reg [6:0] shin;
    reg [7:0] tx;
    reg       is_rd;
    wire [7:0] byte_in = {shin, mosi_s};

    always @(posedge clk) begin
        if (!rst_n) begin
            st <= ST_CMD; bitc <= 3'd0; shin <= 7'd0; tx <= 8'd0; is_rd <= 1'b0;
            wr <= 1'b0; rd <= 1'b0; addr <= 16'd0; wdata <= 8'd0;
        end else begin
            wr <= 1'b0;
            rd <= 1'b0;
            if (wr) addr <= addr + 16'd1;
            if (rd_ack) begin
                tx   <= rd_data;
                addr <= addr + 16'd1;
            end
            if (cs_s) begin
                st <= ST_CMD; bitc <= 3'd0; tx <= 8'd0;
            end else if (rise) begin
                shin <= byte_in[6:0];
                bitc <= bitc + 3'd1;
                if (bitc != 3'd7) tx <= {tx[6:0], 1'b0};
                else begin
                    case (st)
                        ST_CMD: begin
                            is_rd <= (byte_in == 8'h03);
                            st    <= ((byte_in == 8'h02) | (byte_in == 8'h03)) ? ST_AH : ST_IGN;
                        end
                        ST_AH: begin addr[15:8] <= byte_in; st <= ST_AL; end
                        ST_AL: begin addr[7:0] <= byte_in; st <= ST_DATA; rd <= is_rd; end
                        ST_DATA: begin
                            if (is_rd) rd <= 1'b1;
                            else begin wr <= 1'b1; wdata <= byte_in; end
                        end
                        default: ;
                    endcase
                end
            end
        end
    end
    assign miso = tx[7];
endmodule
`default_nettype wire
