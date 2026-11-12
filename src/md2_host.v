// Metronome v2 host link (wiki/SPEC_V2.md section 9): SPI target, mode 0, MSB first, on the chip's shared input
// synchronisers (SPEC 2). SR = synchronised SCK rising edge while the synchronised CS_N is low.
//   Byte 0: command (0x02 write, 0x03 read; anything else ignores the rest of the transaction).
//   Bytes 1, 2: ADDR[15:8], ADDR[7:0]; for a read, a read request at ADDR is issued in the next cycle.
//   Write, bytes 3 onward: `wr` (a host write of `wdata` at `addr`) in the cycle after the byte completes; ADDR' =
//   ADDR + 1 at the end of that cycle.
//   Read, bytes 3 onward: a read request at ADDR in the cycle after the byte completes.
// Read response: a register read requested in cycle R loads TX at the end of R+1 with `rd_val` sampled in R; a data
// RAM read loads TX at the end of the landing cycle (`hland`). ADDR increments with each load. MISO = TX[7].
`timescale 1ns/1ps
`default_nettype none
module md2_host (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        sck,          // synchronised levels (s2) and previous SCK (sp)
    input  wire        sck_p,
    input  wire        cs_n,
    input  wire        mosi,
    output reg  [15:0] addr,
    output reg         wr,           // host write of wdata at addr in this cycle
    output reg  [7:0]  wdata,
    output reg         rd,           // read request at addr in this cycle
    input  wire        rd_data,      // addr is a data RAM address (the read becomes a RAM request)
    input  wire [7:0]  rd_val,       // register value at addr in this cycle
    input  wire        hland,        // data RAM byte for the host lands this cycle
    input  wire [7:0]  hland_d,
    output wire        miso
);
    localparam [2:0] ST_CMD = 3'd0, ST_AH = 3'd1, ST_AL = 3'd2, ST_DATA = 3'd3, ST_IGN = 3'd4;

    reg [2:0] st;
    reg [2:0] bitc;
    reg [6:0] rx;
    reg [7:0] tx;
    reg       is_rd;
    reg       rack;          // register read value waiting to load TX
    reg [7:0] rackv;

    wire       cs   = ~cs_n;
    wire       sr   = cs & sck & ~sck_p;
    wire [7:0] byte_in = {rx, mosi};
    wire       ack  = rack | hland;
    wire [7:0] ackv = rack ? rackv : hland_d;
    wire [15:0] addr_i = (wr | ack) ? addr + 16'd1 : addr;

    always @(posedge clk) begin
        if (!rst_n) begin
            st <= ST_CMD; bitc <= 3'd0; rx <= 7'd0; tx <= 8'd0; is_rd <= 1'b0; rack <= 1'b0; rackv <= 8'd0;
            addr <= 16'd0; wr <= 1'b0; wdata <= 8'd0; rd <= 1'b0;
        end else begin
            rack  <= rd & ~rd_data;
            rackv <= rd_val;
            wr    <= 1'b0;
            rd    <= 1'b0;
            addr  <= addr_i;
            tx    <= ack ? ackv : tx;
            if (!cs) begin
                st <= ST_CMD; bitc <= 3'd0; tx <= 8'd0;
            end else if (sr) begin
                rx <= byte_in[6:0];
                if (bitc != 3'd7) begin
                    tx   <= {tx[6:0], 1'b0};
                    bitc <= bitc + 3'd1;
                end else begin
                    bitc <= 3'd0;
                    case (st)
                        ST_CMD: begin
                            is_rd <= (byte_in == 8'h03);
                            st    <= ((byte_in == 8'h02) | (byte_in == 8'h03)) ? ST_AH : ST_IGN;
                        end
                        ST_AH: begin addr <= {byte_in, addr_i[7:0]}; st <= ST_AL; end
                        ST_AL: begin addr <= {addr_i[15:8], byte_in}; st <= ST_DATA; rd <= is_rd; end
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
