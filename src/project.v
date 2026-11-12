// Minimal Tiny Tapeout top for a later physical-flow run of the 256-byte (2,048-bit) latch configuration bank.
// NOT the Metronome design: it only exercises cfg_latch_bank at full size so area, clock-gate and latch handling
// can be measured, with every latch bit observable so nothing is optimised away.
//
// Pins (uio[1:0] inputs, uio[7:2] outputs; uio_oe is constant 8'b1111_1100):
//   ui_in[7:0]  data byte (hold stable for >= 4 clk around a strobe)
//   uio_in[0]   strobe (asynchronous: 2-flop synchroniser + rising-edge detect)
//   uio_in[1]   mode: 0 = load the address register from ui_in; 1 = write ui_in to byte [addr], then addr += 1
//   uo_out      readback: byte [addr] of the bank
//   uio_out[7:2] XOR fold of all 2,048 bits: output j = XOR of q[i] for i mod 6 == j
module tt_um_brentius_metronome (
    input  wire [7:0] ui_in,
    output wire [7:0] uo_out,
    input  wire [7:0] uio_in,
    output wire [7:0] uio_out,
    output wire [7:0] uio_oe,
    input  wire       ena,
    input  wire       clk,
    input  wire       rst_n
);
    localparam BYTES = 256;

    reg        s1, s2, s3;
    reg        go, mode_r;
    reg  [7:0] data_r, addr_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s1 <= 1'b0; s2 <= 1'b0; s3 <= 1'b0;
            go <= 1'b0; mode_r <= 1'b0; data_r <= 8'd0; addr_r <= 8'd0;
        end else begin
            s1 <= uio_in[0];
            s2 <= s1;
            s3 <= s2;
            go <= s2 & ~s3;
            if (s2 & ~s3) begin
                data_r <= ui_in;
                mode_r <= uio_in[1];
            end
            if (go) begin
                if (mode_r) addr_r <= addr_r + 8'd1;
                else        addr_r <= data_r;
            end
        end
    end

    wire [8*BYTES-1:0] q;
    cfg_latch_bank #(.BYTES(BYTES)) u_bank (
        .clk(clk), .rst_n(rst_n),
        .we(go & mode_r), .waddr(addr_r), .wdata(data_r),
        .q(q)
    );

    // readback mux of the addressed byte
    assign uo_out = q[{addr_r, 3'b000} +: 8];

    // XOR fold of every bit onto six outputs
    reg [5:0] fold;
    integer i;
    always @* begin
        fold = 6'd0;
        for (i = 0; i < 8*BYTES; i = i + 1)
            fold[i % 6] = fold[i % 6] ^ q[i];
    end
    assign uio_out = {fold, 2'b00};
    assign uio_oe  = 8'b1111_1100;

    wire _unused = &{ena, uio_in[7:2], 1'b0};
endmodule
