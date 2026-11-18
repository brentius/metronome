// Calibration/regression sim of the formal build: prints every O8 (uo_out[2]) transition with the cycle number
// counted from rst_n release. Compile with -DFV_PAYLOAD=8'hXX -DFV_DELAY=N (see run_proofs.py).
`timescale 1ns/1ps
module tb_calib;
    reg clk = 0; reg rst_n = 0; reg [7:0] ui_in = 8'h00, uio_in = 8'h00;
    wire [7:0] uo, uio, oe;
    tt_um_brentius_metronome dut(.ui_in(ui_in), .uo_out(uo), .uio_in(uio_in), .uio_out(uio), .uio_oe(oe),
                                 .ena(1'b1), .clk(clk), .rst_n(rst_n));
    always #5 clk = ~clk;
    integer cyc = 0; reg prev = 1'b1;
    always @(posedge clk) begin
        #1;
        if (rst_n) cyc <= cyc + 1;
        if (cyc > 0 && uo[2] !== prev) $display("EDGE cyc=%0d O8=%b", cyc, uo[2]);
        prev <= uo[2];
    end
    initial begin
        repeat (4) @(posedge clk);
        #2 rst_n = 1;
        repeat (300) @(posedge clk);
        $display("DONE");
        $finish;
    end
endmodule
