"""Generate UART training and check a reply using a separately authored Verilog UART."""
import argparse
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory


TRAINING = bytes.fromhex("a55c38e713f48927") * 4
TX_TESTBENCH = """
`timescale 1ns/1ps
module drive_uart_peer;
    reg clk = 0;
    reg rst = 1;
    reg [7:0] data = 0;
    reg valid = 0;
    wire txd, ready, busy;
    integer input_fd, output_fd, value;
    always #5 clk = !clk;
    uart_tx peer (
        .clk(clk), .rst(rst), .prescale(16'd3),
        .s_axis_tdata(data), .s_axis_tvalid(valid), .s_axis_tready(ready),
        .txd(txd), .busy(busy)
    );
    always @(negedge clk) if (!rst) $fwrite(output_fd, "%c", {7'b0, txd});
    initial begin
        input_fd = $fopen("payload.bin", "rb");
        output_fd = $fopen("txd.bin", "wb");
        if (!input_fd || !output_fd) $fatal(1, "cannot open training files");
        repeat (4) @(negedge clk);
        #1 rst = 0;
        value = $fgetc(input_fd);
        while (value >= 0) begin
            wait (ready);
            @(negedge clk);
            #1 data = value[7:0];
            valid = 1;
            @(negedge clk);
            #1 valid = 0;
            value = $fgetc(input_fd);
        end
        wait (!busy);
        repeat (24) @(negedge clk);
        #1 $fclose(input_fd);
        $fclose(output_fd);
        $finish;
    end
    initial begin
        #200000 $fatal(1, "peer transmitter timed out");
    end
endmodule
"""


TESTBENCH = """
`timescale 1ns/1ps
module check_uart_peer;
    reg clk = 0;
    reg rst = 1;
    reg rxd = 1;
    wire [7:0] data;
    wire valid, error, overrun;
    integer fd, sample;
    always #5 clk = !clk;
    uart_rx peer (
        .clk(clk), .rst(rst), .rxd(rxd), .prescale(16'd3),
        .m_axis_tdata(data), .m_axis_tvalid(valid), .m_axis_tready(1'b1),
        .busy(), .overrun_error(overrun), .frame_error(error)
    );
    always @(negedge clk) begin
        if (valid) $display("byte %02x", data);
        if (error) $display("frame error");
        if (overrun) $fatal(1, "peer RX overrun");
    end
    initial begin
        fd = $fopen("rxd.bin", "rb");
        if (fd == 0) $fatal(1, "cannot open pin trace");
        repeat (4) @(negedge clk);
        rst = 0;
        sample = $fgetc(fd);
        while (sample >= 0) begin
            rxd = sample[0];
            @(negedge clk);
            sample = $fgetc(fd);
        end
        $fclose(fd);
        $finish;
    end
endmodule
"""


def emit_training(peer, output):
    with TemporaryDirectory() as directory:
        work = Path(directory)
        (work / "tx_tb.v").write_text(TX_TESTBENCH, encoding="utf-8")
        (work / "payload.bin").write_bytes(TRAINING)
        subprocess.run(["iverilog", "-g2012", "-s", "drive_uart_peer", "-o", "peer.vvp",
                        "tx_tb.v", str(peer.resolve())], cwd=work, check=True)
        subprocess.run(["vvp", "peer.vvp"], cwd=work, check=True)
        levels = (work / "txd.bin").read_bytes()
    output.write_bytes(levels)
    print(f"training: {len(TRAINING)} bytes, {len(levels)} samples")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path, nargs="?", help="LOCKSTEP_TRACE_UO output for v4_uart_reply")
    parser.add_argument("peer", type=Path, help="path to alexforencich/verilog-uart rtl/uart_rx.v or rtl/uart_tx.v")
    parser.add_argument("--emit-training", type=Path, metavar="OUTPUT", help="write training from the peer TX")
    args = parser.parse_args()
    if args.emit_training is not None:
        if args.trace is not None:
            parser.error("give only the TX Verilog source when emitting training")
        emit_training(args.peer, args.emit_training)
        return
    if args.trace is None:
        parser.error("a pin trace is required when checking the reply")

    # O8 is uo_out[2]. The scenario transmits at 24 clocks per bit after O8
    # first reaches the learned idle level.
    samples = bytearray((value >> 2) & 1 for value in args.trace.read_bytes())
    try:
        clean = samples[samples.index(1):]
        start = clean.index(0)
    except ValueError:
        parser.error("trace does not contain an idle-high interval followed by a start bit")
    period = 24
    stop = start + 9 * period
    if len(clean) < stop + 2 * period:
        parser.error("trace ends before the full reply and trailing idle")
    # Keep three trailing bit periods in the control. This observes the framing
    # error before the peer can resynchronize and complete another frame.
    bad_stop = clean[:stop + 3 * period]
    bad_stop[stop:stop + period] = bytes(period)

    with TemporaryDirectory() as directory:
        work = Path(directory)
        (work / "tb.v").write_text(TESTBENCH, encoding="utf-8")
        subprocess.run(["iverilog", "-g2012", "-s", "check_uart_peer", "-o", "peer.vvp",
                        "tb.v", str(args.peer.resolve())], cwd=work, check=True)
        for label, trace, expected in [
            ("reply", clean, ["byte 42"]),
            ("bad stop bit", bad_stop, ["frame error"]),
        ]:
            (work / "rxd.bin").write_bytes(trace)
            log = subprocess.check_output(["vvp", "peer.vvp"], cwd=work, text=True)
            result = [line for line in log.splitlines() if line.startswith(("byte ", "frame error"))]
            if result != expected:
                raise SystemExit(f"{label}: expected {expected}, got {result}")
            print(f"{label}: {result[0]}")


if __name__ == "__main__":
    main()
