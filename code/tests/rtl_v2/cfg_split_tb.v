`timescale 1ns/1ps
module cfg_split_tb;
    reg clk = 0;
    always #5 clk = ~clk;
    reg rst_n = 1;
    reg wr = 0;
    reg [15:0] addr = 0;
    reg [7:0] data = 0;
    tt_um_brentius_metronome dut (.clk(clk), .rst_n(rst_n), .ena(1'b1),
                                 .ui_in(8'h02), .uio_in(8'h00));
    frozen_v3_top ref_dut (.clk(clk), .rst_n(rst_n), .ena(1'b1),
                           .ui_in(8'h02), .uio_in(8'h00));

    task compare;
        begin
            if (dut.cfg !== ref_dut.cfg)
                $fatal(1, "configuration differs at host address %h time %t", addr, $time);
            if ({dut.l_beat, dut.l_tap, dut.l_run} !==
                {ref_dut.l_beat, ref_dut.l_tap, ref_dut.l_run})
                $fatal(1, "line behavior differs at host address %h time %t", addr, $time);
        end
    endtask

    task write_byte;
        input [15:0] address;
        input [7:0] value;
        begin
            @(negedge clk);
            wr = 1;
            addr = address;
            data = value;
            @(posedge clk); #1; compare;
            @(negedge clk); #1;
            wr = 0;
            data = ~value;  // Host pins may change while the staged value must hold.
            compare;
            @(posedge clk); #1; compare;
        end
    endtask

    integer i;
    initial begin
        force dut.h_wr = wr;
        force dut.ha = addr;
        force dut.h_wd = data;
        force ref_dut.h_wr = wr;
        force ref_dut.ha = addr;
        force ref_dut.h_wd = data;
        #1 rst_n = 0;
        #2;
        if (dut.cfg !== 0) $fatal(1, "configuration did not clear asynchronously");
        repeat (3) @(negedge clk);
        rst_n = 1;
        repeat (3) @(negedge clk);
        for (i = 0; i < 512; i = i + 1)
            write_byte(16'h2000 + i[15:0], 8'hff);
        if (dut.cfg !== dut.CFG_MASK) $fatal(1, "mask does not match populated bits");
        for (i = 511; i >= 0; i = i - 1)
            write_byte(16'h2000 + i[15:0], i[7:0] ^ 8'h5a);
        #1 rst_n = 0;
        #1;
        if (dut.cfg !== 0) $fatal(1, "written configuration did not reset");
        compare;
        $display("PASS 512 addresses, reverse rewrite, earliest legal writes and async reset");
        $finish;
    end
endmodule
