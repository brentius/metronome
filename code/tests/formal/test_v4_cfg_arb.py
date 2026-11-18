"""Prove the configuration-port interlock and host byte conservation."""
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
RTL = ROOT / "src/md2_cfg_bank.v"
PROPERTIES = """
module check_cfg_arb (
    input clk, rst_s, host_valid, core_valid,
    input [8:0] host_addr, core_addr,
    input [7:0] host_data, core_data
);
    reg past_valid = 0;
    reg previous_write;
    wire bank_write, core_issue;
    wire [8:0] bank_addr;
    wire [7:0] bank_data;
    md2_cfg_arb dut (.*);
    always @(posedge clk) begin
        past_valid <= 1;
        previous_write <= rst_s && bank_write;
        if (!past_valid) assume(!rst_s);
        if (past_valid && $past(host_valid)) assume(!host_valid);
        if (past_valid && rst_s && $past(rst_s)) begin
            assert(!(previous_write && bank_write));
            if ($past(host_valid && previous_write)) begin
                assert(bank_write && !core_issue);
                assert(bank_addr == $past(host_addr));
                assert(bank_data == $past(host_data));
            end else if (host_valid && !previous_write) begin
                assert(bank_write && !core_issue);
                assert(bank_addr == host_addr);
                assert(bank_data == host_data);
            end else if (core_valid && !previous_write) begin
                assert(bank_write && core_issue);
                assert(bank_addr == core_addr && bank_data == core_data);
            end else begin
                assert(!bank_write && !core_issue);
            end
        end
    end
endmodule
"""


@pytest.mark.skipif(not shutil.which("yosys"), reason="requires Yosys")
@pytest.mark.parametrize("mutation", ["none", "spacing", "priority", "held_data"])
def test_config_arbiter(tmp_path, mutation):
    rules = {
        "spacing": ("core_valid & ~previous_write & ~host_issue", "core_valid & ~host_issue"),
        "priority": ("core_valid & ~previous_write & ~host_issue", "core_valid & ~previous_write"),
        "held_data": ("held_addr <= host_addr", "held_addr <= core_addr"),
    }
    rtl = RTL.read_text(encoding="utf-8")
    if mutation in rules:
        before, after = rules[mutation]
        assert rtl.count(before) == 1
        rtl = rtl.replace(before, after)
    (tmp_path / "rtl.v").write_text(rtl, encoding="utf-8")
    (tmp_path / "properties.sv").write_text(PROPERTIES, encoding="utf-8")
    run = subprocess.run(
        ["yosys", "-Q", "-p",
         "read_verilog -formal -sv rtl.v properties.sv; prep -top check_cfg_arb -flatten; "
         "async2sync; chformal -lower; "
         "sat -seq 5 -tempinduct -maxsteps 12 -set-assumes -verify -prove-asserts"],
        cwd=tmp_path, capture_output=True, text=True, timeout=60,
    )
    output = run.stdout + run.stderr
    if mutation == "none":
        assert run.returncode == 0 and "Induction step proven" in output, output[-4500:]
    else:
        assert run.returncode != 0 and "proof did fail" in output, output[-4500:]
