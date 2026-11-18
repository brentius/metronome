"""Unit tests for cdc_check.py on small synthetic netlists (good, bad, waived)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cdc_check as C

PORTS = "module t (clk, rst_n, ena, ui_in, uio_in);\n input clk; input rst_n; input ena; input [7:0] ui_in; input [7:0] uio_in;\n"


def ff(name, d, q, rst="rq"):
    return f" sg13cmos5l_dfrbpq_1 {name} (.CLK(clk), .D({d}), .Q({q}), .RESET_B({rst}));\n"


def sync_chain(bit, extra=""):
    """tie-high reset chain rm -> rq driven by rst_n, then one input bit through two flops."""
    return (" sg13cmos5l_tiehi th (.L_HI(one));\n"
            " sg13cmos5l_dfrbpq_1 rm (.CLK(clk), .D(one), .Q(rmq), .RESET_B(rst_n));\n"
            " sg13cmos5l_dfrbpq_1 rq_f (.CLK(clk), .D(rmq), .Q(rq), .RESET_B(rst_n));\n" + extra)


def run(body, bits=None):
    text = PORTS + body + "endmodule\n"
    return C.check(C.Netlist(text))


def others(skip):   # tie the other 15 input bits into trivial two-flop chains so only `skip` is under test
    s = ""
    for bus in ("ui_in", "uio_in"):
        for b in range(8):
            n = f"{bus}[{b}]"
            if n == skip:
                continue
            k = f"{bus}{b}"
            s += ff(f"a_{k}", n, f"q1_{k}") + ff(f"b_{k}", f"q1_{k}", f"q2_{k}")
    return s


def test_clean_two_flop_synchroniser_passes():
    r = run(sync_chain(0) + ff("s1", "ui_in[0]", "m") + ff("s2", "m", "s") + " sg13cmos5l_inv_1 u (.A(s), .Y(y));\n"
            + others("ui_in[0]"))
    assert r["inputs"]["ui_in[0]"]["ok"] and r["inputs"]["ui_in[0]"]["stage2"] == ["s2"]
    assert not r["exceptions"], r["exceptions"]


def test_input_into_logic_before_flop_is_an_exception():
    r = run(sync_chain(0) + " sg13cmos5l_nand2_1 g (.A(ui_in[0]), .B(uio_in[0]), .Y(w));\n"
            + ff("s1", "w", "m") + ff("s2", "m", "s") + others("ui_in[0]"))
    assert any("ui_in[0]: reaches" in e for e in r["exceptions"])


def test_single_flop_feeding_logic_is_an_exception():
    r = run(sync_chain(0) + ff("s1", "ui_in[0]", "m") + " sg13cmos5l_nand2_1 u (.A(m), .B(uio_in[1]), .Y(y));\n" + others("ui_in[0]"))
    assert any("not a second flop" in e for e in r["exceptions"])


def test_buffers_are_transparent_and_flop_driven_and_is_waived():
    body = (sync_chain(0) + " sg13cmos5l_buf_1 ib (.A(ui_in[0]), .X(bi));\n"
            " sg13cmos5l_and2_1 g1 (.A(rq), .B(bi), .X(d1));\n" + ff("s1", "d1", "m")
            + " sg13cmos5l_and2_1 g2 (.A(rq), .B(m), .X(d2));\n" + ff("s2", "d2", "s") + others("ui_in[0]"))
    r = run(body)
    assert not r["exceptions"], r["exceptions"]
    assert len(r["waivers"]) == 2


def test_raw_reset_into_logic_is_an_exception():
    r = run(sync_chain(0) + " sg13cmos5l_nand2_1 bad (.A(rst_n), .B(rq), .Y(z));\n" + others("none"))
    assert any("raw reset reaches" in e for e in r["exceptions"])
