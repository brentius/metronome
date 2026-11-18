"""MDIO clause 22: every byte value in both halves of the data word, read and write, against an independent frame
decoder (IEEE 802.3 clause 22.2.4.5); scorec refuses the frame shape."""
import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("mdio")


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def frame(op, phy, reg, data):
    ev = [("op", op), ("phyad", phy), ("regad", reg)]
    return ev + ([("data", data)] if op == 1 else [("ta", 0), ("data", data)])


def test_every_byte_value_read_and_write():
    c = Codec(parse(SRC))
    ev, want = [], []
    for v in range(256):
        for op in (1, 2):
            data = (v << 8) | (255 - v) if op == 1 else ((255 - v) << 8) | v
            phy, reg = v & 31, (v * 3) & 31
            ev += frame(op, phy, reg, data)
            want.append({"op": "write" if op == 1 else "read", "phy": phy, "reg": reg, "data": data})
    enc = c.encode_all(ev)
    got = ind.mdio_decode(enc.bus["mdc"], enc.bus["mdio"])
    assert len(got) == 512
    assert [{k: g[k] for k in ("op", "phy", "reg", "data")} for g in got] == want
    assert all(g["ta"] == [1, 0] for g in got)                  # write 10 driven by the STA; read Z (pulled high) then 0 from the PHY
    assert {(g["data"] >> 8) & 255 for g in got} == set(range(256)) and {g["data"] & 255 for g in got} == set(range(256))


def test_read_turnaround_is_released_then_driven_low_by_the_phy():
    enc = Codec(parse(SRC)).encode_all(frame(2, 5, 7, 0xBEEF))
    rises = [i for i in range(1, enc.bus.n) if enc.bus["mdc"][i] and not enc.bus["mdc"][i - 1]]
    sta, phy = enc.drives["sta"]["mdio"], enc.drives["phy"]["mdio"]
    ta1, ta2 = rises[46], rises[47]
    assert sta[ta1] is None and phy[ta1] is None                 # nobody drives the first turnaround bit
    assert sta[ta2] is None and phy[ta2] == 0                    # the PHY drives the second one low
    assert enc.bus["mdio"][ta1] == 1 and enc.bus["mdio"][ta2] == 0


def test_codec_decodes_both_ops():
    c = Codec(parse(SRC))
    for op in (1, 2):
        r = c.decode("phy", c.encode_all(frame(op, 3, 4, 0x1234)).bus)
        assert r.ok, r.notes
        assert ("data", 0x1234) in r.events and ("op", op) in r.events


def test_compiler_refuses_the_frame_shape():
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "sta", "mdc=O8 mdio=P0/O0")
    assert e.value.code == "E-UNSUPPORTED" and "START REQUEST" in str(e.value)
