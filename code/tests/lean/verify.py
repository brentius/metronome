"""Check the Metronome Lean proofs against the current Verilog."""

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from rtlil import Cone, DffCone, UnsupportedRTL, require


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TOP = "tt_um_brentius_metronome"
ARB = "md2_cfg_arb"
STAGE = "md2_cfg_stage"
CORE_GRANT = "core_valid & ~previous_write & ~host_issue"
CONFIG_MUTATIONS = ("spacing", "priority", "held_addr", "held_data", "stage_capture")
HOST_MUTATIONS = ("host_gate", "host_counter")
DECODE_MUTATIONS = ("decode_permissive", "decode_core_bypass", "decode_mask_byte")
CORE_QUEUE_MUTATIONS = ("cwq_drain_clears", "cwq_hold_addr", "cwq_accept_pending",
                        "cwq_frz_gate", "cwq_overrun_clear")


def mask_byte_mutation(content, byte=30, value=0xFF):
    """Set one bank-mask byte in md2_map.vh without changing the decode table.

    The byte is currently zero and decodes as a hole, so the mutant leaves the
    RTL decode live while the elaborated latch bank has no latch for it.
    """
    match = re.search(rb"CFG_MASK = 3840'h([0-9A-Fa-f]{960})", content)
    require(match is not None, "decode_mask_byte: CFG_MASK anchor changed")
    digits = match.group(1).decode("ascii")
    start = len(digits) - 2 * (byte + 1)
    require(digits[start:start + 2] == "00",
            "decode_mask_byte: expected a zero mask byte")
    changed = digits[:start] + f"{value:02X}" + digits[start + 2:]
    return content[:match.start(1)] + changed.encode("ascii") + content[match.end(1):]


MUTATIONS = {
    "spacing": ("md2_cfg_bank.v", CORE_GRANT, "core_valid & ~host_issue"),
    "priority": ("md2_cfg_bank.v", CORE_GRANT, "core_valid & ~previous_write"),
    "held_addr": ("md2_cfg_bank.v", "held_addr <= host_addr", "held_addr <= core_addr"),
    "held_data": ("md2_cfg_bank.v", "held_data <= host_data", "held_data <= core_data"),
    "stage_capture": ("md2_cfg_bank.v", "if (we) data1 <= wdata", "if (we) data1 <= 8'd0"),
    "feedback": ("project.v", ".previous_write(cfg_we1)", ".previous_write(1'b0)"),
    "host_gate": ("md2_host.v", "            wr    <= 1'b0;", "            wr    <= 1'b1;"),
    "host_counter": ("md2_host.v",
                     "                    bitc <= 3'd0;\n                    case (st)",
                     "                    bitc <= 3'd1;\n                    case (st)"),
    "host_filter": ("project.v",
                    "wire cfg_host_now = h_wr & in_cfg & cfg_address_is_live(ha);",
                    "wire cfg_host_now = h_wr | (in_cfg & cfg_address_is_live(ha));"),
    # The decode table keeps bytes 29..31 of every line block live although
    # the latch bank has no latches there. A write/readback bench cannot see
    # this because the extra bytes are not writable.
    "decode_permissive": ("md2_map.vh",
                          "CFG_VALID_LINE_0 = 32'h1FFFFFFF",
                          "CFG_VALID_LINE_0 = 32'hFFFFFFFF"),
    # The core decode stays wired into the arbiter but sees bit 1 in place of
    # address bit 0. This is a core-only decode-site regression.
    "decode_core_bypass": ("project.v",
                           "wire cw_is_cfg = cfg_address_is_live(cw_pending_addr);",
                           "wire cw_is_cfg = cfg_address_is_live({cw_pending_addr[15:1], cw_pending_addr[1]});"),
    # A non-live window byte gains a latch while the decode still calls it a
    # hole. This is the reverse drift from decode_permissive.
    "decode_mask_byte": ("md2_map.vh", mask_byte_mutation),
    # The core arbiter takes nine low bits; changing one bit breaks the
    # address tie without touching the decode function.
    "decode_core_addr": ("project.v",
                         ".core_addr(cw_pending_addr[8:0]),",
                         ".core_addr({cw_pending_addr[8:1], 1'b0}),"),
    # Core pending-write queue. Each of these changes one register equation
    # that the independent SPEC_V2 13.1 queue specification pins down.
    "cwq_drain_clears": ("project.v",
                         "if (cw_drain) cw_pending <= 1'b0;",
                         "if (cw_drain) cw_pending <= cw_pending;"),
    "cwq_hold_addr": ("project.v",
                      "cw_pending_addr <= cw_addr;",
                      "cw_pending_addr <= {cw_addr[15:1], ~cw_addr[0]};"),
    "cwq_accept_pending": ("project.v",
                           "wire cw_accept = cw_write_data & (~cw_pending | cw_drain);",
                           "wire cw_accept = cw_write_data;"),
    "cwq_frz_gate": ("project.v",
                     "wire cw_drain = cw_pending & ~frz & (~cw_is_cfg | cfg_core_issue);",
                     "wire cw_drain = cw_pending & (~cw_is_cfg | cfg_core_issue);"),
    "cwq_overrun_clear": ("project.v",
                          "cw_overrun <= (cw_write_data & ~cw_accept) | "
                          "(cw_overrun & ~(c_wr_stk & h_wd[2]));",
                          "cw_overrun <= (cw_write_data & ~cw_accept) | cw_overrun;"),
}


def check_top(modules):
    """Check that the two translated instances form the intended chip-top cone."""
    top = modules[TOP]
    arb = top["cells"]["u_cfg_arb"]
    stage = top["cells"]["u_cfg_stage"]
    bank = top["cells"]["u_cfg"]
    require(arb["type"] == ARB and stage["type"] == STAGE, "unexpected arbiter or stage type")
    require(modules[bank["type"]]["attributes"].get("hdlname") == "md2_cfg_cells",
            "unexpected configuration bank type")

    for name, cell in (("u_cfg_arb", arb), ("u_cfg_stage", stage), ("u_cfg", bank)):
        pins = cell["connections"]
        require(pins["clk"] == top["ports"]["clk"]["bits"], f"{name}: unexpected clock")
        require(pins["rst_s"] == top["netnames"]["rst_q"]["bits"], f"{name}: unexpected reset")

    drivers = defaultdict(list)
    for name, port in top["ports"].items():
        if port["direction"] in ("input", "inout"):
            for bit in port["bits"]:
                drivers[bit].append(("<port>", name))
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit].append((name, pin))

    links = [
        ("u_cfg_stage", "we1", "u_cfg_arb", "previous_write"),
        ("u_cfg_arb", "bank_write", "u_cfg_stage", "we"),
        ("u_cfg_arb", "bank_addr", "u_cfg_stage", "waddr"),
        ("u_cfg_arb", "bank_data", "u_cfg_stage", "wdata"),
        ("u_cfg_stage", "we1", "u_cfg", "we1"),
        ("u_cfg_stage", "addr1", "u_cfg", "addr1"),
        ("u_cfg_stage", "data1", "u_cfg", "data1"),
    ]
    for sender, output, receiver, port in links:
        bits = top["cells"][sender]["connections"][output]
        link = f"{sender}.{output} -> {receiver}.{port}"
        require(bits == top["cells"][receiver]["connections"][port], f"broken top link: {link}")
        require(all(drivers[bit] == [(sender, output)] for bit in bits),
                f"multiple or missing drivers: {link}")


def top_drivers(top):
    drivers = defaultdict(list)
    for name, port in top["ports"].items():
        if port["direction"] in ("input", "inout"):
            for bit in port["bits"]:
                drivers[bit].append(("<port>", name))
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit].append((name, pin))
    return drivers


def and_leaves(top, drivers, bit, seen=None):
    """Expand scalar AND gates, treating any other driver as an opaque leaf."""
    if seen is None:
        seen = set()
    require(bit not in seen, "scalar AND cone has a combinational loop")
    seen.add(bit)
    owners = drivers[bit]
    require(len(owners) == 1, "scalar AND bit has multiple or no drivers")
    cell_name, pin = owners[0]
    cell = top["cells"].get(cell_name)
    if cell is None:
        return [bit]
    if cell["type"] in ("$and", "$logic_and"):
        require(pin == "Y" and len(cell["connections"]["Y"]) == 1,
                "scalar AND must be one bit wide")
        return (and_leaves(top, drivers, cell["connections"]["A"][0], seen) +
                and_leaves(top, drivers, cell["connections"]["B"][0], seen))
    return [bit]


def constant_value(bits, where):
    """Read a Yosys constant bus (little-endian) as an integer."""
    require(bits and all(bit in ("0", "1") for bit in bits),
            f"{where}: expected a constant bus")
    return int("".join(reversed(bits)), 2)


def module_parameters(modules, top, cell_name):
    """Read an instance's specialized parameters, from the cell or its module."""
    cell = top["cells"][cell_name]
    params = cell.get("parameters") or {}
    if not params:
        params = modules[cell["type"]].get("parameter_default_values", {})
    require(params, f"{cell_name}: no elaborated parameters")
    return {name: int(value, 2) if set(value) <= {"0", "1"} else value
            for name, value in params.items()}


def check_bank_mask(modules):
    """Check that every non-zero mask byte has a gate and its exact latches."""
    top = modules[TOP]
    cell = top["cells"]["u_cfg"]
    module = modules[cell["type"]]
    require(module["attributes"].get("hdlname") == "md2_cfg_cells",
            "unexpected configuration bank type")
    params = module_parameters(modules, top, "u_cfg")
    for name in ("BYTES", "MASK", "BASE", "AW"):
        require(name in params, f"u_cfg: missing {name} parameter")
    bytes_n, mask, base, aw = (params["BYTES"], params["MASK"],
                               params["BASE"], params["AW"])
    require(base == 0, "u_cfg: unexpected bank BASE")
    require(aw == 9, "u_cfg: unexpected address width")
    require(0 < bytes_n <= 512, "u_cfg: window does not fit the 9-bit address")
    require(mask >> (8 * bytes_n) == 0, "u_cfg: mask exceeds the bank")

    q = tuple(module["ports"]["q"]["bits"])
    require(len(q) == 8 * bytes_n, "u_cfg: unexpected q width")
    clk_bit = tuple(module["ports"]["clk"]["bits"])[0]
    rst_bit = tuple(module["ports"]["rst_s"]["bits"])[0]
    we1_bit = tuple(module["ports"]["we1"]["bits"])[0]
    addr1 = set(module["ports"]["addr1"]["bits"])
    data1 = tuple(module["ports"]["data1"]["bits"])

    drivers = {}
    for cell_name, cell in module["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "output":
                for bit in bits:
                    require(bit not in drivers, f"u_cfg: multiple drivers at {bit}")
                    drivers[bit] = (cell_name, pin)

    def dependencies(bit, seen=None):
        """Leaf module inputs behind one net bit; fail on unrelated sources."""
        if seen is None:
            seen = set()
        if bit in ("0", "1"):
            return set()
        if bit in addr1 or bit in (we1_bit, clk_bit, rst_bit):
            return {bit}
        if bit in seen:
            return set()
        seen.add(bit)
        require(bit in drivers, f"u_cfg: undriven gate input {bit}")
        cell_name, pin = drivers[bit]
        cell = module["cells"][cell_name]
        require(cell["type"] not in ("$dff", "$adff"),
                f"u_cfg: gate select depends on a register")
        require(pin == "Y" or pin in ("Q", "GCLK"),
                f"u_cfg: unexpected gate driver {cell_name}.{pin}")
        found = set()
        for input_pin, bits in cell["connections"].items():
            if cell["port_directions"][input_pin] == "input":
                for source in bits:
                    found |= dependencies(source, seen)
        return found

    latches = {}
    gates = set()
    for name in module["cells"]:
        match = re.fullmatch(r"g_byte\[(\d+)\]\.g_used\.g_bit\[(\d+)\]\.g_l\.u_l", name)
        if match:
            latches.setdefault(int(match.group(1)), set()).add(int(match.group(2)))
            continue
        match = re.fullmatch(r"g_byte\[(\d+)\]\.g_used\.u_cg", name)
        if match:
            gates.add(int(match.group(1)))

    for k in range(bytes_n):
        byte = (mask >> (8 * k)) & 0xFF
        bits = {b for b in range(8) if byte & (1 << b)}
        require(latches.get(k, set()) == bits,
                f"u_cfg: latch set of byte {k} does not match the mask")
        require((k in gates) == bool(bits),
                f"u_cfg: clock gate of byte {k} does not match the mask")
        if bits:
            gate = module["cells"][f"g_byte[{k}].g_used.u_cg"]
            require(tuple(gate["connections"]["CLK"]) == (clk_bit,),
                    f"u_cfg: byte {k} gate has an unexpected clock")
            gate_bit = tuple(gate["connections"]["GATE"])[0]
            require(gate_bit not in ("0", "1"),
                    f"u_cfg: byte {k} gate is tied off")
            require(gate_bit in drivers, f"u_cfg: byte {k} gate has no driver")
            enable_name, enable_pin = drivers[gate_bit]
            enable = module["cells"][enable_name]
            require(enable_pin == "Y" and enable["type"] in ("$logic_and", "$and"),
                    f"u_cfg: byte {k} gate is not an AND enable")
            enable_inputs = [bits_ for pin, bits_ in enable["connections"].items()
                             if enable["port_directions"][pin] == "input"]
            require(all(len(bits_) == 1 for bits_ in enable_inputs),
                    f"u_cfg: byte {k} gate enable is not scalar")
            inputs = [bits_[0] for bits_ in enable_inputs]
            require(len(inputs) == 2 and we1_bit in inputs,
                    f"u_cfg: byte {k} gate is not enabled by we1")
            selector = inputs[0] if inputs[1] == we1_bit else inputs[1]
            require(selector != we1_bit and dependencies(selector) <= addr1,
                    f"u_cfg: byte {k} gate is not selected by addr1")
            gclk_bit = tuple(gate["connections"]["GCLK"])[0]
            for b in bits:
                latch = module["cells"][f"g_byte[{k}].g_used.g_bit[{b}].g_l.u_l"]
                require(tuple(latch["connections"]["D"]) == (data1[b],),
                        f"u_cfg: byte {k} bit {b} latch has the wrong data")
                require(tuple(latch["connections"]["Q"]) == (q[8 * k + b],),
                        f"u_cfg: byte {k} bit {b} latch does not drive q")
                require(tuple(latch["connections"]["RESET_B"]) == (rst_bit,),
                        f"u_cfg: byte {k} bit {b} latch has the wrong reset")
                require(tuple(latch["connections"]["GATE"]) == (gclk_bit,),
                        f"u_cfg: byte {k} bit {b} latch has the wrong gate")
        for b in range(8):
            bit = q[8 * k + b]
            if byte & (1 << b):
                require(bit not in ("0", "1"),
                        f"u_cfg: masked bit {k}.{b} is tied off")
            else:
                require(bit == "0", f"u_cfg: unmasked bit {k}.{b} is not zero")
    return bytes_n, mask


def check_decode_top(modules):
    """Check both live-decode sites and their arbiter address connections."""
    top = modules[TOP]
    found = check_host_top(modules)
    live_leaf = found[2]

    drivers = top_drivers(top)
    ha = tuple(top["netnames"]["ha"]["bits"])
    cw_addr = tuple(top["netnames"]["cw_pending_addr"]["bits"])
    a_cfg = tuple(top["netnames"]["a_cfg"]["bits"])
    require(len(ha) == 16 and len(cw_addr) == 16 and len(a_cfg) == 16,
            "expected 16-bit host and core configuration addresses")

    arb = top["cells"]["u_cfg_arb"]
    require(tuple(arb["connections"]["host_addr"]) == a_cfg[:9],
            "host arbiter address is not a_cfg[8:0]")
    require(tuple(arb["connections"]["core_addr"]) == cw_addr[:9],
            "core arbiter address is not cw_pending_addr[8:0]")
    require(tuple(arb["connections"]["host_valid"]) ==
            tuple(top["netnames"]["cfg_host_now"]["bits"]),
            "host arbiter valid is not cfg_host_now")

    core_valid = tuple(arb["connections"]["core_valid"])
    require(len(core_valid) == 1, "core valid must be scalar")
    cw_is_cfg = tuple(top["netnames"]["cw_is_cfg"]["bits"])
    require(len(cw_is_cfg) == 1, "cw_is_cfg must be scalar")
    require(cw_is_cfg[0] in and_leaves(top, drivers, core_valid[0]),
            "core arbiter valid does not include cw_is_cfg")

    owners = drivers[a_cfg[0]]
    require(len(owners) == 1, "a_cfg has multiple or no drivers")
    sub_name, sub_pin = owners[0]
    sub = top["cells"][sub_name]
    require(sub["type"] == "$sub" and sub_pin == "Y", "a_cfg is not a subtraction")
    require(tuple(sub["connections"]["A"]) == ha, "a_cfg does not subtract from ha")
    cfg_lo = constant_value(sub["connections"]["B"], "a_cfg subtraction")
    require(all(drivers[bit] == [(sub_name, "Y")] for bit in a_cfg),
            "a_cfg has a sliced or multiple driver")

    in_cfg = tuple(top["netnames"]["in_cfg"]["bits"])
    require(len(in_cfg) == 1, "in_cfg must be scalar")
    owners = drivers[in_cfg[0]]
    require(len(owners) == 1, "in_cfg has multiple or no drivers")
    lt_name, lt_pin = owners[0]
    lt = top["cells"][lt_name]
    require(lt["type"] == "$lt" and lt_pin == "Y", "in_cfg is not a less-than")
    require(tuple(lt["connections"]["A"]) == a_cfg, "in_cfg does not test a_cfg")
    cfg_span = constant_value(lt["connections"]["B"], "in_cfg comparison")

    bytes_n, mask = check_bank_mask(modules)
    require(cfg_span == bytes_n,
            "configuration window span does not match the bank size")
    require(cfg_lo % 512 == 0 and cfg_span <= 512,
            "configuration window is not aligned to the 9-bit bank address")

    live_bytes = 0
    for k in range(bytes_n):
        if (mask >> (8 * k)) & 0xFF:
            live_bytes |= 1 << k
    return {
        "live_leaf": live_leaf,
        "in_cfg_bit": in_cfg[0],
        "cw_is_cfg_bit": cw_is_cfg[0],
        "ha": ha,
        "cw_addr": cw_addr,
        "cfg_lo": cfg_lo,
        "cfg_span": cfg_span,
        "bytes_n": bytes_n,
        "mask": mask,
        "live_bytes": live_bytes,
    }


def check_host_top(modules):
    """Check the actual host instance, its write net and the chip-top filter."""
    top = modules[TOP]
    host = top["cells"]["u_host"]
    require(host["type"] == "md2_host", "unexpected host instance type")
    pins = host["connections"]
    require(pins["clk"] == top["ports"]["clk"]["bits"], "u_host: unexpected clock")
    require(pins["rst_n"] == top["netnames"]["rst_q"]["bits"], "u_host: unexpected reset")
    drivers = top_drivers(top)
    for output, net in (("wr", "h_wr"), ("addr", "ha"), ("wdata", "h_wd")):
        bits = top["netnames"][net]["bits"]
        require(pins[output] == bits, f"u_host.{output}: unexpected connection")
        require(all(drivers[bit] == [("u_host", output)] for bit in bits),
                f"u_host.{output} does not uniquely drive {net}")

    arb = top["cells"]["u_cfg_arb"]
    require(arb["connections"]["host_valid"] == top["netnames"]["cfg_host_now"]["bits"],
            "cfg arbiters host_valid is not cfg_host_now")

    h_wr = tuple(top["netnames"]["h_wr"]["bits"])
    in_cfg = tuple(top["netnames"]["in_cfg"]["bits"])
    require(len(h_wr) == 1 and len(in_cfg) == 1, "scalar host filter expected")
    h_wr_bit, in_cfg_bit = h_wr[0], in_cfg[0]

    root = top["netnames"]["cfg_host_now"]["bits"]
    require(len(root) == 1, "cfg_host_now must be scalar")
    found = and_leaves(top, drivers, root[0])
    require(len(found) == 3 and found[0] == h_wr_bit and found[1] == in_cfg_bit,
            "host filter is not the conjunction u_host.wr & in_cfg & live-decode")
    return found


def lean_host(modules, fingerprint):
    check_host_top(modules)
    host = DffCone("host", modules["md2_host"])
    host.input("rst_n", 1, "input.resetN")
    host.input("sck", 1, "input.sck")
    host.input("sck_p", 1, "input.sckPrev")
    host.input("cs_n", 1, "input.csN")
    host.free("st", 3, "input.st")
    host.free("is_rd", 1, "input.isRd")
    bitc_d = host.register("bitc", 3, "state.bitc")
    wr_d = host.register("wr", 1, "state.wr")
    bitc = host.expression(bitc_d)
    write = host.expression(wr_d)
    lets = "\n".join(host.lines)
    return f"""import Metronome.Compose

set_option autoImplicit false

namespace Metronome.Host

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- The guest state `st` and the command latch `is_rd` are free per-cycle
-- inputs here. Their own next-state equations are outside this cut.
def rtlStep (state : State) (input : Input) : State :=
{lets}
  ⟨{write}, {bitc}⟩

end Metronome.Host

namespace Metronome.Compose

/-- The Python adapter checked that the elaborated `cfg_host_now` net is
exactly `((u_host.wr & in_cfg) & live)` with this definition's leaf order. -/
theorem chipHostValid_witness : chipHostValid true true true = true := rfl

end Metronome.Compose

"""


def _decode_expr(top, bit, free_name, width, value):
    """Resolve one scalar decode net with the address bus bound free."""
    cone = DffCone("decode", top)
    cone.free(free_name, width, value)
    expression = cone.expression((bit,))
    return "\n".join(cone.lines), expression


def _spec_lean(info, fingerprint):
    cfg_lo = info["cfg_lo"]
    cfg_hi = cfg_lo + info["cfg_span"]
    bytes_n = info["bytes_n"]
    live = info["live_bytes"]
    mask = info["mask"]
    hex_digits = (bytes_n + 3) // 4

    runs = []
    k = 0
    while k < bytes_n:
        if (live >> k) & 1:
            end = k
            while end < bytes_n and (live >> end) & 1:
                end += 1
            runs.append((k, end))
            k = end
        else:
            k += 1
    terms = " ||\n    ".join(
        f"(a >= (0x{cfg_lo + lo:04X} : BitVec 16) && "
        f"a < (0x{cfg_lo + hi:04X} : BitVec 16))" for lo, hi in runs)
    require(terms, "configuration bank has no live byte")
    # The named witness addresses below are the current map's documented
    # boundaries. A map change should stop here, not produce a confusing Lean
    # counterexample.
    require(bytes_n > 0x1DF, "decode: window too small for the boundary witnesses")
    require((live >> 0x1D) & 1 == 0, "decode: 0x201d is no longer a hole")
    require((live >> 0x1DF) & 1 == 0, "decode: 0x21df is no longer a mask hole")
    require(((mask >> (8 * 0xD0)) & 0xFF) == 0x03,
            "decode: 0x20d0 is no longer a partial 0x03 byte")
    require((live >> 0xD0) & 1 == 1, "decode: 0x20d0 is no longer live")
    mask_hex = f"{mask:0{2 * bytes_n}X}"
    live_hex = f"{live:0{hex_digits}X}"
    return f"""import Metronome.Compose
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Configuration window and bank mask come from the elaborated chip top:
-- CFG_LO from the `a_cfg = ha - CFG_LO` subtraction, the span from the
-- `in_cfg` comparison, and MASK from the specialized `u_cfg` instance.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000

namespace Metronome.Decode

abbrev cfgLo : BitVec 16 := 0x{cfg_lo:04X}
abbrev cfgHi : BitVec 16 := 0x{cfg_hi:04X}
abbrev cfgBytes : Nat := {bytes_n}

/-- The elaborated `u_cfg` MASK parameter, one byte per window offset. -/
abbrev bankMask : BitVec {8 * bytes_n} := 0x{mask_hex}

/-- Bit k is set iff bank byte k contains at least one latch. -/
abbrev liveBytes : BitVec {bytes_n} := 0x{live_hex}

abbrev maskByte (off : Nat) : BitVec 8 :=
  (bankMask >>> (8 * off)).truncate 8

abbrev inWindow (a : BitVec 16) : Bool :=
  cfgLo <= a && a < cfgHi

/-- The maximal runs of non-zero mask bytes, as absolute addresses. -/
abbrev maskLive (a : BitVec 16) : Bool :=
    {terms}

abbrev byteFlag (a : BitVec 16) : Bool :=
  (((liveBytes >>> (a - cfgLo).toNat) &&& (1 : BitVec {bytes_n})) != 0)

abbrev specLive (a : BitVec 16) : Bool :=
  inWindow a && maskLive a

/-- The run list is exactly the set of non-zero mask bytes. -/
theorem runs_match_mask : forall i : Fin cfgBytes,
    maskLive (cfgLo + BitVec.ofNat 16 i.val) = liveBytes.getLsb i := by
  decide

/-- The extracted flag vector is exactly "the MASK byte is non-zero". -/
theorem liveBytes_eq_mask : forall i : Fin cfgBytes,
    liveBytes.getLsb i = (maskByte i.val != 0) := by
  decide

/-- info: 'Metronome.Decode.runs_match_mask' depends on axioms: [propext] -/
#guard_msgs in #print axioms runs_match_mask

/-- info: 'Metronome.Decode.liveBytes_eq_mask' depends on axioms: [propext] -/
#guard_msgs in #print axioms liveBytes_eq_mask

/-- Interval membership and the flag-vector lookup agree for every address. -/
theorem maskLive_eq_byteFlag (a : BitVec 16) :
    maskLive a = byteFlag a := by
  bv_decide

theorem cfgHi_is_window : cfgHi = cfgLo + BitVec.ofNat 16 cfgBytes := by
  decide

/-- The full 16-bit window offset fits the nine-bit bank address, so no
information is lost by the `a_cfg[8:0]` / low-nine-bit connection. -/
theorem offset_fits_nine (a : BitVec 16) (live : specLive a = true) :
    (a - cfgLo) < (512 : BitVec 16) := by
  bv_decide

theorem first_live : specLive 0x{cfg_lo + next(k for k in range(bytes_n) if (live >> k) & 1):04X} = true := by
  decide

theorem last_live : specLive 0x{cfg_lo + max(k for k in range(bytes_n) if (live >> k) & 1):04X} = true := by
  decide

theorem hole_201D : specLive 0x{cfg_lo + 0x1D:04X} = false := by
  decide

theorem indexed_tail : inWindow 0x{cfg_lo + 0x1DF:04X} = true ∧
    specLive 0x{cfg_lo + 0x1DF:04X} = false := by
  decide

theorem partial_byte : maskByte 0xD0 = 0x03 ∧ specLive 0x{cfg_lo + 0xD0:04X} = true := by
  decide

theorem out_of_window : specLive 0x{cfg_hi:04X} = false := by
  decide

theorem wrapped_below : specLive 0x{cfg_lo - 1:04X} = false := by
  decide

"""


def lean_decode(modules, fingerprint):
    """Generate the host and core configuration-address decode proofs."""
    info = check_decode_top(modules)
    top = modules[TOP]
    ha_lets, in_cfg = _decode_expr(top, info["in_cfg_bit"], "ha", 16, "a")
    live_lets, live = _decode_expr(top, info["live_leaf"], "ha", 16, "a")
    core_lets, core_live = _decode_expr(
        top, info["cw_is_cfg_bit"], "cw_pending_addr", 16, "a")
    spec = _spec_lean(info, fingerprint)

    host = spec + f"""abbrev rtlInCfg (a : BitVec 16) : Bool :=
{ha_lets}
  {in_cfg}

abbrev rtlLive (a : BitVec 16) : Bool :=
{live_lets}
  {live}

abbrev rtlHostQual (a : BitVec 16) : Bool :=
  rtlInCfg a && rtlLive a

/-- The elaborated host qualification `in_cfg & live` equals the mask rule at
every 16-bit address. -/
theorem rtlHostQual_eq_spec (a : BitVec 16) :
    rtlHostQual a = specLive a := by
  bv_decide

/-- `in_cfg` alone is not the qualification: the last indexed window byte is a
mask hole. -/
theorem host_tail_indexed_not_live :
    rtlInCfg 0x{info["cfg_lo"] + 0x1DF:04X} = true ∧
      rtlLive 0x{info["cfg_lo"] + 0x1DF:04X} = false := by
  decide

theorem host_first_live : rtlHostQual 0x{info["cfg_lo"]:04X} = true := by
  decide

theorem host_last_live : rtlHostQual 0x{info["cfg_lo"] + max(k for k in range(info["bytes_n"]) if (info["live_bytes"] >> k) & 1):04X} = true := by
  decide

theorem host_hole : rtlHostQual 0x{info["cfg_lo"] + 0x1D:04X} = false := by
  decide

theorem host_wrapped : rtlHostQual 0x{info["cfg_lo"] - 1:04X} = false := by
  decide

theorem host_out_of_window : rtlHostQual 0x{info["cfg_lo"] + info["cfg_span"]:04X} = false := by
  decide

-- `bv_decide` supplies a native-checked LRAT certificate for the bit-blasted
-- equivalence. The audit below is checked by `verify.py` for the absence of
-- `sorryAx` and for this native certificate axiom.
#print axioms rtlHostQual_eq_spec

end Metronome.Decode
"""

    core = spec + f"""abbrev rtlCoreLive (a : BitVec 16) : Bool :=
{core_lets}
  {core_live}

/-- The elaborated core `cw_is_cfg` equals the mask rule at every 16-bit
address. -/
theorem rtlCoreLive_eq_spec (a : BitVec 16) :
    rtlCoreLive a = specLive a := by
  bv_decide

/-- The nine low bits taken by the core arbiter are the low bits of the
window offset; `cfgLo` is nine-bit aligned. This is a total identity. -/
theorem core_low_bits_are_offset (a : BitVec 16) :
    a.truncate 9 = (a - cfgLo).truncate 9 := by
  bv_decide

theorem core_first_live : rtlCoreLive 0x{info["cfg_lo"]:04X} = true := by
  decide

theorem core_last_live : rtlCoreLive 0x{info["cfg_lo"] + max(k for k in range(info["bytes_n"]) if (info["live_bytes"] >> k) & 1):04X} = true := by
  decide

theorem core_hole : rtlCoreLive 0x{info["cfg_lo"] + 0x1D:04X} = false := by
  decide

theorem core_wrapped : rtlCoreLive 0x{info["cfg_lo"] - 1:04X} = false := by
  decide

theorem core_out_of_window : rtlCoreLive 0x{info["cfg_lo"] + info["cfg_span"]:04X} = false := by
  decide

-- See the host file: this equality carries the same native LRAT certificate
-- axiom from `bv_decide`.
#print axioms rtlCoreLive_eq_spec

end Metronome.Decode
"""
    return host, core


def check_core_queue_top(modules):
    """Check the arbiter request driven by the core queue registers."""
    top = modules[TOP]
    arb = top["cells"]["u_cfg_arb"]
    drivers = top_drivers(top)
    pending = tuple(top["netnames"]["cw_pending"]["bits"])
    frz = tuple(top["netnames"]["frz"]["bits"])
    is_cfg = tuple(top["netnames"]["cw_is_cfg"]["bits"])
    pending_addr = tuple(top["netnames"]["cw_pending_addr"]["bits"])
    pending_data = tuple(top["netnames"]["cw_pending_data"]["bits"])
    require(len(pending) == 1 and len(frz) == 1 and len(is_cfg) == 1,
            "cw_pending, frz and cw_is_cfg must be scalar")
    require(len(pending_addr) == 16 and len(pending_data) == 8,
            "unexpected core queue payload width")
    require(tuple(arb["connections"]["core_addr"]) == pending_addr[:9],
            "core arbiter address is not cw_pending_addr[8:0]")
    require(tuple(arb["connections"]["core_data"]) == pending_data,
            "core arbiter data is not cw_pending_data")
    core_valid = tuple(arb["connections"]["core_valid"])
    require(len(core_valid) == 1, "core valid must be scalar")
    leaves = and_leaves(top, drivers, core_valid[0])
    require(len(leaves) == 3 and leaves[0] == pending[0] and leaves[2] == is_cfg[0],
            "core valid is not cw_pending & ~frz & cw_is_cfg")
    owners = drivers[leaves[1]]
    require(len(owners) == 1, "core valid freeze term has multiple or no drivers")
    not_name, not_pin = owners[0]
    not_cell = top["cells"][not_name]
    require(not_pin == "Y" and not_cell["type"] == "$not" and
            tuple(not_cell["connections"]["A"]) == frz,
            "core valid freeze term is not ~frz")
    issue = tuple(top["netnames"]["cfg_core_issue"]["bits"])
    require(len(issue) == 1, "cfg_core_issue must be scalar")
    require(tuple(arb["connections"]["core_issue"]) == issue,
            "cfg_core_issue is not the arbiter core_issue output")
    require(all(drivers[bit] == [("u_cfg_arb", "core_issue")] for bit in issue),
            "cfg_core_issue has multiple or no drivers")


def lean_core_queue(modules, fingerprint):
    """Generate the core pending-write queue transition from the chip top."""
    check_core_queue_top(modules)
    cone = DffCone("cwq", modules[TOP])
    cone.leaf("rst_q", 1, "input.resetN")
    cone.leaf("w_cw", 15, "input.cw")
    cone.leaf("frz", 1, "input.frz")
    cone.leaf("cfg_core_issue", 1, "input.coreIssue")
    cone.leaf("cw_is_cfg", 1, "input.isCfg")
    cone.leaf("c_wr_stk", 1, "input.clearSticky")
    cone.leaf("h_wd", 8, "input.hostData")
    addr_d = cone.register("cw_addr", 16, "state.addr")
    pending_d = cone.register("cw_pending", 1, "state.pending")
    pending_addr_d = cone.register("cw_pending_addr", 16, "state.pendingAddr")
    pending_data_d = cone.register("cw_pending_data", 8, "state.pendingData")
    overrun_d = cone.register("cw_overrun", 1, "state.overrun")
    addr = cone.expression(addr_d)
    pending = cone.expression(pending_d)
    pending_addr = cone.expression(pending_addr_d)
    pending_data = cone.expression(pending_data_d)
    overrun = cone.expression(overrun_d)
    require(not cone.registers, "unmodeled core queue state")
    lets = "\n".join(cone.lines)
    return f"""import Metronome.CoreQueue

set_option autoImplicit false

namespace Metronome.CoreQueue

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- `w_cw` (the picked CW group), `frz`, `cfg_core_issue`, `cw_is_cfg` and the
-- `CTRL.STICKY` clear leaf `c_wr_stk & h_wd[2]` are free per-cycle inputs.
def rtlStep (state : State) (input : Input) : State :=
{lets}
  {{ addr := {addr}
    pending := {pending}
    pendingAddr := {pending_addr}
    pendingData := {pending_data}
    overrun := {overrun} }}

end Metronome.CoreQueue

"""


def lean_transition(modules, fingerprint):
    check_top(modules)
    arb = Cone("arb", modules[ARB])
    for name, width, value in (
        ("rst_s", 1, "input.resetN"),
        ("previous_write", 1, "previousWrite"),
        ("host_valid", 1, "input.hostValid"),
        ("host_addr", 9, "input.host.addr"),
        ("host_data", 8, "input.host.data"),
        ("core_valid", 1, "input.coreValid"),
        ("core_addr", 9, "input.core.addr"),
        ("core_data", 8, "input.core.data"),
    ):
        arb.input(name, width, value)

    hold_d = arb.register("host_held", 1, "state.heldValid", "$dff")
    hold_addr_d = arb.register("held_addr", 9, "state.held.addr", "$dff")
    hold_data_d = arb.register("held_data", 8, "state.held.data", "$dff")
    core_issue = arb.expression(arb.port("core_issue", "output", 1))
    bank_write = arb.expression(arb.port("bank_write", "output", 1))
    bank_addr = arb.expression(arb.port("bank_addr", "output", 9))
    bank_data = arb.expression(arb.port("bank_data", "output", 8))
    held = arb.expression(hold_d)
    held_addr = arb.expression(hold_addr_d)
    held_data = arb.expression(hold_data_d)

    stage = Cone("stage", modules[STAGE])
    stage.input("rst_s", 1, "input.resetN")
    stage.input("we", 1, bank_write)
    stage.input("waddr", 9, bank_addr)
    stage.input("wdata", 8, bank_data)
    for name, width in (("we1", 1), ("addr1", 9), ("data1", 8)):
        require(stage.port(name, "output", width) == tuple(stage.module["netnames"][name]["bits"]),
                f"{STAGE}.{name}: expected register to drive this output")
    # Both modules see the stage strobe after its asynchronous clear.
    we_d = stage.register("we1", 1, "previousWrite", "$adff")
    addr_d = stage.register("addr1", 9, "state.staged.addr", "$dff")
    data_d = stage.register("data1", 8, "state.staged.data", "$dff")
    previous = stage.next_value(we_d, "$adff")
    staged_addr = stage.expression(addr_d)
    staged_data = stage.expression(data_d)
    require(not arb.registers and not stage.registers, "unmodeled configuration state")

    lets = "\n".join(arb.lines + stage.lines)
    return f"""import Metronome.Config

set_option autoImplicit false

namespace Metronome.Config

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
def rtlStep (state : State) (input : Input) : Result :=
  let previousWrite := input.resetN && state.previousWrite
{lets}
  {{ coreIssue := {core_issue}
    bankWrite := {bank_write}
    bank := ⟨{bank_addr}, {bank_data}⟩
    next := {{ previousWrite := {previous}
              heldValid := {held}
              held := ⟨{held_addr}, {held_data}⟩
              staged := ⟨{staged_addr}, {staged_data}⟩ }} }}

end Metronome.Config

"""


class CachedResult:
    """A successful Lean run whose generated source was unchanged."""

    def __init__(self, text):
        self.returncode = 0
        self.stdout = text


DECODE_HOST_CACHE = set()
DECODE_CORE_CACHE = set()


def run(command, cwd, timeout=900):
    return subprocess.run(command, cwd=cwd, text=True, encoding="utf-8",
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)


def run_lean(source, filename, artifact, lake, work, evidence):
    path = work / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (evidence / artifact).write_text(source, encoding="utf-8")
    # Windows cold starts have been observed to stall a Lean process. One
    # retry keeps a transient tool-startup failure from failing the check.
    for attempt in range(2):
        try:
            return run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
                       HERE, timeout=300)
        except subprocess.TimeoutExpired:
            if attempt:
                raise


def verify_case(case, snapshot, lake, yosys, work, evidence):
    work.mkdir()
    src = work / "src"
    src.mkdir()
    digest = hashlib.sha256()
    for name, content in sorted(snapshot.items()):
        mutation = MUTATIONS.get(case)
        if mutation and name == mutation[0]:
            if len(mutation) == 3:
                _, before, after = mutation
                require(content.count(before.encode()) == 1, f"{case}: mutation anchor changed")
                content = content.replace(before.encode(), after.encode(), 1)
            else:
                content = mutation[1](content)
        (src / name).write_bytes(content)
        digest.update(name.encode() + b"\0" + hashlib.sha256(content).digest())

    files = " ".join(f"src/{path.name}" for path in sorted(src.glob("*.v")))
    commands = (f"read_verilog -I src {files}; hierarchy -check -top {TOP}; "
                "proc; opt_clean; write_json design.json")
    design = run([yosys, "-Q", "-q", "-p", commands], work)
    log = f"RTL snapshot SHA-256: {digest.hexdigest()}\nYosys command: {commands}\n"
    log += design.stdout
    host_log = ""
    decode_log = ""
    core_log = ""
    try:
        if design.returncode != 0:
            raise RuntimeError("Yosys elaboration failed")
        modules = json.loads((work / "design.json").read_text(encoding="utf-8"))["modules"]
        try:
            source = lean_transition(modules, digest.hexdigest())
        except UnsupportedRTL as exc:
            if case == "feedback" and str(exc) == (
                "broken top link: u_cfg_stage.we1 -> u_cfg_arb.previous_write"
            ):
                log += f"Importer rejected {case}: {exc}\n"
                print(f"{case}: rejected by top-level wiring check", flush=True)
                return
            raise
        try:
            host_source = lean_host(modules, digest.hexdigest())
        except UnsupportedRTL as exc:
            if case == "host_filter" and str(exc) == (
                "host filter is not the conjunction u_host.wr & in_cfg & live-decode"
            ):
                log += f"Importer rejected {case}: {exc}\n"
                print(f"{case}: rejected by chip-top host filter check", flush=True)
                return
            raise
        try:
            decode_host_source, decode_core_source = lean_decode(
                modules, digest.hexdigest())
        except UnsupportedRTL as exc:
            if case == "decode_core_addr" and str(exc) == (
                "core arbiter address is not cw_pending_addr[8:0]"
            ):
                log += f"Importer rejected {case}: {exc}\n"
                print(f"{case}: rejected by core arbiter address check", flush=True)
                return
            raise
        source += (HERE / "RtlEquivalence.lean.in").read_text(encoding="utf-8")
        host_source += (HERE / "HostEquivalence.lean.in").read_text(encoding="utf-8")
        core_source = lean_core_queue(modules, digest.hexdigest())
        core_source += (HERE / "CoreQueueEquivalence.lean.in").read_text(encoding="utf-8")
        proof = run_lean(source, "ConfigProof.lean", f"{case}.lean", lake, work, evidence)
        host = run_lean(host_source, "HostProof.lean", f"{case}.host.lean",
                        lake, work, evidence)
        if case != "baseline" and decode_host_source in DECODE_HOST_CACHE:
            decode_host = CachedResult(
                "Decode host source is byte-identical to an accepted case; "
                "proof result reused.\n")
        else:
            decode_host = run_lean(decode_host_source, "DecodeHostProof.lean",
                                   f"{case}.decodehost.lean", lake, work, evidence)
            if decode_host.returncode == 0:
                DECODE_HOST_CACHE.add(decode_host_source)
        if case != "baseline" and decode_core_source in DECODE_CORE_CACHE:
            decode_core = CachedResult(
                "Decode core source is byte-identical to an accepted case; "
                "proof result reused.\n")
        else:
            decode_core = run_lean(decode_core_source, "DecodeCoreProof.lean",
                                   f"{case}.decodecore.lean", lake, work, evidence)
            if decode_core.returncode == 0:
                DECODE_CORE_CACHE.add(decode_core_source)
        core = run_lean(core_source, "CoreQueueProof.lean", f"{case}.corequeue.lean",
                        lake, work, evidence)
        log += proof.stdout
        host_log += host.stdout
        decode_log = decode_host.stdout + decode_core.stdout
        core_log = core.stdout
        log += f"Config proof outcome: {'accepted' if proof.returncode == 0 else 'rejected'}\n"
        host_log += f"Host proof outcome: {'accepted' if host.returncode == 0 else 'rejected'}\n"
        decode_log += (f"Decode host outcome: "
                       f"{'accepted' if decode_host.returncode == 0 else 'rejected'}\n")
        decode_log += (f"Decode core outcome: "
                       f"{'accepted' if decode_core.returncode == 0 else 'rejected'}\n")
        core_log += (f"Core queue outcome: "
                     f"{'accepted' if core.returncode == 0 else 'rejected'}\n")
        config_ok = proof.returncode == 0
        host_ok = host.returncode == 0
        decode_host_ok = decode_host.returncode == 0
        decode_core_ok = decode_core.returncode == 0
        core_ok = core.returncode == 0
        config_rejected = proof.returncode == 1 and 'Tactic `rfl` failed' in proof.stdout
        host_rejected = host.returncode == 1 and 'Tactic `rfl` failed' in host.stdout

        def proof_failed(result):
            text = result.stdout
            return result.returncode == 1 and (
                "counterexample" in text or "unsolved goals" in text or
                "Tactic" in text)

        decode_host_rejected = proof_failed(decode_host)
        decode_core_rejected = proof_failed(decode_core)
        core_rejected = proof_failed(core)
        if case == "baseline":
            if not (config_ok and host_ok and decode_host_ok and decode_core_ok and core_ok):
                raise RuntimeError(
                    "baseline: Lean failed (config {}, host {}, decode host {}, "
                    "decode core {}, core queue {})".format(proof.returncode,
                                                            host.returncode,
                                                            decode_host.returncode,
                                                            decode_core.returncode,
                                                            core.returncode))
            require("sorryAx" not in decode_log,
                    "baseline: decode proof used sorryAx")
            require("sorryAx" not in core_log,
                    "baseline: core queue proof used sorryAx")
            require("bv_decide" in decode_log,
                    "baseline: expected the native BV certificate audit")
            print("baseline: Lean verified the configuration transition, host write cone, "
                  "both configuration-address decodes, the core pending-write queue, "
                  "their traces and axiom dependencies",
                  flush=True)
            print(proof.stdout + host.stdout + decode_log + core_log, end="", flush=True)
        elif case in CONFIG_MUTATIONS:
            if not (config_rejected and host_ok and decode_host_ok and decode_core_ok
                    and core_ok):
                raise RuntimeError(
                    f"{case}: expected config rejection and host/decode queue success "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by Lean configuration equivalence proof", flush=True)
        elif case in HOST_MUTATIONS:
            if not (config_ok and host_rejected and decode_host_ok and decode_core_ok
                    and core_ok):
                raise RuntimeError(
                    f"{case}: expected host rejection and config/decode/queue success "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by Lean host equivalence proof", flush=True)
        elif case == "decode_permissive":
            if not (config_ok and host_ok and decode_host_rejected and decode_core_rejected
                    and core_ok):
                raise RuntimeError(
                    f"{case}: expected both decode rejections and config/host/queue success "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by both Lean decode equivalence proofs", flush=True)
        elif case == "decode_mask_byte":
            if not (config_ok and host_ok and decode_host_rejected and decode_core_rejected
                    and core_ok):
                raise RuntimeError(
                    f"{case}: expected both decode rejections and config/host/queue success "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by both Lean decode equivalence proofs", flush=True)
        elif case == "decode_core_bypass":
            if not (config_ok and host_ok and decode_host_ok and decode_core_rejected
                    and core_ok):
                raise RuntimeError(
                    f"{case}: expected core decode rejection only "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by Lean core decode equivalence proof", flush=True)
        elif case in CORE_QUEUE_MUTATIONS:
            if not (core_rejected and config_ok and host_ok and decode_host_ok
                    and decode_core_ok):
                raise RuntimeError(
                    f"{case}: expected core queue rejection and config/host/decode success "
                    f"(config {proof.returncode}, host {host.returncode}, "
                    f"decode host {decode_host.returncode}, "
                    f"decode core {decode_core.returncode}, core {core.returncode})")
            print(f"{case}: rejected by Lean core pending-write queue proof", flush=True)
        else:
            raise RuntimeError(f"{case}: unexpected Lean proof outcome")
    except (RuntimeError, UnsupportedRTL):
        print(log, end="", file=sys.stderr)
        raise
    finally:
        if evidence:
            (evidence / f"{case}.log").write_text(log, encoding="utf-8")
            (evidence / f"{case}.host.log").write_text(host_log, encoding="utf-8")
            (evidence / f"{case}.decode.log").write_text(decode_log, encoding="utf-8")
            (evidence / f"{case}.corequeue.log").write_text(core_log, encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true", help="also check planted RTL regressions")
    parser.add_argument("--artifacts-dir", type=Path, help="new directory for proof sources and logs")
    args = parser.parse_args()
    lake, yosys = (shutil.which(tool) for tool in ("lake", "yosys"))
    if not lake or not yosys:
        parser.error("lake and yosys must be on PATH")
    if args.artifacts_dir:
        args.artifacts_dir.mkdir(parents=True, exist_ok=False)
    versions = [run([lake, "--version"], HERE), run([yosys, "-V"], HERE)]
    version_log = "".join(result.stdout for result in versions)
    print(version_log, end="", flush=True)
    if args.artifacts_dir:
        (args.artifacts_dir / "tools.log").write_text(version_log, encoding="utf-8")
    if any(result.returncode for result in versions):
        return 1
    build = run([lake, "build"], HERE)
    print(build.stdout, end="", flush=True)
    if args.artifacts_dir:
        (args.artifacts_dir / "lake.log").write_text(build.stdout, encoding="utf-8")
    if build.returncode != 0:
        return 1
    snapshot = {p.name: p.read_bytes() for p in (ROOT / "src").iterdir()
                if p.suffix in (".v", ".vh")}
    cases = ("baseline", *MUTATIONS) if args.mutations else ("baseline",)
    with tempfile.TemporaryDirectory(prefix="metronome-lean-") as tmp:
        for case in cases:
            verify_case(case, snapshot, lake, yosys, Path(tmp) / case, args.artifacts_dir)
        # Latch-bank cut (bank_check.py): per-byte gate enable equivalence and the
        # masked write contract. It costs minutes per accepted case, so it runs once
        # on the baseline plus its own bank-specific mutants, not for every case above.
        import bank_check
        bank_dir = args.artifacts_dir / "bank" if args.artifacts_dir else Path(tmp) / "bank"
        bank_dir.mkdir()
        report = bank_check.check_bank(ROOT / "src", bank_dir, lake=lake, yosys=yosys)
        if not report["ok"]:
            raise RuntimeError(f"bank baseline: {report['outcome']}")
        print(f"bank baseline: {report['outcome']} ({report['live_bytes']}/{report['bytes']} "
              f"live bytes, {report['latch_bits']} latch bits)", flush=True)
        if args.mutations:
            for case, rejected, stage, _ in bank_check.run_mutations(
                    snapshot, bank_dir, lake, yosys):
                if not rejected:
                    raise RuntimeError(f"{case}: bank mutant accepted")
                print(f"{case}: rejected by latch-bank {stage.splitlines()[0]}", flush=True)
        # Host command cut (hostcmd_check.py) and core-control cut (corectl_check.py):
        # they discharge the host cut's free st/is_rd and the core queue's free
        # w_cw / frz / CTRL.STICKY leaves. Each runs once on the baseline plus its
        # own mutants, like the bank cut.
        # Host map write decode (hostmap_check.py) and host read path
        # (hostread_check.py) follow the same pattern.
        import corectl_check
        import hostcmd_check
        import hostmap_check
        import hostread_check
        import spipins_check
        import strobes_check
        import glue_check
        import debug_check
        import hostpins_check
        import core_check
        import line_check
        import moves_check
        import units_check
        import stream_check
        import thread_check
        import mem_check
        for name, module, check in (("hostcmd", hostcmd_check, hostcmd_check.check_hostcmd),
                                    ("corectl", corectl_check, corectl_check.check_corectl),
                                    ("hostmap", hostmap_check, hostmap_check.check_hostmap),
                                    ("hostread", hostread_check, hostread_check.check_hostread),
                                    ("spipins", spipins_check, spipins_check.check_spipins),
                                    ("mem", mem_check, mem_check.check_mem),
                                    ("thread", thread_check, thread_check.check_thread),
                                    ("stream", stream_check, stream_check.check_stream),
                                    ("units", units_check, units_check.check_units),
                                    ("moves", moves_check, moves_check.check_moves),
                                    ("line", line_check, line_check.check_line),
                                    ("core", core_check, core_check.check_core),
                                    ("hostpins", hostpins_check, hostpins_check.check_hostpins),
                                    ("debug", debug_check, debug_check.check_debug),
                                    ("glue", glue_check, glue_check.check_glue),
                                    ("strobes", strobes_check, strobes_check.check_strobes)):
            cut_dir = args.artifacts_dir / name if args.artifacts_dir else Path(tmp) / name
            cut_dir.mkdir()
            report = check(ROOT / "src", cut_dir, lake=lake, yosys=yosys)
            if not report["ok"]:
                raise RuntimeError(f"{name} baseline: {report['outcome']}")
            print(f"{name} baseline: {report['outcome']}", flush=True)
            if args.mutations:
                for case, rejected, stage, _ in module.run_mutations(
                        snapshot, cut_dir, lake, yosys):
                    if not rejected:
                        raise RuntimeError(f"{case}: {name} mutant accepted")
                    print(f"{case}: rejected by {name} {stage.splitlines()[0]}", flush=True)
    return 0


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    try:
        raise SystemExit(main())
    except (OSError, KeyError, RuntimeError, ValueError, subprocess.TimeoutExpired) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
