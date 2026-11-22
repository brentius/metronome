"""Translate a restricted, two-state Yosys RTLIL cone to Lean expressions."""


class UnsupportedRTL(ValueError):
    """A circuit outside the supported subset needs an explicit adapter change."""


def require(condition, message):
    if not condition:
        raise UnsupportedRTL(message)


# Combinational cell shapes the translator can express. Anything else reachable
# from a requested register input fails the extraction. `$ge`, `$lt`, `$sub` and
# `$shiftx` are used by the generated configuration-address decode; `$logic_*`
# are Yosys's 1-bit logical forms of `$and`/`$or`.
SUPPORTED = ("$mux", "$and", "$or", "$not", "$eq", "$ne", "$add",
             "$ge", "$lt", "$sub", "$shiftx", "$logic_and", "$logic_or")


class Cone:
    """Bind whole input and register buses, then resolve drivers on demand.

    Each bus is in Yosys little-endian order. Partial bus joins and slices are
    deliberately unsupported. Looking up the full ordered tuple preserves its
    width and bit order.
    """

    def __init__(self, name, module):
        self.name = name
        self.module = module
        self.bound = {}
        self.drivers = {}
        self.registers = {}
        self.claimed = set()
        self.lines = []
        self.resolving = set()
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            params = cell["parameters"]
            pins = {p: tuple(bits) for p, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind in ("$dff", "$adff"):
                width = len(pins["Q"])
                require(len(pins["D"]) == width and int(params["WIDTH"], 2) == width,
                        f"{where}: inconsistent register width")
                require(pins["CLK"] == self.port("clk", "input", 1) and
                        int(params["CLK_POLARITY"], 2) == 1, f"{where}: expected posedge clk")
                if kind == "$adff":
                    require(width == 1 and pins["ARST"] == self.port("rst_s", "input", 1) and
                            int(params["ARST_POLARITY"], 2) == 0 and
                            int(params["ARST_VALUE"], 2) == 0,
                            f"{where}: expected single-bit, active-low async clear")
                self.claim(pins["Q"])
                self.registers[pins["Q"]] = (kind, pins["D"])
                continue
            require(kind in SUPPORTED, f"{where}: unsupported cell")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, params, where)

    def claim(self, bits):
        require(bits and all(isinstance(bit, int) for bit in bits) and len(set(bits)) == len(bits),
                f"{self.name}: invalid driver bus {bits}")
        require(self.claimed.isdisjoint(bits), f"{self.name}: multiple drivers at {bits}")
        self.claimed.update(bits)

    def port(self, name, direction, width):
        port = self.module["ports"][name]
        require(port["direction"] == direction and len(port["bits"]) == width,
                f"{self.name}.{name}: expected {width}-bit {direction}")
        return tuple(port["bits"])

    def input(self, name, width, value):
        bits = self.port(name, "input", width)
        self.claim(bits)
        self.bound[bits] = value

    def register(self, name, width, current, kind):
        net = self.module["netnames"][name]
        bits = tuple(net["bits"])
        require(len(bits) == width and bits in self.registers,
                f"{self.name}.{name}: expected a {width}-bit register")
        require("init" not in net["attributes"], f"{self.name}.{name}: unexpected initial value")
        actual, data = self.registers.pop(bits)
        require(actual == kind, f"{self.name}.{name}: expected {kind}, got {actual}")
        self.bound[bits] = current
        return data

    def next_value(self, data, kind):
        expr = self.expression(data)
        return f"(input.resetN && {expr})" if kind == "$adff" else expr

    def expression(self, bits):
        if bits in self.bound:
            return self.bound[bits]
        if all(bit in ("0", "1") for bit in bits):
            if len(bits) == 1:
                return "true" if bits == ("1",) else "false"
            value = int("".join(reversed(bits)), 2)
            return f"({value} : BitVec {len(bits)})"
        # A sub-bus of one bound whole bus is a truncation of the shifted value.
        # This is the shape Yosys emits for `table[index_bits]` in the generated
        # configuration decode.
        slices = []
        for key, value in self.bound.items():
            if len(bits) < len(key):
                for offset in range(len(key) - len(bits) + 1):
                    if key[offset:offset + len(bits)] == bits:
                        slices.append((key, value, offset))
        if slices:
            require(len(slices) == 1, f"{self.name}: ambiguous sliced bus {bits}")
            _, value, offset = slices[0]
            return (f"(BitVec.truncate {len(bits)} "
                    f"(BitVec.ushiftRight {value} {offset}))")
        if bits not in self.drivers:
            return self._assemble(bits)
        require(bits not in self.resolving, f"{self.name}: combinational loop at {bits}")
        require(bits in self.drivers, f"{self.name}: unsupported, sliced or undriven bus {bits}")
        kind, pins, params, where = self.drivers[bits]
        self.resolving.add(bits)
        a = pins["A"]
        if kind == "$mux":
            b, select = pins["B"], pins["S"]
            require(len(a) == len(b) == len(bits) == int(params["WIDTH"], 2) and len(select) == 1,
                    f"{where}: inconsistent mux widths")
            expr = (f"if {self.expression(select)} then {self.expression(b)} "
                    f"else {self.expression(a)}")
        elif kind in ("$eq", "$ne"):
            b = pins["B"]
            require(len(bits) == 1 and int(params["Y_WIDTH"], 2) == 1 and
                    int(params["A_WIDTH"], 2) == len(a) and
                    int(params["B_WIDTH"], 2) == len(b) and len(a) == len(b),
                    f"{where}: expected a scalar equal-width comparison")
            operator = "==" if kind == "$eq" else "!="
            expr = f"({self.expression(a)} {operator} {self.expression(b)})"
        elif kind in ("$add", "$sub"):
            b = pins["B"]
            require(len(a) == len(b) == len(bits) and
                    int(params["A_WIDTH"], 2) == len(a) and
                    int(params["B_WIDTH"], 2) == len(b) and
                    int(params["Y_WIDTH"], 2) == len(bits),
                    f"{where}: expected an equal-width arithmetic cell")
            operator = "+" if kind == "$add" else "-"
            expr = f"({self.expression(a)} {operator} {self.expression(b)})"
        elif kind in ("$ge", "$lt"):
            b = pins["B"]
            require(len(bits) == 1 and int(params["Y_WIDTH"], 2) == 1 and
                    int(params["A_WIDTH"], 2) == len(a) and
                    int(params["B_WIDTH"], 2) == len(b) and len(a) == len(b),
                    f"{where}: expected a scalar equal-width comparison")
            operator = ">=" if kind == "$ge" else "<"
            expr = f"({self.expression(a)} {operator} {self.expression(b)})"
        elif kind == "$shiftx":
            b = pins["B"]
            require(len(bits) == 1 and int(params["Y_WIDTH"], 2) == 1 and
                    int(params["A_WIDTH"], 2) == len(a) and
                    int(params["B_WIDTH"], 2) == len(b) and len(b) > 0,
                    f"{where}: expected a scalar indexed shift")
            a_width = int(params["A_WIDTH"], 2)
            expr = (f"(((BitVec.ushiftRight {self.expression(a)} "
                    f"({self.expression(b)}).toNat) &&& (1 : BitVec {a_width})) != 0)")
        else:
            require(kind in ("$and", "$logic_and", "$or", "$logic_or", "$not"),
                    f"{where}: unsupported cell")
            require(len(a) == len(bits) == int(params["A_WIDTH"], 2) ==
                    int(params["Y_WIDTH"], 2) == 1, f"{where}: expected scalar logic")
            left = self._bit_bool(a[0])
            if kind == "$not":
                expr = f"!{left}"
            else:
                require(len(pins["B"]) == int(params["B_WIDTH"], 2) == 1,
                        f"{where}: expected scalar logic")
                operator = "&&" if kind in ("$and", "$logic_and") else "||"
                expr = f"{left} {operator} {self._bit_bool(pins['B'][0])}"
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        self.bound[bits] = wire
        self.resolving.remove(bits)
        return wire


    def _bit_bool(self, bit):
        """Express one net bit as a Lean Bool, resolving a slice or a cell."""
        if bit == "0":
            return "false"
        if bit == "1":
            return "true"
        for key, value in self.bound.items():
            if bit in key:
                index = key.index(bit)
                if len(key) == 1:
                    return value
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight {value} "
                        f"{index})) != 0)")
        for output, (kind, _, _, where) in self.drivers.items():
            if bit in output:
                index = output.index(bit)
                if len(output) == 1:
                    expression = self.expression(output)
                    # Scalar logical cells and comparisons produce Bool; a
                    # one-bit mux produces BitVec 1.
                    return f"({expression} != 0)" if kind == "$mux" else expression
                value = self.expression(output)
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight {value} "
                        f"{index})) != 0)")
        raise UnsupportedRTL(f"{self.name}: undriven net bit {bit}")

    def _assemble(self, bits):
        """Assemble a bus that is a permutation of slices, cells and constants."""
        width = len(bits)
        pieces = []
        for index, bit in enumerate(bits):
            value = self._bit_bool(bit)
            pieces.append(
                f"(if {value} then (BitVec.shiftLeft (1 : BitVec {width}) {index}) "
                f"else (0 : BitVec {width}))")
        return "(" + " ||| ".join(pieces) + ")"


class DffCone(Cone):
    """A cone restricted to the combinational logic feeding named registers.

    Unlike `Cone`, this indexes every supported combinational cell in the
    module but never rejects unrelated cells. Reachability is checked by
    `expression`: a requested bus that is neither bound nor driven by a
    supported cell fails the extraction, so an unsupported cell in the cone is
    still an error.
    """

    def __init__(self, name, module):
        self.name = name
        self.module = module
        self.bound = {}
        self.drivers = {}
        self.registers = {}
        self.claimed = set()
        self.lines = []
        self.resolving = set()
        for cell_name, cell in module["cells"].items():
            if cell["type"] not in SUPPORTED:
                continue
            kind = cell["type"]
            params = cell["parameters"]
            pins = {p: tuple(bits) for p, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, params, where)

    def free(self, name, width, value):
        """Bind a net that is not a module port, such as a register output."""
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = tuple(net["bits"])
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        self.claim(bits)
        self.bound[bits] = value
        return bits

    def leaf(self, name, width, value):
        """Bind a driven net as an opaque free input.

        The net may be the output of a supported cell or of a register.  The
        cell (or register) is dropped and the net becomes a free per-cycle
        input, which over-approximates the real cone and is sound for a
        universal safety property.  Partial overlaps with another bound bus or
        with a cell output fail the extraction.
        """
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = tuple(net["bits"])
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        require("init" not in net["attributes"], f"{self.name}.{name}: unexpected initial value")
        require(bits not in self.bound, f"{self.name}.{name}: already bound")
        if bits in self.drivers:
            del self.drivers[bits]
        for output in tuple(self.drivers) + tuple(self.registers) + tuple(self.bound):
            require(not (set(output) & set(bits)),
                    f"{self.name}.{name}: overlaps the bound bus {output}")
        require(set(bits) <= self.claimed or set(bits).isdisjoint(self.claimed),
                f"{self.name}.{name}: partially claimed net")
        self.claimed.difference_update(bits)
        self.bound[bits] = value
        return bits

    def register(self, name, width, current, kind="$dff"):
        """Bind a register output and return its input bus."""
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = tuple(net["bits"])
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        require("init" not in net["attributes"], f"{self.name}.{name}: unexpected initial value")
        matches = [(cell_name, cell) for cell_name, cell in self.module["cells"].items()
                   if cell["type"] in ("$dff", "$adff") and
                   tuple(cell["connections"]["Q"]) == bits]
        require(len(matches) == 1, f"{self.name}.{name}: expected exactly one register driver")
        cell_name, cell = matches[0]
        where = f"{self.name}.{cell_name} ({cell['type']})"
        require(cell["type"] == kind, f"{where}: expected {kind}")
        require(tuple(cell["connections"]["CLK"]) == self.port("clk", "input", 1) and
                int(cell["parameters"]["CLK_POLARITY"], 2) == 1,
                f"{where}: expected posedge clk")
        self.claim(bits)
        self.bound[bits] = current
        return tuple(cell["connections"]["D"])

