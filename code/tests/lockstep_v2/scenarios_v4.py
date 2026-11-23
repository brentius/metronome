"""Exercise the v4 paths through the chip's SPI host link and pins."""
import binascii
import os
import sys
from pathlib import Path

from scenarios import HM, I, Scn, lut, reg_addr
from check_uart_peer import TRAINING


def address_for(address):
    return [I(("IMM", "CW.AL"), imm=address & 255),
            I(("IMM", "CW.AH"), imm=address >> 8)]


def config_write():
    s = Scn("v4_config_write")
    s.reset()
    s.blk("LINE", 0, INC=0, MOD=8)
    inc, _ = reg_addr("LINE", 0, "INC")
    mask, _ = reg_addr("DBG", 0, "EMASK")
    s.program(0, address_for(inc) + [
        I(("IMM", "CW.D"), imm=1),
        I(("IMM", "CW.D"), imm=0),
        I(("IMM", "CW.D"), imm=0x55),  # third consecutive write must be dropped
        I(),
    ] + address_for(mask) + [
        I(("IMM", "CW.D"), imm=0x25),
        I(("ZERO", "T.STOP"), pause=1),
    ])
    s.thread(0, trig="ALWAYS")
    s.blk("CTRL", IRQEN=2, RUN=1)
    s.idle(40)
    s.read(HM["CTRL_BASE"], 9)
    s.read(mask, 2)
    s.blk("CTRL", STICKY=4)
    s.blk("LRT", 0, CTL=1)
    s.idle(113)
    s.read(HM["LRT_BASE"], 2)
    s.read(HM["CTRL_BASE"], 9)
    return s


def replay():
    s = Scn("v4_replay")
    s.reset()
    words = [(24 << 13) | 1, (12 << 13), (17 << 13) | 1, (21 << 13)]
    s.data(0x80, b"".join(word.to_bytes(4, "little") for word in words))
    s.blk("STREAM", 0, MODE=1, START=0x80, LEN=16)
    s.blk("LINE", 0, PINS=0x10)
    s.blk("OUT", 8, BIND=0b1100, LUT=lut(lambda index: (index >> 2) & 1))
    s.blk("DBG", EMASK=1, RLV=0)
    s.blk("SRT", 0, CTL=1)
    s.blk("DBG", ECTL=2)
    s.uio = 1  # Replay masks the physical pad even when it disagrees.
    s.idle(110)
    s.read(HM["DBG_BASE"], 0x14)
    s.read(HM["SRT_BASE"], 3)
    s.blk("DBG", DBG=1)
    s.blk("DBG", RLV=1)
    s.blk("DBG", DBG=0)
    s.idle(12)
    s.blk("DBG", ECTL=0)
    s.blk("SRT", 0, CTL=1)
    s.idle(8)
    return s


def stage1():
    """Load real stage-1 firmware and drive an 8N1 stream at 80 clocks/bit."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "host2"))
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from transcribe.fw_stage1 import RES, source

    s = Scn("v4_stage1")
    pin, clocks_per_bit = 5, 80
    s.uio = 1 << pin
    s.reset()
    s.blk("LINE", 0, PINS=(pin << 4) | pin)
    s.blk("OUT", 8, BIND=0b1100, LUT=lut(lambda index: (index >> 2) & 1))
    for address, data, _ in host_writes(assemble_text(source(pin, replay_capture=True))):
        s.write(address, data)
    s.idle(100)
    for value in (0x55, 0x67, 0xD3, 0xAE) * 4:
        for level in [0] + [(value >> bit) & 1 for bit in range(8)] + [1]:
            s.uio = level << pin
            s.idle(clocks_per_bit)
    replay_edges = []
    previous = 1

    def observe(tick, outs):
        nonlocal previous
        pin_value = (outs[0] >> 2) & 1
        if pin_value != previous:
            replay_edges.append((tick, pin_value))
        previous = pin_value
        return 1 << pin

    # Wait for the real input to settle, then observe the dedicated output.
    s.uio = 1 << pin
    s.idle(12)
    s.uio = observe
    s.idle(68_000)
    s.read(HM["DATA_BASE"] + RES, 6)
    s.read(HM["CTRL_BASE"], 9)

    def check(model):
        result = model.mem.data[RES:RES+6]
        assert tuple(result[:4]) == (1, 1, 0, 10), list(result)
        assert (model.lines[0].INC, model.lines[0].MOD) == (32, clocks_per_bit * 32)
        assert not model.contract_violations
        assert not (model.ctrl.CWOVR or model.ctrl.CONFLICT or model.ctrl.MEMHAZ)
        words = [int.from_bytes(model.mem.data[offset:offset+4], "little")
                 for offset in range(0, 4 * 64, 4)]
        assert not model.mem.streams[0].STARVED
        assert len(replay_edges) == len(words)
        assert [level for _, level in replay_edges] == [(word >> pin) & 1 for word in words]
        intervals = [right[0] - left[0] for left, right in zip(replay_edges, replay_edges[1:])]
        assert intervals == [word >> 13 for word in words[1:]]

    s.check = check
    return s


def stage2(reply=None):
    """Infer UART framing and transmit complete training frames or a fresh byte."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "host2"))
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from transcribe.fw_stage1 import FRAME_RES, RES, source

    s = Scn("v4_stage2" if reply is None else "v4_uart_reply")
    pin, bit_period = 5, 24
    payload = TRAINING
    def frame(word):
        return [0] + [(word >> bit) & 1 for bit in range(8)] + [1]

    s.uio = 1 << pin
    s.reset()
    for address, data, _ in host_writes(assemble_text(source(pin, framing=True, transmit=True, reply=reply))):
        s.write(address, data)
    s.idle(100)
    training_file = os.environ.get("LOCKSTEP_UART_TRAINING") if reply is not None else None
    if training_file:
        training = Path(training_file).read_bytes()
        if set(training) != {0, 1}:
            raise ValueError("training trace must contain byte values 0 and 1")
        for level in training:
            s.uio = level << pin
            s.idle(1)
    else:
        for word in payload:
            for level in frame(word):
                s.uio = level << pin
                s.idle(bit_period)

    tx = []

    def observe(_tick, outputs):
        tx.append((outputs[0] >> 2) & 1)
        return 1 << pin

    s.uio = observe
    s.idle(65_000)
    s.read(HM["DATA_BASE"] + RES, 11)
    s.read(HM["CTRL_BASE"], 9)

    def check(model):
        result = model.mem.data[RES:RES+4]
        assert tuple(result[:2]) == (1, 1)
        learned_period = int.from_bytes(result[2:], "little")
        # The peer inserts a two-cycle inter-frame gap, so the mean of the
        # captured intervals can differ slightly from its programmed period.
        nominal_period = bit_period * 32
        assert abs(learned_period - nominal_period) <= (nominal_period // 100 if training_file else 0)
        status, width, parity, count, stops = model.mem.data[FRAME_RES:FRAME_RES+5]
        assert (status, width, parity, stops) == (1, 8, 0, 1)
        assert 4 <= count < len(payload)
        assert model.host.OUTV and model.host.OUTB == 1
        assert not any(stream.STARVED for stream in model.mem.streams)
        assert not any(thread.LATE or thread.OVR for thread in model.threads)
        assert not (model.ctrl.CWOVR or model.ctrl.CONFLICT or model.ctrl.MEMHAZ or model.contract_violations)
        idle = tx.index(1)
        start = tx.index(0, idle + 1)
        words = payload[:count] if reply is None else (reply,)
        expected = [level for word in words for level in frame(word)]
        assert tx[start + bit_period // 2:start + bit_period * len(expected):bit_period] == expected
        assert set(tx[start + bit_period * len(expected):]) == {1}

    s.check = check
    return s


def crc_reply():
    """Load decoded codewords over SPI, then check the new reply on O8."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "host2"))
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from transcribe.fw_crc import CLOCKS_PER_BIT, REPLY, source

    def codeword(data):
        return data + binascii.crc_hqx(data, 0xFFFF).to_bytes(2, "big")

    s = Scn("v4_crc_reply")
    s.reset()
    reply = b"new!"
    frames = [codeword(data) for data in (b"test", b"tset", b"mock")]
    expected = codeword(reply)
    for address, data, _ in host_writes(assemble_text(source(frames, reply))):
        s.write(address, data)

    tx = []

    def observe(_tick, outputs):
        tx.append((outputs[0] >> 2) & 1)
        return 0

    s.uio = observe
    s.idle(13_000)
    s.read(HM["DATA_BASE"] + REPLY, len(expected))
    s.read(HM["CTRL_BASE"], 9)

    def check(model):
        assert model.host.OUTV and model.host.OUTB == 2
        assert bytes(model.mem.data[REPLY:REPLY + len(expected)]) == expected
        assert not any(thread.LATE or thread.OVR for thread in model.threads)
        assert not (model.ctrl.CWOVR or model.ctrl.CONFLICT or model.ctrl.MEMHAZ or model.contract_violations)
        cursor = tx.index(1) + 1
        for byte in expected:
            start = tx.index(0, cursor)
            center = start + CLOCKS_PER_BIT // 2
            stop = center + 9 * CLOCKS_PER_BIT
            expected_bits = [0] + [(byte >> bit) & 1 for bit in range(8)] + [1]
            assert tx[center:stop + 1:CLOCKS_PER_BIT] == expected_bits
            cursor = stop + 1
        assert set(tx[cursor:]) == {1}

    s.check = check
    return s


DIRECTED_V4 = {
    "v4_config_write": config_write, "v4_replay": replay, "v4_stage1": stage1,
    "v4_stage2": stage2, "v4_uart_reply": lambda: stage2(reply=0x42), "v4_crc_reply": crc_reply,
}
