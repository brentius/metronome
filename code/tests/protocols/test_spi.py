"""spi_controller.mas on the reference model: loaded over pin-level SPI, a mode-0 slave model answers on MISO, and
the master's SCK/MOSI/CS_N are decoded by the independent spi_decode. "verified in simulation against the reference model"."""
import proto_scenarios as ps
from protocols import spi_decode


def test_spi_controller_model():
    s = ps.spi_controller()
    tr = s.model_trace
    uo = [t[3][0] for t in tr]
    sck, mosi, cs = ([u >> b & 1 for u in uo] for b in (2, 3, 4))
    miso = [t[0] >> 3 & 1 for t in tr]
    txs = spi_decode(sck, mosi, miso, cs, mode=0)
    xfers = [t for t in txs if len(t[0]) == 1]
    assert [t[0][0] for t in xfers] == [0xA5, 0x3C, 0xFF]       # MOSI as sent by the host
    assert [t[1][0] for t in xfers] == [0x5A, 0xC3, 0x81]       # MISO as sampled at the SCK rising edges
    # host-visible result: HOSTOUT after each transfer, read over SPI pins from the model trace
    class T(list):
        pass
    trace = [(i, 0, 0, None, t[3]) for i, t in enumerate(tr)]
    got = []
    for st, out in s.out_reads:
        v = lambda a: sum(((trace[a + k * 16 + 2][4][0] & 1) << (7 - k)) for k in range(8))
        got.append(v(out) if v(st) & 2 else None)
    assert got == [0x5A, 0xC3, 0x81], got
    rises = [t for t in range(1, len(sck)) if sck[t] and not sck[t - 1]]
    pitch = {b - a for a, b in zip(rises, rises[1:]) if b - a < 100}
    assert pitch == {60}, pitch
    first_fall = next(t for t in range(1, len(cs)) if not cs[t] and cs[t - 1])
    first_rise = next(t for t in rises if t > first_fall)
    print(f"spi_controller: 3 bytes ok, SCK period {pitch} clocks, CS_N low to first SCK rise {first_rise - first_fall} "
          f"clocks (verified in simulation against the reference model)")
