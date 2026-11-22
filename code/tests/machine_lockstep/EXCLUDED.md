# Excluded state-dump keys

None. Every key of the plan's state dump (`BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md`, Interface contract) is produced by
`dump_model.py` (197 keys per cycle) from a direct model attribute or an exact derivation. Mapping notes:

| Key | Python model source | Note |
|---|---|---|
| `uo_out uio_out uio_oe` | return value of `Chip.step` | pins of the cycle just stepped |
| `L{l}.W` | `Line.W` | already `{B1,A2,A1,A0}` in bits 3..0 (tap 0 sets bit 0, tap 1 bits 1 and 3, tap 2 bit 2) |
| `L{l}.*`, `T{t}.*`, `C{c}.*` | same-named attributes | `C{c}.IR` is the instruction register, `FPC` the fetch PC |
| `F FP A Z C N R0..R3` | `flags.F/FP`, `acc.A/Z/C/N/R[k]` | |
| `SH{k}.D CNT LEN MSB`, `CNT{k}.V`, `LF{k}.S`, `P0.PTR D RDY` | `sh[k]`, `cnt[k]`, `lf[k]`, `mem.ptr` | |
| `S{k}.*` | `mem.streams[k]` | `WB`, `PEND`, `CUR` are plain registers |
| `RUN IRQEN CONFLICT MEMHAZ CWOVR` | `chip.ctrl` | |
| `INB INV INVP OUTB OUTV` | `chip.host` | |
| `FREEZE FRZ FRZD MEN MISR CEN EMASK DC` | `chip.*` | |
| `CWA CWV BWP RPL RLV` | `chip.*` | |
| `CWQA CWQD` | `chip.CWQ` tuple `(address, byte)` | |
| `DMEM.sum` | `mem.data` | `sum(mem[i]*(i+1)) mod 2^32`, 2,048 bytes |
| `PMEM{c}.sum` | `cores[c].prog` | same formula over the 64-bit words packed little-endian (2,048 bytes) |

Model state that is deliberately **not** in the dump (internal or non-architectural, so it is not part of the contract):
`Stream.rdword/NB/NV` (`NB/NV` exist only in the v4 replay second buffer; the plan lists no key for them, so a
divergence there surfaces only through `S0.WB/WV/RQ/LD`, `RLV` and the pins), `Host.RX/bitcnt/st/ADDR/TX/WR/RD/rack`
(the SPI link internals; visible through `uo_out` MISO and the register effects), `Chip.HH` (the held host config
write), `cfg_pipe`, the decoded configuration bytes, `rst_hold`, and the `DB` doorbell. Configuration registers are
covered indirectly through behaviour and through the memory sums only if the Lean side also dumps them; they are not
dumped by either side. If triage needs them, add keys on both sides and record the decision.

Memory sums are cached per image (see `dump_model.py`), so they are compared every cycle at negligible cost; no
"every N cycles" mode exists.
