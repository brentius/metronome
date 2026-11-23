# ChipCut configuration bank

Lean 4.35.0, warnings as errors, on `metronome-v4.0` at working-tree base
`b7b4068`. The bank cut models the W+2 write using the arbiter's staged
address, data and write strobe. `src/project.v` instantiates `md2_cfg_cells`
with `CFG_MASK` from `src/md2_map.vh`. The structural bank checker owns the
netlist link and the latch and gate timing abstraction.

## Mask and decoding

`cfgMaskFin` indexes the RTL mask by configuration window offset. It selects
2,112 latch bits in 480 bytes, including 56 partially latched bytes. For
example, offset 17 has mask `0x7F`.

```lean
cfgView_maskImg (c : Machine.Config) :
  Machine.cfgView (maskImg c) = Machine.cfgView c

cfgMask_poly (c : Machine.Config) (i : Fin 2) :
  (maskImg c).poly i.val = c.poly i.val

cfgView_of_masked {d c : Machine.Config} (h : MaskedImage d c) :
  Machine.cfgView d = Machine.cfgView c

cfgView_bankImg (b : Bank.State) (c : Machine.Config)
    (h : ∀ k, Bank.read b k = BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k) :
  Machine.cfgView (bankImg b) = Machine.cfgView c
```

`MaskedImage d c` says each byte of `d` equals the corresponding byte of
`c` ANDed with the RTL mask. The proof handles every LINE, THREAD, STREAM and
OUT field, plus both LFSR polynomials. There are no decoded-field
divergences. Machine writes can retain unused raw bits in the image. The
decode proof is independent of their values.

AMBIG 4 concerns address acceptance. For example, `OUT[8].OE` at address
`0x2188`, offset `0x188`, has mask `0x00` and
`Machine.Config.isCfgAddr 0x2188 = true`. The machine forces its decoded
`oe` to zero for indices 8 through 13. The bank proof establishes
`cfgMaskFin k ≠ 0 → isCfgAddr (LINE_BASE + k.val) = true`. The opposite
implication fails at that address, so the bank proof supplies no port
timing or decode equivalence for AMBIG 4.

## Bank relation and writes

```lean
BankRel (b : Bank.State) (c : Machine.Config) :=
  b.mask = cfgMaskFin ∧
  ∀ k : Fin Bank.BYTES, Bank.read b k =
    BitVec.ofNat 8 (Machine.Util.cfgByte c (Machine.Tables.LINE_BASE + k.val)) &&& b.mask k

bank_decode_of_rel {b : Bank.State} {c : Machine.Config} (h : BankRel b c) :
  Machine.cfgView (bankImg b) = Machine.cfgView c ∧
  ∀ i : Fin 2, (bankImg b).poly i.val = c.poly i.val

premise_bank (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (bank_open_size : m.cfg.img.size = Machine.Util.cfgSize) :
  BankRel (activeStep s pin).bank (Machine.step m pin).cfg
```

`resetState` loads `cfgMaskFin` as the bank mask and clears the latches.
`Bank.step` retains the mask. `premise_bank` uses the mask equality already
stored in `BankRel`, and uses `bank_live_cfg` for address acceptance.
`ExplicitPremises.bankMask` and `ExplicitPremises.bankCfg` can be dropped
from the caller. `trace_cfg_size pins m hsize n` transports the initial
condition `m.cfg.img.size = Machine.Util.cfgSize` through every cycle.
`bank_decode_of_rel` justifies the configuration decoded from `s.cont.cfg`
using the bank output and the existing contents equality in `ChipRel`.

## Reset

`MaskedZero c` means
`∀ k : Fin Bank.BYTES, BitVec.ofNat 8 (bget c.img k.val) &&& cfgMaskFin k = 0`.
`rel_reset cont hzero` requires `hzero : MaskedZero cont.cfg`.
`maskedZero_zero` proves it for `Machine.Config.zero`. The general reset
step accepts `pin.rstn = true → MaskedZero (Machine.cfgNext m.cfg m.cw)`
because the machine can retain the staged image during reset release while
the product clears the bank. An asserted reset clears both. For a trace
from reset, `maskedZero_release_trace pins cont n m hrel` supplies the
release fact from `ChipRel`, an idle write stage and a clear bank while
`rst_q` is low. No per-cycle reset-release assumption is needed in
`trace_refines`.

## Verification

Run from `lean` with Lean 4.35.0 on PATH.

| Command | Exit | Wall | Evidence |
| --- | ---: | ---: | --- |
| `lake build Metronome.ChipCut.Discharge.BankWire` | 0 | 31.59 s | [bankwire_kernel.log](../data/raw/lean_chipcut_bank_v4_20261122/bankwire_kernel.log) |
| `lake build Metronome.ChipCut.Proof` | 0 | 16.33 s | [bank_reset.log](../data/raw/lean_chipcut_bank_v4_20261122/bank_reset.log) |
| `lake build Metronome.ChipCut.Discharge.MemHostCfg Metronome.ChipCut.Discharge.BankWire` | 0 | 15.22 s | [bank_discharge_final.log](../data/raw/lean_chipcut_bank_v4_20261122/bank_discharge_final.log) |
| `lake env lean -DwarningAsError=true ../data/raw/lean_chipcut_bank_v4_20261122/check_bank_wire.lean` | 0 | 3.64 s | [bank_wire_audit.log](../data/raw/lean_chipcut_bank_v4_20261122/bank_wire_audit.log) |
| `lake build Metronome.ChipCut.Assembly` | 1 | 96.81 s | [assembly_bank_boundary.log](../data/raw/lean_chipcut_bank_v4_20261122/assembly_bank_boundary.log) |

The audit records elaborated statements and axiom dependencies. The bank
proofs add no `sorryAx` or native-decision axioms. The general trace theorem
inherits the existing native `bv_decide` axiom from `Mem.reqNext_three`.

The Assembly build stopped at downstream callers of the old API:

- `DbgMapWire.lean:277` applies `bankRel_reset` to arbitrary contents.
- `CoreCombCbs.lean:271` destructures a partial application of `rel_reset`.
  Its broken-bank witness at lines 1131–1135 still applies the old
  nonzero-mask guard to the byte relation.

Source inspection of `Assembly.lean` identifies the remaining integration
points. At lines 922–923, pass only the size fact to `premise_bank`.
At line 942, the general one-step theorem needs the reset-release
implication. Its trace caller can supply `maskedZero_release_trace`.
At line 975, pass the initial `MaskedZero cont.cfg` to `rel_reset`.
The Assembly module itself did not reach elaboration in this run.
