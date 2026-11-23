/-
# ChipCut: the whole-chip product of the verification cuts (item 4Q)

Entry point for the whole-chip refinement:

* `Metronome.ChipCut.State` — the product of every cut state and the memory/
  configuration contents;
* `Metronome.ChipCut.Wire` — the chip-top wiring of every cut input from the
  cut output functions;
* `Metronome.ChipCut.Step` — `step : State -> PinIn -> State`;
* `Metronome.ChipCut.Proof` — `absChip`, `ChipRel`, `Inv`, `SideConds`,
  `Premises`, `chip_step_refines`, `inv_reset`/`inv_step` and `trace_refines`.

See `CHIPCUT_NOTES.md` for the premise list and the RTL → cut → machine link.
-/

import Metronome.ChipCut.Proof
