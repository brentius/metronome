/-
# Statement-match check against `Assembly.OpenWiring`

`Assembly.lean` is the assembler's file (not this module's to edit).  Each of the
five `OpenWiring` fields must be *definitionally* the statement proved here, so
that the assembler can pass the theorem for the field.  This file checks that by
`rfl`: the field's proposition (as projected from an arbitrary `OpenWiring`) and
the theorem's proposition are the same term.

Run:  lake env lean .../check_assembly_fields.lean
-/
import Metronome.ChipCut.Assembly
import Metronome.ChipCut.Discharge.MovePayloadWire

set_option autoImplicit false

namespace Metronome.ChipCut.Discharge.MovePayloadWire.Check

open Metronome
open Metronome.ChipCut
open Metronome.ChipCut.Discharge

variable (s : State) (m : Machine.State) (pin : Machine.PinIn)

/-- The `FLAGS`/`P0`/`CW` table row is the `unitFlagPQ` field, verbatim. -/
example (hT : MoveFabric.DstPayloadTable) (hF : DstFlagP0CwTable)
    (ho : OpenWiring s m pin) :
    OpenWiring.unitFlagPQ ho = MovePayloadWire.unitFlagPQ hT hF := rfl

/-- `p0Move` is the field, verbatim. -/
example (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : MoveFabric.DstPayloadTable) (hF : DstFlagP0CwTable)
    (ho : OpenWiring s m pin) :
    OpenWiring.p0Move ho = MovePayloadWire.p0Move s m pin hrel hinv hJGTab hbus hgrp hkind hT hF :=
  rfl

/-- `cwMove` is the field, verbatim. -/
example (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hF : DstFlagP0CwTable) (ho : OpenWiring s m pin) :
    OpenWiring.cwMove ho = MovePayloadWire.cwMove s m pin hrel hinv hJGTab hbus hgrp hkind hF :=
  rfl

/-- `ctrlMemhaz` is the field, verbatim. -/
example (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hsrc : Bridge.Glue.SrcTable) (hT : MoveFabric.DstPayloadTable)
    (hF : DstFlagP0CwTable)
    (hserved : (machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin))
    (ho : OpenWiring s m pin) :
    OpenWiring.ctrlMemhaz ho =
      MovePayloadWire.ctrlMemhaz s m pin hrel hinv hJGTab hbus hgrp hkind hsrc hT hF hserved :=
  rfl

/-- `ctrlCwovr` is the field, verbatim. -/
example (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hF : DstFlagP0CwTable) (ho : OpenWiring s m pin) :
    OpenWiring.ctrlCwovr ho = MovePayloadWire.ctrlCwovr s m pin hrel hinv hJGTab hbus hgrp hkind hF :=
  rfl

/-- The `hserved` argument of `ctrlMemhaz` is `CoreCombWire.p0_open_served`
(an already-proved theorem, not a new hypothesis): the `Glue`-local arbiter is
the `p0_open_served` one definitionally. -/
example (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    (machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin) :=
  p0_open_served s m pin hrel hinv hmode

end Metronome.ChipCut.Discharge.MovePayloadWire.Check
