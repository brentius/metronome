import Metronome.ChipCut.Discharge.MovePayloadWire

/-! # Axiom report for `Metronome.ChipCut.Discharge.MovePayloadWire`

Every public theorem of the module: `#print axioms` must show no `sorryAx`, no
`Lean.trustCompiler`, no `native_decide` axiom.  The only non-core axioms
permitted are `bv_decide` certificates of the kind `Bridge`/`MoveFabric` already
use (here: none are expected, since this module uses `decide` only on closed
`BitVec`/`Nat` computations).
-/
open Metronome.ChipCut.Discharge.MovePayloadWire

#print axioms unitFlagPQ
#print axioms hPQ_p0
#print axioms mhcP0Move_isSome
#print axioms p0Move
#print axioms hPQ_cw
#print axioms cwWord_code
#print axioms cwWord_data
#print axioms cwWord_we
#print axioms cwMove
#print axioms p0Next_haz
#print axioms pending_req
#print axioms isPD_class
#print axioms srcOpOf_pD_all
#print axioms srcPD_iff
#print axioms pdSlot
#print axioms pdScan
#print axioms readsOf_any
#print axioms ctrlInTrue_memhaz_unfold
#print axioms p0Haz_eq
#print axioms ctrlMemhaz
#print axioms step_coreIssue
#print axioms arbIn_coreIssue
#print axioms accept_not
#print axioms mhcDrains
#print axioms cwNext_coreDrain_val
#print axioms mhcDrains_eq
#print axioms mhcCwo_ovr_eq
#print axioms ctrlCwovr
#print axioms DstFlagP0CwTable
