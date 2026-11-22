import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
open Metronome

#check @Vector.toList_ofFn
#check @Vector.toList_toArray
#check @Vector.toList_mk
#check @Vector.toArray_ofFn
#check @Vector.getElem?_toList
#check @List.ofFn_succ
#check @List.any_cons
#check @Vector.toList_length
#check @List.any_congr
#check @Vector.toList_empty
#check @Vector.toList_push
#check @Vector.length_toList
#check @Array.toList_foldl
#check @Vector.toList_eq_nil
#check @Vector.getElem_toList
#check @Vector.toList_getElem?

example (a b : Nat) : (Vector.toList ⟨#[a, b], rfl⟩ : List Nat).any (· > 0) = (a > 0 || b > 0) := by decide

namespace Metronome.ChipCut.Discharge
example (f : Fin 2 → Bool) : (Vector.ofFn f).toList.any id = (f 0 || f 1) := by decide
end Metronome.ChipCut.Discharge
