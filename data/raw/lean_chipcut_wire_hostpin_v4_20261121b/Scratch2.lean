import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

theorem list_any_len_two {α : Type} (l : List α) (h : l.length = 2) (p : α → Bool) :
    l.any p = (p l[0] || p l[1]) := by
  match l with
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => simp
  | a :: b :: c :: rest => simp at h

theorem toList_any_two {α : Type} (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p v[0] || p v[1]) := by
  have hlen : v.toList.length = 2 := Vector.length_toList
  rw [list_any_len_two v.toList hlen p]
  have h0 : v.toList[0]'(by rw [hlen]; omega) = v[0] := Vector.getElem_toList _
  have h1 : v.toList[1]'(by rw [hlen]; omega) = v[1] := Vector.getElem_toList _
  rw [h0, h1]

theorem vget_toList_any_two {α : Type} [Inhabited α] (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p (Machine.Util.vget v 0) || p (Machine.Util.vget v 1)) := by
  rw [toList_any_two, vget_eq' _ (by decide : 0 < 2), vget_eq' _ (by decide : 1 < 2)]

theorem streams_any_starved {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).streams.toList.any (fun x => x.starved) =
      m.streams.toList.any (fun x => x.starved) := by
  rw [vget_toList_any_two, vget_toList_any_two, vget_streams_starved hrel 0,
    vget_streams_starved hrel 1]

end Metronome.ChipCut.Discharge
