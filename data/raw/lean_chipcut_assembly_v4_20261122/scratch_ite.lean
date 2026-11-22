import Metronome.ChipCut.Assembly

#check @ite_eq_left
#check @ite_eq_right
#check @ite_eq_left_iff
#check @ite_eq_right_iff
#check @if_pos
#check @ite_true
#check @ite_false

example (c : Bool) (a b : Nat) (h : c = true) : (if c then a else b) = a := by
  rw [if_pos h]

example (c : Bool) (a b : Nat) (h : c = true) : (if c then a else b) = a := by
  rw [ite_eq_left.mpr h]

example (c : Bool) (a b : Nat) (h : c = false) : (if c then a else b) = b := by
  rw [ite_eq_right.mpr h]
