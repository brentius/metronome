import Metronome.Machine

set_option autoImplicit false

open Metronome

#print Array.any
#print Array.all
#check @Array.any_eq_true
#check @Array.all_eq_true
#check @Array.mem_toList
#check @Array.mem_iff_get
#check @Array.getElem_mem_toList
#check @Array.any_toList
#check @Array.all_toList
#check @List.any_eq_true
#check @List.all_eq_true
#check @List.mem_iff_get
#check @List.get_mem
#check @Array.toList_any
