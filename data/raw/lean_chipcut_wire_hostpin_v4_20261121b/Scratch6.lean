import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-- The whole control record is the cut's (`CtrlRel`). -/
theorem ctrl_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl = m.ctrl := by
  have h := hrel.ctrl
  simp only [CtrlRel] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [absChip]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11, ← h12]

/-- The units' `A` register agrees (`UnitsRel`). -/
theorem absChip_units_a {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.a = m.units.a := by
  obtain ⟨_, _, h, _, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `Z` flag agrees. -/
theorem absChip_units_z {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.z = m.units.z := by
  obtain ⟨_, _, _, h, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `C` flag agrees. -/
theorem absChip_units_c {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.c = m.units.c := by
  obtain ⟨_, _, _, _, h, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `N` flag agrees. -/
theorem absChip_units_n {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.n = m.units.n := by
  obtain ⟨_, _, _, _, _, h, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The units' `F` register agrees. -/
theorem absChip_units_f {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.f = m.units.f := by
  obtain ⟨h, _, _, _, _, _, _, _, _, _⟩ := hrel.units
  exact h.symm

/-- The machine's line vector is the cut's. -/
theorem absChip_lines_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).lines = m.lines := by
  apply Vector.ext
  intro k hk
  have hl := (hrel.lines ⟨k, hk⟩).symm
  simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
  have hlk : lineAt s k = s.lines[k] := by
    simpa using lineAt_fin s ⟨k, hk⟩
  rw [hlk] at hl
  exact hl

/-- The machine's thread vector is the cut's. -/
theorem absChip_threads_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).threads = m.threads := by
  apply Vector.ext
  intro k hk
  have hl := (hrel.threads ⟨k, hk⟩).symm
  simp only [absChip, Fin.getElem_fin, Vector.getElem_ofFn] at hl ⊢
  have hlk : threadAt s k = s.threads[k] := by
    simpa using threadAt_fin s ⟨k, hk⟩
  rw [hlk] at hl
  exact hl

/-- `List.any` over a two-element list. -/
theorem list_any_len_two {α : Type} (l : List α) (h : l.length = 2) (p : α → Bool) :
    l.any p = (p l[0] || p l[1]) := by
  match l with
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => simp
  | a :: b :: c :: rest => simp at h

/-- `List.any` over a two-element `Vector`. -/
theorem toList_any_two {α : Type} (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p v[0] || p v[1]) := by
  have hlen : v.toList.length = 2 := Vector.length_toList
  rw [list_any_len_two v.toList hlen p]
  have h0 : v.toList[0]'(by rw [hlen]; omega) = v[0] := Vector.getElem_toList _
  have h1 : v.toList[1]'(by rw [hlen]; omega) = v[1] := Vector.getElem_toList _
  rw [h0, h1]

/-- `List.any` over a two-element `Vector`, in `vget` form. -/
theorem vget_toList_any_two {α : Type} [Inhabited α] (v : Vector α 2) (p : α → Bool) :
    v.toList.any p = (p (Machine.Util.vget v 0) || p (Machine.Util.vget v 1)) := by
  rw [toList_any_two, vget_eq' _ (by decide : 0 < 2), vget_eq' _ (by decide : 1 < 2)]

/-- The `ERRSUM` arm's stream `starved` scan. -/
theorem streams_any_starved {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).streams.toList.any (fun x => x.starved) =
      m.streams.toList.any (fun x => x.starved) := by
  rw [vget_toList_any_two, vget_toList_any_two, vget_streams_starved hrel 0,
    vget_streams_starved hrel 1]

/-- **`Machine.hostRead` is a `ChipRel` congruence.** -/
theorem hostRead_eq (s : State) (m : Machine.State) (hrel : ChipRel s m)
    (cv : Machine.CfgView) (a : Nat) :
    Machine.hostRead (absChip s) cv a = Machine.hostRead m cv a := by
  unfold Machine.hostRead
  by_cases hd : (Machine.Tables.DATA_BASE ≤ a && a <
      Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) = true
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]
    split
    · rfl
    · split <;> simp_all only [ctrl_eq hrel, absChip_units_a hrel, absChip_units_z hrel, absChip_units_c hrel,
        absChip_units_n hrel, absChip_units_f hrel, dbg_eq hrel, absChip_lines_eq hrel,
        absChip_threads_eq hrel, streams_any_starved hrel, vget_lines hrel,
        vget_threads hrel, vget_cores_xt hrel, vget_cores_xv hrel, vget_cores_rv hrel,
        vget_cores_fpc hrel, vget_streams_pos hrel, vget_streams_bidx hrel,
        vget_streams_starved hrel]

/-- **`host_open_regVal`.** -/
theorem host_open_regVal (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg) :=
  host_open_regVal_of s m pin hrel hinv hact (fun cv a => hostRead_eq s m hrel cv a)

/-- The pin-timing premise of `host_open_quiet`. -/
def host_sck_spacing (s : State) (pin : Machine.PinIn) : Prop :=
  HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
    s.hostRead.rack = false ∧ hostLand s = false

/-- **`host_open_quiet`.** -/
theorem host_open_quiet (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hpinv : HostPinInv s) (hspacing : host_sck_spacing s pin) :
    HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
      (s.hostRead.toHostCmd s.hostCmd.cmd).wr = false ∧
        HostCmd.ackBit (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = false := by
  intro h
  refine ⟨quiet_wr s m pin hrel hinv hact hpinv h, ?_⟩
  obtain ⟨hrack, hland⟩ := hspacing h
  unfold HostCmd.ackBit
  rw [show (s.hostRead.toHostCmd s.hostCmd.cmd).rack = s.hostRead.rack from rfl,
    show (hostReadIn s pin).toHostCmd.hland = hostLand s from rfl, hrack, hland]
  rfl

end Metronome.ChipCut.Discharge
