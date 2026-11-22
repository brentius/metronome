import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-! ### Host-command and host-read scalar congruences (`hostRead`'s 30-arm body) -/

theorem absChip_ctrl_run {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.run = m.ctrl.run := hrel.ctrl.run.symm

theorem absChip_ctrl_irqen {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.irqen = m.ctrl.irqen := hrel.ctrl.irqen.symm

theorem absChip_ctrl_conflict {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.conflict = m.ctrl.conflict := hrel.ctrl.conflict.symm

theorem absChip_ctrl_memhaz {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.memhaz = m.ctrl.memhaz := hrel.ctrl.memhaz.symm

theorem absChip_ctrl_cwovr {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.cwovr = m.ctrl.cwovr := hrel.ctrl.cwovr.symm

theorem absChip_ctrl_inb {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.inb = m.ctrl.inb := hrel.ctrl.inb.symm

theorem absChip_ctrl_inv {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.inv = m.ctrl.inv := hrel.ctrl.inv.symm

theorem absChip_ctrl_outb {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.outb = m.ctrl.outb := hrel.ctrl.outb.symm

theorem absChip_ctrl_outv {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).ctrl.outv = m.ctrl.outv := hrel.ctrl.outv.symm

theorem absChip_units_f {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.f = m.units.f := hrel.units.f.symm

theorem absChip_units_a {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.a = m.units.a := hrel.units.a.symm

theorem absChip_units_z {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.z = m.units.z := hrel.units.z.symm

theorem absChip_units_c {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.c = m.units.c := hrel.units.c.symm

theorem absChip_units_n {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).units.n = m.units.n := hrel.units.n.symm

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

/-- The `ERRSUM` arm's stream `starved` scan (pointwise; the whole stream
vectors are not equal because `BufRel` guards `WB`/`NV`). -/
theorem streams_any_starved {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    (absChip s).streams.toList.any (fun x => x.starved) =
      m.streams.toList.any (fun x => x.starved) := by
  rw [vget_toList_any_two, vget_toList_any_two, vget_streams_starved hrel 0,
    vget_streams_starved hrel 1]

/-! ### The `hostRead` congruence -/

/-- **`Machine.hostRead` is a `ChipRel` congruence.**  Every arm of the register
decode reads only `ChipRel` projections (the `ctrl`/`units` scalars, the whole
`dbg` record, the whole line/thread vectors, the core and stream projections),
so the two decodes agree. -/
theorem hostRead_eq (s : State) (m : Machine.State) (hrel : ChipRel s m)
    (cv : Machine.CfgView) (a : Nat) :
    Machine.hostRead (absChip s) cv a = Machine.hostRead m cv a := by
  unfold Machine.hostRead
  by_cases hd : (Machine.Tables.DATA_BASE ≤ a && a <
      Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) = true
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]
    cases hl : Machine.hostLocate a with
    | none => rfl
    | some l =>
      split <;> simp_all only [absChip_ctrl_run, absChip_ctrl_irqen,
        absChip_ctrl_conflict, absChip_ctrl_memhaz, absChip_ctrl_cwovr, absChip_ctrl_inb,
        absChip_ctrl_inv, absChip_ctrl_outb, absChip_ctrl_outv, absChip_units_f,
        absChip_units_a, absChip_units_z, absChip_units_c, absChip_units_n,
        dbg_eq hrel, absChip_lines_eq hrel, absChip_threads_eq hrel,
        streams_any_starved hrel, vget_cores_xt hrel, vget_cores_xv hrel,
        vget_cores_rv hrel, vget_cores_fpc hrel, vget_streams_pos hrel,
        vget_streams_bidx hrel]

/-- **`host_open_regVal`.**  The machine's register-read value is the cut's
`regVal` input (the `Machine.hostRead` congruence at the related address). -/
theorem host_open_regVal (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Bridge.Host.regVal (absChip s) (Machine.cfgView s.cont.cfg) =
      Bridge.Host.regVal m (Machine.cfgView m.cfg) :=
  host_open_regVal_of s m pin hrel hinv hact (fun cv a => hostRead_eq s m hrel cv a)

/-! ### `host_open_quiet`: the pin-timing premise and the field -/

/-- The pin-timing premise of `host_open_quiet`: a byte-completing `SR` edge
never coincides with a host acknowledgement (a data-RAM landing or a pending
register-read acknowledgement).

`SPEC_V2` §9 bounds `SCK` at `clk/16`, so two `SR` edges are at least 16 clock
cycles apart.  Both acknowledgement sources are responses to the preceding
completing byte: a data-RAM landing is the arbiter's service of the read request
issued at the next byte completion (one to two cycles later), and `rack` is set
by the read request of a completing byte and held until the landing.  Neither
can therefore fall in the *next* completing cycle.  This is a pin-timing fact of
the waveform, not a state invariant: `rack`, `hostCmd.wr`/`rd` and the
`s.hostRead.rack` register are set from the pins, and a `clk/2`-rate `SCK` would
satisfy every `ChipRel`/`Inv` state while breaking the coincidence. -/
def host_sck_spacing (s : State) (pin : Machine.PinIn) : Prop :=
  HostCmd.completing (s.hostRead.toHostCmd s.hostCmd.cmd) (hostReadIn s pin).toHostCmd = true →
    s.hostRead.rack = false ∧ hostLand s = false

/-- **`host_open_quiet`.**  In a completing cycle the host link has no write
strobe, no `rack` and no RAM landing (`HostCmd.ackBit` is their `||`). -/
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
