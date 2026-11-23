import Metronome.Bridge.Stream

/-!
# Bridge: the replay buffer `WB` / `WV` / `NB` / `NV` under a strong relation

`Metronome/Bridge/Stream.lean` bridges the ten scalar stream registers of
`Metronome.Stream` to `Metronome.Machine.Stream` under `AbsRelB`, but relates the
two-deep replay buffer only through `BufRel`, which guards `WB` by `WV` and `NB`
by `NV`.  That leaves three corners of the §13.2 buffer open
(`BRIDGE_UNITS_STREAM_NOTES.md`, "The replay buffer relation"):

1. a frozen landing with `WV = 0`: the cut parks the landing word in `NB`
   (`nbNext`'s frozen branch) and the machine in `WB`
   (`Machine/Stream.lean`'s `mode == 3 && s.wv` test, AMBIG(11));
2. `apply ∧ LD` in one cycle: the machine's next landing word is its `NB`,
   the cut's stale `NB` is unconstrained by `BufRel`;
3. a landing into the second slot in the first unfrozen cycle after a freeze
   (`LD ∧ occupied ∧ FRZD`): the cut's landing word is `NB`, the machine's is
   its pre-state `NB`/`WB` slot.

`BufRelX` below is the strong relation that closes 2 and 3 and turns 1 into the
single named hypothesis `LD → !FRZD` of the unfrozen step:

* the *whole* replay buffer agrees (`WB`, `WV`, `NB`, `NV`), not only its valid
  part — under the chip's freeze discipline the raw slots never diverge, so the
  stale-slot clauses are not needed and the capture-mode `PV → WB` clause of
  `WIRE_CORECOMB_NOTES.md` §8 holds outright;
* for `CAP = 0` only `WB`, `WV`, `NB` are asked, because the cut's `NV` is inert
  and the machine clears it on a rewind (witness (b') of
  `BRIDGE_UNITS_STREAM_NOTES.md`, AMBIG(14)).

The step lemmas take the same inputs and side conditions as
`abs_step_unfrozen` / `abs_step_frozen` / `abs_step_frozen_rewind`, plus
`LD → !FRZD` for the unfrozen step (`hfresh`): a landing that reads a *buffer
slot* instead of the RAM output is the one place where the two readings can
differ, and it can only happen in an unfrozen cycle that follows a frozen one
with `LD = 1` — which `LD → FRZD` (the frozen bridge's `hland`) excludes.  The
predecessor fact is proved: the first frozen cycle of a run has `FRZD = 0` with
`LD → FRZD`, so `LD = 0` there (`frozen_ld_false`), and `ld_frozen_hold` keeps
it clear through the run, so the first unfrozen cycle has `FRZD = 1` with
`LD = 0` and `hfresh` is vacuous.

Corner 1 is a genuine reading difference at a reachable state: the ending of
`frozen_landing_witness` is a three-cycle trace from reset (request a replay
read, serve it, freeze) after which the cut holds the word in `NB` and the
machine in `WB`, so `BufRelX` fails.  That is why `hland` is kept as the named
hypothesis (it is the discharge's `StreamWire.landing`), and why the frozen
lemma below needs it.

`StreamWire.landing` is in fact *false* (`streamWire_landing_false` in the
discharge): a host freeze one cycle after a served read gives `LD = 1` with
`FRZD = 0`, the landing exception of §12.3.  The last section therefore *covers*
that cycle: `abs_step_frozen_landing` is the exact-state bridge for the cases
where both readings write the same slot (transmit, or replay with `WV = 1`),
`bufRelX_step_frozen_landing` is the strong buffer relation there, and
`frozen_rel_landing_flush` / `frozen_rel_landing_rewind_flush` preserve the
guarded `BufRel` in **all** modes under `LD → (transmit ∨ replay)` (the chip's
`ldModeInv`) and the replay well-formedness `ShapeOK : WV = 0 → NV = 0`.  So the
discharge can drop `StreamWire.landing`, keeping only `ldModeInv` (which it
already has) and a shape premise.  The one remaining case — a frozen landing
into an empty replay head with a valid second slot — is genuinely divergent and
is witnessed (`frozen_landing_invalid_nv_disagrees`).

The four …_flush theorems re-prove the frozen bridges without the
`flush = false` side condition — the exact-state forms and the *relational* forms
the discharge uses — because the cut's `Stream.fl` gates the flush by `!FRZ` and
the machine gates `flushReq` by `!frozen` (`Machine/Stream.lean` 151/154): a
frozen cycle ignores a flush request in both readings, so the discharge's
`StreamWire.hostctl` flush field is not needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.Bridge

open Metronome

namespace StreamBuf

open StreamB

/-! ## The strong buffer relation -/

/-- The replay buffer of the cut and the machine agree slot by slot: `WB`, `WV`
and `NB` always, and `NV` for a `CAP = 1` stream (a `CAP = 0` stream has no
second slot in the cut and the machine clears `NV` on a rewind, AMBIG(14)). -/
def BufRelX (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  s.wb = m.wb ∧ s.wv = m.wv ∧ s.nb = m.nb ∧ (cap = true → s.nv = m.nv)

/-- The first buffer word agrees. -/
theorem BufRelX.wb_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) : s.wb = m.wb := h.1

/-- The first validity bit agrees. -/
theorem BufRelX.wv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) : s.wv = m.wv := h.2.1

/-- The second buffer word agrees. -/
theorem BufRelX.nb_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) : s.nb = m.nb := h.2.2.1

/-- The second validity bit agrees for a `CAP = 1` stream. -/
theorem BufRelX.nv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) (hc : cap = true) : s.nv = m.nv := h.2.2.2 hc

/-- **The capture clause** of `WIRE_CORECOMB_NOTES.md` §8: while a record waits
for its RAM write (`PV`), `WB` agrees — for every mode, since the whole slot
agrees. -/
theorem BufRelX.capture_wb {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) (_hpv : s.pv = true) : s.wb = m.wb := h.wb_eq

/-- `BufRelX` implies `BufRel`; the read-handshake clause `¬ (RQ ∧ LD)` of
`BufRel` is orthogonal to the buffers (it is preserved by the chip's
`stream_mode_quiet`, `WIRE_CORECOMB_NOTES.md` §11) and is taken separately. -/
theorem BufRelX.toBufRel {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRelX cap s m) (hno : ¬ (s.rq = true ∧ s.ld = true)) : BufRel cap s m := by
  obtain ⟨hwb, hwv, hnb, hnv⟩ := h
  refine ⟨?_, ?_, hno⟩
  · intro hc
    exact ⟨hwv, hnv hc, fun _ => hwb, fun _ => hnb⟩
  · intro _
    exact ⟨hwb, hwv, hnb⟩

/-- At the two reset states the strong buffer relation holds (both are the zero
record). -/
theorem bufRelX_reset (cap : Bool) :
    BufRelX cap Stream.resetState (default : Machine.StreamSt) :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- The reset form against the abstraction map. -/
theorem bufRelX_abs_reset (cap : Bool) :
    BufRelX cap Stream.resetState (abs Stream.resetState) :=
  bufRelX_reset cap

/-! ## The unfrozen step

`frz = false`, `resetN = true`, the same `AbsRelB` as `abs_step_unfrozen`, and
`hfresh : LD → !FRZD`: a landing takes the RAM output, not a buffer slot. -/

set_option maxHeartbeats 1600000 in
/-- `WB` in the two readings, unfrozen cycle. -/
theorem wb_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).wb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).wb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · have hcap : cap = true := (Stream.rpl_facts cap i hrpl).1
    have hnveq : s.nv = m.nv := hnv hcap
    have hfzd : s.ld = true → i.frzd = false := hfresh
    ssimp
    simp only [hwb, hwv, hnb, hnveq, hld, hreset, hfrz, hm, hend, bv_id, hfzd]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hcp : i.capPush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hpv' : m.pv = true <;>
      by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hfz : i.frzd = true <;> by_cases hcv' : s.cv = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hb7 : s.bidx.toNat = 7 <;> smash

set_option maxHeartbeats 1600000 in
/-- `WV` in the two readings, unfrozen cycle. -/
theorem wv_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).wv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).wv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  have hlane : (BitVec.truncate 2 s.ba == 3) = (m.ba.toNat % 4 == 3) :=
    lane_three s m hba
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · have hcap : cap = true := (Stream.rpl_facts cap i hrpl).1
    have hnveq : s.nv = m.nv := hnv hcap
    ssimp
    simp only [hwb, hwv, hnb, hnveq, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id,
      advT_eq cap s i m htx hend, hlast, hlane]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hfz : i.frzd = true <;> by_cases hcv' : s.cv = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hb7 : s.bidx.toNat = 7 <;> smash

set_option maxHeartbeats 1600000 in
/-- `NB` in the two readings, unfrozen cycle. -/
theorem nb_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).nb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).nb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · have hcap : cap = true := (Stream.rpl_facts cap i hrpl).1
    have hnveq : s.nv = m.nv := hnv hcap
    ssimp
    simp only [hwb, hwv, hnb, hnveq, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hcp : i.capPush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hpv' : m.pv = true <;>
      by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hfz : i.frzd = true <;> by_cases hcv' : s.cv = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hb7 : s.bidx.toNat = 7 <;> smash

set_option maxHeartbeats 1600000 in
/-- `NV` in the two readings, unfrozen `CAP = 1` cycle.  (With `CAP = 0` the
cut's `NV` is inert and a rewind leaves the machine's clear — witness (b').) -/
theorem nv_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false) (hcap : cap = true)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).nv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).nv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hnveq : s.nv = m.nv := hnv hcap
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwb, hwv, hnb, hnveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwb, hwv, hnb, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash

/-- **`BufRelX` is preserved by an unfrozen stream step, in every mode.**  The
premises are those of `abs_step_unfrozen` (`resetN = true`, `frz = false`,
`AbsRelB`) plus `hfresh : LD → !FRZD`. -/
theorem bufRelX_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false) :=
  ⟨wb_step_unfrozen cap s i m hreset hfrz hfresh h hb,
   wv_step_unfrozen cap s i m hreset hfrz hfresh h hb,
   nb_step_unfrozen cap s i m hreset hfrz hfresh h hb,
   fun hc => nv_step_unfrozen cap s i m hreset hfrz hfresh hc h hb⟩

/-! ## The frozen step

`frz = true` and `LD → FRZD` (the frozen bridge's `hland`): the landing
exception is off, so both readings hold the whole buffer and `BufRelX` is
preserved *reflexively* — no flush, move, rewind or `FRZD` condition is needed
beyond `hland`. -/

set_option maxHeartbeats 1600000 in
/-- `WB` in the two readings, frozen cycle. -/
theorem wb_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).wb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true).wb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hln : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · rw [hland hl]; simp
    · simp [hl]
  ssimp
  simp only [hwb, hwv, hnb, hld, hreset, hfrz, hln, cond_eq_ite, bv_id]
  by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;> smash

set_option maxHeartbeats 1600000 in
/-- `WV` in the two readings, frozen cycle. -/
theorem wv_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).wv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true).wv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hln : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · rw [hland hl]; simp
    · simp [hl]
  ssimp
  simp only [hwb, hwv, hnb, hld, hreset, hfrz, hln, cond_eq_ite, bv_id]
  by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;> smash

set_option maxHeartbeats 1600000 in
/-- `NB` in the two readings, frozen cycle. -/
theorem nb_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).nb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true).nb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hln : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · rw [hland hl]; simp
    · simp [hl]
  ssimp
  simp only [hwb, hwv, hnb, hld, hreset, hfrz, hln, cond_eq_ite, bv_id]
  by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;> smash

set_option maxHeartbeats 1600000 in
/-- `NV` in the two readings, frozen `CAP = 1` cycle. -/
theorem nv_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true) (hcap : cap = true)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    (Stream.step cap s i).nv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true).nv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hnveq : s.nv = m.nv := hnv hcap
  have hln : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · rw [hland hl]; simp
    · simp [hl]
  ssimp
  simp only [hwb, hwv, hnb, hnveq, hld, hreset, hfrz, hln, cond_eq_ite, bv_id, hcap]
  by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;> smash

/-- **`BufRelX` is preserved by a frozen stream step**, with or without a host
rewind, for *every* flush input.  The only premise on the landing is the frozen
bridge's `hland : LD → FRZD`; `hreset` and `frz = true` are its other inputs. -/
theorem bufRelX_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true) (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true) :=
  ⟨wb_step_frozen cap s i m hreset hfrz hland h hb,
   wv_step_frozen cap s i m hreset hfrz hland h hb,
   nb_step_frozen cap s i m hreset hfrz hland h hb,
   fun hc => nv_step_frozen cap s i m hreset hfrz hland hc h hb⟩

/-- **`LD` is clear after a frozen cycle whose landing test is off.**  A frozen
run starts with `FRZD = 0` (the previous cycle was unfrozen), so `LD → FRZD`
forces `LD = 0` there, and the frozen cycle propagates it; the first unfrozen
cycle after the run therefore has `FRZD = 1` with `LD = 0`, making the unfrozen
step's `hfresh` vacuous. -/
theorem frozen_ld_false (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hfzd : i.frzd = false)
    (hland : s.ld = true → i.frzd = true) : (Stream.step cap s i).ld = false := by
  have hs : s.ld = false := by
    by_cases hl : s.ld = true
    · rw [hland hl] at hfzd
      exact Bool.noConfusion hfzd
    · simpa using hl
  simp only [Stream.step, Stream.ldNext, hs, hreset, hfrz, cond_eq_ite]
  by_cases hrew : i.rewind = true <;> simp [hrew]

/-! ## The frozen state bridges with a flush input

The cut's `Stream.fl` gates the flush by `!FRZ` (`Stream.lean` 287) and the
machine gates `flushReq` by `!frozen` (`Machine/Stream.lean` 151/154), so a
frozen cycle ignores a flush in both readings.  These restate
`abs_step_frozen` / `abs_step_frozen_rewind` without `flush = false`. -/

set_option maxHeartbeats 1600000 in
/-- **Frozen-cycle register-step bridge, flushed input allowed.**  Identical to
`abs_step_frozen` but the side condition no longer fixes `flush`. -/
theorem abs_step_frozen_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧
      i.replayLate = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true := by
  have hcon : ¬ (s.ld = true ∧ i.frzd = false) := by
    rintro ⟨h1, h2⟩
    rw [hland h1] at h2
    exact Bool.noConfusion h2
  obtain ⟨ha, hrx, hce, hla⟩ := hside
  unfold Stream.step Machine.streamNext
  simp only [abs, absIn, cfgOf, cond_eq_ite, hreset, hfrz, hrew, ha, hrx, hce, hla,
    Stream.posNext, Stream.bidxNext, Stream.baNext, Stream.curNext, Stream.cvNext,
    Stream.wbNext, Stream.wvNext, Stream.rqNext, Stream.ldNext, Stream.pendNext,
    Stream.pvNext, Stream.starvedNext, Stream.nbNext, Stream.nvNext,
    Stream.starveEvent, Stream.starveTx, Stream.starveRx, Stream.advT, Stream.bitin,
    Stream.fl, Stream.push, Stream.done, Stream.endC, Stream.last,
    Machine.Util.streamAuto, Machine.streamEnd, bv_id,
    Option.getD_some, Option.getD_none, nbit_ctl0, nbit_ctl1, nbit_clr7, nbit_clr0,
    Bool.not_true, Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    ite_false, ite_true, beq_nat]
  by_cases h0 : cap = true <;> by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;>
    simp_all

set_option maxHeartbeats 2000000 in
/-- **Frozen-cycle register-step bridge with a host rewind, flush allowed.**
Identical to `abs_step_frozen_rewind` but the side condition no longer fixes
`flush`. -/
theorem abs_step_frozen_rewind_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧
      i.replayLate = false)
    (hnv : cap = true ∨ s.nv = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true := by
  have hcon : ¬ (s.ld = true ∧ i.frzd = false) := by
    rintro ⟨h1, h2⟩
    rw [hland h1] at h2
    exact Bool.noConfusion h2
  obtain ⟨ha, hrx, hce, hla⟩ := hside
  unfold Stream.step Machine.streamNext
  simp only [abs, absIn, cfgOf, cond_eq_ite, hreset, hfrz, hrew, ha, hrx, hce, hla,
    Stream.posNext, Stream.bidxNext, Stream.baNext, Stream.curNext, Stream.cvNext,
    Stream.wbNext, Stream.wvNext, Stream.rqNext, Stream.ldNext, Stream.pendNext,
    Stream.pvNext, Stream.starvedNext, Stream.nbNext, Stream.nvNext,
    Stream.starveEvent, Stream.starveTx, Stream.starveRx, Stream.advT, Stream.bitin,
    Stream.fl, Stream.push, Stream.done, Stream.endC, Stream.last,
    Machine.Util.streamAuto, Machine.streamEnd, bv_id,
    Option.getD_some, Option.getD_none, nbit_ctl0, nbit_ctl1, nbit_clr7, nbit_clr0,
    Bool.not_true, Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    ite_false, ite_true, beq_nat]
  rcases hnv with hc | hn
  · by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;> simp_all
  · by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;> simp_all

/-! ### The relational frozen steps, flush unconstrained

The discharge's `premise_streams` uses the relational form (`frozen_rel` /
`frozen_rel_rewind` in `Metronome.ChipCut.Discharge.StreamDbg`), not the
exact-state bridge above, because `AbsRelB` does not fix the invalid slots.
These two theorems are that relational form with the `flush = false` premise
removed, so the discharge can drop `StreamWire.hostctl` entirely. -/

set_option maxHeartbeats 1600000 in
/-- **The relational frozen stream step, flush unconstrained.**  In a frozen
cycle with no host rewind, no landing and no move input, `AbsRelB` is preserved;
`streamNext` holds every register except `STARVED`, which follows the host
clear.  (Same proof as `frozen_rel`; `hfrz` alone makes `Stream.fl` false, so no
flush premise is needed.) -/
theorem frozen_rel_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg) (mode : Nat)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c mode m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hlandB : (m.ld && (s.ld && !i.frzd)) = false := by
    by_cases hs : s.ld = true
    · have hz : i.frzd = true := hland hs
      simp [hs, hz]
    · simp [hs]
  have hmach : Machine.streamNext c mode m (absIn cap s i) true =
      { m with starved := m.starved && !i.clrStarved } := by
    have hrewB : (Machine.Util.nbit (ctlVal i) 0 ||
        Machine.Util.nbit (clrVal i) 0) = false := by
      rw [nbit_ctl0, nbit_clr0, hrew]
      rfl
    simp only [Machine.streamNext, absIn, Option.getD_some, hrewB, hrew,
      hlandB, hfrz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.and_self,
      nbit_clr7, Bool.or_false]
  rw [hmach]
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hz0 : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · have hz : i.frzd = true := hland hl
      simp only [hl, hz, Bool.not_true, Bool.and_false, Bool.true_and]
    · have hlf : s.ld = false := by simpa using hl
      simp [hlf]
  have hwb : (Stream.step cap s i).wb = s.wb := by
    have htx : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
      simp [Bool.and_assoc, hz0]
    have hcen : (Stream.cen cap i && Stream.push cap s i && !(s.pv && !i.gnt) && !i.frz) =
        false := by simp [hfrz]
    simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, if_false, if_true, htx, hcen,
      hfrz, Bool.false_eq_true, Bool.and_false, Bool.and_true]
  have hwv : (Stream.step cap s i).wv = s.wv := hfrz0.2.2.2.2.2.2.2.1
  have hrq' : (Stream.step cap s i).rq = s.rq := hfrz0.2.2.2.2.2.2.2.2
  have hld' : (Stream.step cap s i).ld = s.ld := by
    simp only [Stream.step, Stream.ldNext, hreset, Bool.not_true, if_false, if_true, hrew, hfrz,
      Bool.false_eq_true]
  have hnb : (Stream.step cap s i).nb = s.nb := by
    have h1 : (Stream.rpl cap i && s.ld && !i.frzd && i.frz) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h2 : (Stream.rpl cap i && s.ld && !i.frzd && Stream.occupied s i) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    simp only [Stream.step, Stream.nbNext, h3, Bool.false_eq_true, if_false, if_true, h1, h2,
      Bool.and_false]
  have hnv : (Stream.step cap s i).nv = s.nv := by
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    have h4 : (cap && i.rewind) = false := by simp [hrew]
    simp only [Stream.step, Stream.nvNext, h3, Bool.false_eq_true, if_false, if_true, h4, hfrz]
  have hst : (Stream.step cap s i).starved = (s.starved && !i.clrStarved) := by
    have h1 : Stream.starveTx cap s i = false := by
      simp [Stream.starveTx, Stream.advT, hadv]
    have h2 : Stream.starveRx cap s i = false := by
      simp [Stream.starveRx, Stream.push, Stream.done, Stream.bitin, Stream.fl, hrx, hpush,
        hfrz]
    have h3 : (Stream.rpl cap i && i.replayLate) = false := by rw [hlate]; simp
    simp only [Stream.step, Stream.starvedNext, hreset, Bool.not_true, if_false, if_true,
      Stream.starveEvent, h1, h2, h3, Bool.false_or, Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfrz0.1, hpos]
  · rw [hfrz0.2.1, hbidx]
  · rw [hfrz0.2.2.1, hba]
  · rw [hfrz0.2.2.2.1, hcur]
  · rw [hfrz0.2.2.2.2.1, hcv]
  · rw [hrq', hrq]
  · rw [hld', hld]
  · rw [hfrz0.2.2.2.2.2.1, hpend]
  · rw [hfrz0.2.2.2.2.2.2.1, hpv]
  · rw [hst]
    rw [hstar]
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hwv]; exact hbuf.wv_eq
    · rw [hnv]; exact hbuf.nv_eq ‹cap = true›
    · intro hh
      rw [hwb]
      exact hbuf.wb_of_wv (by rw [← hwv]; exact hh)
    · intro hh
      rw [hnb]
      exact hbuf.nb_of_nv ‹cap = true› (by rw [← hnv]; exact hh)
  · intro hc
    obtain ⟨hwb0, hwv0, hnb0⟩ := hbuf.2.1 hc
    exact ⟨by rw [hwb]; exact hwb0, by rw [hwv]; exact hwv0, by rw [hnb]; exact hnb0⟩
  · intro hc
    exact hbuf.2.2 ⟨by rw [← hrq']; exact hc.1, by rw [← hld']; exact hc.2⟩

set_option maxHeartbeats 2000000 in
/-- **The relational frozen step with a host rewind, flush unconstrained.**
`frozen_rel_rewind` without the `flush = false` premise; the cut's flush is
gated by `!FRZ`, so the starve-event argument goes through with `hfrz` alone. -/
theorem frozen_rel_rewind_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg) (mode : Nat)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hstart : Machine.Util.bv 11 c.start = i.cfgStart)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c mode m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hbaq, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hlandB : (m.ld && (s.ld && !i.frzd)) = false := by
    by_cases hs : s.ld = true
    · have hz : i.frzd = true := hland hs
      simp [hs, hz]
    · simp [hs]
  have hz0 : (s.ld && !i.frzd) = false := by
    by_cases hl : s.ld = true
    · have hz : i.frzd = true := hland hl
      simp only [hl, hz, Bool.not_true, Bool.and_false, Bool.true_and]
    · have hlf : s.ld = false := by simpa using hl
      simp [hlf]
  have hmach : Machine.streamNext c mode m (absIn cap s i) true =
      { m with
        pos := 0,
        bidx := 0,
        ba := Machine.Util.bv 11 c.start,
        cur := 0,
        cv := false,
        wv := false,
        rq := false,
        ld := false,
        pv := false,
        starved := m.starved && !i.clrStarved,
        nv := false } := by
    have hrewT : (Machine.Util.nbit (ctlVal i) 0 ||
        Machine.Util.nbit (clrVal i) 0) = true := by
      rw [nbit_ctl0, nbit_clr0, hrew]
      rfl
    simp only [Machine.streamNext, absIn, Option.getD_some, hrewT, hlandB,
      hfrz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.and_self,
      nbit_clr7, Bool.or_false]
  rw [hmach]
  have hwb : (Stream.step cap s i).wb = s.wb := by
    have htx : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
      simp [Bool.and_assoc, hz0]
    have hcen : (Stream.cen cap i && Stream.push cap s i && !(s.pv && !i.gnt) && !i.frz) =
        false := by simp [hfrz]
    simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, if_false, if_true, htx, hcen,
      hfrz, Bool.false_eq_true, Bool.and_false, Bool.and_true]
  have hnb : (Stream.step cap s i).nb = s.nb := by
    have h1 : (Stream.rpl cap i && s.ld && !i.frzd && i.frz) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h2 : (Stream.rpl cap i && s.ld && !i.frzd && Stream.occupied s i) = false := by
      rw [show (Stream.rpl cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
      simp
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    simp only [Stream.step, Stream.nbNext, h3, Bool.false_eq_true, if_false, if_true, h1, h2,
      Bool.and_false]
  have hnv : cap = true → (Stream.step cap s i).nv = false := by
    intro hc
    have h3 : (cap && !i.resetN) = false := by simp [hreset]
    have h4 : (cap && i.rewind) = true := by simp [hc, hrew]
    simp only [Stream.step, Stream.nvNext, h3, Bool.false_eq_true, if_false, if_true, h4]
  have hpend' : (Stream.step cap s i).pend = s.pend := by
    simp [Stream.step, Stream.pendNext, hreset, hfrz]
  have hst : (Stream.step cap s i).starved = (s.starved && !i.clrStarved) := by
    have h1 : Stream.starveTx cap s i = false := by
      simp [Stream.starveTx, Stream.advT, hadv]
    have h2 : Stream.starveRx cap s i = false := by
      simp [Stream.starveRx, Stream.push, Stream.done, Stream.bitin, Stream.fl, hrx, hpush,
        hfrz]
    have h3 : (Stream.rpl cap i && i.replayLate) = false := by rw [hlate]; simp
    simp only [Stream.step, Stream.starvedNext, hreset, Bool.not_true, if_false, if_true,
      Stream.starveEvent, h1, h2, h3, Bool.false_or, Bool.false_eq_true]
  obtain ⟨hwpos, hwbidx, hwba, hwcur, hwcv, hwwv, hwrq, hwld, hwpv⟩ :=
    Stream.rewind_overrides cap s i hrew hreset
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hwpos
  · exact hwbidx
  · exact hwba.trans hstart.symm
  · exact hwcur
  · exact hwcv
  · exact hwrq
  · exact hwld
  · exact hpend'.trans hpend
  · exact hwpv
  · rw [hst, hstar]
  · refine ⟨?_, ?_, ?_⟩
    · intro _
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hwwv
      · exact hnv ‹cap = true›
      · intro hh
        rw [hwwv] at hh
        exact Bool.noConfusion hh
      · intro hh
        rw [hnv ‹cap = true›] at hh
        exact Bool.noConfusion hh
    · intro hc
      obtain ⟨hwb0, _, hnb0⟩ := hbuf.2.1 hc
      exact ⟨hwb.trans hwb0, hwwv, hnb.trans hnb0⟩
    · intro hc
      rw [hwrq] at hc
      exact Bool.noConfusion hc.1

/-! ## The genuine divergence: a frozen landing

A replay read is requested in cycle 1 (from reset), served in cycle 2, and
cycle 3 freezes with `FRZD = 0`: the cut lands the word in `NB` and the machine
in `WB` (`Machine/Stream.lean`'s `mode == 3 && s.wv` test, AMBIG(11)).  With
`WV = 0` the word is only *pending*, and the next unfrozen cycle re-converges,
but the raw slots differ and `BufRelX` fails at the frozen state — so the frozen
step's `hland` is a real hypothesis, not a convenience. -/

/-- Inputs of cycle 1: replay mode, no service yet, no freeze. -/
def wV1 : Stream.Input :=
  { resetN := true, frz := false, frzd := false, capEn := false, capPush := false,
    capRec := 0, replayEn := true, replayApply := false, replayLate := false,
    cfgMode := false, cfgMsb := false, cfgStart := 0, cfgLen := 0x100, cfgMark := 0,
    adv := false, rxWe := false, rxBit := false, rewind := false, flush := false,
    clrStarved := false, gnt := true, rdata := 0 }

/-- Inputs of cycle 2: the replay read is served, still unfrozen. -/
def wV2 : Stream.Input :=
  { wV1 with gnt := true, rdata := 0xAAAAAAAA }

/-- Inputs of cycle 3: the freeze, one cycle after the served read. -/
def wV3 : Stream.Input :=
  { wV1 with frz := true, frzd := false, gnt := false, rdata := 0xAAAAAAAA }

/-- The cut's state after cycles 1, 2. -/
def wS1 : Stream.State := Stream.step true Stream.resetState wV1
/-- The cut's state after cycle 2. -/
def wS2 : Stream.State := Stream.step true wS1 wV2
/-- The machine's stream state after cycle 1. -/
def wM1 : Machine.StreamSt :=
  Machine.streamNext (cfgOf wV1) (modeOf true wV1) (default : Machine.StreamSt)
    (absIn true Stream.resetState wV1) false
/-- The machine's stream state after cycle 2. -/
def wM2 : Machine.StreamSt :=
  Machine.streamNext (cfgOf wV2) (modeOf true wV2) wM1 (absIn true wS1 wV2) false
/-- The machine's stream state after cycle 3 (the frozen cycle). -/
def wM3 : Machine.StreamSt :=
  Machine.streamNext (cfgOf wV3) (modeOf true wV3) wM2 (absIn true wS2 wV3) true

/-- **The frozen-landing witness (AMBIG 11), on a reachable state.**  Three
composed stream steps from reset: the cut parks the landed word in `NB`, the
machine in `WB`. -/
theorem frozen_landing_witness :
    (Stream.step true wS2 wV3).wb = 0 ∧
    (Stream.step true wS2 wV3).wv = false ∧
    (Stream.step true wS2 wV3).nb = 0xAAAAAAAA ∧
    (Stream.step true wS2 wV3).nv = false ∧
    wM3.wb = 0xAAAAAAAA ∧
    wM3.nb = 0 := by
  decide

/-- At that reachable state `BufRelX` fails: `WB` is `0` against `0xAAAAAAAA` and
`NB` is `0xAAAAAAAA` against `0`.  This is the frozen landing of AMBIG(11), and
the reason the frozen step keeps `hland : LD → FRZD`. -/
theorem frozen_landing_bufrelX_fails :
    ¬ BufRelX true (Stream.step true wS2 wV3) wM3 := by
  unfold BufRelX
  decide

/-- The same trace read as the next-cycle landing: `LD` is still set, `WV = 0`,
and `FRZD` becomes `1` in the following (unfrozen) cycle, which is exactly the
`FRZD ∧ LD` case the unfrozen step's `hfresh` excludes. -/
theorem frozen_landing_ld :
    wS2.ld = true ∧ wS2.wv = false ∧ wS2.rq = false := by
  decide

/-- **A frozen cycle holds `LD`.**  With `frozen_ld_false` this keeps `LD` clear
through a whole frozen run: the run's first cycle has `LD = 0` (it has
`FRZD = 0` and `LD → FRZD`), and every later frozen cycle holds it, so the
first unfrozen cycle after the run has `FRZD = 1` with `LD = 0` and the unfrozen
step's `hfresh : LD → !FRZD` is vacuous there. -/
theorem ld_frozen_hold (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hfrz : i.frz = true) (hld : s.ld = false) : (Stream.step cap s i).ld = false := by
  simp only [Stream.step, Stream.ldNext, hld, hfrz, cond_eq_ite]
  by_cases hrew : i.rewind = true <;> simp [hrew]

/-! ## The landing exception (§12.3)

The assembler proved `LD → FRZD` *false* (`streamWire_landing_false`): `LD` is
held through a frozen cycle, so a host freeze one cycle after a served read
gives `LD = 1` with `FRZD = 0`, and the machine's frozen branch then captures
the RAM output (`Machine/Stream.lean` 154-157).  The lemmas below cover that
cycle: exact state equality when both readings write the same slot (transmit,
or replay with `WV = 1`), and the guarded `BufRel` in all cases under the chip
facts `LD → (transmit ∨ replay)` and the replay well-formedness
`ShapeOK : WV = 0 → NV = 0`.  The replay "empty head" case is the witnessed
divergence. -/

/-- Frozen post record of the machine, landing exception included. -/
theorem mach_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (hld : s.ld = m.ld) (hwv : s.wv = m.wv) (hrew : i.rewind = false) :
    Machine.streamNext c (modeOf cap i) m (absIn cap s i) true =
      { m with
        wb := (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb),
        nb := (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb),
        starved := m.starved && !i.clrStarved } := by
  simp only [Machine.streamNext, absIn, Option.getD_some, nbit_ctl0, nbit_clr0, nbit_clr7,
    hrew, Bool.false_eq_true, Bool.not_false, Bool.or_false, if_false, if_true, bv_id,
    ← hld, hwv]
  by_cases hl : s.ld = true <;> by_cases hf : i.frzd = true <;>
    by_cases hm : ((modeOf cap i == 3) && s.wv) = true <;>
    by_cases hm3 : modeOf cap i = 3 <;> by_cases hw : m.wv = true <;>
    simp_all [Bool.and_assoc, Bool.and_self]

/-- Frozen post record of the machine with a host rewind, landing exception
included. -/
theorem mach_frozen_rewind_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (hld : s.ld = m.ld) (hwv : s.wv = m.wv) (hrew : i.rewind = true) :
    Machine.streamNext c (modeOf cap i) m (absIn cap s i) true =
      { pos := 0, bidx := 0, ba := Machine.Util.bv 11 c.start, cur := 0, cv := false,
        wb := (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb),
        wv := false, rq := false, ld := false, pend := m.pend, pv := false,
        starved := (m.starved && !i.clrStarved),
        nb := (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb),
        nv := false } := by
  simp only [Machine.streamNext, absIn, Option.getD_some, nbit_ctl0, nbit_clr0, nbit_clr7,
    hrew, Bool.false_eq_true, Bool.not_false, Bool.or_false, if_false, if_true, bv_id,
    ← hld, hwv, Bool.true_and, Bool.and_self]
  by_cases hl : s.ld = true <;> by_cases hf : i.frzd = true <;>
    by_cases hm : ((modeOf cap i == 3) && s.wv) = true <;>
    by_cases hm3 : modeOf cap i = 3 <;> by_cases hw : m.wv = true <;>
    simp_all [Bool.and_assoc, Bool.and_self]

/-- Frozen WB of the cut, landing exception included. -/
theorem wb_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) :
    (Stream.step cap s i).wb =
      (if Stream.txMode cap i && s.ld && !i.frzd then i.rdata else s.wb) := by
  simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, Bool.false_eq_true, if_false,
    if_true, hfrz, cond_eq_ite]
  by_cases htx : Stream.txMode cap i = true <;> by_cases hld : s.ld = true <;>
    by_cases hfz : i.frzd = true <;> simp_all

/-- Frozen NB of the cut, landing exception included. -/
theorem nb_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) :
    (Stream.step cap s i).nb =
      (if Stream.rpl cap i && s.ld && !i.frzd then i.rdata else s.nb) := by
  simp only [Stream.step, Stream.nbNext, hreset, Bool.not_true, Bool.false_eq_true, if_false,
    if_true, hfrz, cond_eq_ite, Stream.occupied]
  by_cases hrpl : Stream.rpl cap i = true <;> by_cases hld : s.ld = true <;>
    by_cases hfz : i.frzd = true <;> by_cases hcap : cap = true <;> simp_all

/-- The machine mode 3 is the cut's RPL. -/
theorem modeOf_eq_three (cap : Bool) (i : Stream.Input) :
    (modeOf cap i == 3) = Stream.rpl cap i := by
  simp only [modeOf, Stream.rpl]
  by_cases h1 : cap = true <;> by_cases h2 : i.replayEn = true <;>
    by_cases h3 : i.capEn = true <;> by_cases h4 : i.cfgMode = true <;>
    simp_all [Bool.and_eq_true]

/-- LD holds through a frozen cycle with no rewind. -/
theorem ld_frozen_eq (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false) :
    (Stream.step cap s i).ld = s.ld := by
  simp only [Stream.step, Stream.ldNext, hreset, Bool.not_true, Bool.false_eq_true, if_false,
    if_true, hrew, hfrz, cond_eq_ite]

/-- RQ holds through a frozen cycle with no rewind. -/
theorem rq_frozen_hold (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false) :
    (Stream.step cap s i).rq = s.rq := by
  simp only [Stream.step, Stream.rqNext, hreset, Bool.not_true, Bool.false_eq_true, if_false,
    if_true, hrew, hfrz, cond_eq_ite]

/-- STARVED in a frozen cycle with no move input. -/
theorem starved_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    (Stream.step cap s i).starved = (s.starved && !i.clrStarved) := by
  have h1 : Stream.starveTx cap s i = false := by
    simp [Stream.starveTx, Stream.advT, hadv]
  have h2 : Stream.starveRx cap s i = false := by
    simp [Stream.starveRx, Stream.push, Stream.done, Stream.bitin, Stream.fl, hrx, hpush, hfrz]
  have h3 : (Stream.rpl cap i && i.replayLate) = false := by rw [hlate]; simp
  simp only [Stream.step, Stream.starvedNext, hreset, Bool.not_true, if_false, if_true,
    Stream.starveEvent, h1, h2, h3, Bool.false_or, Bool.false_eq_true]

/-- NV holds through a frozen cycle with no rewind. -/
theorem nv_frozen_hold (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false) :
    (Stream.step cap s i).nv = s.nv := by
  simp only [Stream.step, Stream.nvNext, hreset, Bool.not_true, Bool.false_eq_true,
    Bool.and_false, if_false, if_true, hrew, hfrz, cond_eq_ite]

/-- **`BufRelX` across a frozen landing when both readings write the same slot.** -/
theorem bufRelX_step_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hslot : s.ld = true → i.frzd = true ∨ Stream.txMode cap i = true ∨
      (Stream.rpl cap i = true ∧ s.wv = true)) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hwbc := wb_frozen_landing cap s i hreset hfrz
  have hnbc := nb_frozen_landing cap s i hreset hfrz
  have hnv' := nv_frozen_hold cap s i hreset hfrz hrew
  have hmach := mach_frozen_landing cap s i m c hld hwv hrew
  have mwb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb =
      (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb) := by
    rw [hmach]
  have mnb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb =
      (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb) := by
    rw [hmach]
  have mwv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv = m.wv := by
    rw [hmach]
  have mnv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv = m.nv := by
    rw [hmach]
  have hwbeq : (Stream.step cap s i).wb =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb := by
    rw [hwbc, mwb]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
          simp [htx, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3]
        rw [if_pos hc1, if_pos hc2]
      · have htxf : Stream.txMode cap i = false := by
          unfold Stream.txMode
          simp [hrpl]
        have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
          simp [htxf]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
        exact hwb
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
      exact hwb
  have hwveq : (Stream.step cap s i).wv =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv := by
    rw [hfrz0.2.2.2.2.2.2.2.1, mwv]
    exact hwv
  have hnbeq : (Stream.step cap s i).nb =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb := by
    rw [hnbc, mnb]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
          simp [hrplf]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
        exact hnb
      · have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = true := by
          simp [hrpl, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_pos hc1, if_pos hc2]
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
      exact hnb
  have hnveq : cap = true → (Stream.step cap s i).nv =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv := by
    intro hc
    rw [hnv', mnv]
    exact hnv hc
  exact ⟨hwbeq, hwveq, hnbeq, hnveq⟩

/-- **`BufRelX` across a frozen landing with a host rewind**, same-slot cases. -/
theorem bufRelX_step_frozen_landing_rewind (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hslot : s.ld = true → i.frzd = true ∨ Stream.txMode cap i = true ∨
      (Stream.rpl cap i = true ∧ s.wv = true)) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨hwb, hwv, hnb, hnv⟩ := hb
  have hwbc := wb_frozen_landing cap s i hreset hfrz
  have hnbc := nb_frozen_landing cap s i hreset hfrz
  have hwv' : (Stream.step cap s i).wv = false :=
    (Stream.rewind_overrides cap s i hrew hreset).2.2.2.2.2.1
  have hnv' : cap = true → (Stream.step cap s i).nv = false :=
    fun hc => Stream.rewind_nv cap s i hrew hc
  have hmach := mach_frozen_rewind_landing cap s i m c hld hwv hrew
  have mwb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb =
      (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb) := by
    rw [hmach]
  have mnb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb =
      (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb) := by
    rw [hmach]
  have mwv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv = false := by
    rw [hmach]
  have mnv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv = false := by
    rw [hmach]
  have hwbeq : (Stream.step cap s i).wb =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb := by
    rw [hwbc, mwb]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
          simp [htx, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3]
        rw [if_pos hc1, if_pos hc2]
      · have htxf : Stream.txMode cap i = false := by
          unfold Stream.txMode
          simp [hrpl]
        have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
          simp [htxf]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
        exact hwb
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
      exact hwb
  have hwveq : (Stream.step cap s i).wv =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv := by
    rw [hwv', mwv]
  have hnbeq : (Stream.step cap s i).nb =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb := by
    rw [hnbc, mnb]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
          simp [hrplf]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
        exact hnb
      · have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = true := by
          simp [hrpl, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_pos hc1, if_pos hc2]
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
      exact hnb
  have hnveq : cap = true → (Stream.step cap s i).nv =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv := by
    intro hc
    rw [hnv' hc, mnv]
  exact ⟨hwbeq, hwveq, hnbeq, hnveq⟩

/-! ## Witnesses for the replay "empty head" divergence -/

/-- The replay first slot is empty while the second is valid. -/
def ShapeOK (s : Stream.State) : Prop := s.wv = false → s.nv = false

/-- The state of the witness: a valid second slot with an empty first slot. -/
def wS4 : Stream.State := { wS with nv := true }

theorem wS4_not_shape : ¬ ShapeOK wS4 := by
  intro h
  have := h rfl
  simp [wS4] at this

/-- **Genuine divergence at a frozen landing with `WV = 0` but `NV = 1`.**
The cut stores the landed word in `NB` (clobbering the valid second slot) while
the machine stores it in `WB`, so even the guarded `BufRel` fails after the
step; `ShapeOK` is the named hypothesis that excludes this state. -/
theorem frozen_landing_invalid_nv_disagrees :
    BufRel true wS4 (abs wS4) ∧
    ¬ BufRel true (Stream.step true wS4 wI2)
      (Machine.streamNext (cfgOf wI2) (modeOf true wI2) (abs wS4) (absIn true wS4 wI2) true) := by
  constructor
  · unfold BufRel
    decide
  · unfold BufRel
    decide

/-- **The exact-state frozen bridge with the landing exception** (no rewind,
flush free), for the same-slot cases.  This is `abs_step_frozen` without the
`LD → FRZD` premise, under `hslot`; the replay "empty head" case is the
witnessed divergence and is excluded. -/
theorem abs_step_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hslot : s.ld = true → i.frzd = true ∨ Stream.txMode cap i = true ∨
      (Stream.rpl cap i = true ∧ s.wv = true))
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧
      i.replayLate = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true := by
  obtain ⟨ha, hrx, hce, hla⟩ := hside
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hwbc := wb_frozen_landing cap s i hreset hfrz
  have hnbc := nb_frozen_landing cap s i hreset hfrz
  have hld' := ld_frozen_eq cap s i hreset hfrz hrew
  have hrq' := rq_frozen_hold cap s i hreset hfrz hrew
  have hnv' := nv_frozen_hold cap s i hreset hfrz hrew
  have hst := starved_frozen cap s i hreset hfrz ha hrx hce hla
  have hmach := mach_frozen_landing cap s i (abs s) (cfgOf i) rfl rfl hrew
  have hwbE : (Stream.step cap s i).wb =
      (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else s.wb) := by
    rw [hwbc]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
          simp [htx, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3]
        rw [if_pos hc1, if_pos hc2]
      · have htxf : Stream.txMode cap i = false := by
          unfold Stream.txMode
          simp [hrpl]
        have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
          simp [htxf]
        have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
  have hnbE : (Stream.step cap s i).nb =
      (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else s.nb) := by
    rw [hnbc]
    by_cases hland : (s.ld && !i.frzd) = true
    · have h1 := (Bool.and_eq_true ..).mp hland
      have hlds : s.ld = true := h1.1
      have hfz : i.frzd = false := by simpa using h1.2
      rcases hslot hlds with hf | htx | ⟨hrpl, hwvt⟩
      · exact absurd hf (by simp [hfz])
      · have hrplf : Stream.rpl cap i = false := by
          unfold Stream.txMode at htx
          simp_all
        have hm3 : (modeOf cap i == 3) = false := by
          rw [modeOf_eq_three]; exact hrplf
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
          simp [hrplf]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
          simp [hlds, hfz, hm3]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
      · have hm3 : (modeOf cap i == 3) = true := by
          rw [modeOf_eq_three]; exact hrpl
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = true := by
          simp [hrpl, hlds, hfz]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = true := by
          simp [hlds, hfz, hm3, hwvt]
        rw [if_pos hc1, if_pos hc2]
    · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
      have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
        simp [Bool.and_assoc, hlandf]
      have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
        simp [hlandf]
      rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
  rw [hmach]
  simp only [abs, Machine.StreamSt.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfrz0.1
  · exact hfrz0.2.1
  · exact hfrz0.2.2.1
  · exact hfrz0.2.2.2.1
  · exact hfrz0.2.2.2.2.1
  · exact hwbE
  · exact hfrz0.2.2.2.2.2.2.2.1
  · exact hrq'
  · exact hld'
  · exact hfrz0.2.2.2.2.2.1
  · exact hfrz0.2.2.2.2.2.2.1
  · exact hst
  · exact hnbE
  · exact hnv'

theorem frozen_rel_landing_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hldmode : s.ld = true → Stream.txMode cap i = true ∨ Stream.rpl cap i = true)
    (hshape : ShapeOK s)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hwbc := wb_frozen_landing cap s i hreset hfrz
  have hnbc := nb_frozen_landing cap s i hreset hfrz
  have hld' := ld_frozen_eq cap s i hreset hfrz hrew
  have hrq' := rq_frozen_hold cap s i hreset hfrz hrew
  have hnv' := nv_frozen_hold cap s i hreset hfrz hrew
  have hst := starved_frozen cap s i hreset hfrz hadv hrx hpush hlate
  have hmach := mach_frozen_landing cap s i m c hld hbuf.wv_eq hrew
  have mwb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb =
      (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb) := by
    rw [hmach]
  have mnb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb =
      (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb) := by
    rw [hmach]
  have mwv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv = m.wv := by
    rw [hmach]
  have mnv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv = m.nv := by
    rw [hmach]
  have mro : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).rq = m.rq := by
    rw [hmach]
  have mld : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).ld = m.ld := by
    rw [hmach]
  have mst : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).starved =
      (m.starved && !i.clrStarved) := by
    rw [hmach]
  have mpos : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pos = m.pos := by
    rw [hmach]
  have mbidx : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).bidx = m.bidx := by
    rw [hmach]
  have mba : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).ba = m.ba := by
    rw [hmach]
  have mcur : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).cur = m.cur := by
    rw [hmach]
  have mcv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).cv = m.cv := by
    rw [hmach]
  have mpend : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pend = m.pend := by
    rw [hmach]
  have mpv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pv = m.pv := by
    rw [hmach]
  have hbuf' : BufRel cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
    refine ⟨?_, ?_, ?_⟩
    · -- CAP = 1
      intro hc
      have hwv : s.wv = m.wv := hbuf.wv_eq
      have hnv : s.nv = m.nv := hbuf.nv_eq hc
      have hwbv : s.wv = true → s.wb = m.wb := fun h => hbuf.wb_of_wv h
      have hnbv : s.nv = true → s.nb = m.nb := fun h => hbuf.nb_of_nv hc h
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfrz0.2.2.2.2.2.2.2.1, mwv]
        exact hwv
      · rw [hnv', mnv]
        exact hnv
      · -- WV' → WB'
        intro hwv'
        rw [hfrz0.2.2.2.2.2.2.2.1] at hwv'
        rw [hwbc, mwb]
        by_cases hland : (s.ld && !i.frzd) = true
        · have h1 := (Bool.and_eq_true ..).mp hland
          have hlds : s.ld = true := h1.1
          have hfz : i.frzd = false := by simpa using h1.2
          rcases hldmode hlds with htx | hrpl
          · have hrplf : Stream.rpl cap i = false := by
              unfold Stream.txMode at htx
              simp_all
            have hm3 : (modeOf cap i == 3) = false := by
              rw [modeOf_eq_three]; exact hrplf
            have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
              simp [htx, hlds, hfz]
            have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
              simp [hlds, hfz, hm3]
            rw [if_pos hc1, if_pos hc2]
          · have htxf : Stream.txMode cap i = false := by
              unfold Stream.txMode
              simp [hrpl]
            have hm3 : (modeOf cap i == 3) = true := by
              rw [modeOf_eq_three]; exact hrpl
            have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
              simp [htxf]
            have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
              simp [hlds, hfz, hm3, hwv']
            rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
            exact hwbv hwv'
        · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
          have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
            simp [Bool.and_assoc, hlandf]
          have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
            simp [hlandf]
          rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hwbv hwv'
      · -- NV' → NB'
        intro hnvtrue
        rw [hnv'] at hnvtrue
        rw [hnbc, mnb]
        by_cases hland : (s.ld && !i.frzd) = true
        · have h1 := (Bool.and_eq_true ..).mp hland
          have hlds : s.ld = true := h1.1
          have hfz : i.frzd = false := by simpa using h1.2
          rcases hldmode hlds with htx | hrpl
          · have hrplf : Stream.rpl cap i = false := by
              unfold Stream.txMode at htx
              simp_all
            have hm3 : (modeOf cap i == 3) = false := by
              rw [modeOf_eq_three]; exact hrplf
            have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
              simp [hrplf]
            have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
              simp [hlds, hfz, hm3]
            rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
            exact hnbv hnvtrue
          · have hm3 : (modeOf cap i == 3) = true := by
              rw [modeOf_eq_three]; exact hrpl
            by_cases hwvt : s.wv = true
            · have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = true := by
                simp [hrpl, hlds, hfz]
              have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = true := by
                simp [hlds, hfz, hm3, hwvt]
              rw [if_pos hc1, if_pos hc2]
            · have hwvf : s.wv = false := by simpa using hwvt
              exact absurd (hshape hwvf) (by simp [hnvtrue])
        · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
          have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
            simp [Bool.and_assoc, hlandf]
          have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
            simp [hlandf]
          rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hnbv hnvtrue
    · -- CAP = 0
      intro hc
      obtain ⟨hwbf, hwvf, hnbf⟩ := hbuf.2.1 hc
      have hrplf : Stream.rpl cap i = false := by
        unfold Stream.rpl
        simp [hc]
      have hm3f : (modeOf cap i == 3) = false := by
        rw [modeOf_eq_three]; exact hrplf
      refine ⟨?_, ?_, ?_⟩
      · by_cases hland : (s.ld && !i.frzd) = true
        · have h1 := (Bool.and_eq_true ..).mp hland
          have hlds : s.ld = true := h1.1
          have hfz : i.frzd = false := by simpa using h1.2
          rcases hldmode hlds with htx | hrpl
          · have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
              simp [htx, hlds, hfz]
            have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
              simp [hlds, hfz, hm3f]
            rw [hwbc, mwb, if_pos hc1, if_pos hc2]
          · exact absurd hrpl (by simp [hrplf])
        · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
          have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
            simp [Bool.and_assoc, hlandf]
          have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
            simp [hlandf]
          rw [hwbc, mwb, if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hwbf
      · rw [hfrz0.2.2.2.2.2.2.2.1, mwv]
        exact hwvf
      · by_cases hland : (s.ld && !i.frzd) = true
        · have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
            simp [hrplf]
          have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
            simp [hm3f]
          rw [hnbc, mnb, if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hnbf
        · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
          have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
            simp [Bool.and_assoc, hlandf]
          have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
            simp [hlandf]
          rw [hnbc, mnb, if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hnbf
    · intro hno
      exact hbuf.2.2 ⟨by rw [← hrq']; exact hno.1, by rw [← hld']; exact hno.2⟩
  exact ⟨by rw [hfrz0.1, mpos, hpos], by rw [hfrz0.2.1, mbidx, hbidx],
    by rw [hfrz0.2.2.1, mba, hba], by rw [hfrz0.2.2.2.1, mcur, hcur],
    by rw [hfrz0.2.2.2.2.1, mcv, hcv], by rw [hrq', mro, hrq], by rw [hld', mld, hld],
    by rw [hfrz0.2.2.2.2.2.1, mpend, hpend], by rw [hfrz0.2.2.2.2.2.2.1, mpv, hpv],
    by rw [hst, mst, hstar], hbuf'⟩


/-- **The relational frozen step with a host rewind and the landing exception.**
`BufRel` is preserved: the rewind clears `WV`/`NV` on both sides, so the guarded
buffer clauses are reflexive, and the landed slots agree under `hldmode`. -/
theorem frozen_rel_landing_rewind_flush (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hstart : Machine.Util.bv 11 c.start = i.cfgStart)
    (hldmode : s.ld = true → Stream.txMode cap i = true ∨ Stream.rpl cap i = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hwbc := wb_frozen_landing cap s i hreset hfrz
  have hnbc := nb_frozen_landing cap s i hreset hfrz
  obtain ⟨hwpos, hwbidx, hwba, hwcur, hwcv, hwwv, hwrq, hwld, hwpv⟩ :=
    Stream.rewind_overrides cap s i hrew hreset
  have hnvrew : cap = true → (Stream.step cap s i).nv = false :=
    fun hc => Stream.rewind_nv cap s i hrew hc
  have hpend' : (Stream.step cap s i).pend = s.pend := by
    simp [Stream.step, Stream.pendNext, hreset, hfrz]
  have hst := starved_frozen cap s i hreset hfrz hadv hrx hpush hlate
  have hmach := mach_frozen_rewind_landing cap s i m c hld hbuf.wv_eq hrew
  have mpos : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pos = 0 := by
    rw [hmach]
  have mbidx : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).bidx = 0 := by
    rw [hmach]
  have mba : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).ba =
      Machine.Util.bv 11 c.start := by rw [hmach]
  have mcur : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).cur = 0 := by
    rw [hmach]
  have mcv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).cv = false := by
    rw [hmach]
  have mwv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wv = false := by
    rw [hmach]
  have mnv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nv = false := by
    rw [hmach]
  have mro : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).rq = false := by
    rw [hmach]
  have mld : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).ld = false := by
    rw [hmach]
  have mpv : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pv = false := by
    rw [hmach]
  have mpend : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).pend = m.pend := by
    rw [hmach]
  have mst : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).starved =
      (m.starved && !i.clrStarved) := by
    rw [hmach]
  have mwb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb =
      (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb) := by
    rw [hmach]
  have mnb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb =
      (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb) := by
    rw [hmach]
  have hbuf' : BufRel cap (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hwwv, mwv]
      · rw [hnvrew hc, mnv]
      · intro hh
        rw [hwwv] at hh
        exact Bool.noConfusion hh
      · intro hh
        rw [hnvrew hc] at hh
        exact Bool.noConfusion hh
    · intro hc
      obtain ⟨hwbf, hwvf, hnbf⟩ := hbuf.2.1 hc
      have hrplf : Stream.rpl cap i = false := by
        unfold Stream.rpl
        simp [hc]
      have hm3f : (modeOf cap i == 3) = false := by
        rw [modeOf_eq_three]; exact hrplf
      refine ⟨?_, ?_, ?_⟩
      · rw [hwbc, mwb]
        by_cases hland : (s.ld && !i.frzd) = true
        · have h1 := (Bool.and_eq_true ..).mp hland
          have hlds : s.ld = true := h1.1
          have hfz : i.frzd = false := by simpa using h1.2
          rcases hldmode hlds with htx | hrpl
          · have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = true := by
              simp [htx, hlds, hfz]
            have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = true := by
              simp [hlds, hfz, hm3f]
            rw [if_pos hc1, if_pos hc2]
          · exact absurd hrpl (by simp [hrplf])
        · have hlandf : (s.ld && !i.frzd) = false := by simpa using hland
          have hc1 : (Stream.txMode cap i && s.ld && !i.frzd) = false := by
            simp [Bool.and_assoc, hlandf]
          have hc2 : (s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv)) = false := by
            simp [hlandf]
          rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
          exact hwbf
      · rw [hwwv, mwv]
      · rw [hnbc, mnb]
        have hc1 : (Stream.rpl cap i && s.ld && !i.frzd) = false := by
          simp [Bool.and_assoc, hrplf]
        have hc2 : (s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv)) = false := by
          simp [hm3f]
        rw [if_neg (by rw [hc1]; simp), if_neg (by rw [hc2]; simp)]
        exact hnbf
    · intro hno
      rw [hwrq] at hno
      exact Bool.noConfusion hno.1
  exact ⟨by rw [hwpos, mpos], by rw [hwbidx, mbidx],
    by rw [hwba, mba]; exact hstart.symm, by rw [hwcur, mcur], by rw [hwcv, mcv],
    by rw [hwrq, mro], by rw [hwld, mld], by rw [hpend', mpend, hpend],
    by rw [hwpv, mpv], by rw [hst, mst, hstar], hbuf'⟩



/-! ## `ShapeOK` as a stream invariant (round 2026-11-22b) -/

def ShapeModeOK (mode : Nat) (s : Stream.State) : Prop :=
  ShapeOK s ∧ (s.nv = true → mode = 3)

theorem shapeModeOK_reset (mode : Nat) : ShapeModeOK mode Stream.resetState := by
  refine ⟨?_, ?_⟩ <;> simp [ShapeOK, Stream.resetState]

/-- `NV' = 1` comes from a valid second slot or a replay landing. -/
theorem nv_step_true_or (s : Stream.State) (i : Stream.Input) :
    (Stream.step true s i).nv = true → s.nv = true ∨ Stream.rpl true i = true := by
  intro h
  stream_simp
  by_cases hres : i.resetN = true <;> by_cases hrew : i.rewind = true <;>
    by_cases hfrz : i.frz = true <;> by_cases hld : s.ld = true <;>
    by_cases hocc : ((i.replayApply && s.nv) || (!i.replayApply && s.wv)) = true <;>
    by_cases hap : i.replayApply = true <;> by_cases hnv : s.nv = true <;>
    simp_all [Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.true_and, Bool.false_and, Bool.false_eq_true]

/-- In replay, `NV' = 1` forces `WV' = 1` (the shape of a FIFO). -/
theorem rpl_nv_wv (s : Stream.State) (i : Stream.Input) (hshape : ShapeOK s)
    (hrpl : Stream.rpl true i = true) (hnv' : (Stream.step true s i).nv = true) :
    (Stream.step true s i).wv = true := by
  stream_simp
  by_cases hres : i.resetN = true <;> by_cases hrew : i.rewind = true <;>
    by_cases hfrz : i.frz = true <;> by_cases hld : s.ld = true <;>
    by_cases hocc : ((i.replayApply && s.nv) || (!i.replayApply && s.wv)) = true <;>
    by_cases hap : i.replayApply = true <;> by_cases hnv : s.nv = true <;>
    by_cases hwv : s.wv = true <;>
    simp_all [ShapeOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.true_and, Bool.false_and, Bool.false_eq_true]

/-- **`ShapeOK` is preserved** provided a mode change only happens with
`WV = NV = false` (the strengthened mode-quietness premise). -/
theorem shapeOK_step (s : Stream.State) (i : Stream.Input) (pmode : Nat)
    (h : ShapeModeOK pmode s)
    (hchange : modeOf true i = pmode ∨ (s.wv = false ∧ s.nv = false)) :
    ShapeOK (Stream.step true s i) := by
  obtain ⟨hshape, hnv3⟩ := h
  intro hwv'
  by_cases hnv' : (Stream.step true s i).nv = true
  · rcases nv_step_true_or s i hnv' with hsnv | hrpl
    · rcases hchange with hm | ⟨hwv0, hnv0⟩
      · have hrpl : Stream.rpl true i = true := by
          have hm3 : modeOf true i = 3 := by rw [hm]; exact hnv3 hsnv
          have hbeq : (modeOf true i == 3) = true := by rw [hm3]; rfl
          rwa [modeOf_eq_three] at hbeq
        have hh := rpl_nv_wv s i hshape hrpl hnv'
        rw [hwv'] at hh
        exact Bool.noConfusion hh
      · exact Bool.noConfusion (hnv0 ▸ hsnv)
    · have hh := rpl_nv_wv s i hshape hrpl hnv'
      rw [hwv'] at hh
      exact Bool.noConfusion hh
  · simpa using hnv'

/-- **The mode-indexed shape invariant is preserved.** -/
theorem shapeModeOK_step (s : Stream.State) (i : Stream.Input) (pmode : Nat)
    (h : ShapeModeOK pmode s)
    (hchange : modeOf true i = pmode ∨ (s.wv = false ∧ s.nv = false)) :
    ShapeModeOK (modeOf true i) (Stream.step true s i) := by
  obtain ⟨hshape, hnv3⟩ := h
  refine ⟨shapeOK_step s i pmode ⟨hshape, hnv3⟩ hchange, ?_⟩
  intro hnv'
  rcases nv_step_true_or s i hnv' with hsnv | hrpl
  · rcases hchange with hm | ⟨hwv0, hnv0⟩
    · rw [hm]; exact hnv3 hsnv
    · exact Bool.noConfusion (hnv0 ▸ hsnv)
  · have hbeq : (modeOf true i == 3) = true := by rwa [modeOf_eq_three]
    exact of_decide_eq_true hbeq

/-- **`ShapeOK` is preserved under the relaxed mode-change hypothesis**
(`LD = NV = 0`, orchestrator decision 2026-11-22d): `WV` is *not* needed.  A mode
change only has to exclude a live **second** slot; `NV' = 1` then comes from
`NV = 1` (excluded) or from a replay landing, and a replay landing forces
`WV' = 1` (`rpl_nv_wv`).  This is the form the chip-level premise uses, because
a settle-at-startup transmit stream legitimately holds `WV = 1` (reset defaults
to `TX` and the transmit branch prefetches: `src/md2_stream.v` ~130). -/
theorem shapeOK_step_nv (s : Stream.State) (i : Stream.Input) (pmode : Nat)
    (h : ShapeModeOK pmode s)
    (hchange : modeOf true i = pmode ∨ (s.ld = false ∧ s.nv = false)) :
    ShapeOK (Stream.step true s i) := by
  obtain ⟨hshape, hnv3⟩ := h
  intro hwv'
  by_cases hnv' : (Stream.step true s i).nv = true
  · rcases nv_step_true_or s i hnv' with hsnv | hrpl
    · rcases hchange with hm | ⟨-, hnv0⟩
      · have hrpl : Stream.rpl true i = true := by
          have hm3 : modeOf true i = 3 := by rw [hm]; exact hnv3 hsnv
          have hbeq : (modeOf true i == 3) = true := by rw [hm3]; rfl
          rwa [modeOf_eq_three] at hbeq
        have hh := rpl_nv_wv s i hshape hrpl hnv'
        rw [hwv'] at hh
        exact Bool.noConfusion hh
      · exact Bool.noConfusion (hnv0 ▸ hsnv)
    · have hh := rpl_nv_wv s i hshape hrpl hnv'
      rw [hwv'] at hh
      exact Bool.noConfusion hh
  · simpa using hnv'

/-- **The mode-indexed shape invariant survives the relaxed mode change**: the
`ShapeOK` half is `shapeOK_step_nv`, and the mode-indexed clause is vacuous
because a mode change with `LD = NV = 0` gives `NV' = 0`. -/
theorem shapeModeOK_step_nv (s : Stream.State) (i : Stream.Input) (pmode : Nat)
    (h : ShapeModeOK pmode s)
    (hchange : modeOf true i = pmode ∨ (s.ld = false ∧ s.nv = false)) :
    ShapeModeOK (modeOf true i) (Stream.step true s i) := by
  obtain ⟨hshape, hnv3⟩ := h
  refine ⟨shapeOK_step_nv s i pmode ⟨hshape, hnv3⟩ hchange, ?_⟩
  intro hnv'
  rcases nv_step_true_or s i hnv' with hsnv | hrpl
  · rcases hchange with hm | ⟨-, hnv0⟩
    · rw [hm]; exact hnv3 hsnv
    · exact Bool.noConfusion (hnv0 ▸ hsnv)
  · have hbeq : (modeOf true i == 3) = true := by rwa [modeOf_eq_three]
    exact of_decide_eq_true hbeq

/-- The state of the shape-breaking witness: a transmit stream holding a full
replay buffer (`WV = NV = 1`) with no current byte, at lane 3. -/
def wS5 : Stream.State := { wS with wv := true, nv := true, cv := false, ba := 3 }

/-- The transmit input of the witness: unfrozen, no advance. -/
def wI5 : Stream.Input := { wI with frz := false, adv := false }

/-- **`ShapeOK` breaks without the mode-change hypothesis**: a transmit cycle
consumes the first slot (`WV' = 0`) while the second stays valid (`NV' = 1`).
The pre-state is a transmit stream with `WV = NV = 1`, which the strengthened
quietness excludes at a mode change. -/
theorem shapeOK_break_witness :
    ShapeOK wS5 ∧ ¬ ShapeOK (Stream.step true wS5 wI5) := by
  constructor
  · unfold ShapeOK
    decide
  · unfold ShapeOK
    decide


def HeldLanding (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  (s.wv = false → s.nb = m.wb) ∧ (s.wv = true → s.nb = m.nb)

/-- The held-landing condition of the unfrozen step: no landing, or the landed
slot agrees (transmit writes `WB`, replay uses the pending word). -/
def HeldOK (cap : Bool) (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt) : Prop :=
  i.frzd = false ∨ (Stream.txMode cap i = true ∧ s.wb = m.wb) ∨
    (Stream.rpl cap i = true ∧ HeldLanding s m)

theorem heldLanding_frozen_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hld : s.ld = m.ld) (hwv : s.wv = m.wv)
    (hlds : s.ld = true) (hfzd : i.frzd = false) (hrpl : Stream.rpl cap i = true) :
    HeldLanding (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true) := by
  have hfrz0 := Stream.frozen_holds cap s i hfrz hreset hrew
  have hwvhold : (Stream.step cap s i).wv = s.wv := hfrz0.2.2.2.2.2.2.2.1
  have hmach := mach_frozen_landing cap s i m c hld hwv hrew
  have hm3 : (modeOf cap i == 3) = true := by rw [modeOf_eq_three]; exact hrpl
  constructor
  · intro hwv0
    have hsw : s.wv = false := by rw [← hwvhold]; exact hwv0
    have hnb : (Stream.step cap s i).nb = i.rdata := by
      rw [nb_frozen_landing cap s i hreset hfrz]
      rw [if_pos (by simp [hrpl, hlds, hfzd])]
    have hwb : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb = i.rdata := by
      rw [hmach]
      show (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb) = i.rdata
      rw [if_pos (by simp [hlds, hfzd, hsw])]
    rw [hnb, hwb]
  · intro hwv1
    have hsw : s.wv = true := by rw [← hwvhold]; exact hwv1
    have hnb : (Stream.step cap s i).nb = i.rdata := by
      rw [nb_frozen_landing cap s i hreset hfrz]
      rw [if_pos (by simp [hrpl, hlds, hfzd])]
    have hnb' : (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).nb = i.rdata := by
      rw [hmach]
      show (if s.ld && !i.frzd && ((modeOf cap i == 3) && s.wv) then i.rdata else m.nb) = i.rdata
      rw [if_pos (by simp [hlds, hfzd, hm3, hsw])]
    rw [hnb, hnb']

theorem nv_step_unfrozen_ab (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true)
    (hfrz : i.frz = false) (hcap : cap = true) (h : AbsRelB cap s m) :
    (Stream.step cap s i).nv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).nv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hnveq : s.nv = m.nv := hbuf.nv_eq hcap
  have hwveq : s.wv = m.wv := hbuf.wv_eq
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hnveq, hwveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hnveq, hwveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hnveq, hwveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hnveq, hwveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> smash

macro "sb_simp" : tactic =>
  `(tactic| simp only [Stream.step, Stream.posNext, Stream.bidxNext, Stream.baNext,
    Stream.curNext, Stream.cvNext, Stream.wbNext, Stream.wvNext, Stream.rqNext,
    Stream.ldNext, Stream.pendNext, Stream.pvNext, Stream.starvedNext, Stream.nbNext,
    Stream.nvNext, Stream.advT, Stream.starveTx, Stream.starveRx, Stream.starveEvent,
    Stream.push, Stream.done, Stream.bitin, Stream.fl, Stream.last, Stream.occupied,
    Stream.landing, Machine.streamNext, Machine.Util.streamAuto, absIn, beq_nat, bne_nat,
    lane_val, cfgStart_bv, bv_id] at *)

set_option maxHeartbeats 4000000 in
theorem wb_step_unfrozen_guarded (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hc : cap = true) (h : AbsRelB cap s m)
    (hok : s.ld = true → HeldOK cap s i m)
    (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hwv' : (Stream.step cap s i).wv = true) :
    (Stream.step cap s i).wb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).wb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := hbuf.wv_eq
  have hwbv : s.wv = true → s.wb = m.wb := hbuf.wb_of_wv
  have hnbv : s.nv = true → s.nb = m.nb := hbuf.nb_of_nv hc
  have hnveq : s.nv = m.nv := hbuf.nv_eq hc
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · -- replay
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hlds : s.ld = true <;>
      by_cases hfzd : i.frzd = true <;> by_cases hap : i.replayApply = true <;>
      by_cases hwv : s.wv = true <;> by_cases hnv : s.nv = true <;>
      simp_all [HeldOK, HeldLanding, hwbv, hnbv, hnveq, hok, hm]
  · -- capture
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hlds : s.ld = true <;>
      by_cases hcp : i.capPush = true <;> by_cases hwv : s.wv = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hpv' : m.pv = true <;>
      by_cases hg : i.gnt = true <;>
      simp_all [HeldOK, HeldLanding, hwbv, hnbv, hnveq, hok, hm]
  · -- receive
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hwv : s.wv = true <;>
      simp_all [HeldOK, HeldLanding, hwbv, hnbv, hnveq, hok, hm]
  · -- transmit
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hlds : s.ld = true <;>
      by_cases hfzd : i.frzd = true <;> by_cases hcv' : s.cv = true <;>
      by_cases hwv : s.wv = true <;> by_cases hb7 : s.bidx.toNat = 7 <;>
      by_cases hln : (BitVec.truncate 2 s.ba == 3) = true <;>
      simp_all [HeldOK, HeldLanding, hwbv, hnbv, hnveq, hok, hm]

set_option maxHeartbeats 4000000 in
theorem nb_step_unfrozen_guarded (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hc : cap = true) (h : AbsRelB cap s m)
    (hok : s.ld = true → HeldOK cap s i m)
    (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hnv' : (Stream.step cap s i).nv = true) :
    (Stream.step cap s i).nb =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).nb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hnbv : s.nv = true → s.nb = m.nb := hbuf.nb_of_nv hc
  have hnveq : s.nv = m.nv := hbuf.nv_eq hc
  have hwveq : s.wv = m.wv := hbuf.wv_eq
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · -- replay
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hlds : s.ld = true <;>
      by_cases hfzd : i.frzd = true <;> by_cases hap : i.replayApply = true <;>
      by_cases hwv : s.wv = true <;> by_cases hnv : s.nv = true <;>
      simp_all [HeldOK, HeldLanding, hnbv, hnveq, hwveq, hok, hm]
  · -- capture
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hwv : s.wv = true <;>
      by_cases hnv : s.nv = true <;>
      simp_all [HeldOK, HeldLanding, hnbv, hnveq, hok, hm]
  · -- receive
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hwv : s.wv = true <;>
      by_cases hnv : s.nv = true <;>
      simp_all [HeldOK, HeldLanding, hnbv, hnveq, hok, hm]
  · -- transmit
    sb_simp
    by_cases hrew : i.rewind = true <;> by_cases hwv : s.wv = true <;>
      by_cases hnv : s.nv = true <;>
      simp_all [HeldOK, HeldLanding, hnbv, hnveq, hok, hm]

set_option maxHeartbeats 4000000 in
theorem wb_nb_unfrozen_capF (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hc : cap = false)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = false) :
    (Stream.step cap s i).wb = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).wb ∧
    (Stream.step cap s i).nb = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).nb := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwbf : s.wb = m.wb := (hbuf.2.1 hc).1
  have hwvf : s.wv = m.wv := (hbuf.2.1 hc).2.1
  have hnbf : s.nb = m.nb := (hbuf.2.1 hc).2.2
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · exfalso; simp [Stream.rpl, hc] at hrpl
  · exfalso; simp [Stream.cen, hc] at hcen
  · refine ⟨?_, ?_⟩ <;> (sb_simp; by_cases hrew : i.rewind = true <;> simp_all [hwbf, hwvf, hnbf])
  · refine ⟨?_, ?_⟩ <;> (sb_simp; by_cases hrew : i.rewind = true <;>
      by_cases hlds : s.ld = true <;> by_cases hfzd : i.frzd = true <;> simp_all [hwbf, hwvf, hnbf])

set_option maxHeartbeats 1600000 in
theorem wv_step_unfrozen_ab (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).wv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).wv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwv : s.wv = m.wv := hbuf.wv_eq
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  have hlane : (BitVec.truncate 2 s.ba == 3) = (m.ba.toNat % 4 == 3) := lane_three s m hba
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · have hcap : cap = true := (Stream.rpl_facts cap i hrpl).1
    have hnveq : s.nv = m.nv := hbuf.nv_eq hcap
    ssimp
    simp only [hwv, hnveq, hld, hreset, hfrz, hm, hend, bv_id, hcap]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hap : i.replayApply = true <;> by_cases hfz : i.frzd = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hnv' : s.nv = true <;> smash
  · ssimp
    simp only [hwv, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwv, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwv, hld, hreset, hfrz, hm, hend, bv_id]
    by_cases hrew : i.rewind = true <;> by_cases hld' : s.ld = true <;>
      by_cases hfz : i.frzd = true <;> by_cases hcv' : s.cv = true <;>
      by_cases hwv' : s.wv = true <;> by_cases hb7 : s.bidx.toNat = 7 <;> smash
/-- A frozen landing in transmit mode writes `WB` in both readings, giving the
`HeldOK` transmit fact for the next cycle. -/
theorem wb_frozen_tx_landing (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hld : s.ld = m.ld) (hwv : s.wv = m.wv)
    (htx : Stream.txMode cap i = true) (hlds : s.ld = true) (hfzd : i.frzd = false) :
    (Stream.step cap s i).wb =
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) true).wb := by
  have hmz : (modeOf cap i == 3) = false := by
    rw [modeOf_eq_three]
    unfold Stream.txMode at htx
    simp_all
  rw [wb_frozen_landing cap s i hreset hfrz, if_pos (by simp [htx, hlds, hfzd])]
  have hmach := mach_frozen_landing cap s i m c hld hwv hrew
  rw [hmach]
  show i.rdata = (if s.ld && !i.frzd && !((modeOf cap i == 3) && s.wv) then i.rdata else m.wb)
  rw [if_pos (by simp [hlds, hfzd, hmz])]
theorem no_overlap_step (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hno : ¬ (s.rq = true ∧ s.ld = true)) :
    ¬ ((Stream.step cap s i).rq = true ∧ (Stream.step cap s i).ld = true) := by
  intro h
  sb_simp
  by_cases hres : i.resetN = true <;> by_cases hrew : i.rewind = true <;>
    by_cases hfrz : i.frz = true <;> by_cases hrq : s.rq = true <;>
    by_cases hld : s.ld = true <;> by_cases hg : i.gnt = true <;>
    by_cases hend : Stream.endC s i = true <;> by_cases hrpl : Stream.rpl cap i = true <;>
    by_cases hcen : Stream.cen cap i = true <;> by_cases htx : Stream.txMode cap i = true <;>
    by_cases hwv : s.wv = true <;> by_cases hnv : s.nv = true <;> simp_all

theorem bufRel_step_unfrozen_guarded (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (h : AbsRelB cap s m)
    (hok : s.ld = true → HeldOK cap s i m)
    (hreset : i.resetN = true) (hfrz : i.frz = false) :
    BufRel cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false) := by
  have h0 : AbsRelB cap s m := h
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wv_step_unfrozen_ab cap s i m hreset hfrz h0
    · exact nv_step_unfrozen_ab cap s i m hreset hfrz hc h0
    · intro hwv'
      exact wb_step_unfrozen_guarded cap s i m hc h0 hok hreset hfrz hwv'
    · intro hnv'
      exact nb_step_unfrozen_guarded cap s i m hc h0 hok hreset hfrz hnv'
  · intro hc
    obtain ⟨hwb, hnb⟩ := wb_nb_unfrozen_capF cap s i m hc h0 hreset hfrz
    exact ⟨hwb, wv_step_unfrozen_ab cap s i m hreset hfrz h0, hnb⟩
  · exact no_overlap_step cap s i hbuf.2.2

theorem buf_step (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hshape : ShapeOK s)
    (hldmode : s.ld = true → Stream.txMode cap i = true ∨ Stream.rpl cap i = true)
    (hok : s.ld = true → HeldOK cap s i m)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) i.frz) := by
  obtain ⟨ha, hrx, hce, hla⟩ := hside
  by_cases hfrz : i.frz = true
  · rw [hfrz]
    by_cases hrew : i.rewind = true
    · exact frozen_rel_landing_rewind_flush cap s i m (cfgOf i) h hreset hfrz hrew
        (cfgStart_bv i).symm hldmode ha hrx hce hla
    · have hrf : i.rewind = false := by simpa using hrew
      exact frozen_rel_landing_flush cap s i m (cfgOf i) h hreset hfrz hrf hldmode hshape
        ha hrx hce hla
  · have hf : i.frz = false := by simpa using hfrz
    rw [hf]
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
      abs_step_unfrozen cap s i m hreset hf h
    exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10,
      bufRel_step_unfrozen_guarded cap s i m h hok hreset hf⟩

theorem bufRelX_step (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (h : AbsRelB cap s m)
    (hb : BufRelX cap s m) (hreset : i.resetN = true)
    (hslot : s.ld = true → i.frzd = true ∨ Stream.txMode cap i = true ∨
      (Stream.rpl cap i = true ∧ s.wv = true))
    (hfresh : s.ld = true → i.frzd = false) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) i.frz) := by
  by_cases hfrz : i.frz = true
  · rw [hfrz]
    by_cases hrew : i.rewind = true
    · exact bufRelX_step_frozen_landing_rewind cap s i m (cfgOf i) h hb hreset hfrz hrew hslot
    · have hrf : i.rewind = false := by simpa using hrew
      exact bufRelX_step_frozen_landing cap s i m (cfgOf i) h hb hreset hfrz hrf hslot
  · have hf : i.frz = false := by simpa using hfrz
    rw [hf]
    exact bufRelX_step_unfrozen cap s i m hreset hf hfresh h hb

theorem bufRelX_step_abs (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (h : AbsRelB cap s m)
    (hb : BufRelX cap s m) (hreset : i.resetN = true)
    (hslot : s.ld = true → i.frzd = true ∨ Stream.txMode cap i = true ∨
      (Stream.rpl cap i = true ∧ s.wv = true))
    (hfresh : s.ld = true → i.frzd = false)
    (hshape : ShapeOK s)
    (hldmode : s.ld = true → Stream.txMode cap i = true ∨ Stream.rpl cap i = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false) :
    BufRelX cap (Stream.step cap s i) (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) i.frz) ∧
    AbsRelB cap (Stream.step cap s i) (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) i.frz) := by
  have h0 : AbsRelB cap s m := h
  refine ⟨bufRelX_step cap s i m h0 hb hreset hslot hfresh, ?_⟩
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  obtain ⟨ha, hrx, hce, hla⟩ := hside
  by_cases hfrz : i.frz = true
  · rw [hfrz]
    by_cases hrew : i.rewind = true
    · exact frozen_rel_landing_rewind_flush cap s i m (cfgOf i) h0 hreset hfrz hrew
        (cfgStart_bv i).symm hldmode ha hrx hce hla
    · have hrf : i.rewind = false := by simpa using hrew
      exact frozen_rel_landing_flush cap s i m (cfgOf i) h0 hreset hfrz hrf hldmode hshape
        ha hrx hce hla
  · have hf : i.frz = false := by simpa using hfrz
    rw [hf]
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
      abs_step_unfrozen cap s i m hreset hf h0
    exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10,
      (bufRelX_step_unfrozen cap s i m hreset hf hfresh h0 hb).toBufRel
        (no_overlap_step cap s i hbuf.2.2)⟩

/-- A `CAP = 0` stream has no second slot: its `NV` never changes. -/
theorem nv_step_cap_false (s : Stream.State) (i : Stream.Input) :
    (Stream.step false s i).nv = s.nv := by
  simp only [Stream.step, Stream.nvNext, Stream.rpl, cond_eq_ite]
  by_cases hfrz : i.frz = true <;> simp_all

/-- For a `CAP = 0` stream `ShapeOK` is just `NV = false`, which reset gives and
the step holds. -/
theorem shapeOK_step_cap_false (s : Stream.State) (i : Stream.Input) (h : s.nv = false) :
    ShapeOK (Stream.step false s i) := by
  intro _
  rw [nv_step_cap_false, h]

/-! ## The write-buffer facts for the assembler (round 2026-11-22c): `CapRel` and the guarded dbgHwb -/

def CapRel (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  cap = true → s.pv = true → s.wb = m.wb

/-- The replay-mode input template of the witnesses and the trace. -/
def capV0 : Stream.Input :=
  { resetN := true, frz := false, frzd := false, capEn := false, capPush := false, capRec := 0,
    replayEn := true, replayApply := false, replayLate := false, cfgMode := false, cfgMsb := false,
    cfgStart := 0, cfgLen := 0x100, cfgMark := 0, adv := false, rxWe := false, rxBit := false,
    rewind := false, flush := false, clrStarved := false, gnt := false, rdata := 0 }

/-- **One-step witness: `CapRel` is not preserved.**  An `apply` with an empty
second slot (`NV = 0`) publishes the first slot from the two readings' stale
`NB`s, so `WB` diverges while `PV` stays set (the state-level clause fails even
in replay mode; the capture-relevant instance is the reachable trace below). -/
def capS2 : Stream.State :=
  { wS with wb := 7, wv := true, nb := 7, nv := false, pv := true, ld := false, cv := false, rq := false }

def capM2 : Machine.StreamSt := { abs capS2 with nb := 9 }

def capI2 : Stream.Input := { capV0 with replayApply := true }

theorem capRel_step_witness :
    AbsRelB true capS2 capM2 ∧ CapRel true capS2 capM2 ∧
    (Stream.step true capS2 capI2).pv = true ∧
    ¬ CapRel true (Stream.step true capS2 capI2)
      (Machine.streamNext (cfgOf capI2) (modeOf true capI2) capM2 (absIn true capS2 capI2) false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold AbsRelB BufRel
    decide
  · unfold CapRel
    decide
  · decide
  · unfold CapRel
    decide

/-! ### The capture-mode instance is reachable

Five cycles from reset: a served replay read, a frozen landing with a host
rewind (the word parks in `NB` vs `WB`, `WV`/`NV` cleared), a receive cycle that
completes a byte (`PV = 1`), then a capture cycle (`CEN`).  At that state
`PV = 1` and `WB` differs, so the mode-2 `wrWord` request would differ. -/

def capV1 : Stream.Input := { capV0 with gnt := true }
def capV2 : Stream.Input := { capV0 with frz := true, rewind := true, rdata := 1 }
def capV3 : Stream.Input := { capV0 with replayEn := false, cfgMode := true, frzd := true, rewind := true }
def capV4 : Stream.Input := { capV3 with frzd := false, rewind := false, rxWe := true, flush := true }
def capV5 : Stream.Input := { capV0 with replayEn := false, capEn := true, cfgMode := false }

def capSeq : Nat → Stream.Input
  | 0 => capV0
  | 1 => capV1
  | 2 => capV2
  | 3 => capV3
  | 4 => capV4
  | _ => capV5

def capCut (n : Nat) : Stream.State := Stream.stateAt true capSeq Stream.resetState n

def capM : Nat → Machine.StreamSt
  | 0 => (default : Machine.StreamSt)
  | k + 1 => Machine.streamNext (cfgOf (capSeq k)) (modeOf true (capSeq k)) (capM k)
      (absIn true (capCut k) (capSeq k)) (capSeq k).frz

theorem capWb_reachable_witness :
    (capCut 5).pv = true ∧ (capM 5).pv = true ∧ (capM 5).wb ≠ (capCut 5).wb ∧
    modeOf true capV5 = 2 := by
  decide

/-! ## `dbgHwb`: the guarded form is what the consumers use -/

/-- The machine's first replay slot agrees with the cut's while the cut's `WV`
is set — the form `apply_bridge`/`rlv_value_of` actually consume, since the cut's
`replayValid` is `RPL && WV` and `Debug.Ctrl.apply` conjoins `valid`. -/
theorem dbgHwb_of_wv (cap : Bool) (s : Stream.State) (m : Machine.StreamSt)
    (h : AbsRelB cap s m) (hwv : s.wv = true) : m.wb = s.wb := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbuf⟩ := h
  exact (hbuf.wb_of_wv hwv).symm

/-- The same, guarded by the cut's `replayValid` (`RPL && WV`). -/
theorem dbgHwb_of_replayValid (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (h : AbsRelB cap s m)
    (hrv : Stream.replayValid cap s i = true) : m.wb = s.wb := by
  have hwv : s.wv = true := by
    unfold Stream.replayValid at hrv
    exact ((Bool.and_eq_true ..).mp hrv).2
  exact dbgHwb_of_wv cap s m h hwv

/-- The unguarded form is **false** at a reachable state: after the three-cycle
frozen landing of `frozen_landing_witness` (with `WV = 0`). -/
theorem dbgHwb_unguarded_false : wM3.wb ≠ (Stream.step true wS2 wV3).wb := by
  decide



/-! ## The mode-indexed capture invariant (round 2026-11-22d) -/

def CapModeOK (mode : Nat) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  (mode = 2 → s.ld = false) ∧ (mode = 2 → s.pv = true → s.wb = m.wb)

theorem capModeOK_reset (mode : Nat) :
    CapModeOK mode Stream.resetState (default : Machine.StreamSt) := by
  refine ⟨?_, ?_⟩ <;> simp [Stream.resetState]

/-- **`CapModeOK` is preserved** under the extended mode-quietness: a mode change
requires `PV = 0` in the current *and* next state (plus the idle flags
`LD = RQ = false`), and `AbsRelB` supplies the `PV` agreement the two readings
need. -/
theorem capModeOK_step (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg) (pmode : Nat)
    (h : AbsRelB cap s m) (hcap : CapModeOK pmode s m) (hreset : i.resetN = true)
    (hcfg : Machine.streamEnd c m = Machine.streamEnd (cfgOf i) m)
    (hchange : modeOf cap i = pmode ∨
      (s.pv = false ∧ (Stream.step cap s i).pv = false ∧ s.ld = false ∧ s.rq = false)) :
    CapModeOK (modeOf cap i) (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) i.frz) := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  have hpveq : s.pv = m.pv := hpv
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  refine ⟨?_, ?_⟩
  · -- LD is clear in capture
    intro hm2
    rcases hchange with hsame | ⟨hpv0, hpv0', hld0, hrq0⟩
    · have hm2' : pmode = 2 := by rw [← hsame]; exact hm2
      have hlds : s.ld = false := hcap.1 hm2'
      rcases mode_cases cap i with ⟨hm3, _, _, _, _⟩ | ⟨hm2c, hcen, _, _, _⟩ |
        ⟨hm1, _, _, _, _⟩ | ⟨hm0, _, _, _, _⟩
      · omega
      · sb_simp
        by_cases hfrz : i.frz = true <;> by_cases hrew : i.rewind = true <;> simp_all
      · omega
      · omega
    · sb_simp
      by_cases hfrz : i.frz = true <;> by_cases hrew : i.rewind = true <;> simp_all
  · -- WB agrees while PV
    intro hm2 hpv'
    rcases hchange with hsame | ⟨hpv0, hpv0', hld0, hrq0⟩
    · have hm2' : pmode = 2 := by rw [← hsame]; exact hm2
      have hlds : s.ld = false := hcap.1 hm2'
      have hwbs : s.pv = true → s.wb = m.wb := hcap.2 hm2'
      rcases mode_cases cap i with ⟨hm3, _, _, _, _⟩ | ⟨hm2c, hcen, _, _, _⟩ |
        ⟨hm1, _, _, _, _⟩ | ⟨hm0, _, _, _, _⟩
      · omega
      · sb_simp
        by_cases hfrz : i.frz = true <;> by_cases hrew : i.rewind = true <;>
          by_cases hpush : i.capPush = true <;> by_cases hpv : s.pv = true <;>
          by_cases hg : i.gnt = true <;> simp_all [bv_id, hpveq, hend, hcfg]
      · omega
      · omega
    · exact absurd hpv' (by rw [hpv0']; simp)

/-- **The consumer form**: under the mode-change fact of the cycle that produced
`s` (unchanged mode, or `PV = false`), a capture cycle with `PV` set has the
same `WB` in the machine and the cut. -/
theorem contentsWb_of_capModeOK (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (pmode : Nat) (h : CapModeOK pmode s m)
    (hchange : modeOf cap i = pmode ∨ s.pv = false)
    (hm2 : modeOf cap i = 2) (hpv : s.pv = true) :
    m.wb = s.wb := by
  rcases hchange with hsame | hpv0
  · have hm2' : pmode = 2 := by rw [← hsame]; exact hm2
    exact (h.2 hm2' hpv).symm
  · exact absurd hpv (by rw [hpv0]; simp)

/-- **The reachable witness is excluded by the extended discipline.**  Its last
(capture) cycle changes the mode from receive (1) to capture (2) with the
incoming state's `PV` set, so `hchange` fails. -/
theorem capWb_hchange_excluded :
    ¬ (modeOf true capV5 = modeOf true capV4 ∨
        ((capCut 5).pv = false ∧ (Stream.step true (capCut 5) capV5).pv = false ∧
          (capCut 5).ld = false ∧ (capCut 5).rq = false)) := by
  decide


end StreamBuf

end Metronome.Bridge
