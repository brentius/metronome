import Metronome.SpiPins
import Metronome.HostRead
import Metronome.HostMap

/-!
# Pin-level transactions: writes to the host map, reads to MISO

`Metronome.SpiPins` closes the pin layer for the *write* path: a mode-0 SPI
write transaction on the pins (`[0x02, AH, AL, d0..]`) produces one
`HostCmd` write strobe per data byte with the clocked byte as data and `{AH, AL}+j`
as address.  `Metronome.HostMap` proves that the host write-decode enables
exactly the map's target for a strobe, and `Metronome.HostRead` proves the read
response path (a requested `rd_val` is loaded into `TX` two cycles later and
clocked out MSB first).

This module composes them at the pin level:

* **Writes.**  At every strobe of a pin-level write transaction exactly one host
  map target is enabled, and it is the one `HostMap.selList` marks for `{AH, AL}+j`:
  a register byte, a program-memory byte of core 0 or 1, the data RAM, the
  configuration window when the byte is live, and nothing for a read-only or
  unmapped address.  The window table is `sel_prog`/`sel_data`/`sel_cfg`/`sel_reg`.
* **Reads.**  A pin-level read transaction (`[0x03, AH, AL, dummy..]`) drives the
  `Metronome.HostRead` machine: the byte clocked out in data slot `k` is the
  `rd_val` sampled in slot `k`'s request cycle, and the address register in that
  cycle is `{AH, AL}+k`.  So each slot carries the response to its own address.

## What the two machines share

`HostRead.State` keeps the nine command-machine registers and adds `tx` and
`rackv`.  `Agrees` relates a read state to a command state on the nine shared
registers, and `agrees_stateAt` shows that a read trace projects onto the
command trace of the same pin inputs.  That is how the address phase (which is
the command machine's business) is reused instead of reproved; the `cmd`
history variable of `Metronome.HostCmd` is irrelevant to every next-state
equation (`phaseNext_cmd` .. `rackNext_cmd`).

## Timing

The pin model samples one level per clock, so an SCK phase covers at least one
cycle: `2 ≤ period` for the byte framing of `Metronome.SpiPins`.  The read path
needs one cycle more than that: the request pulse of the eighth edge occupies
the cycle after it, the acknowledge latches one cycle later and `TX` loads in
the cycle after that, so the load must precede the next slot's first edge:
`3 ≤ period`.  `Metronome.HostRead`'s own `read_burst_index` states `10`
because it indexes a fixed ten-cycle slot grid; this file indexes the actual
clock (`srAt`) instead, and `3` is then exactly what the load-before-edge
argument needs.  SPEC_V2 §9's clk/16 gives `period ≥ 16`, which satisfies both.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Metronome.HostPins

open Metronome
open Metronome.SpiPins
open Metronome.HostRead

/-! ## The read machine projects onto the command machine

`HostRead.State.toHostCmd` keeps the nine shared registers; `cmd` is the command
machine's history variable.  The nine next-state equations never read `cmd`, so
the projection of a read step is the command step of any history value. -/

/-- Two states agree on the nine registers the two machines share. -/
def Agrees (r : HostRead.State) (c : HostCmd.State) : Prop :=
  r.phase = c.phase ∧ r.bitc = c.bitc ∧ r.rx = c.rx ∧ r.isRd = c.isRd ∧ r.addr = c.addr ∧
    r.wr = c.wr ∧ r.wdata = c.wdata ∧ r.rd = c.rd ∧ r.rack = c.rack

theorem phaseNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.phaseNext { s with cmd := c } i = HostCmd.phaseNext s i := by
  cases s; rfl

theorem bitcNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.bitcNext { s with cmd := c } i = HostCmd.bitcNext s i := by
  cases s; rfl

theorem rxNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.rxNext { s with cmd := c } i = HostCmd.rxNext s i := by
  cases s; rfl

theorem isRdNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.isRdNext { s with cmd := c } i = HostCmd.isRdNext s i := by
  cases s; rfl

theorem addrNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.addrNext { s with cmd := c } i = HostCmd.addrNext s i := by
  cases s; rfl

theorem wrNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.wrNext { s with cmd := c } i = HostCmd.wrNext s i := by
  cases s; rfl

theorem wdataNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.wdataNext { s with cmd := c } i = HostCmd.wdataNext s i := by
  cases s; rfl

theorem rdNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.rdNext { s with cmd := c } i = HostCmd.rdNext s i := by
  cases s; rfl

theorem rackNext_cmd (s : HostCmd.State) (i : HostCmd.Input) (c : BitVec 8) :
    HostCmd.rackNext { s with cmd := c } i = HostCmd.rackNext s i := by
  cases s; rfl

theorem toHostCmd_with (r : HostRead.State) (d e : BitVec 8) :
    { r.toHostCmd d with cmd := e } = r.toHostCmd e := by
  cases r; rfl

theorem toHostCmd_agrees (r : HostRead.State) (c : HostCmd.State) (h : Agrees r c) :
    r.toHostCmd c.cmd = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases r; cases c
  simp_all [HostRead.State.toHostCmd]

/-- One read step projects onto one command step: the nine shared registers
follow `HostCmd.step`, whatever the command history variable. -/
theorem agrees_step (r : HostRead.State) (c : HostCmd.State) (i : HostRead.Input)
    (h : Agrees r c) :
    Agrees (HostRead.step r i) (HostCmd.step c i.toHostCmd) := by
  have hc : r.toHostCmd c.cmd = c := toHostCmd_agrees r c h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.phaseNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, phaseNext_cmd, hc]
  · show HostCmd.bitcNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.bitcNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, bitcNext_cmd, hc]
  · show HostCmd.rxNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.rxNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, rxNext_cmd, hc]
  · show HostCmd.isRdNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.isRdNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, isRdNext_cmd, hc]
  · show HostCmd.addrNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.addrNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, addrNext_cmd, hc]
  · show HostCmd.wrNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.wrNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, wrNext_cmd, hc]
  · show HostCmd.wdataNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.wdataNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, wdataNext_cmd, hc]
  · show HostCmd.rdNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.rdNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, rdNext_cmd, hc]
  · show HostCmd.rackNext (r.toHostCmd 0#8) i.toHostCmd = HostCmd.rackNext c i.toHostCmd
    rw [← toHostCmd_with r c.cmd 0#8, rackNext_cmd, hc]

/-! ## The read machine's input trace of the pins

The read machine's inputs are the command machine's seven plus the register-read
value `rdVal` and the data-RAM landing byte `hlandD`. -/

/-- The `HostRead` input trace of a raw pin trace.  The first seven fields are
`Metronome.SpiPins.hostInputs` (the synchronised pins plus the two data-RAM
inputs); `rdVal` is the host register-read value of the cycle and `hlandD` the
byte a data-RAM landing delivers. -/
def readInputs (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) : Nat → HostRead.Input :=
  fun n =>
    let w := SpiPins.hostInputs raws rst initial rdData hland n
    ⟨w.resetN, w.sck, w.sckPrev, w.csN, w.mosi, w.rdData, rdVal n, w.hland, hlandD n⟩

/-- The command-machine view of the read inputs is `SpiPins.hostInputs`. -/
theorem readInputs_toHostCmd (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).toHostCmd
      = SpiPins.hostInputs raws rst initial rdData hland n := rfl

@[simp] theorem readInputs_resetN (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).resetN = rst n := rfl

@[simp] theorem readInputs_csN (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).csN
      = SpiPins.csN (SpiPins.syncAt (SpiPins.pinInputs raws rst) initial n) := rfl

@[simp] theorem readInputs_hland (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).hland = hland n := rfl

@[simp] theorem readInputs_rdData (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).rdData = rdData n := rfl

@[simp] theorem readInputs_rdVal (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (readInputs raws rst initial rdData rdVal hland hlandD n).rdVal = rdVal n := rfl

/-- The read machine's `SR` is the command machine's `SR` of the same pins. -/
theorem readInputs_sr (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    HostRead.sr (readInputs raws rst initial rdData rdVal hland hlandD n)
      = HostCmd.sr (SpiPins.hostInputs raws rst initial rdData hland n) := rfl

/-- The read machine's state projects onto the command machine's at every
cycle of the pin trace. -/
theorem agrees_stateAt (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    Agrees (HostRead.stateAt (readInputs raws rst initial rdData rdVal hland hlandD)
        HostRead.resetState n)
      (HostCmd.stateAt (SpiPins.hostInputs raws rst initial rdData hland)
        HostCmd.resetState n) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [HostRead.stateAt_succ, HostCmd.stateAt_succ]
    exact agrees_step _ _ _ ih

/-! ## The one-step fields of the read request and the response slot

`rd` is a one-cycle pulse (the cycle after the completing edge of an `ST_AL` or
`ST_DATA` byte of a read); `rack` is set in the cycle after a pulse and cleared
in the cycle after that.  Both equations are the RTL's, stated on the
specification's definitions. -/

theorem rd_step (s : HostCmd.State) (i : HostCmd.Input) :
    (HostCmd.step s i).rd = (i.resetN && !i.csN && HostCmd.completing s i &&
      (s.phase == HostCmd.ST_AL || s.phase == HostCmd.ST_DATA) && s.isRd) := by
  simp [HostCmd.step, HostCmd.rdNext]

theorem rack_step (s : HostCmd.State) (i : HostCmd.Input) :
    (HostCmd.step s i).rack = (if i.resetN then s.rd && !i.rdData else false) := by
  simp [HostCmd.step, HostCmd.rackNext]

/-- The read machine's acknowledge latch: set by a pending request, cleared the
cycle after it. -/
theorem rack_step_read (s : HostRead.State) (i : HostRead.Input) :
    (HostRead.step s i).rack = (if i.resetN then s.rd && !i.rdData else false) := by
  show HostCmd.rackNext (s.toHostCmd 0#8) i.toHostCmd = _
  rw [HostCmd.rackNext]
  by_cases h : i.resetN <;> simp [h]

/-! ## A byte of a read slot at pin spacing

`HostRead.read_byte_msb` states the eight samples of a byte for eight
*consecutive* `SR` cycles.  A pin clock leaves idle cycles between the edges
(`period ≥ 2`), so the byte has to be clocked edge by edge here: each edge
shifts, the idle cycles in between frame the state (`sendingN_frame_range`), and
the eighth edge leaves an `AfterByte`. -/

/-- `SendingN` holds across an idle cycle. -/
theorem sendingN_frame (t : HostRead.State) (i : HostRead.Input) (a : BitVec 16)
    (b : BitVec 8) (n : Nat) (h : HostRead.SendingN t a b n)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hnosr : HostRead.sr i = false)
    (hnoack : HostRead.ack t i = false) : HostRead.SendingN (HostRead.step t i) a b n := by
  obtain ⟨hphase, hisrd, hbitc, htx, haddr, hwr, hrd, hrack⟩ := h
  have hcomp : HostCmd.completing (t.toHostCmd 0#8) i.toHostCmd = false := by
    show (HostRead.sr i && ((t.toHostCmd 0#8).bitc == 7)) = false
    rw [hnosr]
    rfl
  have htx' : (HostRead.step t i).tx = HostRead.shifted b n := by
    rw [HostRead.tx_holds _ _ hreset hcs hnosr hnoack]
    exact htx
  refine ⟨?_, ?_, ?_, htx', ?_, ?_, ?_, ?_⟩
  · show HostCmd.phaseNext (t.toHostCmd 0#8) i.toHostCmd = HostCmd.ST_DATA
    rw [HostCmd.phaseNext]
    simp [hreset, hcs, hcomp, hphase]
  · show HostCmd.isRdNext (t.toHostCmd 0#8) i.toHostCmd = true
    rw [HostCmd.isRdNext]
    simp [hreset, hcomp, hisrd]
  · show HostCmd.bitcNext (t.toHostCmd 0#8) i.toHostCmd = BitVec.ofNat 3 n
    rw [HostCmd.bitcNext]
    simp [hreset, hcs, hnosr, hbitc]
  · rw [HostRead.addr_holds t i hwr hnoack hreset (by rw [hphase]; decide)
      (by rw [hphase]; decide), haddr]
  · show HostCmd.wrNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.wrNext]
    simp [hreset, hcs, hcomp]
  · show HostCmd.rdNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rdNext]
    simp [hreset, hcs, hcomp]
  · show HostCmd.rackNext (t.toHostCmd 0#8) i.toHostCmd = false
    rw [HostCmd.rackNext]
    simp [hreset, hrd]

/-- `SendingN` holds across a range of idle cycles. -/
theorem sendingN_frame_range (inputs : Nat → HostRead.Input) (initial : HostRead.State)
    (m n : Nat) (a : BitVec 16) (b : BitVec 8) (d : Nat) (hmn : m ≤ n)
    (h : HostRead.SendingN (HostRead.stateAt inputs initial m) a b d)
    (hgap : ∀ j, m ≤ j → j < n → (inputs j).resetN = true ∧ (inputs j).csN = false ∧
      HostRead.sr (inputs j) = false ∧
      HostRead.ack (HostRead.stateAt inputs initial j) (inputs j) = false) :
    HostRead.SendingN (HostRead.stateAt inputs initial n) a b d := by
  obtain ⟨e, rfl⟩ : ∃ e, n = m + e := ⟨n - m, by omega⟩
  induction e with
  | zero => simpa using h
  | succ e ih =>
    have hs := ih (by omega) (fun j hj hj' => hgap j hj (by omega))
    have hstep : HostRead.stateAt inputs initial (m + (e + 1)) =
        HostRead.step (HostRead.stateAt inputs initial (m + e)) (inputs (m + e)) := by
      rw [show m + (e + 1) = (m + e) + 1 from by omega]
      exact HostRead.stateAt_succ _ _ (m + e)
    rw [hstep]
    exact sendingN_frame _ _ _ _ _ hs (hgap (m + e) (by omega) (by omega)).1
      (hgap (m + e) (by omega) (by omega)).2.1
      (hgap (m + e) (by omega) (by omega)).2.2.1
      (hgap (m + e) (by omega) (by omega)).2.2.2

/-- Between two consecutive edges of a byte there is no edge at all: a cycle
strictly inside the byte that differs from the byte's eight edges is no `srAt`
index. -/
theorem not_edge_of_gap (first period base : Nat) (hp : 1 ≤ period) {j : Nat}
    (h1 : srAt first period base ≤ j) (h2 : j < srAt first period (base + 8))
    (hne : ∀ k, k < 8 → j ≠ srAt first period (base + k)) :
    ∀ k, j ≠ srAt first period k := by
  intro k hk
  rcases Nat.lt_or_ge k base with hlt | hge
  · have hlt' : srAt first period k < srAt first period base :=
      SpiPins.srAt_lt first period hp hlt
    omega
  · rcases Nat.lt_or_ge k (base + 8) with hlt2 | hge2
    · have hkb : base + (k - base) = k := by omega
      exact hne (k - base) (by omega) (by rw [hkb]; exact hk)
    · have hge' : srAt first period (base + 8) ≤ srAt first period k :=
        SpiPins.srAt_le first period hp hge2
      omega

/-- Eight `SR` edges of a read data byte, with idle gaps between them: the `TX`
samples are the byte's bits MSB first and the eighth edge leaves an
`AfterByte`.  The acknowledgement premise is `Metronome.HostRead`'s own: no
response lands while the byte is clocked. -/
theorem sending_byte_pins (ins : Nat → HostRead.Input) (t : HostRead.State)
    (first period base : Nat) (a : BitVec 16) (b : BitVec 8) (hp : 1 ≤ period)
    (h : HostRead.Sending (HostRead.stateAt ins t (srAt first period base)) a b)
    (hcyc : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      (ins j).resetN = true ∧ (ins j).csN = false)
    (hsr : ∀ k, k < 8 → HostRead.sr (ins (srAt first period (base + k))) = true)
    (hnosr : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      (∀ k, k < 8 → j ≠ srAt first period (base + k)) → HostRead.sr (ins j) = false)
    (hack : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      HostRead.ack (HostRead.stateAt ins t j) (ins j) = false) :
    (∀ k, k < 8 → bitAt (HostRead.stateAt ins t (srAt first period (base + k))).tx 7
        = bitAt b (7 - k)) ∧
      HostRead.AfterByte (HostRead.stateAt ins t (srAt first period (base + 7) + 1)) a b := by
  have mono : ∀ {x y : Nat}, x ≤ y → srAt first period x ≤ srAt first period y :=
    fun hxy => SpiPins.srAt_le first period hp hxy
  have monoLt : ∀ {x y : Nat}, x < y → srAt first period x < srAt first period y :=
    fun hxy => SpiPins.srAt_lt first period hp hxy
  have hofNat : ∀ k, k < 7 → (BitVec.ofNat 3 k : BitVec 3) ≠ 7 := by
    intro k hk hc
    have hk8 : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    have hv : (BitVec.ofNat 3 k).toNat = 7 := by rw [hc]; rfl
    simp [BitVec.ofNat, hk8] at hv
    omega
  have hsn : ∀ k, k < 8 → HostRead.SendingN (HostRead.stateAt ins t (srAt first period (base + k)))
      a b k := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      have hk7 : k < 7 := by omega
      have hprev := ih (by omega)
      have hge0 : srAt first period base ≤ srAt first period (base + k) := mono (by omega)
      have hlt0 : srAt first period (base + k) < srAt first period (base + 8) := monoLt (by omega)
      have hedge : HostRead.SendingN
          (HostRead.stateAt ins t (srAt first period (base + k) + 1)) a b (k + 1) := by
        rw [HostRead.stateAt_succ]
        refine HostRead.sending_step _ _ _ _ _ hprev (hcyc _ hge0 hlt0).1
          (hcyc _ hge0 hlt0).2 (hsr k (by omega)) (hack _ hge0 hlt0) ?_
        rw [hprev.bitc_eq]; exact hofNat k hk7
      have hidx : srAt first period (base + (k + 1)) =
          srAt first period (base + k) + 1 + (period - 1) := by
        rw [show base + (k + 1) = (base + k) + 1 from by omega, SpiPins.srAt_succ]
        omega
      rw [hidx]
      refine sendingN_frame_range ins t (srAt first period (base + k) + 1)
        (srAt first period (base + k) + 1 + (period - 1)) a b (k + 1) (by omega) hedge ?_
      intro j hj1 hj2
      have hjb : j < srAt first period (base + k + 1) := by
        rw [SpiPins.srAt_succ first period (base + k)]
        rw [Nat.add_assoc, show 1 + (period - 1) = period from by omega] at hj2
        exact hj2
      have hbase : srAt first period base ≤ srAt first period (base + k) := mono (by omega)
      have hge : srAt first period base ≤ j :=
        Nat.le_trans hbase (Nat.le_trans (Nat.le_succ _) hj1)
      have h8 : srAt first period (base + k + 1) ≤ srAt first period (base + 8) := mono (by omega)
      have hlt : j < srAt first period (base + 8) := Nat.lt_of_lt_of_le hjb h8
      refine ⟨(hcyc j hge hlt).1, (hcyc j hge hlt).2, ?_, hack j hge hlt⟩
      apply hnosr j hge hlt
      intro k' hk' heq
      rcases Nat.lt_or_ge k' (k + 1) with hlt' | hge'
      · have hle : srAt first period (base + k') ≤ srAt first period (base + k) :=
          mono (by omega)
        omega
      · have hle : srAt first period (base + k + 1) ≤ srAt first period (base + k') :=
          mono (by omega)
        omega
  refine ⟨?_, ?_⟩
  · intro k hk
    have htx := (hsn k hk).tx_eq
    rw [htx]
    exact HostRead.shifted_bit b ⟨k, hk⟩
  · have hge7 : srAt first period base ≤ srAt first period (base + 7) := mono (by omega)
    have hlt7 : srAt first period (base + 7) < srAt first period (base + 8) := monoLt (by omega)
    have h7 := hsn 7 (by omega)
    have hstep := HostRead.sending_finish (HostRead.stateAt ins t (srAt first period (base + 7)))
      (ins (srAt first period (base + 7))) a b h7
      (hcyc _ hge7 hlt7).1 (hcyc _ hge7 hlt7).2
      (hsr 7 (by omega)) (hack _ hge7 hlt7)
    rw [HostRead.stateAt_succ]
    exact hstep

/-- One read data slot at pin spacing: the byte's eight edges, then the request
pulse (`rd`), the acknowledge (`rack`) and the load of `TX`, then the idle
cycles up to the next slot.  The slot's byte is the `rd_val` of the request
cycle, and the next slot starts at `a + 1`. -/
theorem read_slot_pins (ins : Nat → HostRead.Input) (t : HostRead.State)
    (first period base : Nat) (a : BitVec 16) (b : BitVec 8) (hp : 3 ≤ period)
    (h : HostRead.Sending (HostRead.stateAt ins t (srAt first period base)) a b)
    (hcyc : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      (ins j).resetN = true ∧ (ins j).csN = false)
    (hsr : ∀ k, k < 8 → HostRead.sr (ins (srAt first period (base + k))) = true)
    (hnosr : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      (∀ k, k < 8 → j ≠ srAt first period (base + k)) → HostRead.sr (ins j) = false)
    (hack : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 8) →
      HostRead.ack (HostRead.stateAt ins t j) (ins j) = false)
    (hrdData : (ins (srAt first period (base + 7) + 1)).rdData = false) :
    (∀ k, k < 8 → bitAt (HostRead.stateAt ins t (srAt first period (base + k))).tx 7
        = bitAt b (7 - k)) ∧
      HostRead.AfterByte (HostRead.stateAt ins t (srAt first period (base + 7) + 1)) a b ∧
      HostRead.Sending (HostRead.stateAt ins t (srAt first period (base + 8))) (a + 1)
        ((ins (srAt first period (base + 7) + 1)).rdVal) := by
  have hp1 : 1 ≤ period := by omega
  have mono : ∀ {x y : Nat}, x ≤ y → srAt first period x ≤ srAt first period y :=
    fun hxy => SpiPins.srAt_le first period hp1 hxy
  have monoLt : ∀ {x y : Nat}, x < y → srAt first period x < srAt first period y :=
    fun hxy => SpiPins.srAt_lt first period hp1 hxy
  obtain ⟨hbits, hAB⟩ := sending_byte_pins ins t first period base a b hp1 h hcyc hsr hnosr hack
  -- the request cycle and its successors
  have hS8 : srAt first period (base + 8) = srAt first period (base + 7) + period := by
    rw [show base + 8 = (base + 7) + 1 from by omega]
    exact SpiPins.srAt_succ first period (base + 7)
  have hRlt : srAt first period (base + 7) + 1 < srAt first period (base + 8) := by
    rw [hS8]; omega
  have hR1lt : srAt first period (base + 7) + 2 < srAt first period (base + 8) := by
    rw [hS8]; omega
  have hRge : srAt first period base ≤ srAt first period (base + 7) + 1 :=
    Nat.le_trans (mono (by omega)) (Nat.le_succ _)
  have hR1ge : srAt first period base ≤ srAt first period (base + 7) + 2 := by omega
  -- no `SR` in the slot once the byte's edges are over
  have hnoEdge : ∀ i, srAt first period (base + 7) + 1 ≤ i → i < srAt first period (base + 8) →
      ∀ k, k < 8 → i ≠ srAt first period (base + k) := by
    intro i hi1 hi2 k hk heq
    have hle : srAt first period (base + k) ≤ srAt first period (base + 7) := mono (by omega)
    omega
  have hsrR : HostRead.sr (ins (srAt first period (base + 7) + 1)) = false :=
    hnosr _ hRge hRlt (hnoEdge _ (Nat.le_refl _) hRlt)
  have hsrR1 : HostRead.sr (ins (srAt first period (base + 7) + 2)) = false :=
    hnosr _ (by omega) hR1lt (hnoEdge _ (by omega) hR1lt)
  have hlandR : (ins (srAt first period (base + 7) + 1)).hland = false := by
    have hac := hack _ hRge hRlt
    rw [HostRead.ack] at hac
    cases hh : (ins (srAt first period (base + 7) + 1)).hland
    · rfl
    · rw [hh] at hac; simp at hac
  have hstep := HostRead.read_slot_step (HostRead.stateAt ins t (srAt first period (base + 7) + 1))
    (ins (srAt first period (base + 7) + 1)) (ins (srAt first period (base + 7) + 2)) a b hAB
    (hcyc _ hRge hRlt).1 (hcyc _ hRge hRlt).2 hsrR hlandR hrdData
    (hcyc _ hR1ge hR1lt).1 (hcyc _ hR1ge hR1lt).2 hsrR1
  -- the load lands two cycles after the request
  have hload : HostRead.Sending
      (HostRead.stateAt ins t (srAt first period (base + 7) + 3)) (a + 1)
      ((ins (srAt first period (base + 7) + 1)).rdVal) := by
    have e : HostRead.stateAt ins t (srAt first period (base + 7) + 3) =
        HostRead.step (HostRead.step (HostRead.stateAt ins t (srAt first period (base + 7) + 1))
          (ins (srAt first period (base + 7) + 1))) (ins (srAt first period (base + 7) + 2)) := by
      rw [show srAt first period (base + 7) + 3 = (srAt first period (base + 7) + 1) + 1 + 1
        from by omega, HostRead.stateAt_succ, HostRead.stateAt_succ]
    rw [e]
    exact hstep
  -- idle up to the next slot
  refine ⟨hbits, hAB, ?_⟩
  have hS8eq : srAt first period (base + 8) = srAt first period (base + 7) + 3 + (period - 3) := by
    rw [hS8]; omega
  rw [hS8eq]
  refine sendingN_frame_range ins t (srAt first period (base + 7) + 3)
    (srAt first period (base + 7) + 3 + (period - 3)) (a + 1)
    ((ins (srAt first period (base + 7) + 1)).rdVal) 0 (by omega) hload ?_
  intro j hj1 hj2
  have hjlt : j < srAt first period (base + 8) := by
    rw [show srAt first period (base + 7) + 3 + (period - 3) = srAt first period (base + 8)
      from by rw [hS8]; omega] at hj2
    exact hj2
  have hjge : srAt first period base ≤ j := Nat.le_trans hR1ge (by omega)
  refine ⟨(hcyc j hjge hjlt).1, (hcyc j hjge hjlt).2, ?_, hack j hjge hjlt⟩
  exact hnosr j hjge hjlt (hnoEdge j (by omega) hjlt)

/-- The command machine's input trace of the pins (abbreviation). -/
abbrev cins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (hland : Nat → Bool) : Nat → HostCmd.Input :=
  SpiPins.hostInputs raws rst initial rdData hland

/-- The read machine's input trace of the pins (abbreviation). -/
abbrev rins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) : Nat → HostRead.Input :=
  readInputs raws rst initial rdData rdVal hland hlandD

/-- The shared-register projections of `Agrees`. -/
theorem Agrees.phase_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.phase = c.phase := h.1

theorem Agrees.bitc_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.bitc = c.bitc := h.2.1

theorem Agrees.rx_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.rx = c.rx := h.2.2.1

theorem Agrees.isRd_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.isRd = c.isRd := h.2.2.2.1

theorem Agrees.addr_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.addr = c.addr := h.2.2.2.2.1

theorem Agrees.wr_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.wr = c.wr := h.2.2.2.2.2.1

theorem Agrees.wdata_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.wdata = c.wdata := h.2.2.2.2.2.2.1

theorem Agrees.rd_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.rd = c.rd := h.2.2.2.2.2.2.2.1

theorem Agrees.rack_eq {r : HostRead.State} {c : HostCmd.State} (h : Agrees r c) :
    r.rack = c.rack := h.2.2.2.2.2.2.2.2

theorem rins_toHostCmd (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (n : Nat) :
    (rins raws rst initial rdData rdVal hland hlandD n).toHostCmd
      = cins raws rst initial rdData hland n := rfl

theorem rins_sr (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (n : Nat) :
    HostRead.sr (rins raws rst initial rdData rdVal hland hlandD n)
      = HostCmd.sr (cins raws rst initial rdData hland n) := rfl

theorem rins_csN (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (n : Nat) :
    (rins raws rst initial rdData rdVal hland hlandD n).csN
      = (cins raws rst initial rdData hland n).csN := rfl

theorem rins_hland (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (n : Nat) :
    (rins raws rst initial rdData rdVal hland hlandD n).hland
      = (cins raws rst initial rdData hland n).hland := rfl

theorem rins_rdData (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (n : Nat) :
    (rins raws rst initial rdData rdVal hland hlandD n).rdData = rdData n := rfl

theorem rins_rdVal (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (n : Nat) :
    (rins raws rst initial rdData rdVal hland hlandD n).rdVal = rdVal n := rfl

/-- `rd` is low in a cycle whose predecessor raises no `SR`: the request pulse
only follows a completing edge. -/
theorem rd_false_of_no_sr (ins : Nat → HostRead.Input) (n : Nat) (hn : 1 ≤ n)
    (hsr : HostRead.sr (ins (n - 1)) = false) :
    (HostRead.stateAt ins HostRead.resetState n).rd = false := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsr' : HostCmd.sr (ins m).toHostCmd = false := hsr
  rw [HostRead.stateAt_succ]
  show HostCmd.rdNext ((HostRead.stateAt ins HostRead.resetState m).toHostCmd 0#8)
    (ins m).toHostCmd = false
  rw [HostCmd.rdNext]
  simp only [HostCmd.completing]
  rw [hsr']
  simp

/-- `Clean` for a byte whose acknowledgement bound is the byte's own window, not
the whole trace: the address phase of a read has no acknowledgement, but the
data phase that follows it does. -/
theorem clean_of_read_pins (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData hland : Nat → Bool) (first period base : Nat)
    (hp : 1 ≤ period) (hinit : initial = SpiPins.resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, k < 7 → pinRise raws (srAt first period (base + k)) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hack : ∀ j, j < srAt first period (base + 7) →
      HostCmd.ackBit (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState j)
        (cins raws rst initial rdData hland j) = false) :
    SpiPins.Clean (cins raws rst initial rdData hland) HostCmd.resetState first period base := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    exact hreset j
  · intro j _
    exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs j
  · intro k hk
    exact SpiPins.sr_of_pinRise raws rst initial rdData hland hinit hreset hcs _
      (hrise k hk)
  · intro j hb hlt hne
    by_cases hrise' : pinRise raws j = true
    · exfalso
      obtain ⟨k, hk⟩ := honly j hrise'
      have hmono : ∀ {x y : Nat}, x ≤ y → srAt first period x ≤ srAt first period y :=
        fun hxy => SpiPins.srAt_le first period hp hxy
      have hkb : base ≤ k := by
        rcases Nat.lt_or_ge k base with h' | h'
        · exfalso
          have h1 : srAt first period k < srAt first period base := SpiPins.srAt_lt first period hp h'
          omega
        · exact h'
      have hkt : k < base + 7 := by
        rcases Nat.lt_or_ge k (base + 7) with h' | h'
        · exact h'
        · exfalso
          have h1 : srAt first period (base + 7) ≤ srAt first period k := hmono h'
          omega
      exact hne (k - base) (by omega) (by
        rw [show base + (k - base) = k from by omega]
        exact hk)
    · have hpf : pinRise raws j = false := by simpa using hrise'
      exact SpiPins.sr_of_not_pinRise raws rst initial rdData hland hinit hreset hcs j hpf
  · intro j hj
    exact hack j hj

/-- `TX` stays zero until a response lands. -/
theorem shifted_zero (n : Nat) : HostRead.shifted (0 : BitVec 8) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [HostRead.shifted_succ, ih]; exact BitVec.zero_shiftLeft ..

theorem tx_zero (ins : Nat → HostRead.Input) (n : Nat)
    (hreset : ∀ j, j < n → (ins j).resetN = true)
    (hcs : ∀ j, j < n → (ins j).csN = false)
    (hack : ∀ j, j < n → HostRead.ack (HostRead.stateAt ins HostRead.resetState j) (ins j) = false) :
    (HostRead.stateAt ins HostRead.resetState n).tx = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [HostRead.stateAt_succ]
    show HostRead.txNext (HostRead.stateAt ins HostRead.resetState n) (ins n) = 0
    have hr := hreset n (by omega)
    have hc := hcs n (by omega)
    have ha := hack n (by omega)
    have hz : (HostRead.stateAt ins HostRead.resetState n).tx = 0 := ih
      (fun j hj => hreset j (by omega)) (fun j hj => hcs j (by omega))
      (fun j hj => hack j (by omega))
    rw [HostRead.txNext, hr, hc]
    simp only [Bool.not_true, ite_true, ite_false]
    by_cases hs : HostRead.sr (ins n) = true
    · by_cases hb : (HostRead.stateAt ins HostRead.resetState n).bitc = 7
      · rw [show ((HostRead.stateAt ins HostRead.resetState n).bitc != 7) = false from
          bne_eq_false_iff_eq.mpr hb]
        simp [ha, hz]
      · rw [show ((HostRead.stateAt ins HostRead.resetState n).bitc != 7) = true from
          bne_iff_ne.mpr hb]
        simp [hs, hz, shifted]
    · simp [hs, ha, hz]

/-- The completing `ST_AL` edge of a read transaction: the machine enters the
data bytes with the loaded address, raises the request pulse and keeps the
response slot empty. -/
theorem read_al_step (t : HostCmd.State) (i : HostCmd.Input) (a : BitVec 16) (r : BitVec 7)
    (h : SpiPins.Prog t HostCmd.ST_AL true 7 a r) (hrd : t.rd = false)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hsr : HostCmd.sr i = true)
    (hack : HostCmd.ackBit t i = false) :
    (HostCmd.step t i).phase = HostCmd.ST_DATA ∧ (HostCmd.step t i).rd = true ∧
      (HostCmd.step t i).addr = (a >>> 8).truncate 8 ++ HostCmd.byteIn t i ∧
      (HostCmd.step t i).bitc = 0 ∧ (HostCmd.step t i).wr = false ∧
      (HostCmd.step t i).isRd = true ∧ (HostCmd.step t i).rack = false := by
  obtain ⟨hphase, hisrd, hbitc, hwr, haddr, hrx⟩ := h
  simp only [HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn, HostCmd.ackBit,
    HostCmd.addrInc] at hphase hisrd hbitc hwr haddr hrx hrd hreset hcs hsr hack ⊢
  bv_decide


/-- The address phase of a pin-level read transaction: `0x03`, `AH`, `AL` on
eight rising edges each drive the command machine into `ST_DATA` with the loaded
address, raise the read request, and leave the response slot empty.  `TX` is
still zero, so the first data slot finds a `Sending` state carrying the byte the
request samples. -/
theorem read_open (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : SpiPins.Sync)
    (rdData : Nat → Bool) (rdVal : Nat → BitVec 8) (hland : Nat → Bool)
    (hlandD : Nat → BitVec 8) (first period nbytes : Nat) (bytes : Nat → BitVec 8)
    (hp : 3 ≤ period) (hf : 3 ≤ first) (hnb : 3 ≤ nbytes)
    (hinit : initial = SpiPins.resetState)
    (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, k < 8 * nbytes → pinRise raws (srAt first period k) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hbit : ∀ m k, m < 3 → k < 8 →
      bit (raws (srAt first period (8 * m + k) - 2)) 10 = bit8 (bytes m) (7 - k))
    (hcmd : bytes 0 = HostCmd.CMD_READ)
    (hackAddr : ∀ j, j < srAt first period (8 * 2 + 7) + 1 →
      HostCmd.ackBit (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState j)
        (cins raws rst initial rdData hland j) = false)
    (hnoland : ∀ j, j < srAt first period (8 * 3) →
      (rins raws rst initial rdData rdVal hland hlandD j).hland = false)
    (hrdData0 : (rins raws rst initial rdData rdVal hland hlandD
      (srAt first period (8 * 2 + 7) + 1)).rdData = false) :
    HostRead.AfterByte
        (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (srAt first period (8 * 2 + 7) + 1)) (bytes 1 ++ bytes 2) 0 ∧
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (srAt first period (8 * 2 + 7) + 1)).rd = true ∧
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (srAt first period (8 * 2 + 7) + 1)).addr = bytes 1 ++ bytes 2 ∧
      HostRead.Sending
        (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (srAt first period (8 * 3))) ((bytes 1 ++ bytes 2) + 1)
        ((rins raws rst initial rdData rdVal hland hlandD
          (srAt first period (8 * 2 + 7) + 1)).rdVal) := by
  have hp1 : 1 ≤ period := by omega
  have hp2 : 2 ≤ period := by omega
  -- the transaction's rising edges and the pin program
  have hsrAll : ∀ k, k < 8 * nbytes → HostCmd.sr (cins raws rst initial rdData hland
      (srAt first period k)) = true := by
    intro k hk
    exact SpiPins.sr_of_pinRise raws rst initial rdData hland hinit hreset hcs _ (hrise k hk)
  have hnosrAll : ∀ m, (∀ k, m ≠ srAt first period k) →
      HostCmd.sr (cins raws rst initial rdData hland m) = false := by
    intro m hm
    have hne : pinRise raws m ≠ true := by
      intro h
      obtain ⟨k, hk⟩ := honly m h
      exact hm k hk
    have hpf : pinRise raws m = false := by simpa using hne
    exact SpiPins.sr_of_not_pinRise raws rst initial rdData hland hinit hreset hcs m hpf
  have hmosi8 : ∀ m k, m < 3 → k < 8 →
      (cins raws rst initial rdData hland (srAt first period (8 * m + k))).mosi
        = bit8 (bytes m) (7 - k) := by
    intro m k hm hk
    have hge : 2 ≤ srAt first period (8 * m + k) := by
      have h1 : 2 ≤ srAt first period 0 := by
        rw [show srAt first period 0 = first from rfl]
        omega
      exact Nat.le_trans h1 (SpiPins.srAt_le first period hp1 (Nat.zero_le (8 * m + k)))
    exact SpiPins.mosi_pins_at raws rst initial rdData hland (srAt first period (8 * m + k))
      hge (hreset _) (hreset _) |>.trans (hbit m k hm hk)
  -- a bounded `Clean` for each address byte
  have hclean : ∀ base, base + 8 ≤ 8 * 2 + 8 → SpiPins.Clean
      (cins raws rst initial rdData hland) HostCmd.resetState first period base := by
    intro base hb
    refine clean_of_read_pins raws rst initial rdData hland first period base hp1 hinit hreset hcs
      (fun k _ => hrise (base + k) (by omega)) honly ?_
    intro j hj
    refine hackAddr j (Nat.lt_of_lt_of_le hj ?_)
    exact Nat.le_trans (SpiPins.srAt_le first period hp1 (by omega)) (Nat.le_succ _)
  -- the machine starts at the first edge in the reset state
  have hstart : Prog (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period 0)) HostCmd.ST_CMD false 0 (0 : BitVec 16) (0 : BitVec 7) := by
    have h0 : Prog HostCmd.resetState HostCmd.ST_CMD false 0 (0 : BitVec 16) (0 : BitVec 7) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hidle : ∀ m, m < first →
        (cins raws rst initial rdData hland m).resetN = true ∧
        (cins raws rst initial rdData hland m).csN = false ∧
        HostCmd.sr (cins raws rst initial rdData hland m) = false ∧
        HostCmd.ackBit (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState m)
          (cins raws rst initial rdData hland m) = false := by
      intro m hm
      refine ⟨hreset m, SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs m, ?_,
        hackAddr m (by
          have h1 : first ≤ srAt first period (8 * 2 + 7) := by
            have h0' : srAt first period 0 = first := rfl
            rw [← h0']
            exact SpiPins.srAt_le first period hp1 (by omega)
          omega)⟩
      apply hnosrAll
      intro k hk
      have h0' : srAt first period 0 = first := rfl
      have h1 : first ≤ srAt first period k := by
        rw [← h0']
        exact SpiPins.srAt_le first period hp1 (Nat.zero_le k)
      omega
    exact SpiPins.prog_idle_n (cins raws rst initial rdData hland) HostCmd.resetState
      HostCmd.ST_CMD false 0 (0 : BitVec 16) (0 : BitVec 7) first h0 hidle
  -- idle cycles after a byte's eighth edge
  have settle : ∀ (base : Nat) (p : BitVec 3) (ir : Bool) (a : BitVec 16),
      base + 8 ≤ 8 * 2 + 7 →
      AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (base + 7) + 1) p ir a →
      AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (base + 8)) p ir a := by
    intro base p ir a hb h
    exact SpiPins.settle_phase (cins raws rst initial rdData hland) HostCmd.resetState p ir a
      first period base hp2 h
      (fun j _ => hreset j)
      (fun j _ => SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs j)
      (fun j hj1 hj2 => by
        apply hnosrAll
        intro k hk
        rcases Nat.lt_or_ge k (base + 8) with hlt | hge
        · have h1 : srAt first period k ≤ srAt first period (base + 7) :=
            SpiPins.srAt_le first period hp1 (by omega)
          omega
        · have h1 : srAt first period (base + 8) ≤ srAt first period k :=
            SpiPins.srAt_le first period hp1 hge
          omega)
      (fun j hj => hackAddr j (by
        have h1 : srAt first period (base + 8) ≤ srAt first period (8 * 2 + 7) :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega))
  -- byte 0: the read command
  have hbyte0 : AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period (0 + 7) + 1) HostCmd.ST_AH true 0 := by
    have hb := SpiPins.complete_cmd (cins raws rst initial rdData hland) HostCmd.resetState
      first period 0 hp1 false 0 0 (bytes 0) hstart (hclean 0 (by omega))
      (fun k hk => by simpa using hmosi8 0 k (by omega) hk) (hsrAll 7 (by omega))
      (hreset _) (SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs _)
      (hackAddr _ (by
        have h1 : srAt first period (0 + 7) ≤ srAt first period (8 * 2 + 7) :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega))
    have hcond : (bytes 0 == HostCmd.CMD_WRITE || bytes 0 == HostCmd.CMD_READ) = true := by
      rw [hcmd]; decide
    have hread : (bytes 0 == HostCmd.CMD_READ) = true := by rw [hcmd]; rfl
    rw [hcond, hread] at hb
    simpa using hb
  -- byte 1: the high address byte
  have hbyte1 : AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period (8 + 7) + 1) HostCmd.ST_AL true (bytes 1 ++ (0 : BitVec 8)) := by
    have hs : AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 + 0)) HostCmd.ST_AH true 0 := by
      simpa using settle 0 HostCmd.ST_AH true 0 (by omega) hbyte0
    obtain ⟨r, hr⟩ := hs
    have hb := SpiPins.complete_ah (cins raws rst initial rdData hland) HostCmd.resetState
      first period 8 hp1 true 0 r (bytes 1) hr (hclean 8 (by omega))
      (fun k hk => by simpa using hmosi8 1 k (by omega) hk) (hsrAll 15 (by omega))
      (hreset _) (SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs _)
      (hackAddr _ (by
        have h1 : srAt first period (8 + 7) ≤ srAt first period (8 * 2 + 7) :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega))
    simpa using hb
  -- byte 2: the low address byte, entering the data bytes
  have hsAL : AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period (8 * 2)) HostCmd.ST_AL true (bytes 1 ++ (0 : BitVec 8)) := by
    have hs : AtPhase (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 + 8)) HostCmd.ST_AL true (bytes 1 ++ (0 : BitVec 8)) := by
      simpa using settle 8 HostCmd.ST_AL true (bytes 1 ++ (0 : BitVec 8)) (by omega) hbyte1
    simpa using hs
  obtain ⟨r2, hr2⟩ := hsAL
  have hb2 := SpiPins.byte_end (cins raws rst initial rdData hland) HostCmd.resetState
    HostCmd.ST_AL true (bytes 1 ++ (0 : BitVec 8)) r2 first period (8 * 2) hp1 (bytes 2) hr2
    (hclean 16 (by omega)) (fun k hk => by simpa using hmosi8 2 k (by omega) hk)
  -- the AL completion: request, address, data phase
  have hrdAL : (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period (8 * 2 + 7))).rd = false := by
    have hsrn : HostCmd.sr (cins raws rst initial rdData hland
        (srAt first period (8 * 2 + 7) - 1)) = false := by
      apply hnosrAll
      intro k hk
      have h22 : srAt first period (8 * 2 + 7) = srAt first period (8 * 2 + 6) + period :=
        SpiPins.srAt_succ first period (8 * 2 + 6)
      rcases Nat.lt_or_ge k (8 * 2 + 7) with hlt | hge
      · have h1 : srAt first period k ≤ srAt first period (8 * 2 + 6) :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega
      · have h1 : srAt first period (8 * 2 + 7) ≤ srAt first period k :=
          SpiPins.srAt_le first period hp1 hge
        omega
    have hpos : 0 < srAt first period (8 * 2 + 7) := by
      have h0 : srAt first period 0 = first := rfl
      have h1 : srAt first period 0 ≤ srAt first period (8 * 2 + 7) :=
        SpiPins.srAt_le first period hp1 (by omega)
      omega
    have e : HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * 2 + 7)) =
        HostCmd.step (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
          (srAt first period (8 * 2 + 7) - 1))
          (cins raws rst initial rdData hland (srAt first period (8 * 2 + 7) - 1)) := by
      rw [show srAt first period (8 * 2 + 7) = (srAt first period (8 * 2 + 7) - 1) + 1 from by omega]
      exact HostCmd.stateAt_succ _ _ _
    rw [e]
    show HostCmd.rdNext (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * 2 + 7) - 1))
      (cins raws rst initial rdData hland (srAt first period (8 * 2 + 7) - 1)) = false
    simp only [HostCmd.rdNext, HostCmd.completing]
    rw [hsrn]
    simp
  have hstep := read_al_step (HostCmd.stateAt (cins raws rst initial rdData hland)
      HostCmd.resetState (srAt first period (8 * 2 + 7)))
    (cins raws rst initial rdData hland (srAt first period (8 * 2 + 7)))
    (bytes 1 ++ (0 : BitVec 8)) _ hb2.1 hrdAL (hreset _)
    (SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs _)
    (hsrAll (8 * 2 + 7) (by omega))
    (hackAddr _ (by
      have h1 : srAt first period (8 * 2 + 7) ≤ srAt first period (8 * 2 + 7) :=
        Nat.le_refl _
      omega))
  rw [hb2.2] at hstep

  -- the read machine's view of the AL completion
  have hS : HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
      (srAt first period (8 * 2 + 7) + 1) =
      HostCmd.step (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * 2 + 7)))
        (cins raws rst initial rdData hland (srAt first period (8 * 2 + 7))) :=
    HostCmd.stateAt_succ _ _ _
  have hag := agrees_stateAt raws rst initial rdData rdVal hland hlandD
    (srAt first period (8 * 2 + 7) + 1)
  have htx0 : (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
      HostRead.resetState (srAt first period (8 * 2 + 7) + 1)).tx = 0 :=
    tx_zero _ _ (fun j _ => hreset j)
      (fun j _ => by rw [rins_csN]; exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs j)
      (fun j hj => by
        rw [HostRead.ack, (agrees_stateAt raws rst initial rdData rdVal hland hlandD j).rack_eq]
        exact hackAddr j hj)
  have hABR : HostRead.AfterByte
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
        (srAt first period (8 * 2 + 7) + 1)) (bytes 1 ++ bytes 2) 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hag.phase_eq, hS]; exact hstep.1
    · rw [hag.isRd_eq, hS]; exact hstep.2.2.2.2.2.1
    · rw [hag.bitc_eq, hS]; exact hstep.2.2.2.1
    · rw [htx0]; exact (shifted_zero 7).symm
    · rw [hag.addr_eq, hS, hstep.2.2.1, SpiPins.highByte]
    · rw [hag.wr_eq, hS]; exact hstep.2.2.2.2.1
    · rw [hag.rd_eq, hS]; exact hstep.2.1
    · rw [hag.rack_eq, hS]; exact hstep.2.2.2.2.2.2
  -- the request cycle: `rd` is raised there and one cycle later `rack` latches
  have hsrR : HostRead.sr (rins raws rst initial rdData rdVal hland hlandD
      (srAt first period (8 * 2 + 7) + 1)) = false := by
    rw [rins_sr]
    apply hnosrAll
    intro k hk
    have h22 : srAt first period (8 * 2 + 8) = srAt first period (8 * 2 + 7) + period :=
      SpiPins.srAt_succ first period (8 * 2 + 7)
    rcases Nat.lt_or_ge k (8 * 2 + 7) with hlt | hge
    · have h1 : srAt first period k ≤ srAt first period (8 * 2 + 7) :=
        SpiPins.srAt_le first period hp1 (by omega)
      omega
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
      · subst heq; omega
      · have h1 : srAt first period (8 * 2 + 8) ≤ srAt first period k :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega
  have hsrR1 : HostRead.sr (rins raws rst initial rdData rdVal hland hlandD
      (srAt first period (8 * 2 + 7) + 2)) = false := by
    rw [rins_sr]
    apply hnosrAll
    intro k hk
    have h22 : srAt first period (8 * 2 + 8) = srAt first period (8 * 2 + 7) + period :=
      SpiPins.srAt_succ first period (8 * 2 + 7)
    rcases Nat.lt_or_ge k (8 * 2 + 7) with hlt | hge
    · have h1 : srAt first period k ≤ srAt first period (8 * 2 + 7) :=
        SpiPins.srAt_le first period hp1 (by omega)
      omega
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
      · subst heq; omega
      · have h1 : srAt first period (8 * 2 + 8) ≤ srAt first period k :=
          SpiPins.srAt_le first period hp1 (by omega)
        omega
  have h24 : srAt first period (8 * 3) = srAt first period (8 * 2 + 7) + period := by
    rw [show 8 * 3 = (8 * 2 + 7) + 1 from by omega]
    exact SpiPins.srAt_succ first period (8 * 2 + 7)
  have hlandR : (rins raws rst initial rdData rdVal hland hlandD
      (srAt first period (8 * 2 + 7) + 1)).hland = false := by
    rw [rins_hland]
    refine hnoland _ ?_
    rw [h24]
    omega
  have hload : HostRead.Sending
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
        (srAt first period (8 * 2 + 7) + 3)) ((bytes 1 ++ bytes 2) + 1)
      ((rins raws rst initial rdData rdVal hland hlandD
        (srAt first period (8 * 2 + 7) + 1)).rdVal) := by
    have hstep2 := HostRead.read_slot_step
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
        (srAt first period (8 * 2 + 7) + 1))
      (rins raws rst initial rdData rdVal hland hlandD (srAt first period (8 * 2 + 7) + 1))
      (rins raws rst initial rdData rdVal hland hlandD (srAt first period (8 * 2 + 7) + 2))
      (bytes 1 ++ bytes 2) 0 hABR (hreset _)
      (by rw [rins_csN]; exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs _)
      hsrR hlandR hrdData0 (hreset _)
      (by rw [rins_csN]; exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs _)
      hsrR1
    have e : HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
        HostRead.resetState (srAt first period (8 * 2 + 7) + 3) =
        HostRead.step (HostRead.step
          (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
            (srAt first period (8 * 2 + 7) + 1))
          (rins raws rst initial rdData rdVal hland hlandD (srAt first period (8 * 2 + 7) + 1)))
          (rins raws rst initial rdData rdVal hland hlandD (srAt first period (8 * 2 + 7) + 2)) := by
      rw [show srAt first period (8 * 2 + 7) + 3 = (srAt first period (8 * 2 + 7) + 1) + 1 + 1
        from by omega, HostRead.stateAt_succ, HostRead.stateAt_succ]
    rw [e]
    exact hstep2
  -- idle cycles up to the first data slot
  have hrd : (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
      (srAt first period (8 * 2 + 7) + 1)).rd = true := by
    rw [hag.rd_eq, hS]; exact hstep.2.1
  have haddr : (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
      HostRead.resetState (srAt first period (8 * 2 + 7) + 1)).addr = bytes 1 ++ bytes 2 := by
    rw [hag.addr_eq, hS, hstep.2.2.1, SpiPins.highByte]
  refine ⟨hABR, hrd, haddr, ?_⟩
  have hS24 : srAt first period (8 * 3) =
      srAt first period (8 * 2 + 7) + 3 + (period - 3) := by
    rw [h24]
    omega
  rw [hS24]
  refine sendingN_frame_range (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
    (srAt first period (8 * 2 + 7) + 3) (srAt first period (8 * 2 + 7) + 3 + (period - 3))
    ((bytes 1 ++ bytes 2) + 1)
    ((rins raws rst initial rdData rdVal hland hlandD
      (srAt first period (8 * 2 + 7) + 1)).rdVal) 0 (by omega) hload ?_
  intro j hj1 hj2
  have h24' : srAt first period (8 * 2 + 8) = srAt first period (8 * 2 + 7) + period := by
    rw [show 8 * 2 + 8 = (8 * 2 + 7) + 1 from by omega]
    exact SpiPins.srAt_succ first period (8 * 2 + 7)
  have hjlt : j < srAt first period (8 * 2 + 8) := by
    rw [h24']
    omega
  refine ⟨hreset j,
    (by rw [rins_csN]; exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs j), ?_, ?_⟩
  · rw [rins_sr]
    apply hnosrAll
    intro k hk
    rcases Nat.lt_or_ge k (8 * 2 + 8) with hlt | hge
    · have h1 : srAt first period k ≤ srAt first period (8 * 2 + 7) :=
        SpiPins.srAt_le first period hp1 (by omega)
      omega
    · have h1 : srAt first period (8 * 2 + 8) ≤ srAt first period k :=
        SpiPins.srAt_le first period hp1 hge
      omega
  · rw [HostRead.ack]
    have hlandj : (rins raws rst initial rdData rdVal hland hlandD j).hland = false := by
      rw [rins_hland]
      exact hnoland j (by omega)
    have hrack : (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
        HostRead.resetState j).rack = false := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [HostRead.stateAt_succ, rack_step_read]
      have hrn : (rins raws rst initial rdData rdVal hland hlandD j').resetN = true := hreset j'
      rw [hrn]
      simp only [Bool.not_true, ite_true]
      have hrd' : (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
          HostRead.resetState j').rd = false := by
        apply rd_false_of_no_sr _ j' (by omega)
        rw [rins_sr]
        apply hnosrAll
        intro k hk
        have h2 : j' - 1 < srAt first period (8 * 2 + 8) := by
          rw [h24']
          omega
        rcases Nat.lt_or_ge k (8 * 2 + 8) with hlt | hge
        · have h1 : srAt first period k ≤ srAt first period (8 * 2 + 7) :=
            SpiPins.srAt_le first period hp1 (by omega)
          omega
        · have h1 : srAt first period (8 * 2 + 8) ≤ srAt first period k :=
            SpiPins.srAt_le first period hp1 hge
          omega
      rw [hrd']
      rfl
    rw [hrack, hlandj]
    rfl

/-- The cycle of slot `k`'s first `SR`: slot 0 starts after the address phase,
each later slot `period` cycles after the previous one's eighth edge. -/
def slotAt (first period : Nat) : Nat → Nat
  | 0 => srAt first period (8 * 3)
  | k + 1 => srAt first period (8 * (3 + k) + 8)

/-- The request cycle of the byte slot `k` carries: slot 0's request is the one
the completing `ST_AL` edge issues, slot `k+1`'s the one after slot `k`'s
eighth edge. -/
def reqAt (first period : Nat) : Nat → Nat
  | 0 => srAt first period (8 * 2 + 7) + 1
  | k + 1 => srAt first period (8 * (3 + k) + 7) + 1

theorem slotAt_zero (first period : Nat) : slotAt first period 0 = srAt first period (8 * 3) := rfl

theorem slotAt_succ (first period k : Nat) :
    slotAt first period (k + 1) = srAt first period (8 * (3 + k) + 8) := rfl

theorem reqAt_zero (first period : Nat) :
    reqAt first period 0 = srAt first period (8 * 2 + 7) + 1 := rfl

theorem reqAt_succ (first period k : Nat) :
    reqAt first period (k + 1) = srAt first period (8 * (3 + k) + 7) + 1 := rfl

/-- **The read burst.**  From the `Sending` state the address phase leaves at the
first data slot, slot `k`'s eight `SR` edges shift out the byte its request
sampled, MSB first; the slot's address register is `{AH, AL} + (k+1)`, and its
eighth edge issues the next request, which the next slot carries.  The last
conjunct is the `Sending` state of the next slot, so a single induction covers
the whole burst. -/
theorem read_burst (ins : Nat → HostRead.Input) (first period nbytes : Nat)
    (bytes : Nat → BitVec 8) (hp : 3 ≤ period) (hnb4 : 4 ≤ nbytes)
    (h0 : HostRead.Sending (HostRead.stateAt ins HostRead.resetState (slotAt first period 0))
      ((bytes 1 ++ bytes 2) + 1) ((ins (reqAt first period 0)).rdVal))
    (hcyc : ∀ j, srAt first period (8 * 3) ≤ j →
      j < srAt first period (8 * nbytes) → (ins j).resetN = true ∧ (ins j).csN = false)
    (hsr : ∀ k, k < 8 * nbytes → HostRead.sr (ins (srAt first period k)) = true)
    (hnosr : ∀ j, srAt first period (8 * 3) ≤ j → j < srAt first period (8 * nbytes) →
      (∀ k, j ≠ srAt first period k) → HostRead.sr (ins j) = false)
    (hackSlot : ∀ k, k + 3 < nbytes → ∀ j, srAt first period (8 * (3 + k)) ≤ j →
      j < srAt first period (8 * (3 + k) + 8) →
      HostRead.ack (HostRead.stateAt ins HostRead.resetState j) (ins j) = false)
    (hrdData : ∀ k, (ins (reqAt first period k)).rdData = false) :
    ∀ k, k + 3 < nbytes →
      HostRead.Sending (HostRead.stateAt ins HostRead.resetState (slotAt first period k))
          ((bytes 1 ++ bytes 2) + ((k + 1 : Nat) : BitVec 16))
          ((ins (reqAt first period k)).rdVal) ∧
        (∀ j, j < 8 →
          bitAt (HostRead.stateAt ins HostRead.resetState
            (srAt first period (8 * (3 + k) + j))).tx 7
            = bitAt ((ins (reqAt first period k)).rdVal) (7 - j)) ∧
        HostRead.AfterByte (HostRead.stateAt ins HostRead.resetState (reqAt first period (k + 1)))
          ((bytes 1 ++ bytes 2) + ((k + 1 : Nat) : BitVec 16))
          ((ins (reqAt first period k)).rdVal) ∧
        HostRead.Sending (HostRead.stateAt ins HostRead.resetState (slotAt first period (k + 1)))
          ((bytes 1 ++ bytes 2) + ((k + 2 : Nat) : BitVec 16))
          ((ins (reqAt first period (k + 1))).rdVal) := by
  have hp1 : 1 ≤ period := by omega
  -- every slot's window lies inside the transaction
  have hwin : ∀ k, 8 * (3 + k) + 8 ≤ 8 * nbytes → ∀ j, srAt first period (8 * (3 + k)) ≤ j →
      j < srAt first period (8 * (3 + k) + 8) → j < srAt first period (8 * nbytes) := by
    intro k hk j hj1 hj2
    have hmono : srAt first period (8 * (3 + k) + 8) ≤ srAt first period (8 * nbytes) :=
      SpiPins.srAt_le first period hp1 hk
    omega
  intro k
  induction k with
  | zero =>
    intro _
    have hwindow : 8 * (3 + 0) + 8 ≤ 8 * nbytes := by omega
    have hcyc0 : ∀ j, srAt first period (8 * (3 + 0)) ≤ j →
        j < srAt first period (8 * (3 + 0) + 8) →
        (ins j).resetN = true ∧ (ins j).csN = false := by
      intro j hj1 hj2
      exact ⟨(hcyc j hj1 (hwin 0 hwindow j hj1 hj2)).1,
        (hcyc j hj1 (hwin 0 hwindow j hj1 hj2)).2⟩
    have hnosr0 : ∀ j, srAt first period (8 * (3 + 0)) ≤ j →
        j < srAt first period (8 * (3 + 0) + 8) →
        (∀ k', k' < 8 → j ≠ srAt first period (8 * (3 + 0) + k')) →
        HostRead.sr (ins j) = false := by
      intro j hj1 hj2 hne
      exact hnosr j hj1 (hwin 0 hwindow j hj1 hj2)
        (not_edge_of_gap first period (8 * (3 + 0)) hp1 hj1 hj2 hne)
    have hrd0 : (ins (srAt first period (8 * (3 + 0) + 7) + 1)).rdData = false :=
      hrdData 1
    obtain ⟨hbits, hAB, hsend⟩ := read_slot_pins ins HostRead.resetState first period
      (8 * (3 + 0)) ((bytes 1 ++ bytes 2) + 1) ((ins (reqAt first period 0)).rdVal) hp
      h0 hcyc0
      (fun k' hk' => hsr (8 * (3 + 0) + k') (by omega)) hnosr0
      (hackSlot 0 (by omega)) hrd0
    refine ⟨h0, hbits, hAB, ?_⟩
    have haddr : ((bytes 1 ++ bytes 2) + (1 : BitVec 16)) + 1
        = (bytes 1 ++ bytes 2) + ((0 + 2 : Nat) : BitVec 16) :=
      SpiPins.addrSucc (bytes 1 ++ bytes 2) 1
    rw [← haddr]
    exact hsend
  | succ k ih =>
    intro hk
    obtain ⟨_, _, hABprev, hS⟩ := ih (by omega)
    have hwindow : 8 * (3 + (k + 1)) + 8 ≤ 8 * nbytes := by omega
    have hge' : srAt first period (8 * 3) ≤ srAt first period (8 * (3 + (k + 1))) :=
      SpiPins.srAt_le first period hp1 (by omega)
    have hcyc' : ∀ j, srAt first period (8 * (3 + (k + 1))) ≤ j →
        j < srAt first period (8 * (3 + (k + 1)) + 8) →
        (ins j).resetN = true ∧ (ins j).csN = false := by
      intro j hj1 hj2
      exact ⟨(hcyc j (by omega) (hwin (k + 1) hwindow j hj1 hj2)).1,
        (hcyc j (by omega) (hwin (k + 1) hwindow j hj1 hj2)).2⟩
    have hnosr' : ∀ j, srAt first period (8 * (3 + (k + 1))) ≤ j →
        j < srAt first period (8 * (3 + (k + 1)) + 8) →
        (∀ k', k' < 8 → j ≠ srAt first period (8 * (3 + (k + 1)) + k')) →
        HostRead.sr (ins j) = false := by
      intro j hj1 hj2 hne
      have hge : srAt first period (8 * 3) ≤ srAt first period (8 * (3 + (k + 1))) :=
        SpiPins.srAt_le first period hp1 (by omega)
      exact hnosr j (by omega) (hwin (k + 1) hwindow j hj1 hj2)
        (not_edge_of_gap first period (8 * (3 + (k + 1))) hp1 hj1 hj2 hne)
    obtain ⟨hbits, hAB, hsend⟩ := read_slot_pins ins HostRead.resetState first period
      (8 * (3 + (k + 1))) ((bytes 1 ++ bytes 2) + ((k + 2 : Nat) : BitVec 16))
      ((ins (reqAt first period (k + 1))).rdVal) hp hS hcyc'
      (fun k' hk' => hsr (8 * (3 + (k + 1)) + k') (by omega)) hnosr'
      (hackSlot (k + 1) (by omega)) (hrdData (k + 2))
    refine ⟨hS, hbits, hAB, ?_⟩
    have haddr : ((bytes 1 ++ bytes 2) + ((k + 2 : Nat) : BitVec 16)) + 1
        = (bytes 1 ++ bytes 2) + ((k + 2 + 1 : Nat) : BitVec 16) :=
      SpiPins.addrSucc (bytes 1 ++ bytes 2) (k + 2)
    rw [← haddr]
    exact hsend

/-! ## Negative witnesses: the premises are needed -/

/-- Writing `0x02` is not enough: a cycle with `CS_N` high is no data-byte
completion at all, so no `SR` and no write strobe can come from it. -/
theorem witness_cs_high_no_strobe (s : HostCmd.State) (i : HostCmd.Input)
    (hcs : i.csN = true) :
    HostCmd.sr i = false ∧ HostCmd.completing s i = false ∧ (HostCmd.step s i).wr = false := by
  have hsr : HostCmd.sr i = false := by simp [HostCmd.sr, hcs]
  refine ⟨hsr, ?_, ?_⟩
  · simp [HostCmd.completing, hsr]
  · simp [HostCmd.step, HostCmd.wrNext, hcs]

/-- A clock whose `SCK` pin is high in every sampled cycle has no rising edge at
all, so no sampled trace can represent an SCK period of one cycle: `period ≥ 2`
is needed. -/
theorem witness_no_rise_of_always_high (raws : Nat → BitVec 16)
    (hsck : ∀ n, bit (raws n) 8 = true) : ∀ m, 3 ≤ m → pinRise raws m = false := by
  intro m hm
  rcases m with _ | _ | _ | n
  · omega
  · omega
  · omega
  · simp [pinRise, hsck]

/-- With `SCK` high in every cycle there is no `SR`: the trace is not a clock. -/
theorem witness_no_sr_of_always_high (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData hland : Nat → Bool) (m : Nat) (hm : 3 ≤ m)
    (hinit : initial = SpiPins.resetState) (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false) (hsck : ∀ n, bit (raws n) 8 = true) :
    HostCmd.sr (cins raws rst initial rdData hland m) = false := by
  rw [SpiPins.sr_eq_pinRise raws rst initial rdData hland hinit hreset hcs m,
    witness_no_rise_of_always_high raws hsck m hm]

/-- A two-cycle SCK period loads `TX` after the next slot has started: the
acknowledge cycle is `+2` and the load `+3`, while the next slot's first edge is
only `+2`.  So `3 ≤ period` is needed, not just `2 ≤ period`. -/
theorem witness_read_load_late (first : Nat) :
    srAt first 2 (8 * 3) < srAt first 2 (8 * 2 + 7) + 3 := by
  rw [show 8 * 3 = (8 * 2 + 7) + 1 from by omega, SpiPins.srAt_succ]
  omega

/-! ## The read transaction at the pins -/

/-- **A pin-level read transaction.**  `0x03`, `AH`, `AL` and then data bytes on
a mode-0 clock: the byte clocked out in data slot `k` is the `rd_val` sampled in
the cycle that requested `{AH, AL} + k` (MSB first, on the slot's eight rising
edges), and the address register in that request cycle is `{AH, AL} + k` itself.
A write strobe never appears (`wr` is low in the request cycle). -/
theorem transaction_read_bytes (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData : Nat → Bool) (rdVal : Nat → BitVec 8)
    (hland : Nat → Bool) (hlandD : Nat → BitVec 8) (first period nbytes : Nat)
    (bytes : Nat → BitVec 8)
    (hp : 3 ≤ period) (hf : 3 ≤ first) (hnb : 3 ≤ nbytes)
    (hinit : initial = SpiPins.resetState)
    (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, k < 8 * nbytes → pinRise raws (srAt first period k) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hbit : ∀ m k, m < 3 → k < 8 →
      bit (raws (srAt first period (8 * m + k) - 2)) 10 = bit8 (bytes m) (7 - k))
    (hcmd : bytes 0 = HostCmd.CMD_READ)
    (hackAddr : ∀ j, j < srAt first period (8 * 2 + 7) + 1 →
      HostCmd.ackBit (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState j)
        (cins raws rst initial rdData hland j) = false)
    (hnoland : ∀ j, j < srAt first period (8 * nbytes) →
      (rins raws rst initial rdData rdVal hland hlandD j).hland = false)
    (hackSlot : ∀ k, k + 3 < nbytes → ∀ j, srAt first period (8 * (3 + k)) ≤ j →
      j < srAt first period (8 * (3 + k) + 8) →
      HostRead.ack (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
        HostRead.resetState j) (rins raws rst initial rdData rdVal hland hlandD j) = false)
    (hrdData : ∀ k, (rins raws rst initial rdData rdVal hland hlandD
      (reqAt first period k)).rdData = false) :
    ∀ k, k + 3 < nbytes →
      (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (reqAt first period k)).rd = true ∧
        (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (reqAt first period k)).addr = (bytes 1 ++ bytes 2) + (k : BitVec 16) ∧
        (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD) HostRead.resetState
          (reqAt first period k)).wr = false ∧
        (∀ j, j < 8 →
          bitAt (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
            HostRead.resetState (srAt first period (8 * (3 + k) + j))).tx 7
            = bitAt ((rins raws rst initial rdData rdVal hland hlandD
              (reqAt first period k)).rdVal) (7 - j)) := by
  intro k hk
  have hp1 : 1 ≤ period := by omega
  -- the address phase and the first slot
  have hopen := read_open raws rst initial rdData rdVal hland hlandD first period nbytes bytes
    hp hf hnb hinit hreset hcs hrise honly hbit hcmd hackAddr
    (fun j hj => hnoland j (by
      have hmono : srAt first period (8 * 3) ≤ srAt first period (8 * nbytes) :=
        SpiPins.srAt_le first period hp1 (by omega)
      omega))
    (by rw [rins_rdData]; exact hrdData 0)
  obtain ⟨hAB0, _, _, hS0⟩ := hopen
  rcases Nat.lt_or_ge nbytes 4 with hsmall | h4
  · omega
  · -- the burst
    have hsrAll : ∀ m, m < 8 * nbytes →
        HostRead.sr (rins raws rst initial rdData rdVal hland hlandD (srAt first period m)) = true := by
      intro m hm
      rw [rins_sr]
      exact SpiPins.sr_of_pinRise raws rst initial rdData hland hinit hreset hcs _ (hrise m hm)
    have hnosrAll : ∀ m, (∀ k, m ≠ srAt first period k) →
        HostRead.sr (rins raws rst initial rdData rdVal hland hlandD m) = false := by
      intro m hm
      rw [rins_sr]
      have hne : pinRise raws m ≠ true := by
        intro h
        obtain ⟨k, hk'⟩ := honly m h
        exact hm k hk'
      have hpf : pinRise raws m = false := by simpa using hne
      exact SpiPins.sr_of_not_pinRise raws rst initial rdData hland hinit hreset hcs m hpf
    have hburst := read_burst (rins raws rst initial rdData rdVal hland hlandD) first period
      nbytes bytes hp h4 hS0
      (fun j hj1 hj2 => ⟨hreset j,
        (by rw [rins_csN]; exact SpiPins.cs_low raws rst initial rdData hland hinit hreset hcs j)⟩)
      hsrAll (fun j _ _ hne => hnosrAll j hne) hackSlot hrdData
    obtain ⟨_, hbits, _, _⟩ := hburst k hk
    refine ⟨?_, ?_, ?_, hbits⟩
    · rcases Nat.eq_zero_or_pos k with hzero | hpos
      · rw [hzero]
        exact hAB0.rd_eq
      · obtain ⟨_, _, hABprev, _⟩ := hburst (k - 1) (by omega)
        rw [show k - 1 + 1 = k from by omega] at hABprev
        exact hABprev.rd_eq
    · rcases Nat.eq_zero_or_pos k with hzero | hpos
      · rw [hzero]
        show (HostRead.stateAt (rins raws rst initial rdData rdVal hland hlandD)
            HostRead.resetState (srAt first period (8 * 2 + 7) + 1)).addr
          = (bytes 1 ++ bytes 2) + ((0 : Nat) : BitVec 16)
        rw [show ((0 : Nat) : BitVec 16) = 0 from rfl, hAB0.addr_eq]
        exact (BitVec.add_zero _).symm
      · obtain ⟨_, _, hABprev, _⟩ := hburst (k - 1) (by omega)
        rw [show k - 1 + 1 = k from by omega] at hABprev
        exact hABprev.addr_eq
    · rcases Nat.eq_zero_or_pos k with hzero | hpos
      · rw [hzero]
        exact hAB0.wr_eq
      · obtain ⟨_, _, hABprev, _⟩ := hburst (k - 1) (by omega)
        rw [show k - 1 + 1 = k from by omega] at hABprev
        exact hABprev.wr_eq

/-! ## The write transaction at the pins, against the host map -/

/-- At a real write strobe the host map's enabled list is its selection list. -/
theorem enabledSels_true (live : Bool) (a : BitVec 16) :
    HostMap.enabledSels live true a = HostMap.selList live a := by
  simp [HostMap.enabledSels]

/-- The map's selection list is the 43 register-byte comparisons followed by one
flag per non-register block. -/
theorem selList_eq (live : Bool) (a : BitVec 16) :
    HostMap.selList live a = HostMap.regAddrs.map (fun x => a == x) ++
      [HostMap.progCore0 a, HostMap.progCore1 a, HostMap.inRegion .data a,
        HostMap.cfgSel live a] := rfl

/-- In the program window exactly one write target is enabled: a program-memory
byte, of the core the address selects.  The register, data-RAM and configuration
entries are off, so the target cannot be any of them. -/
theorem count_prog (live : Bool) (a : BitVec 16) (h : a < 0x1000) :
    HostMap.bitCount (HostMap.enabledSels live true a) = 1 ∧
      HostMap.bitCount (HostMap.regAddrs.map (fun x => a == x)) = 0 ∧
      HostMap.inRegion .data a = false ∧ HostMap.cfgSel live a = false ∧
      HostMap.progCore0 a = HostMap.progCore0 a := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [enabledSels_true]
    simp only [HostMap.selList, HostMap.selListRegs, HostMap.regAddrs, HostMap.progCore0,
      HostMap.progCore1, HostMap.inRegion, HostMap.base, HostMap.span, HostMap.cfgSel,
      HostMap.bitCount, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    bv_decide
  · simp only [HostMap.regAddrs, List.map_cons, List.map_nil, HostMap.bitCount]
    bv_decide
  · simp only [HostMap.inRegion, HostMap.base, HostMap.span]
    bv_decide
  · simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]
    bv_decide

/-- In the data window exactly one write target is enabled: the data-RAM byte. -/
theorem count_data (live : Bool) (a : BitVec 16) (h1 : 0x1000 ≤ a) (h2 : a < 0x1800) :
    HostMap.bitCount (HostMap.enabledSels live true a) = 1 ∧
      HostMap.progCore0 a = false ∧ HostMap.progCore1 a = false ∧
      HostMap.inRegion .data a = true ∧ HostMap.cfgSel live a = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [enabledSels_true]
    simp only [HostMap.selList, HostMap.selListRegs, HostMap.regAddrs, HostMap.progCore0,
      HostMap.progCore1, HostMap.inRegion, HostMap.base, HostMap.span, HostMap.cfgSel,
      HostMap.bitCount, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    bv_decide
  · simp only [HostMap.progCore0]; bv_decide
  · simp only [HostMap.progCore1]; bv_decide
  · simp only [HostMap.inRegion, HostMap.base, HostMap.span]; bv_decide
  · simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]; bv_decide

/-- In the configuration window the only possible target is the window byte, and
it is enabled exactly when the byte is live. -/
theorem count_cfg (live : Bool) (a : BitVec 16) (h1 : 0x2000 ≤ a) (h2 : a < 0x21E0) :
    HostMap.bitCount (HostMap.enabledSels live true a) = (if live then 1 else 0) ∧
      HostMap.progCore0 a = false ∧ HostMap.progCore1 a = false ∧
      HostMap.inRegion .data a = false ∧ HostMap.cfgSel live a = live := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [enabledSels_true]
    simp only [HostMap.selList, HostMap.selListRegs, HostMap.regAddrs, HostMap.progCore0,
      HostMap.progCore1, HostMap.inRegion, HostMap.base, HostMap.span, HostMap.cfgSel,
      HostMap.bitCount, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    cases live <;> bv_decide
  · simp only [HostMap.progCore0]; bv_decide
  · simp only [HostMap.progCore1]; bv_decide
  · simp only [HostMap.inRegion, HostMap.base, HostMap.span]; bv_decide
  · simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]
    cases live <;> bv_decide

/-- The count of a concatenation is the sum of the counts. -/
theorem bitCount_append (l1 l2 : List Bool) :
    HostMap.bitCount (l1 ++ l2) = HostMap.bitCount l1 + HostMap.bitCount l2 := by
  induction l1 with
  | nil => simp [HostMap.bitCount]
  | cons b bs ih => simp [HostMap.bitCount, ih, BitVec.add_assoc]

/-- In the register window the only possible targets are the 43 register bytes:
the program, data and configuration entries are off. -/
theorem count_reg (live : Bool) (a : BitVec 16) (h1 : 0x2400 ≤ a) (h2 : a < 0x2480) :
    HostMap.bitCount (HostMap.enabledSels live true a)
        = HostMap.bitCount (HostMap.regAddrs.map (fun x => a == x)) ∧
      HostMap.progCore0 a = false ∧ HostMap.progCore1 a = false ∧
      HostMap.inRegion .data a = false ∧ HostMap.cfgSel live a = false := by
  have hp0 : HostMap.progCore0 a = false := by simp only [HostMap.progCore0]; bv_decide
  have hp1 : HostMap.progCore1 a = false := by simp only [HostMap.progCore1]; bv_decide
  have hd : HostMap.inRegion .data a = false := by
    simp only [HostMap.inRegion, HostMap.base, HostMap.span]; bv_decide
  have hc : HostMap.cfgSel live a = false := by
    simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]; bv_decide
  refine ⟨?_, hp0, hp1, hd, hc⟩
  rw [enabledSels_true, selList_eq, hp0, hp1, hd, hc, bitCount_append]
  simp [HostMap.bitCount]

/-- **A pin-level write transaction, against the host map.**  At every data
byte's strobe the host map enables at most one write target, and the target is
the one `HostMap.selList` marks for `{AH, AL} + j`: a program-memory byte (the
core the address selects), a data-RAM byte, a live configuration byte, or a
register byte.  Read-only and unmapped addresses enable nothing. -/
theorem transaction_write_target (raws : Nat → BitVec 16) (rst : Nat → Bool)
    (initial : SpiPins.Sync) (rdData hland : Nat → Bool) (first period nbytes : Nat)
    (bytes : Nat → BitVec 8) (live : Bool)
    (hp : 2 ≤ period) (hf : 3 ≤ first) (hnb : 3 ≤ nbytes)
    (hinit : initial = SpiPins.resetState)
    (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, pinRise raws (srAt first period k) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hbit : ∀ m k, m < nbytes → k < 8 →
      bit (raws (srAt first period (8 * m + k) - 2)) 10 = bit8 (bytes m) (7 - k))
    (hcmd : bytes 0 = HostCmd.CMD_WRITE)
    (hack : ∀ j, HostCmd.ackBit
      (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState j)
      (cins raws rst initial rdData hland j) = false) :
    ∀ j, j + 3 < nbytes →
      let a : BitVec 16 := (bytes 1 ++ bytes 2) + (j : BitVec 16)
      (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
          (srAt first period (8 * (3 + j) + 7) + 1)).wr = true ∧
        (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
          (srAt first period (8 * (3 + j) + 7) + 1)).addr = a ∧
        (HostCmd.stateAt (cins raws rst initial rdData hland) HostCmd.resetState
          (srAt first period (8 * (3 + j) + 7) + 1)).wdata = bytes (3 + j) ∧
        HostMap.bitCount (HostMap.enabledSels live true a) ≤ 1 ∧
        (a < 0x1000 →
          HostMap.bitCount (HostMap.enabledSels live true a) = 1 ∧
            HostMap.bitCount (HostMap.regAddrs.map (fun x => a == x)) = 0 ∧
            HostMap.inRegion .data a = false ∧ HostMap.cfgSel live a = false) ∧
        (0x1000 ≤ a → a < 0x1800 →
          HostMap.bitCount (HostMap.enabledSels live true a) = 1 ∧
            HostMap.inRegion .data a = true) ∧
        (0x2000 ≤ a → a < 0x21E0 →
          HostMap.bitCount (HostMap.enabledSels live true a) = (if live then 1 else 0) ∧
            HostMap.cfgSel live a = live) ∧
        (0x2400 ≤ a → a < 0x2480 →
          HostMap.progCore0 a = false ∧ HostMap.progCore1 a = false ∧
            HostMap.inRegion .data a = false ∧ HostMap.cfgSel live a = false) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := SpiPins.transaction_strobes raws rst initial rdData hland first period
    nbytes bytes hp hf hnb hinit hreset hcs hrise honly hbit hcmd hack j hj
  exact ⟨h1, h2, h3, HostMap.enabledSels_le_one live true _,
    fun h => ⟨(count_prog live _ h).1, (count_prog live _ h).2.1,
      (count_prog live _ h).2.2.1, (count_prog live _ h).2.2.2.1⟩,
    fun h1' h2' => ⟨(count_data live _ h1' h2').1, (count_data live _ h1' h2').2.2.2.1⟩,
    fun h1' h2' => ⟨(count_cfg live _ h1' h2').1, (count_cfg live _ h1' h2').2.2.2.2⟩,
    fun h1' h2' => ⟨(count_reg live _ h1' h2').2.1, (count_reg live _ h1' h2').2.2.1,
      (count_reg live _ h1' h2').2.2.2.1, (count_reg live _ h1' h2').2.2.2.2⟩⟩

end Metronome.HostPins
