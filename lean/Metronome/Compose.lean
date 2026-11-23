import Metronome.Config
import Metronome.Host

/-!
# Composing the host write filter with the configuration service contract

`Metronome.Config.trace_host_service` assumes `SpacedHost`: no two adjacent
`host_valid` samples.  This module builds `host_valid` from the actual host
write strobe and the chip-top filter

`cfg_host_now = h_wr & in_cfg & cfg_address_is_live(ha)`

and discharges that premise with `Metronome.Host.trace_spacing`.

The extracted check (see `verify.py`) establishes that the elaborated
`cfg_host_now` net is exactly the conjunction of `u_host.wr`, `in_cfg`, and one
further free leaf.  The host payload and address decode are deliberately not
modelled here.

Cycle 0 of the composed trace must be the host link's reset state; the sampled
reset edge that precedes operation leaves `wr = false`, which makes the
cycle-0 premise vacuous.  Without that premise an arbitrary power-up `wr`
could be high in cycle 0 and the first post-edge cycle, as
`Metronome.Host.powerup_boundary_witness` shows.
-/

namespace Metronome.Compose

open Metronome

/-- The chip-top host filter, reduced to its three checked leaves. -/
def chipHostValid (wr inCfg live : Bool) : Bool :=
  wr && inCfg && live

theorem chipHostValid_implies_wr (wr inCfg live : Bool)
    (valid : chipHostValid wr inCfg live = true) : wr = true := by
  simp [chipHostValid] at valid
  exact valid.1.1

/-- The chip-top `host_valid` implies the actual host write strobe
`u_host.wr`; the Python adapter checks the elaborated net against
`chipHostValid` with the first leaf bound to `u_host.wr`. -/
theorem chip_host_valid_implies_host_wr (wr inCfg live : Bool)
    (valid : chipHostValid wr inCfg live = true) : wr = true :=
  chipHostValid_implies_wr wr inCfg live valid

/-- A positive witness: the filter can pass, and a passing filter grants a
configuration bank write through the arbiter. -/
theorem positive_write_witness (write : Config.Write) :
    chipHostValid true true true = true ∧
      (Config.step ⟨false, false, write, write⟩
        ⟨true, chipHostValid true true true, write, false, write⟩).bankWrite = true := by
  refine ⟨rfl, ?_⟩
  exact (Config.fresh_host_priority
    (⟨false, false, write, write⟩ : Config.State)
    (⟨true, chipHostValid true true true, write, false, write⟩ : Config.Input)
    rfl rfl rfl).1

/-- `host_valid` at cycle `n` from the host register trace and the two filter
leaves.  The host state is sampled after `n` edges, which is the value the
chip presents during cycle `n`. -/
def topHostValid (hostInputs : Nat → Host.Input) (hostInitial : Host.State)
    (inCfg live : Nat → Bool) (n : Nat) : Bool :=
  chipHostValid (Host.stateAt hostInputs hostInitial n).wr (inCfg n) (live n)

/-- A configuration input trace whose `hostValid` comes from the host filter.
The remaining fields, including the host payload, come from `rest`. -/
def withTopHostValid (rest : Nat → Config.Input) (hostInputs : Nat → Host.Input)
    (hostInitial : Host.State) (inCfg live : Nat → Bool) : Nat → Config.Input :=
  fun n => { rest n with hostValid := topHostValid hostInputs hostInitial inCfg live n }

/-- The host filter is spaced when the trace starts in the reset state
(`wr = false`).  Cycle 0 is discharged by that premise; every later cycle is
`Metronome.Host.trace_spacing`. -/
theorem spaced_of_top (rest : Nat → Config.Input) (hostInputs : Nat → Host.Input)
    (hostInitial : Host.State) (inCfg live : Nat → Bool)
    (cleared : hostInitial.wr = false) :
    Config.SpacedHost (withTopHostValid rest hostInputs hostInitial inCfg live) := by
  intro n valid
  cases n with
  | zero =>
    exfalso
    have powerup : hostInitial.wr = true := by
      have := valid
      simp [withTopHostValid, topHostValid, chipHostValid] at this
      exact this.1.1
    rw [cleared] at powerup
    cases powerup
  | succ k =>
    have wr : (Host.stateAt hostInputs hostInitial (k + 1)).wr = true := by
      have := valid
      simp [withTopHostValid, topHostValid, chipHostValid] at this
      exact this.1.1
    have following := Host.trace_spacing hostInputs hostInitial k wr
    simp [withTopHostValid, topHostValid, chipHostValid, following]

/-- Adjacent chip-top `host_valid` samples are impossible from cycle 1 onward:
a valid sample at `n+1` forces the next one low. -/
theorem host_valid_spacing (hostInputs : Nat → Host.Input) (hostInitial : Host.State)
    (inCfg live : Nat → Bool) (n : Nat)
    (valid : topHostValid hostInputs hostInitial inCfg live (n + 1) = true) :
    topHostValid hostInputs hostInitial inCfg live (n + 2) = false := by
  have wr : (Host.stateAt hostInputs hostInitial (n + 1)).wr = true := by
    have := valid
    simp [topHostValid, chipHostValid] at this
    exact this.1.1
  have following := Host.trace_spacing hostInputs hostInitial n wr
  simp [topHostValid, chipHostValid, following]

/-- The post-reset suffix of a trace whose cycle 0 has the sampled reset low:
cycle `n` of the composed trace is chip cycle `n+1`, starting in `resetState`.
The caller supplies the configuration-input suffix `restSuffix`. -/
theorem spaced_after_sampled_reset (restSuffix : Nat → Config.Input)
    (hostInputs : Nat → Host.Input) (hostInitial : Host.State)
    (inCfgSuffix liveSuffix : Nat → Bool)
    (reset : (hostInputs 0).resetN = false) :
    Config.SpacedHost
      (withTopHostValid restSuffix (fun n => hostInputs (n + 1))
        (Host.stateAt hostInputs hostInitial 1) inCfgSuffix liveSuffix) := by
  rw [Host.reset_state_after_edge hostInputs hostInitial reset]
  exact spaced_of_top restSuffix (fun n => hostInputs (n + 1)) Host.resetState
    inCfgSuffix liveSuffix rfl

/-- The configuration service result of `Metronome.Config` with its
`SpacedHost` premise discharged by the actual host write strobe.  The host
trace starts in the reset state, so this covers the cycle-0 boundary. -/
theorem config_host_service_from_top (rest : Nat → Config.Input)
    (hostInputs : Nat → Host.Input) (hostInitial : Host.State)
    (inCfg live : Nat → Bool) (cfgInitial : Config.State) (n : Nat)
    (cleared : hostInitial.wr = false)
    (reset : (withTopHostValid rest hostInputs hostInitial inCfg live 0).resetN = false)
    (active : (withTopHostValid rest hostInputs hostInitial inCfg live (n + 1)).resetN = true)
    (valid : (withTopHostValid rest hostInputs hostInitial inCfg live (n + 1)).hostValid = true) :
    let inputs := withTopHostValid rest hostInputs hostInitial inCfg live
    let state := Config.stateAt inputs cfgInitial (n + 1)
    let input := inputs (n + 1)
    if state.previousWrite then
      (Config.step state input).bankWrite = false ∧
        ((inputs (n + 2)).resetN = true →
          Config.HostIssued
            (Config.step (Config.stateAt inputs cfgInitial (n + 2)) (inputs (n + 2)))
            input.host)
    else Config.HostIssued (Config.step state input) input.host := by
  exact Config.trace_host_service (withTopHostValid rest hostInputs hostInitial inCfg live)
    cfgInitial reset (spaced_of_top rest hostInputs hostInitial inCfg live cleared)
    n active valid

end Metronome.Compose
