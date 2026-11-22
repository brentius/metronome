import Metronome.Machine.Debug

/-! §13.1 Configuration written by the cores (`CW.AL`, `CW.AH`, `CW.D`), the latch bank port (`BWP`, `HH`) and the
§1 W+2 visibility of configuration writes. -/

namespace Metronome.Machine

open Util Tables

/-- §13.1 The winning move to write group `CW`: 0 `CW.AL`, 1 `CW.AH`, 2 `CW.D`, with bus value. -/
structure CwMove where
  op : Nat
  v : Nat
deriving Repr, Inhabited

/-- §13.1 Runtime targets a pending core write may drain to: `DBG.ECTL`, `EMASK`, `RLV`. -/
def cwRuntimeTarget (a : Nat) : Bool :=
  match hostLocate a with
  | some l => l.blk == "DBG" && (l.reg == "ECTL" || l.reg == "EMASK" || l.reg == "RLV")
  | none => false

/-- §13.1 / §1 Result of the configuration write machinery in cycle t. -/
structure CwOut where
  st : CwSt
  /-- the write performed on the latch bank in t (seen by the logic from t+2) -/
  performed : Option (Nat × Nat)
  /-- `CWOVR` set in t -/
  ovr : Bool
  /-- a pending core write draining as a runtime write in t -/
  rt : Option HostWr

/-- §13.1 / §1 Core configuration writes and the bank port, in cycle t from cycle-t state.

* `CW.AL`, `CW.AH`: `CWA[7:0]` or `CWA[15:8] := bus`.
* `CW.D`: if `CWV` and the pending write does not drain in t, `CWOVR' = 1` and the new write is dropped; otherwise
  `CWQ' = (CWA, bus)`, `CWV' = 1`, `CWA' = CWA + 1`.
* Bank port: a held host write `HH` is performed; otherwise a host configuration write issued in t is performed,
  unless `BWP`, in which case it is held to t+1. If neither is performed and `CWV` holds a configuration address and
  `!BWP`, the core write is performed and drains. `BWP' = 1` iff a write was performed.
* A pending write to `DBG.ECTL`, `EMASK` or `RLV` drains in the cycle after it was queued as a runtime write; a pending
  write to any other non-configuration address drains with no effect.
* §12.3 / §13.1 (D50): in a frozen cycle the queue holds: a pending write drains neither to the bank nor as a
  runtime write (`frozen`). Host configuration writes and a held `HH` still use the bank port.
* §1: a configuration write in the two cycles after `rst_q` rises is ignored (`window`). -/
def cwNext (cw : CwSt) (hostCfg : Option (Nat × Nat)) (mv : Option CwMove) (window : Bool)
    (frozen : Bool := false) : CwOut :=
  let qa := cw.cwqa.toNat
  let qIsCfg := cw.cwv && Config.isCfgAddr qa
  -- bank port
  let (perf0, hh', hha', hhd', coreDrain) : Option (Nat × Nat) × Bool × Nat × Nat × Bool :=
    if cw.hh then
      -- AMBIG(19) a new host write while HH is pending (unreachable: host writes are an SPI byte apart) is held
      match hostCfg with
      | some (a, v) => (some (cw.hha.toNat, cw.hhd.toNat), true, a, v, false)
      | none => (some (cw.hha.toNat, cw.hhd.toNat), false, 0, 0, false)
    else match hostCfg with
      | some (a, v) =>
        if cw.bwp then (none, true, a, v, false) else (some (a, v), false, 0, 0, false)
      | none =>
        if !frozen && cw.cwv && qIsCfg && !cw.bwp then (some (qa, cw.cwqd.toNat), false, 0, 0, true)
        else (none, false, 0, 0, false)
  let performed := if window then none else perf0
  let drains := !frozen && cw.cwv && (if qIsCfg then coreDrain else true)
  let rt : Option HostWr :=
    if !frozen && cw.cwv && !qIsCfg && cwRuntimeTarget qa then some ⟨qa, cw.cwqd.toNat, hostLocate qa⟩ else none
  -- CW moves
  let cwa := cw.cwa.toNat
  let (cwa', cwv', cwqa', cwqd', ovr) : Nat × Bool × Nat × Nat × Bool := match mv with
    | some ⟨0, v⟩ => ((cwa / 256) * 256 + v % 256, cw.cwv && !drains, qa, cw.cwqd.toNat, false)
    | some ⟨1, v⟩ => ((v % 256) * 256 + cwa % 256, cw.cwv && !drains, qa, cw.cwqd.toNat, false)
    | some ⟨_, v⟩ =>
      if cw.cwv && !drains then (cwa, true, qa, cw.cwqd.toNat, true)
      else ((cwa + 1) % 65536, true, cwa, v % 256, false)
    | none => (cwa, cw.cwv && !drains, qa, cw.cwqd.toNat, false)
  let (bpa, bpd) := performed.getD (0, 0)
  { st := { cwa := bv 16 cwa', cwv := cwv', cwqa := bv 16 cwqa', cwqd := bv 8 cwqd', bwp := performed.isSome,
            hh := hh', hha := bv 16 hha', hhd := bv 8 hhd', bpa := bv 16 bpa, bpd := bv 8 bpd },
    performed, ovr, rt }

/-- §1 Configuration latches at the end of cycle t: the write performed in t-1 enters the latches, so a write
performed in cycle W is seen by all logic from W+2 (logic sees the old value through W+1). -/
def cfgNext (cfg : Config) (cw : CwSt) : Config :=
  if cw.bwp then cfg.write cw.bpa.toNat cw.bpd.toNat else cfg

end Metronome.Machine
