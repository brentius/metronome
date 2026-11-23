import Metronome.Machine.Host

/-! §12.2 – §12.4 and §13.2 debug block state: freeze and step, digest control, edge capture control and timer,
replay levels. -/

namespace Metronome.Machine

open Util Tables

/-- §12.4 `cev = CEN && ((RISE | FALL)[12:0] & EMASK) != 0` (capture is off while `RPL`, §13.2; no event in a frozen
cycle, §12.3) and the record `rec = {DC[18:0], PIN[12:0]}`. -/
def captureEvent (d : DbgSt) (p : PinView) (frozen : Bool) : Bool × Nat :=
  let edges := (List.range N_IN_PINS).foldl (fun acc k => acc ||| (if p.rise k || p.fall k then 2 ^ k else 0)) 0
  (!frozen && d.cen && !d.rpl && (edges &&& d.emask.toNat) != 0, d.dc.toNat * 2 ^ N_IN_PINS + p.lvl)

/-- §12.2 / §12.3 / §12.4 / §13.1 / §13.2 Debug block next state.

* §12.3: a `DBG` write of byte d sets `FREEZE' = d[0]`, `FRZ' = d[0] && !d[1]`; otherwise `FRZ' = FREEZE`;
  `FRZD' = FRZ`.
* §12.2: `MEN` is `MCTL` bit 0; `M` per `misrNext`.
* §12.4 / §13.2: `ECTL` bit 0 `CEN`, bit 1 `RPL`; every `ECTL` write sets `DC' = 0` (also frozen). Capture:
  `DC' = !CEN ? 0 : (cev ? 1 : min(DC + 1, 2^19 - 1))`; replay: `apply: DC' = 0` else `min(DC + 1, 2^19 - 1)`; `DC`
  holds in a frozen cycle.
* §13.2: `apply: RLV' = (RLV & ~EMASK) | (WB[12:0] & EMASK)`; `RLV`, `EMASK` read/write.
* §13.1: a pending core write to `ECTL`, `EMASK` or `RLV` (`cwRt`) acts as a runtime write before a host write in the
  same cycle, which wins. -/
def dbgNext (s : State) (hw : Option HostWr) (cwRt : Option HostWr) (cev : Bool) (apply : Bool) (frozen : Bool) :
    DbgSt :=
  let d := s.dbg
  let hb := hwByte hw "DBG" 0
  let cb := hwByte cwRt "DBG" 0
  let pick (r : String) : Option Nat := match hb r with
    | some v => some v
    | none => cb r
  let wDbg := hb "DBG"
  let wMctl := hb "MCTL"
  let wEctl := pick "ECTL"
  let maxdc := 2 ^ 19 - 1
  let inc := min (d.dc.toNat + 1) maxdc
  let dc' : Nat :=
    if wEctl.isSome then 0
    else if frozen then d.dc.toNat
    else if d.rpl then (if apply then 0 else inc)
    else if d.cen then (if cev then 1 else inc)
    else 0
  let wb := (vget s.streams 0).wb.toNat
  let rlv1 := if apply then (d.rlv.toNat &&& (2 ^ N_IN_PINS - 1 - d.emask.toNat)) ||| (wb &&& d.emask.toNat)
    else d.rlv.toNat
  let byteW (x : Nat) (r : String) : Nat :=
    let x1 := match hwAt cwRt "DBG" 0 r with
      | some (k, v) => (setByte (bv 16 x) k v).toNat
      | none => x
    match hwAt hw "DBG" 0 r with
      | some (k, v) => (setByte (bv 16 x1) k v).toNat
      | none => x1
  { freeze := match wDbg with
      | some v => nbit v 0
      | none => d.freeze
    frz := match wDbg with
      | some v => nbit v 0 && !nbit v 1
      | none => d.freeze
    frzd := d.frz
    men := match wMctl with
      | some v => nbit v 0
      | none => d.men
    misr := misrNext s (nbit (wMctl.getD 0) 1)
    cen := match wEctl with
      | some v => nbit v 0
      | none => d.cen
    rpl := match wEctl with
      | some v => nbit v 1
      | none => d.rpl
    emask := bv 13 (byteW d.emask.toNat "EMASK")
    dc := bv 19 dc'
    rlv := bv 13 (byteW rlv1 "RLV")
    -- §12.3 transparency: a frozen cycle holds `RLVP` (RTL `if (!frz) rlv_prev <= rlv`; Python model chip.py
    -- assigns RLVP only in the unfrozen step).  Fixed 2026-11-22 (was `rlvp := d.rlv` every cycle).
    rlvp := if frozen then d.rlvp else d.rlv }

end Metronome.Machine
