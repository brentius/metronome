/-
# W4: the core combinational outputs, the executing-thread invariant and the RAM interface

This file closes the wiring hypotheses of the ChipCut premise discharges that
concern the **per-core combinational bundle** and the **data-RAM grant/landing
interface**:

* `LineThread.WireAgree.dispatch` and `.pause` (`ccw_dispatch`, `ccw_pause`),
  via `Bridge.Core.out_bridge` instantiated at the ChipCut wiring
  (`ltCbs`/`coreIn`/`sIr`), and `WireAgree.pauseDisp` (`ccw_pauseDisp`) under a
  new reachable-state invariant `ExecInv` — "a thread executing on a core is
  `RUNNING` and not `READY`" — which this file states, proves at reset
  (`execInv_reset`), preserves by one product step (`execInv_step`) and lifts to
  the trace (`execInv_trace`);
* the per-core bundle the machine uses (`Machine.coreComb` at `m`) against the
  cut's `Core.out`/`Core.fetchAddr` (`coreDisp_eq`, `corePse_eq`,
  `coreDispThread_eq`, `coreNpc_eq`, `coreFetchEn_eq`, `coreFetchAddr_eq`,
  `coreXt_eq`, `coreXl_eq`), i.e. `Bridge.Core.out_bridge`/`fetch_bridge`
  applied to the wiring of `Wire.lean`;
* the RAM grant (`ccwServed`), the host slot's grant and the streams' served
  flag: `p0_open_served`, `hostReq_open_served`, `stream_served`, through
  `Bridge.Mem.arbiter_eq` with the three requesters identified
  (`arbiter_has_congr`, `has_sreq`, `has_p0`, `has_host`);
* the landing side of the RAM interface (`p0_open_land`, `p0_open_lane`,
  `contents_open_path`, `StreamWire.landNow`): see §8 for the exact remaining
  obligation (a one-cycle landing-lag invariant on the RAM output registers).

Nothing outside this file is edited.  No `sorry`, no `native_decide`; the only
extra hypotheses are the named wiring facts (the `Bridge.Core.CoreInputBus` of
`CoreUnits.lean`, `hJGTab`, the per-stream mode equality of `StreamDbg.lean`).
-/

import Metronome.ChipCut.Proof
import Metronome.ChipCut.Discharge.CoreUnits
import Metronome.ChipCut.Discharge.LineThread
import Metronome.ChipCut.Discharge.StreamDbg
import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. `ltCbs` is the machine's `coreComb` at the cut's core input -/

/-- The machine's per-core combinational bundle `c` is `mCoreComb`. -/
theorem ltCbs_eq_mCoreComb (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2) :
    (ltCbs m)[c] = mCoreComb m pin c := by
  simp only [ltCbs, mCoreComb]
  exact vec_get_ofFn' _ c

/-- The bundle at the cut's input record, with the machine's core index and freeze
sample (the two normalisations `Wire.lean` performs). -/
theorem mCoreComb_cut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (c : Fin 2) :
    mCoreComb m pin c =
      Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz := by
  have hf : (coreIn s pin c.val).frz = m.dbg.frz := (hrel.dbg.2.1).symm
  simp only [mCoreComb, coreNat_fin2, hf]

/-- `bv 3 w` for a thread index. -/
theorem bv3_toNat (w : Nat) (h : w < 8) : (Machine.Util.bv 3 w).toNat = w := by
  simp [Machine.Util.bv, Nat.mod_eq_of_lt h]

/-- The `Bridge.Core.Rel` of the cut's core `c` (the cut state carries the
machine's `IR`, which is the state `Bridge/Core` relates; `ChipRel` pins `IR` only
while `XV`, `CoreUnits.core_next_congr` closes the difference). -/
theorem coreRel_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (c : Fin 2) :
    Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (sIr s m c) (coreIn s pin c.val) :=
  rel_of_bus s m pin c hrel hinv (hbus c)

/-- With `XV` set the cut's core state is `sIr` (the machine's `IR` is the cut's). -/
theorem sIr_eq_of_xv {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (h : (s.cores[c.val]).xv = true) : sIr s m c = s.cores[c.val] := by
  have hi : m.cores[c].ir = (s.cores[c.val]).ir := (hrel.cores c).2.1 h
  have h1 : sIr s m c = { s.cores[c.val] with ir := (s.cores[c.val]).ir } := by
    simp only [sIr, hi]
  rw [h1]

/-! ## 2. `Core.out` agreement between the cut core and the related `sIr` state -/

/-- The `sIr` projections that are unchanged. -/
theorem sIr_rv (s : State) (m : Machine.State) (c : Fin 2) :
    (sIr s m c).rv = (s.cores[c.val]).rv := rfl

/-- `XV` of `sIr`. -/
theorem sIr_xv (s : State) (m : Machine.State) (c : Fin 2) :
    (sIr s m c).xv = (s.cores[c.val]).xv := rfl

/-- `RR` of `sIr`. -/
theorem sIr_rr (s : State) (m : Machine.State) (c : Fin 2) :
    (sIr s m c).rr = (s.cores[c.val]).rr := rfl

/-- `FPC` of `sIr`. -/
theorem sIr_fpc (s : State) (m : Machine.State) (c : Fin 2) :
    (sIr s m c).fpc = (s.cores[c.val]).fpc := rfl

/-- `Core.ra` of `sIr` (reads `RV` only). -/
theorem ra_sIr (s : State) (m : Machine.State) (c : Fin 2) (i : Core.Input) :
    Core.ra (sIr s m c) i = Core.ra (s.cores[c.val]) i := rfl

/-- `Core.dpc` of `sIr` (reads the thread file and `RR`, not `IR`). -/
theorem dpc_sIr (s : State) (m : Machine.State) (c : Fin 2) (cb : Bool) (i : Core.Input) :
    Core.dpc cb (sIr s m c) i = Core.dpc cb (s.cores[c.val]) i := rfl

/-- `dispO` does not read `IR`. -/
theorem dispO_sIr {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) :
    (Core.out cb (sIr s m c) i).dispO = (Core.out cb (s.cores[c.val]) i).dispO := by
  by_cases hx : (s.cores[c.val]).xv = true
  · rw [sIr_eq_of_xv hrel hx]
  · have hx' : (s.cores[c.val]).xv = false := by simpa using hx
    have hx2 : (sIr s m c).xv = false := hx'
    simp [Core.out, Core.disp, Core.free, Core.pse, Core.xa, hx', hx2, sIr_rv]

/-- `dispE` does not read `IR` (it is a pure function of the candidate vector and
`RR`). -/
theorem dispE_sIr {s : State} {m : Machine.State} {c : Fin 2} (_hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) :
    (Core.out cb (sIr s m c) i).dispE = (Core.out cb (s.cores[c.val]) i).dispE := rfl

/-- `pauseO` (`PSE`) agrees: it needs `XV`, where `IR` is pinned. -/
theorem pauseO_sIr {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) :
    (Core.out cb (sIr s m c) i).pauseO = (Core.out cb (s.cores[c.val]) i).pauseO := by
  by_cases hx : (s.cores[c.val]).xv = true
  · rw [sIr_eq_of_xv hrel hx]
  · have hx' : (s.cores[c.val]).xv = false := by simpa using hx
    have hx2 : (sIr s m c).xv = false := hx'
    simp [Core.out, Core.pse, Core.xa, hx', hx2]

/-- `npcO` agrees whenever the pause path reads it (`PSE` ⇒ `XV`). -/
theorem npcO_sIr {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) (hpse : (Core.out cb (s.cores[c.val]) i).pauseO = true) :
    (Core.out cb (sIr s m c) i).npcO = (Core.out cb (s.cores[c.val]) i).npcO := by
  have hx : (s.cores[c.val]).xv = true := by
    by_cases h : (s.cores[c.val]).xv = true
    · exact h
    · have h' : (s.cores[c.val]).xv = false := by simpa using h
      simp [Core.out, Core.pse, Core.xa, h'] at hpse
  rw [sIr_eq_of_xv hrel hx]

/-- `fetchEn` agrees: it needs `XV` for the jump/pause terms, and is `RV`-only
otherwise. -/
theorem fetchEn_sIr {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) :
    (Core.out cb (sIr s m c) i).fetchEn = (Core.out cb (s.cores[c.val]) i).fetchEn := by
  by_cases hx : (s.cores[c.val]).xv = true
  · rw [sIr_eq_of_xv hrel hx]
  · have hx' : (s.cores[c.val]).xv = false := by simpa using hx
    have hx2 : (sIr s m c).xv = false := hx'
    simp [Core.out, Core.fetchEn, Core.jmp, Core.pse, Core.load, Core.xa, hx', hx2, sIr_rv,
      Core.ra, Core.disp, Core.free]

/-- The fetch address agrees: it is `IR`-free once `jmp`/`pse` are excluded (the
watcher address `dpc` reads the thread file and `RR`, not `IR`). -/
theorem fetchAddr_sIr {s : State} {m : Machine.State} {c : Fin 2} (hrel : ChipRel s m)
    (cb : Bool) (i : Core.Input) :
    (Core.out cb (sIr s m c) i).fetchAddr = (Core.out cb (s.cores[c.val]) i).fetchAddr := by
  by_cases hx : (s.cores[c.val]).xv = true
  · rw [sIr_eq_of_xv hrel hx]
  · have hx' : (s.cores[c.val]).xv = false := by simpa using hx
    have hx2 : (sIr s m c).xv = false := hx'
    simp [Core.out, Core.fetchAddr, Core.jmp, Core.pse, Core.load, Core.xa, hx', hx2, sIr_rv,
      sIr_fpc, Core.ra, dpc_sIr]

/-! ## 3. The per-core bundle: the machine's `coreComb` against the cut's `Core.out` -/

theorem coreDisp_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).dispO = (ltCbs m)[c].disp := by
  obtain ⟨_, _, _, hdo, _, _, _, _, _, _, _⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← hdo, dispO_sIr hrel]

theorem corePse_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).pauseO = (ltCbs m)[c].pse := by
  obtain ⟨_, hpo, _, _, _, _, _, _, _, _, _⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← hpo, pauseO_sIr hrel]

/-- With `disp` set, the machine's `dispThread` is the cut's `dispE`. -/
theorem coreDispThread_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) (hd : (ltCbs m)[c].disp = true) :
    (ltCbs m)[c].dispThread =
      (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).dispE.toNat := by
  have hcbc : mCoreComb m pin c =
      Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz :=
    mCoreComb_cut s m pin hrel c
  have hdispM : (Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz).disp = true := by
    rw [← hcbc, ← ltCbs_eq_mCoreComb]
    exact hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hde⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  have hdispC : Core.disp (c.val == 1) (sIr s m c) (coreIn s pin c.val) = true := by
    show (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).dispO = true
    rw [dispO_sIr hrel]
    rw [coreDisp_eq s m pin hrel hinv hbus hJGTab c]
    exact hd
  have hcut := hde hdispC
  have hlt : (Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz).dispThread < 8 := by
    have h := Bridge.Core.dispThread_lt m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz
    omega
  rw [ltCbs_eq_mCoreComb, hcbc, ← dispE_sIr hrel, hcut, bv3_toNat _ hlt]

/-- When `PSE` is set, the machine's `npc` is the cut's `npcO`. -/
theorem coreNpc_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) (hpse : (ltCbs m)[c].pse = true) :
    (ltCbs m)[c].npc =
      (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).npcO.toNat := by
  obtain ⟨_, _, hno, _, _, _, _, _, _, _, _⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  have hpsem : (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).pauseO = true := by
    rw [corePse_eq s m pin hrel hinv hbus hJGTab c]
    exact hpse
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← hno, npcO_sIr hrel _ _ hpsem]

/-- The cut's `fetchEn` is "the machine presents a fetch address". -/
theorem coreFetchEn_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (ltCbs m)[c].fetch.isSome =
      (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).fetchEn := by
  obtain ⟨hfe, _, _, _, _, _, _, _, _, _, _⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← hfe, fetchEn_sIr hrel]

/-- When the machine presents a fetch address, it is the cut's `fetchAddr`. -/
theorem coreFetchAddr_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (c : Fin 2) {a : Nat} (ha : (ltCbs m)[c].fetch = some a) :
    (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).fetchAddr.toNat = a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hfa, _⟩ :=
    Bridge.Core.out_bridge (ms := m) (cv := Machine.cfgView m.cfg)
      (p := Machine.pinView m.sync m.dbg) (s := sIr s m c) (i := coreIn s pin c.val)
      (coreRel_of s m pin hrel hinv hbus c) hJGTab
  have ha' : (Machine.coreComb m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (Bridge.Core.coreNat (c.val == 1)) (coreIn s pin c.val).frz).fetch = some a := by
    rw [← mCoreComb_cut s m pin hrel c, ← ltCbs_eq_mCoreComb]
    exact ha
  rw [← fetchAddr_sIr hrel]
  exact hfa a ha'

/-- The machine's core register file at the cut's `Fin` index. -/
theorem vget_cores (m : Machine.State) (c : Fin 2) :
    Machine.Util.vget m.cores c.val = m.cores[c] := by
  show m.cores[c.val]! = m.cores[c]
  rw [vec_get!_eq_get m.cores c.val c.isLt]

/-- `XT` agrees (the register file is part of `CoreRegsRel`). -/
theorem coreXt_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (c : Fin 2) :
    (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).xtO
      = (Machine.Util.vget m.cores c.val).xt := by
  show (s.cores[c.val]).xt = (Machine.Util.vget m.cores c.val).xt
  rw [vget_cores m c]
  exact ((hrel.cores c).2.2.2.2.1).symm

/-- `XL` agrees. -/
theorem coreXl_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (c : Fin 2) :
    (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).xlO
      = (Machine.Util.vget m.cores c.val).xl := by
  show (s.cores[c.val]).xl = (Machine.Util.vget m.cores c.val).xl
  rw [vget_cores m c]
  exact ((hrel.cores c).2.2.2.2.2.1).symm

/-! ## 4. List and index helpers -/

/-- `List.range 2` as an explicit list. -/
theorem range_two : List.range 2 = [0, 1] := rfl

/-- `any` over `range 2` is the two-way disjunction. -/
theorem any_range_two (f : Nat → Bool) : (List.range 2).any f = (f 0 || f 1) := by
  rw [range_two]
  simp only [List.any_cons, List.any_nil]
  cases (f 0) <;> cases (f 1) <;> rfl

/-- `findSome?` over `range 2` is the two-way choice. -/
theorem findSome_range_two {α : Type} (f : Nat → Option α) :
    (List.range 2).findSome? f = (f 0 <|> f 1) := by
  rw [range_two]
  simp only [List.findSome?_cons, List.findSome?_nil]
  cases (f 0) <;> cases (f 1) <;> rfl

/-- `vget` of `ltCbs` at `0`. -/
theorem vget_ltCbs_zero (m : Machine.State) :
    Machine.Util.vget (ltCbs m) 0 = (ltCbs m)[0] := by
  show (ltCbs m)[0]! = (ltCbs m)[0]
  rw [getElem!_eq_get (ltCbs m) (by decide : 0 < 2)]
  simp [Vector.get]

/-- `vget` of `ltCbs` at `1`. -/
theorem vget_ltCbs_one (m : Machine.State) :
    Machine.Util.vget (ltCbs m) 1 = (ltCbs m)[1] := by
  show (ltCbs m)[1]! = (ltCbs m)[1]
  rw [getElem!_eq_get (ltCbs m) (by decide : 1 < 2)]
  simp [Vector.get]

/-- `vget` of `m.cores` at `0`. -/
theorem vget_cores_zero (m : Machine.State) :
    Machine.Util.vget m.cores 0 = m.cores[0] := by
  show m.cores[0]! = m.cores[0]
  rw [getElem!_eq_get m.cores (by decide : 0 < 2)]
  simp [Vector.get]

/-- `vget` of `m.cores` at `1`. -/
theorem vget_cores_one (m : Machine.State) :
    Machine.Util.vget m.cores 1 = m.cores[1] := by
  show m.cores[1]! = m.cores[1]
  rw [getElem!_eq_get m.cores (by decide : 1 < 2)]
  simp [Vector.get]

/-! ## 5. `WireAgree.dispatch` and `WireAgree.pause` -/

/-- The disp clause at core `0`, in the `false`/`Nat`-indexed form of `Wire.lean`. -/
theorem coreDisp_zero (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.out false (s.cores[0]) (coreIn s pin 0)).dispO = (ltCbs m)[0].disp := by
  simpa using coreDisp_eq s m pin hrel hinv hbus hJGTab (0 : Fin 2)

/-- The disp clause at core `1`. -/
theorem coreDisp_one (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.out true (s.cores[1]) (coreIn s pin 1)).dispO = (ltCbs m)[1].disp := by
  simpa using coreDisp_eq s m pin hrel hinv hbus hJGTab (1 : Fin 2)

/-- The `dispThread`/`dispE` clause at core `0`. -/
theorem coreDispThread_zero (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hd : (ltCbs m)[0].disp = true) :
    (ltCbs m)[0].dispThread = (Core.out false (s.cores[0]) (coreIn s pin 0)).dispE.toNat := by
  simpa using coreDispThread_eq s m pin hrel hinv hbus hJGTab (0 : Fin 2) hd

/-- The `dispThread`/`dispE` clause at core `1`. -/
theorem coreDispThread_one (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hd : (ltCbs m)[1].disp = true) :
    (ltCbs m)[1].dispThread = (Core.out true (s.cores[1]) (coreIn s pin 1)).dispE.toNat := by
  simpa using coreDispThread_eq s m pin hrel hinv hbus hJGTab (1 : Fin 2) hd

/-- The `pse` clause at core `0`. -/
theorem corePse_zero (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.out false (s.cores[0]) (coreIn s pin 0)).pauseO = (ltCbs m)[0].pse := by
  simpa using corePse_eq s m pin hrel hinv hbus hJGTab (0 : Fin 2)

/-- The `pse` clause at core `1`. -/
theorem corePse_one (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.out true (s.cores[1]) (coreIn s pin 1)).pauseO = (ltCbs m)[1].pse := by
  simpa using corePse_eq s m pin hrel hinv hbus hJGTab (1 : Fin 2)

/-- The `npc` clause at core `0`. -/
theorem coreNpc_zero (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hpse : (ltCbs m)[0].pse = true) :
    (ltCbs m)[0].npc = (Core.out false (s.cores[0]) (coreIn s pin 0)).npcO.toNat := by
  simpa using coreNpc_eq s m pin hrel hinv hbus hJGTab (0 : Fin 2) hpse

/-- The `npc` clause at core `1`. -/
theorem coreNpc_one (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hpse : (ltCbs m)[1].pse = true) :
    (ltCbs m)[1].npc = (Core.out true (s.cores[1]) (coreIn s pin 1)).npcO.toNat := by
  simpa using coreNpc_eq s m pin hrel hinv hbus hJGTab (1 : Fin 2) hpse

/-- `XT` of core `0`. -/
theorem coreXt_zero (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m) :
    (Core.out false (s.cores[0]) (coreIn s pin 0)).xtO = (Machine.Util.vget m.cores 0).xt := by
  simpa using coreXt_eq s m pin hrel (0 : Fin 2)

/-- `XT` of core `1`. -/
theorem coreXt_one (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m) :
    (Core.out true (s.cores[1]) (coreIn s pin 1)).xtO = (Machine.Util.vget m.cores 1).xt := by
  simpa using coreXt_eq s m pin hrel (1 : Fin 2)

/-- The two-slot dispatch disjunction agrees slot by slot. -/
theorem disp_agree (a A : Bool) (p P : Nat) (b B : Bool) (q Q : Nat) (t : Nat)
    (ha : a = A) (hb : b = B) (hp : a = true → p = P) (hq : b = true → q = Q) :
    (a && (p == t) || b && (q == t)) = (A && (P == t) || B && (Q == t)) := by
  cases a <;> cases b <;> simp_all

/-- **`WireAgree.dispatch`** (the `LineThread` field, verbatim): the machine's
dispatch input is the cut's thread dispatch.  `Bridge.Core.out_bridge`'s `disp`
and `dispE` clauses at the cut's two cores. -/
theorem ccw_dispatch (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    ∀ t : Fin 6, (ltThreadIn m t).dispatch =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).dispatch := by
  intro t
  have hd0 := coreDisp_zero s m pin hrel hinv hbus hJGTab
  have hd1 := coreDisp_one s m pin hrel hinv hbus hJGTab
  have hb0 := coreDispThread_zero s m pin hrel hinv hbus hJGTab
  have hb1 := coreDispThread_one s m pin hrel hinv hbus hJGTab
  simp only [ltThreadIn, Bridge.Thread.absInput, threadIn, any_range_two, vget_ltCbs_zero,
    vget_ltCbs_one]
  exact disp_agree (ltCbs m)[0].disp (Core.out false (s.cores[0]) (coreIn s pin 0)).dispO
    (ltCbs m)[0].dispThread (Core.out false (s.cores[0]) (coreIn s pin 0)).dispE.toNat
    (ltCbs m)[1].disp (Core.out true (s.cores[1]) (coreIn s pin 1)).dispO
    (ltCbs m)[1].dispThread (Core.out true (s.cores[1]) (coreIn s pin 1)).dispE.toNat
    t.val hd0.symm hd1.symm hb0 hb1

/-- The two-slot pause choice agrees slot by slot, against the machine's
`if isSome then some (getD 0).toNat else none` form. -/
theorem pause_all (P Q : Bool) (n0 : Nat) (m0 : BitVec 8) (n1 : Nat) (m1 : BitVec 8)
    (h0 : P = true → n0 = m0.toNat) (h1 : Q = true → n1 = m1.toNat) :
    ((if P then some n0 else none) <|> (if Q then some n1 else none))
      = (if ((if P then some m0 else (if Q then some m1 else none)).isSome = true) then
          some ((if P then some m0 else (if Q then some m1 else none)).getD 0).toNat
          else none) := by
  cases P <;> cases Q <;> simp_all
/-- **`WireAgree.pause`** (the `LineThread` field, verbatim): the machine's pause
input is the cut's thread pause, with the same `npc`. -/
theorem ccw_pause (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    ∀ t : Fin 6, (ltThreadIn m t).pause =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).pause := by
  intro t
  have hp0 := corePse_zero s m pin hrel hinv hbus hJGTab
  have hp1 := corePse_one s m pin hrel hinv hbus hJGTab
  have hx0 := coreXt_zero s m pin hrel
  have hx1 := coreXt_one s m pin hrel
  have hn0 := coreNpc_zero s m pin hrel hinv hbus hJGTab
  have hn1 := coreNpc_one s m pin hrel hinv hbus hJGTab
  have hA0 : ((ltCbs m)[0].pse && m.cores[0].xt.toNat == t.val)
      = ((Core.out false (s.cores[0]) (coreIn s pin 0)).pauseO &&
          (Core.out false (s.cores[0]) (coreIn s pin 0)).xtO.toNat == t.val) := by
    rw [hp0, hx0, vget_cores_zero]
  have hA1 : ((ltCbs m)[1].pse && m.cores[1].xt.toNat == t.val)
      = ((Core.out true (s.cores[1]) (coreIn s pin 1)).pauseO &&
          (Core.out true (s.cores[1]) (coreIn s pin 1)).xtO.toNat == t.val) := by
    rw [hp1, hx1, vget_cores_one]
  simp only [ltThreadIn, Bridge.Thread.absInput, threadIn, pauseNpc, findSome_range_two,
    vget_ltCbs_zero, vget_ltCbs_one, vget_cores_zero, vget_cores_one]
  rw [hA0, hA1]
  have k0 : ((Core.out false (s.cores[0]) (coreIn s pin 0)).pauseO &&
      (Core.out false (s.cores[0]) (coreIn s pin 0)).xtO.toNat == t.val) = true →
      (ltCbs m)[0].npc = (Core.out false (s.cores[0]) (coreIn s pin 0)).npcO.toNat := by
    intro hp
    have hp' := hp
    rw [← hA0] at hp'
    exact hn0 (Bool.and_eq_true_iff.mp hp').1
  have k1 : ((Core.out true (s.cores[1]) (coreIn s pin 1)).pauseO &&
      (Core.out true (s.cores[1]) (coreIn s pin 1)).xtO.toNat == t.val) = true →
      (ltCbs m)[1].npc = (Core.out true (s.cores[1]) (coreIn s pin 1)).npcO.toNat := by
    intro hp
    have hp' := hp
    rw [← hA1] at hp'
    exact hn1 (Bool.and_eq_true_iff.mp hp').1
  exact pause_all _ _ _ _ _ _ k0 k1

/-! ## 6. The data-RAM grant: `Bridge.Mem.arbiter_eq` at the ChipCut requests -/

/-- "The request asks for the bus" (`arbiter` reads only this test). -/
def hasReq : Machine.RamReq → Bool
  | .none => false
  | _ => true

/-- The arbiter as a function of the four presence bits. -/
theorem arbiter_has (a0 a1 a2 a3 : Machine.RamReq) (f : Bool) :
    Machine.arbiter a0 a1 a2 a3 f
      = (if !f && hasReq a0 then 1 else if !f && hasReq a1 then 2
         else if !f && hasReq a2 then 3 else if hasReq a3 then 4 else 0) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases f <;> rfl

/-- `someReq` preserves presence. -/
theorem has_someReq (b : Bool) : hasReq (Bridge.Mem.someReq b) = b := by
  cases b <;> rfl

/-- Presence of a stream request as a function of `RQ`/`PV` and the mode. -/
theorem has_streamReq_eq (mode : Nat) (st : Machine.StreamSt) :
    hasReq (Machine.streamReq mode st) = (if mode = 1 ∨ mode = 2 then st.pv else st.rq) := by
  by_cases h1 : mode = 1
  · subst h1
    by_cases hp : st.pv = true
    · simp [hasReq, Machine.streamReq, hp]
    · simp [hasReq, Machine.streamReq, hp]
  · by_cases h2 : mode = 2
    · subst h2
      by_cases hp : st.pv = true
      · simp [hasReq, Machine.streamReq, hp]
      · simp [hasReq, Machine.streamReq, hp]
    · have h : ¬ (mode = 1 ∨ mode = 2) := by
        rintro (h | h)
        · exact h1 h
        · exact h2 h
      rw [if_neg h]
      by_cases hr : st.rq = true
      · simp [hasReq, Machine.streamReq, hr]
      · simp [hasReq, Machine.streamReq, hr]

/-- Presence of a stream request depends only on `RQ`/`PV` and the mode. -/
theorem has_streamReq_mode (mode : Nat) (a b : Machine.StreamSt)
    (hrq : a.rq = b.rq) (hpv : a.pv = b.pv) :
    hasReq (Machine.streamReq mode a) = hasReq (Machine.streamReq mode b) := by
  rw [has_streamReq_eq, has_streamReq_eq, hrq, hpv]

/-- The machine's stream request presence is the cut's `Stream.req`. -/
theorem has_streamReq (cap : Bool) (st : Stream.State) (i : Stream.Input) :
    hasReq (Machine.streamReq (Bridge.StreamB.modeOf cap i) (Bridge.StreamB.abs st))
      = Stream.req cap st i := by
  by_cases hcap : cap = true <;> by_cases hrpl : i.replayEn = true <;>
    by_cases hcen : i.capEn = true <;> by_cases hrx : i.cfgMode = true <;>
    cases h1 : st.rq <;> cases h2 : st.pv <;>
    simp [hasReq, Machine.streamReq, Bridge.StreamB.modeOf, Bridge.StreamB.abs, Stream.req,
      Stream.cen, Stream.rpl, hcap, hrpl, hcen, hrx, h1, h2]

/-- The cut's stream-`0` request bit is `Stream.req` of `streamViewIn` (which reads
only the capture/replay and mode fields, the same in both views). -/
theorem sReq_zero (s : State) (pin : Machine.PinIn) :
    (streamReq s 0).req = Stream.req true (streamAt s 0) (streamIn s pin 0) := by
  have h00 : ((0 : Nat) == 0) = true := by decide
  simp only [streamReq, Stream.out, Stream.req, Stream.cen, Stream.rpl, streamViewIn, streamIn,
    Strobes.capEn, h00]
  rfl

/-- The cut's stream-`1` request bit (`CAP = 0` after the `Wire.streamReq` fix):
`Stream.req` reads only the mode and `RQ`/`PV`, which the two input views share. -/
theorem sReq_one (s : State) (pin : Machine.PinIn) :
    (streamReq s 1).req = Stream.req false (streamAt s 1) (streamIn s pin 1) := by
  have h10 : ((1 : Nat) == 0) = false := by decide
  have hcfg : (streamViewIn s 1).cfgMode = (streamIn s pin 1).cfgMode := rfl
  simp only [streamReq, Stream.out, Stream.req, Stream.cen, Stream.rpl, h10, hcfg,
    Bool.false_and, Bool.or_false, Bool.not_false]

/-- Bit 0 of the packed `{S1, S0}` request word is the S0 request. -/
theorem bit0_pair (a b : Bool) :
    Mem.bit0 ((if a then (1 : BitVec 1) else 0) ++ (if b then (1 : BitVec 1) else 0)) = b := by
  cases a <;> cases b <;> decide

/-- Bit 1 of the packed `{S1, S0}` request word is the S1 request. -/
theorem bit1_pair (a b : Bool) :
    Mem.bit1 ((if a then (1 : BitVec 1) else 0) ++ (if b then (1 : BitVec 1) else 0)) = a := by
  cases a <;> cases b <;> decide

/-- The cut's `s0Req` on `memIn` is the S0 stream's request. -/
theorem s0Req_memIn (s : State) (pin : Machine.PinIn) :
    Mem.s0Req (memIn s pin) = (streamReq s 0).req := by
  simp only [Mem.s0Req, Mem.bit0, memIn, sReqV]
  exact bit0_pair (streamReq s 1).req (streamReq s 0).req

/-- The cut's `s1Req` on `memIn` is the S1 stream's request. -/
theorem s1Req_memIn (s : State) (pin : Machine.PinIn) :
    Mem.s1Req (memIn s pin) = (streamReq s 1).req := by
  simp only [Mem.s1Req, Mem.bit1, memIn, sReqV]
  exact bit1_pair (streamReq s 1).req (streamReq s 0).req

/-- The machine's stream-`0` request presence is the cut's `sReq` bit 0. -/
theorem has_sreq_zero (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    hasReq (machSreq m 0) = Mem.s0Req (memIn s pin) := by
  have hrq : m.streams[(0 : Fin 2)].rq = (streamAt s (0 : Fin 2).val).rq :=
    ((hrel.streams 0).2.2.2.2.2.1).symm
  have hpv : m.streams[(0 : Fin 2)].pv = (streamAt s (0 : Fin 2).val).pv :=
    ((hrel.streams 0).2.2.2.2.2.2.2.2.1).symm
  rw [machSreq, hmode 0]
  rw [has_streamReq_mode _ m.streams[(0 : Fin 2)] (Bridge.StreamB.abs (streamAt s (0 : Fin 2).val))
    hrq hpv]
  rw [has_streamReq]
  have hcap : ((↑(0 : Fin 2) : Nat) == 0) = true := by decide
  rw [hcap]
  rw [show Stream.req true (streamAt s (↑(0 : Fin 2))) (streamIn s pin (↑(0 : Fin 2)))
      = (streamReq s 0).req from (sReq_zero s pin).symm]
  exact (s0Req_memIn s pin).symm

/-- The machine's stream-`1` request presence is the cut's `sReq` bit 1 (with no
capture/replay armed; see `sReq_one`). -/
theorem has_sreq_one (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    hasReq (machSreq m 1) = Mem.s1Req (memIn s pin) := by
  have hrq : m.streams[(1 : Fin 2)].rq = (streamAt s (1 : Fin 2).val).rq :=
    ((hrel.streams 1).2.2.2.2.2.1).symm
  have hpv : m.streams[(1 : Fin 2)].pv = (streamAt s (1 : Fin 2).val).pv :=
    ((hrel.streams 1).2.2.2.2.2.2.2.2.1).symm
  rw [machSreq, hmode 1]
  rw [has_streamReq_mode _ m.streams[(1 : Fin 2)] (Bridge.StreamB.abs (streamAt s (1 : Fin 2).val))
    hrq hpv]
  rw [has_streamReq]
  have hcap : ((↑(1 : Fin 2) : Nat) == 0) = false := by decide
  rw [hcap]
  rw [show Stream.req false (streamAt s (↑(1 : Fin 2))) (streamIn s pin (↑(1 : Fin 2)))
      = (streamReq s 1).req from (sReq_one s pin).symm]
  exact (s1Req_memIn s pin).symm

/-- The machine's P0 request presence is the cut's `pending`. -/
theorem has_p0 (s : State) (m : Machine.State) (hrel : ChipRel s m) (hinv : Inv s) :
    hasReq (Machine.p0Req m.p0) = Mem.pending s.p0 := by
  rcases Bridge.Mem.req_cases s.p0 hinv.reqNeThree with h | h | h <;>
    simp [hasReq, Machine.p0Req, Mem.pending, hrel.p0.req, Bridge.Mem.reqOf, h, Mem.RQ_NONE]

/-- The machine's host-slot request presence is the cut's `hostQ`. -/
theorem has_host (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    hasReq (Machine.hostReq m.host) = s.p0.hostQ := by
  have h := hrel.hostReq
  simp only [Bridge.Mem.absSlot] at h
  rw [Machine.hostReq]
  cases hq : s.p0.hostQ <;> cases hw : s.p0.hostWr <;>
    simp [hasReq, h, hq, hw]

/-- **The served index**: the machine's arbiter at `runStep` is the cut's grant
priority.  This is `p0_open_served` and `hostReq_open_served` in one statement. -/
theorem ccw_served (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    machServed m = Bridge.Mem.servedIndex s.p0 (memIn s pin) := by
  have hfrz : m.dbg.frz = (memIn s pin).frz := by
    rw [hrel.dbg.2.1]; rfl
  have h0 := has_sreq_zero s m pin hrel hmode
  have h1 := has_sreq_one s m pin hrel hmode
  have h2 := has_p0 s m hrel hinv
  have h3 := has_host s m hrel
  rw [machServed, arbiter_has, hfrz, h0, h1, h2, h3, <- Bridge.Mem.arbiter_eq, arbiter_has]
  simp [has_someReq]

/-- **`p0_open_served`**: the arbiter's grant of P0 is the cut's `grantP0`. -/
theorem p0_open_served (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    (machServed m == 3) = Mem.grantP0 s.p0 (memIn s pin) := by
  rw [ccw_served s m pin hrel hinv hmode]
  obtain ⟨h01, h0p, h0h, h1p, h1h, hph⟩ := Mem.grants_exclusive s.p0 (memIn s pin)
  simp only [Bridge.Mem.servedIndex]
  cases h0 : Mem.grantS0 (memIn s pin) <;> cases h1 : Mem.grantS1 (memIn s pin) <;>
    cases hp : Mem.grantP0 s.p0 (memIn s pin) <;>
    cases hh : Mem.grantHost s.p0 (memIn s pin)
  all_goals simp_all

/-- **`hostReq_open_served`**: the arbiter's grant of the host is the cut's
`grantHost`. -/
theorem hostReq_open_served (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    (machServed m == 4) = Mem.grantHost s.p0 (memIn s pin) := by
  rw [ccw_served s m pin hrel hinv hmode]
  obtain ⟨h01, h0p, h0h, h1p, h1h, hph⟩ := Mem.grants_exclusive s.p0 (memIn s pin)
  simp only [Bridge.Mem.servedIndex]
  cases h0 : Mem.grantS0 (memIn s pin) <;> cases h1 : Mem.grantS1 (memIn s pin) <;>
    cases hp : Mem.grantP0 s.p0 (memIn s pin) <;>
    cases hh : Mem.grantHost s.p0 (memIn s pin)
  all_goals simp_all

/-- The cut's stream-grant choice is `grantS0`. -/
theorem servedIndex_s0 (s : State) (pin : Machine.PinIn) :
    (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 1) = Mem.grantS0 (memIn s pin) := by
  simp only [Bridge.Mem.servedIndex]
  cases Mem.grantS0 (memIn s pin) <;> cases Mem.grantS1 (memIn s pin) <;>
    cases Mem.grantP0 s.p0 (memIn s pin) <;> cases Mem.grantHost s.p0 (memIn s pin) <;> decide

/-- The cut's stream-grant choice is `grantS1`. -/
theorem servedIndex_s1 (s : State) (pin : Machine.PinIn) :
    (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 2) = Mem.grantS1 (memIn s pin) := by
  obtain ⟨h01, h0p, h0h, h1p, h1h, hph⟩ := Mem.grants_exclusive s.p0 (memIn s pin)
  simp only [Bridge.Mem.servedIndex]
  cases h0 : Mem.grantS0 (memIn s pin) <;> cases h1 : Mem.grantS1 (memIn s pin) <;>
    cases hp : Mem.grantP0 s.p0 (memIn s pin) <;>
    cases hh : Mem.grantHost s.p0 (memIn s pin)
  all_goals simp_all

/-- **`StreamWire.input`'s `served` field**: the machine's per-stream `served` is
the cut's `gnt`. -/
theorem stream_served (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (k : Fin 2) :
    (machStreamIn m k).served = (streamIn s pin k.val).gnt := by
  have hs := ccw_served s m pin hrel hinv hmode
  rcases k with ⟨kv, hk⟩
  have hkv : kv = 0 ∨ kv = 1 := by omega
  rcases hkv with rfl | rfl
  · show (machServed m == 0 + 1) = streamGnt s pin 0
    rw [hs, servedIndex_s0]
    show Mem.grantS0 (memIn s pin) = (if (0 : Nat) == 0 then Mem.grantS0 (memIn s pin)
      else Mem.grantS1 (memIn s pin))
    simp
  · show (machServed m == 1 + 1) = streamGnt s pin 1
    rw [hs, servedIndex_s1]
    show Mem.grantS1 (memIn s pin) = (if (1 : Nat) == 0 then Mem.grantS0 (memIn s pin)
      else Mem.grantS1 (memIn s pin))
    simp


/-! ## 7. The executing-thread invariant for `WireAgree.pauseDisp`

`pauseDisp` needs one cross-cycle fact: a thread that a core is *executing*
(`XT` while `XV`/`RV`) is `RUNNING` and never `READY`.  Two supporting fields
make the invariant inductive: the executing index is a thread index (`xtLt`), and
two different executing cores never share a thread (`sep`) — without `sep` a
pause could be aimed at our own executing thread by the *other* core.

`ExecInv` is proved at reset (`execInv_reset`), preserved by one product step
(`execInv_step`) and lifted to the trace (`execInv_trace`). -/
structure ExecInv (s : State) : Prop where
  /-- The executing thread index is a thread index. -/
  xtLt : ∀ c : Fin 2, (s.cores[c.val].xt).toNat < 6
  /-- An executing thread is not `READY`. -/
  ready : ∀ c : Fin 2, ((s.cores[c.val].xv || s.cores[c.val].rv) = true) →
    (threadAt s (s.cores[c.val].xt).toNat).ready = false
  /-- An executing thread is `RUNNING`. -/
  running : ∀ c : Fin 2, ((s.cores[c.val].xv || s.cores[c.val].rv) = true) →
    (threadAt s (s.cores[c.val].xt).toNat).running = true
  /-- Two executing cores never share their executing thread. -/
  sep : ∀ c c' : Fin 2, c ≠ c' → ((s.cores[c.val].xv || s.cores[c.val].rv) = true) →
    ((s.cores[c'.val].xv || s.cores[c'.val].rv) = true) →
    s.cores[c.val].xt ≠ s.cores[c'.val].xt

/-- The invariant holds in the reset state (no core is executing). -/
theorem execInv_reset (cont : Contents) : ExecInv (resetState cont) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    simp [resetState]
  · intro c h
    simp [resetState] at h
  · intro c h
    simp [resetState] at h
  · intro c c' _ h
    simp [resetState] at h

/-- `ExecInv.ready` from an explicit `XV`/`RV` disjunction. -/
theorem execInv_not_ready {s : State} (hinv : ExecInv s) (c : Fin 2)
    (h : (s.cores[c.val].xv = true ∨ s.cores[c.val].rv = true)) :
    (threadAt s (s.cores[c.val].xt).toNat).ready = false := by
  rcases h with h | h
  · exact hinv.ready c (by simp [h])
  · exact hinv.ready c (by simp [h])

/-! ### Eliminating the cut's two combinational dispatch/pause choices -/

/-- A cut dispatch of thread `t` makes it `READY`. -/
theorem disp_ready (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (hinv : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (t : Fin 6) (h : (threadIn s pin t.val).disp = true) : (threadAt s t.val).ready = true := by
  have hd : (ltThreadIn m t).dispatch = true := by
    rw [ccw_dispatch s m pin hrel hinv hbus hJGTab t]
    exact h
  have hm := ltThreadIn_dispatch_ready m t hd
  rw [hrel.threads t] at hm
  exact hm

/-- A cut pause targets a core whose `PSE` is set on `XT`. -/
theorem pause_pse {s : State} {pin : Machine.PinIn} {t : Nat}
    (h : (threadIn s pin t).pause = true) :
    ∃ c : Fin 2, (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).pauseO = true ∧
      (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).xtO.toNat = t := by
  have hp : (pauseNpc s pin t).isSome = true := h
  simp only [pauseNpc] at hp
  split at hp
  · rename_i h0
    refine ⟨0, ?_, ?_⟩
    · simpa using (Bool.and_eq_true_iff.mp h0).1
    · simpa using (Bool.and_eq_true_iff.mp h0).2
  · split at hp
    · rename_i h1
      refine ⟨1, ?_, ?_⟩
      · simpa using (Bool.and_eq_true_iff.mp h1).1
      · simpa using (Bool.and_eq_true_iff.mp h1).2
    · simp at hp

/-- **`WireAgree.pauseDisp`** (the `LineThread` field, verbatim): no thread is
paused and dispatched in the same cycle. -/
theorem ccw_pauseDisp (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : ExecInv s) (hinvI : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    ∀ t : Fin 6,
      Not ((threadIn s pin t.val).pause = true ∧ (threadIn s pin t.val).disp = true) := by
  intro t hcon
  obtain ⟨hpause, hdisp⟩ := hcon
  obtain ⟨c, hpse, hxt⟩ := pause_pse hpause
  have hxv : (s.cores[c.val].xv = true ∨ s.cores[c.val].rv = true) := by
    left
    have h := hpse
    simp only [Core.out, Core.pse, Core.xa, Bool.and_eq_true] at h
    exact h.1.1
  have hnf : (threadAt s (s.cores[c.val].xt).toNat).ready = false := execInv_not_ready hinv c hxv
  have hnf2 : (threadAt s ((Core.out (c.val == 1) (s.cores[c.val])
      (coreIn s pin c.val)).xtO.toNat)).ready = false := hnf
  rw [hxt] at hnf2
  have htr : (threadAt s t.val).ready = true :=
    disp_ready s m pin hrel hinvI hbus hJGTab t hdisp
  rw [hnf2] at htr
  exact absurd htr (by decide)

/-! ## 8. The one-cycle landing lag (`p0_open_land`, `p0_open_lane`, `landNow`)

The machine writes `ramOwner`/`ramLane`/`ramOut` from the **served read of the
current cycle** (`runStep`: `owner' = match req with | .rd _ l => (served, l)`),
while the cut latches the landing in the **next** cycle (`Mem.landNext`,
`Mem.landLaneNext`, the stream `LD`).  The relation between the two is therefore a
reachable-state invariant, not a current-state identity. -/
def LandingRel (s : State) : Prop :=
  -- A pending P0 landing is the machine's owner-3 output.
  ((s.cont.ramOwner == 3) = (s.p0.land && !s.freeze.frzd)) ∧
  -- While a P0 landing is pending the output lane is P0's.
  (s.p0.land = true → s.cont.ramLane = s.p0.landLane) ∧
  -- A stream's landing is the machine's owner-k+1 output.
  (∀ k : Nat, k < 2 →
    (s.cont.ramOwner == k + 1) = ((streamAt s k).ld && !s.freeze.frzd))

/-- `LandingRel` holds at reset for the power-on contents (owner/lane zero). -/
theorem landingRel_reset (cont : Contents) (h0 : cont.ramOwner = 0) :
    LandingRel (resetState cont) := by
  have h3 : (cont.ramOwner == 3) = false := by
    rw [h0]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [resetState, Mem.resetState, CoreCtl.freezeReset, h3]
  · intro h
    simp [resetState, Mem.resetState, CoreCtl.freezeReset] at h
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    have hk' : (cont.ramOwner == k + 1) = false := by
      rw [h0]
      rcases hk01 with rfl | rfl <;> rfl
    rcases hk01 with rfl | rfl <;>
      simp [resetState, Mem.resetState, CoreCtl.freezeReset, Stream.resetState,
        streamAt, Vector.getElem_replicate, hk']

/-- **`p0_open_land`** from `LandingRel` (`ChipRel.ramOwner`). -/
theorem p0_open_land (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hland : LandingRel s) :
    (m.ramOwner == 3) = (s.p0.land && !(memIn s pin).frzd) := by
  obtain ⟨h1, _, _⟩ := hland
  rw [hrel.ramOwner]
  exact h1

/-- **`p0_open_lane`** in the `Contents` form of `MemHostCfg`, guarded by the
pending landing.  (`p0Next` reads the lane *only* when `ramOwner == 3`; the
unguarded form is false in general — `ramLane` follows any served read, while
`landLane` latches `lane PTR` every unfrozen cycle, `Mem.lean:409-410`.) -/
theorem p0_open_lane_contents (s : State) (hland : LandingRel s) (h : s.p0.land = true) :
    s.cont.ramLane = s.p0.landLane := by
  obtain ⟨_, h2, _⟩ := hland
  exact h2 h

/-- **`p0_open_lane`** from `LandingRel`, in the machine form (<ChipRel.ramLane>`). -/
theorem p0_open_lane (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hland : LandingRel s) (h : s.p0.land = true) :
    m.ramLane = s.p0.landLane := by
  rw [hrel.ramLane]
  exact p0_open_lane_contents s hland h

/-- **The `StreamWire.input.landNow` field** from `LandingRel`. -/
theorem stream_landNow (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hland : LandingRel s) (k : Nat) (hk : k < 2) :
    (m.ramOwner == k + 1) = ((streamAt s k).ld && !(streamIn s pin k).frzd) := by
  obtain ⟨_, _, h3⟩ := hland
  rw [hrel.ramOwner]
  exact h3 k hk

/-! ## 9. `ExecInv` preservation: `execInv_step`

`ExecInv` is preserved by one product step.  The reset branch is the reset
product.  In the active branch a frozen cycle holds every core (`Core.frz_holds`
makes `XV`, `RV`, `XT` unchanged) and presents no dispatch, no pause and no
trigger to any thread (`Core.frz_no_fetch` and `Step.threadIn`'s `!FRZ` gates),
so `READY`/`RUNNING` hold.  In an unfrozen cycle:

* a core that dispatches executes the dispatched thread: the thread step clears
  its `READY` and sets its `RUNNING`, and a pause of the same thread is excluded
  because a dispatched thread is `READY` (`disp_ready_cut`) while a paused
  executing thread is not (`pause_not_ready`);
* a core that does not dispatch keeps its `XT`, and `XV' ‖ RV'` forces
  `XV ‖ RV` (`xvrv_of_step`) because `load` needs `RV` and `jmp` needs `XV`;
  the invariant then carries the thread's `READY` (and `accept` is blocked by
  `RUNNING`) and `RUNNING` down, with a pause of that thread excluded either by
  the pause's own core (`pse` kills `load`/`jmp`) or by `sep`;
* `sep` itself is preserved: two dispatching cores cannot pick the same thread
  because the candidate mask of core 0 is `~~~CORE` and that of core 1 is
  `CORE` (`disp_core_bit`, `dispE_sep`); a dispatching core and a non-dispatching
  one would share a thread whose `READY` bit is both true (dispatch) and false
  (`ExecInv.ready`).

The invariant needs no wiring hypothesis, so the trace form below is
unconditional. -/

theorem coreIn_resetN (s : State) (pin : Machine.PinIn) (c : Nat) :
    (coreIn s pin c).resetN = runRst s pin := rfl

theorem coreIn_frz (s : State) (pin : Machine.PinIn) (c : Nat) :
    (coreIn s pin c).frz = s.freeze.frz := rfl

theorem threadIn_resetN (s : State) (pin : Machine.PinIn) (t : Nat) :
    (threadIn s pin t).resetN = runRst s pin := rfl

theorem activeStep_core (s : State) (pin : Machine.PinIn) (c : Fin 2) :
    (activeStep s pin).cores[c.val] =
      Core.step (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
  have hvec : (activeStep s pin).cores = Vector.ofFn fun i : Fin 2 =>
      Core.step (i.val == 1) (s.cores[i.val]) (coreIn s pin i.val) := rfl
  rw [hvec]
  simp

theorem activeStep_core_xv (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = false) :
    (activeStep s pin).cores[c.val].xv = Core.load (s.cores[c.val]) (coreIn s pin c.val) := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = false := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.xv_next, h1, h2]

theorem activeStep_core_rv (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = false) :
    (activeStep s pin).cores[c.val].rv =
      (Core.jmp (s.cores[c.val]) (coreIn s pin c.val) ||
        Core.load (s.cores[c.val]) (coreIn s pin c.val) ||
        Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)) := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = false := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.rv_next, Core.fetchEn, h1, h2]

theorem activeStep_core_xt (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = false) :
    (activeStep s pin).cores[c.val].xt =
      (if Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) then
        Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)
      else (s.cores[c.val]).xt) := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = false := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.xt_next, h1, h2]

theorem activeStep_core_xv_frz (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) :
    (activeStep s pin).cores[c.val].xv = (s.cores[c.val]).xv := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = true := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.xv_next, h1, h2]

theorem activeStep_core_rv_frz (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) :
    (activeStep s pin).cores[c.val].rv = (s.cores[c.val]).rv := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = true := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.rv_next, h1, h2]

theorem activeStep_core_xt_frz (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) :
    (activeStep s pin).cores[c.val].xt = (s.cores[c.val]).xt := by
  have h1 : (coreIn s pin c.val).resetN = true := by rw [coreIn_resetN]; exact hac
  have h2 : (coreIn s pin c.val).frz = true := by rw [coreIn_frz]; exact hf
  rw [activeStep_core]
  simp [Core.xt_next, h1, h2]

theorem threadIn_frz (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true) (t : Nat) :
    (threadIn s pin t).disp = false ∧ (threadIn s pin t).pause = false ∧
      Thread.trig (threadAt s t) (threadIn s pin t) = false := by
  have hf0 : (coreIn s pin 0).frz = true := by rw [coreIn_frz]; exact hf
  have hf1 : (coreIn s pin 1).frz = true := by rw [coreIn_frz]; exact hf
  have h0 := Core.frz_no_fetch false (s.cores[0]) (coreIn s pin 0) hf0
  have h1 := Core.frz_no_fetch true (s.cores[1]) (coreIn s pin 1) hf1
  have hd0 : (Core.out false (s.cores[0]) (coreIn s pin 0)).dispO = false := h0.2.2.2.1
  have hd1 : (Core.out true (s.cores[1]) (coreIn s pin 1)).dispO = false := h1.2.2.2.1
  have hp0 : (Core.out false (s.cores[0]) (coreIn s pin 0)).pauseO = false := h0.2.2.1
  have hp1 : (Core.out true (s.cores[1]) (coreIn s pin 1)).pauseO = false := h1.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [threadIn, hd0, hd1]
    simp
  · simp only [threadIn, pauseNpc, hp0, hp1]
    simp
  · simp only [Thread.trig, threadIn, hf]
    simp

theorem threadAt_step_eq (s : State) (pin : Machine.PinIn) (n : Nat) (hn : n < 6) :
    threadAt (activeStep s pin) n = Thread.step (threadAt s n) (threadIn s pin n) := by
  simpa using activeStep_thread s pin ⟨n, hn⟩

theorem thread_step_frz_ready (s : State) (pin : Machine.PinIn)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) (n : Nat) (hn : n < 6) :
    (threadAt (activeStep s pin) n).ready = (threadAt s n).ready := by
  obtain ⟨hdisp, _hpause, htrig⟩ := threadIn_frz s pin hf n
  have hres : (threadIn s pin n).resetN = true := by rw [threadIn_resetN]; exact hac
  rw [threadAt_step_eq s pin n hn, Thread.step_active _ _ hres]
  have hacc : Thread.accept (threadAt s n) (threadIn s pin n) = false := by
    simp [Thread.accept, htrig]
  simp [Thread.readyNext, hdisp, hacc]

theorem thread_step_frz_running (s : State) (pin : Machine.PinIn)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) (n : Nat) (hn : n < 6) :
    (threadAt (activeStep s pin) n).running = (threadAt s n).running := by
  obtain ⟨hdisp, hpause, _htrig⟩ := threadIn_frz s pin hf n
  have hres : (threadIn s pin n).resetN = true := by rw [threadIn_resetN]; exact hac
  rw [threadAt_step_eq s pin n hn, Thread.step_active _ _ hres]
  simp [Thread.runningNext, hdisp, hpause]

theorem selIdx_bit (candv : BitVec 6) (rr : BitVec 3) (h : Core.winOf candv rr ≠ 0) :
    Core.bitOf (Core.winOf candv rr) (Core.selIdx (Core.winOf candv rr)).toNat = true := by
  revert h
  revert candv rr
  decide

theorem bitOf_winOf {candv : BitVec 6} {rr : BitVec 3} {j : BitVec 3}
    (h : Core.bitOf (Core.winOf candv rr) j.toNat = true) :
    Core.bitOf candv j.toNat = true := by
  revert h
  revert candv rr j
  decide

theorem bitOf_not {w : Nat} (v : BitVec w) (k : Nat) (hk : k < w) :
    Core.bitOf (~~~v) k = !(Core.bitOf v k) := by
  rw [Bridge.Core.bitOf_eq_getLsbD, Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_not]
  simp [hk]

theorem mine_bit_cb {i : Core.Input} {cb : Bool} {k : Nat} (hk : k < 6)
    (h : Core.bitOf (Core.mine cb i) k = true) : Core.bitOf i.tCore k = cb := by
  cases cb
  · simp only [Core.mine, Bool.false_eq_true, if_false] at h
    rw [bitOf_not i.tCore k hk] at h
    simpa using h
  · simpa [Core.mine] using h

theorem cand_bit_of_disp (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (h : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true) :
    Core.bitOf (Core.cand (c.val == 1) (coreIn s pin c.val))
      (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat = true := by
  have hne : Core.cand (c.val == 1) (coreIn s pin c.val) ≠ 0 := by
    have h' := h
    simp only [Core.disp, Bool.and_eq_true] at h'
    intro h0
    rw [h0] at h'
    simp at h'
  have hw : Core.winOf (Core.cand (c.val == 1) (coreIn s pin c.val)) (s.cores[c.val]).rr ≠ 0 := by
    intro h0
    rw [Bridge.Core.winOf_ne_zero] at h0
    exact hne h0
  have hb : Core.bitOf (Core.winOf (Core.cand (c.val == 1) (coreIn s pin c.val))
        (s.cores[c.val]).rr)
      (Core.selIdx (Core.winOf (Core.cand (c.val == 1) (coreIn s pin c.val))
        (s.cores[c.val]).rr)).toNat = true :=
    selIdx_bit _ _ hw
  exact bitOf_winOf (by simpa [Core.dispE] using hb)

theorem cand_mine_bit (cs : Core.State) (i : Core.Input) (cb : Bool) (j : BitVec 3)
    (h : Core.bitOf (Core.cand cb i) j.toNat = true) :
    Core.bitOf (Core.mine cb i) j.toNat = true := by
  rw [Core.cand, Bridge.Core.bitOf_and, Bridge.Core.bitOf_and,
    Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

theorem disp_core_bit (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (h : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true) :
    Core.bitOf (coreIn s pin c.val).tCore
        (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat = (c.val == 1) :=
  mine_bit_cb (Core.dispE_toNat_le_five _ _ _)
    (cand_mine_bit (s.cores[c.val]) (coreIn s pin c.val) (c.val == 1) _
      (cand_bit_of_disp s pin c h))

theorem fin2_eq_of_beq_eq (a b : Fin 2) (h : (a.val == 1) = (b.val == 1)) : a = b := by
  rcases a with ⟨av, hav⟩
  rcases b with ⟨bv, hbv⟩
  have ha : av = 0 ∨ av = 1 := by omega
  have hb : bv = 0 ∨ bv = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

theorem dispE_sep (s : State) (pin : Machine.PinIn) (c c' : Fin 2) (hne : c ≠ c')
    (h : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true)
    (h' : Core.disp (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) = true) :
    Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) ≠
      Core.dispE (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) := by
  intro he
  have h1 : Core.bitOf (coreIn s pin c.val).tCore
      (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat = (c.val == 1) :=
    disp_core_bit s pin c h
  have h2 : Core.bitOf (coreIn s pin c.val).tCore
      (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat = (c'.val == 1) := by
    have h2' := disp_core_bit s pin c' h'
    rw [← he] at h2'
    simpa only [coreIn] using h2'
  have h1' := h1
  simp only [coreIn] at h1' h2
  rw [h1'] at h2
  exact hne (fin2_eq_of_beq_eq c c' h2)

theorem disp_ready_cut (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (h : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true) :
    (threadAt s (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).ready
      = true := by
  have hc := cand_bit_of_disp s pin c h
  rw [Core.cand, Bridge.Core.bitOf_and, Bridge.Core.bitOf_and,
    Bool.and_eq_true, Bool.and_eq_true] at hc
  have htr : Core.bitOf (coreIn s pin c.val).tReady
      (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat = true := hc.1.1
  have he : (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat < 6 :=
    Core.dispE_toNat_le_five _ _ _
  rw [tReady_bit s pin c.val _ he] at htr
  exact htr

theorem threadIn_disp_of_core (s : State) (pin : Machine.PinIn) (c : Fin 2)
    (h : (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).dispO = true) :
    (threadIn s pin (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).disp
      = true := by
  rcases c with ⟨cv, hcv⟩
  have hc : cv = 0 ∨ cv = 1 := by omega
  rcases hc with rfl | rfl
  · have hb : ((0 : Nat) == 1) = false := by decide
    have hde : (Core.out false (s.cores[0]) (coreIn s pin 0)).dispE =
        Core.dispE false (s.cores[0]) (coreIn s pin 0) := rfl
    simp only [hb] at h
    simp only [threadIn, hde]
    rw [h]
    simp
  · have hb : ((1 : Nat) == 1) = true := by decide
    have hde : (Core.out true (s.cores[1]) (coreIn s pin 1)).dispE =
        Core.dispE true (s.cores[1]) (coreIn s pin 1) := rfl
    simp only [hb] at h
    simp only [threadIn, hde]
    rw [h]
    simp

theorem pause_not_ready {s : State} {pin : Machine.PinIn} (hinv : ExecInv s) (t : Nat)
    (h : (threadIn s pin t).pause = true) : (threadAt s t).ready = false := by
  obtain ⟨c, hpse, hxt⟩ := pause_pse h
  have hpse' : Core.pse (s.cores[c.val]) (coreIn s pin c.val) = true := by
    simpa [Core.out] using hpse
  have hx : (s.cores[c.val].xv || s.cores[c.val].rv) = true := by
    have h' := hpse'
    simp only [Core.pse, Core.xa, Bool.and_eq_true] at h'
    simp [h'.1.1]
  have h1 := hinv.ready c hx
  have hxt' := hxt
  simp only [Core.out] at hxt'
  rwa [hxt'] at h1

theorem rv_of_load {cs : Core.State} {i : Core.Input} (h : Core.load cs i = true) :
    cs.rv = true := by
  by_cases hr : cs.rv = true
  · exact hr
  · have hr' : cs.rv = false := by simpa using hr
    simp [Core.load, Core.ra, hr'] at h

theorem xv_of_jmp {cs : Core.State} {i : Core.Input} (h : Core.jmp cs i = true) :
    cs.xv = true := by
  by_cases hx : cs.xv = true
  · exact hx
  · have hx' : cs.xv = false := by simpa using hx
    simp [Core.jmp, Core.xa, hx'] at h

theorem xvrv_of_step (s : State) (pin : Machine.PinIn) (hac : runRst s pin = true)
    (hf : s.freeze.frz = false) (c : Fin 2)
    (hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = false)
    (hx : ((activeStep s pin).cores[c.val].xv || (activeStep s pin).cores[c.val].rv) = true) :
    ((s.cores[c.val]).xv || (s.cores[c.val]).rv) = true := by
  by_cases hl : Core.load (s.cores[c.val]) (coreIn s pin c.val) = true
  · rw [rv_of_load hl]; simp
  · have hl' : Core.load (s.cores[c.val]) (coreIn s pin c.val) = false := by simpa using hl
    have hj : Core.jmp (s.cores[c.val]) (coreIn s pin c.val) = true := by
      have h' := hx
      rw [activeStep_core_xv s pin c hac hf, activeStep_core_rv s pin c hac hf, hd, hl'] at h'
      simpa using h'
    rw [xv_of_jmp hj]; simp

theorem not_pause_exec (s : State) (pin : Machine.PinIn) (hinv : ExecInv s)
    (hac : runRst s pin = true) (hf : s.freeze.frz = false) (c : Fin 2)
    (hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = false)
    (hx : ((activeStep s pin).cores[c.val].xv || (activeStep s pin).cores[c.val].rv) = true) :
    (threadIn s pin ((s.cores[c.val]).xt).toNat).pause = false := by
  by_cases hp : (threadIn s pin ((s.cores[c.val]).xt).toNat).pause = true
  · obtain ⟨c', hpse, hxt⟩ := pause_pse hp
    have hxrv : ((s.cores[c.val]).xv || (s.cores[c.val]).rv) = true :=
      xvrv_of_step s pin hac hf c hd hx
    have hpse' : Core.pse (s.cores[c'.val]) (coreIn s pin c'.val) = true := by
      simpa [Core.out] using hpse
    have hxv' : (s.cores[c'.val].xv = true) := by
      have h := hpse'
      simp only [Core.pse, Core.xa, Bool.and_eq_true] at h
      exact h.1.1
    by_cases hcc : c' = c
    · rw [hcc] at hpse'
      have hl : Core.load (s.cores[c.val]) (coreIn s pin c.val) = false := by
        simp [Core.load, hpse']
      have hj : Core.jmp (s.cores[c.val]) (coreIn s pin c.val) = false := by
        have hb : Core.i_pause (s.cores[c.val]) = true := by
          have h := hpse'
          simp only [Core.pse, Bool.and_eq_true] at h
          exact h.2
        simp [Core.jmp, hb]
      have hx' := hx
      rw [activeStep_core_xv s pin c hac hf, activeStep_core_rv s pin c hac hf, hl, hj, hd] at hx'
      simp at hx'
    · have hxv'' : (s.cores[c'.val].xv || s.cores[c'.val].rv) = true := by simp [hxv']
      have hsep := hinv.sep c' c hcc hxv'' hxrv
      have hxt' := hxt
      simp only [Core.out] at hxt'
      exact absurd (BitVec.eq_of_toNat_eq hxt') hsep
  · simpa using hp

theorem pause_false_of_disp (s : State) (pin : Machine.PinIn) (hinv : ExecInv s) (c : Fin 2)
    (hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true) :
    (threadIn s pin (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).pause
      = false := by
  by_cases hp : (threadIn s pin
      (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).pause = true
  · have h1 := pause_not_ready hinv _ hp
    have h2 := disp_ready_cut s pin c hd
    rw [h2] at h1
    exact absurd h1 (by decide)
  · simpa using hp

theorem execInv_xtLt_step (s : State) (pin : Machine.PinIn) (hinv : ExecInv s)
    (hac : runRst s pin = true) (c : Fin 2) :
    ((activeStep s pin).cores[c.val].xt).toNat < 6 := by
  by_cases hf : s.freeze.frz = true
  · rw [activeStep_core_xt_frz s pin c hac hf]
    exact hinv.xtLt c
  · have hf' : s.freeze.frz = false := by simpa using hf
    rw [activeStep_core_xt s pin c hac hf']
    by_cases hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true
    · simp [hd, Core.dispE_toNat_le_five]
    · simp only [hd, Bool.false_eq_true, if_false]
      exact hinv.xtLt c

theorem execInv_exec_step_frz (s : State) (pin : Machine.PinIn) (hinv : ExecInv s)
    (hac : runRst s pin = true) (hf : s.freeze.frz = true) (c : Fin 2)
    (hx : ((activeStep s pin).cores[c.val].xv || (activeStep s pin).cores[c.val].rv) = true) :
    (threadAt (activeStep s pin) ((activeStep s pin).cores[c.val].xt).toNat).ready = false ∧
      (threadAt (activeStep s pin) ((activeStep s pin).cores[c.val].xt).toNat).running = true := by
  have hx' : ((s.cores[c.val]).xv || (s.cores[c.val]).rv) = true := by
    have h := hx
    rw [activeStep_core_xv_frz s pin c hac hf, activeStep_core_rv_frz s pin c hac hf] at h
    exact h
  have hlt : ((s.cores[c.val]).xt).toNat < 6 := hinv.xtLt c
  rw [activeStep_core_xt_frz s pin c hac hf]
  exact ⟨by
      rw [thread_step_frz_ready s pin hac hf _ hlt]
      exact hinv.ready c hx',
    by
      rw [thread_step_frz_running s pin hac hf _ hlt]
      exact hinv.running c hx'⟩

theorem execInv_exec_step (s : State) (pin : Machine.PinIn) (hinv : ExecInv s)
    (hac : runRst s pin = true) (hf : s.freeze.frz = false) (c : Fin 2)
    (hx : ((activeStep s pin).cores[c.val].xv || (activeStep s pin).cores[c.val].rv) = true) :
    (threadAt (activeStep s pin) ((activeStep s pin).cores[c.val].xt).toNat).ready = false ∧
      (threadAt (activeStep s pin) ((activeStep s pin).cores[c.val].xt).toNat).running = true := by
  by_cases hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true
  · have hxt : (activeStep s pin).cores[c.val].xt =
        Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
      rw [activeStep_core_xt s pin c hac hf, hd]
      simp
    have hlt : (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat < 6 :=
      Core.dispE_toNat_le_five _ _ _
    have hdin : (threadIn s pin
        (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).disp = true :=
      threadIn_disp_of_core s pin c hd
    have hres : (threadIn s pin
        (Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat).resetN = true := by
      rw [threadIn_resetN]; exact hac
    have hnp := pause_false_of_disp s pin hinv c hd
    refine ⟨?_, ?_⟩
    · rw [hxt, threadAt_step_eq s pin _ hlt, Thread.step_active _ _ hres]
      simp [Thread.readyNext, hdin]
    · rw [hxt, threadAt_step_eq s pin _ hlt, Thread.step_active _ _ hres]
      simp [Thread.runningNext, hdin, hnp]
  · have hdf : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = false := by
      simpa using hd
    have hxt : (activeStep s pin).cores[c.val].xt = (s.cores[c.val]).xt := by
      rw [activeStep_core_xt s pin c hac hf, hdf]
      simp
    have hlt : ((s.cores[c.val]).xt).toNat < 6 := hinv.xtLt c
    have hxrv := xvrv_of_step s pin hac hf c hdf hx
    have hrd : (threadAt s ((s.cores[c.val]).xt).toNat).ready = false := hinv.ready c hxrv
    have hrn : (threadAt s ((s.cores[c.val]).xt).toNat).running = true := hinv.running c hxrv
    have hres : (threadIn s pin ((s.cores[c.val]).xt).toNat).resetN = true := by
      rw [threadIn_resetN]; exact hac
    have hnp := not_pause_exec s pin hinv hac hf c hdf hx
    refine ⟨?_, ?_⟩
    · rw [hxt, threadAt_step_eq s pin _ hlt, Thread.step_active _ _ hres]
      have hacc : Thread.accept (threadAt s ((s.cores[c.val]).xt).toNat)
          (threadIn s pin ((s.cores[c.val]).xt).toNat) = false := by
        simp [Thread.accept, Thread.busy, hrd, hrn]
      simp [Thread.readyNext, hacc, hrd]
    · rw [hxt, threadAt_step_eq s pin _ hlt, Thread.step_active _ _ hres]
      simp [Thread.runningNext, hnp, hrn]

theorem execInv_sep_step (s : State) (pin : Machine.PinIn) (hinv : ExecInv s)
    (hac : runRst s pin = true) (c c' : Fin 2) (hne : c ≠ c')
    (hx : ((activeStep s pin).cores[c.val].xv || (activeStep s pin).cores[c.val].rv) = true)
    (hx' : ((activeStep s pin).cores[c'.val].xv || (activeStep s pin).cores[c'.val].rv) = true) :
    (activeStep s pin).cores[c.val].xt ≠ (activeStep s pin).cores[c'.val].xt := by
  by_cases hf : s.freeze.frz = true
  · have h1 : ((s.cores[c.val]).xv || (s.cores[c.val]).rv) = true := by
      have h := hx
      rw [activeStep_core_xv_frz s pin c hac hf, activeStep_core_rv_frz s pin c hac hf] at h
      exact h
    have h2 : ((s.cores[c'.val]).xv || (s.cores[c'.val]).rv) = true := by
      have h := hx'
      rw [activeStep_core_xv_frz s pin c' hac hf, activeStep_core_rv_frz s pin c' hac hf] at h
      exact h
    rw [activeStep_core_xt_frz s pin c hac hf, activeStep_core_xt_frz s pin c' hac hf]
    exact hinv.sep c c' hne h1 h2
  · have hf' : s.freeze.frz = false := by simpa using hf
    by_cases hd : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true
    · by_cases hd2 : Core.disp (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) = true
      · have h1 : (activeStep s pin).cores[c.val].xt =
            Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
          rw [activeStep_core_xt s pin c hac hf', hd]
          simp
        have h2 : (activeStep s pin).cores[c'.val].xt =
            Core.dispE (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) := by
          rw [activeStep_core_xt s pin c' hac hf', hd2]
          simp
        rw [h1, h2]
        exact dispE_sep s pin c c' hne hd hd2
      · have hdf2 : Core.disp (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) = false := by
          simpa using hd2
        have h1 : (activeStep s pin).cores[c.val].xt =
            Core.dispE (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
          rw [activeStep_core_xt s pin c hac hf', hd]
          simp
        have h2 : (activeStep s pin).cores[c'.val].xt = (s.cores[c'.val]).xt := by
          rw [activeStep_core_xt s pin c' hac hf', hdf2]
          simp
        rw [h1, h2]
        intro heq
        have hready := disp_ready_cut s pin c hd
        rw [heq] at hready
        have h2' := xvrv_of_step s pin hac hf' c' hdf2 hx'
        have hnot := hinv.ready c' h2'
        rw [hnot] at hready
        exact absurd hready (by decide)
    · have hdf : Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = false := by
        simpa using hd
      by_cases hd2 : Core.disp (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) = true
      · have h1 : (activeStep s pin).cores[c.val].xt = (s.cores[c.val]).xt := by
          rw [activeStep_core_xt s pin c hac hf', hdf]
          simp
        have h2 : (activeStep s pin).cores[c'.val].xt =
            Core.dispE (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) := by
          rw [activeStep_core_xt s pin c' hac hf', hd2]
          simp
        rw [h1, h2]
        intro heq
        have hready := disp_ready_cut s pin c' hd2
        rw [← heq] at hready
        have h2' := xvrv_of_step s pin hac hf' c hdf hx
        have hnot := hinv.ready c h2'
        rw [hnot] at hready
        exact absurd hready (by decide)
      · have hdf2 : Core.disp (c'.val == 1) (s.cores[c'.val]) (coreIn s pin c'.val) = false := by
          simpa using hd2
        have h1 : (activeStep s pin).cores[c.val].xt = (s.cores[c.val]).xt := by
          rw [activeStep_core_xt s pin c hac hf', hdf]
          simp
        have h2 : (activeStep s pin).cores[c'.val].xt = (s.cores[c'.val]).xt := by
          rw [activeStep_core_xt s pin c' hac hf', hdf2]
          simp
        rw [h1, h2]
        exact hinv.sep c c' hne (xvrv_of_step s pin hac hf' c hdf hx)
          (xvrv_of_step s pin hac hf' c' hdf2 hx')

theorem execInv_step (s : State) (pin : Machine.PinIn) (hinv : ExecInv s) :
    ExecInv (ChipCut.step s pin) := by
  by_cases hact : runRst s pin = true
  · have hstep : ChipCut.step s pin = activeStep s pin := by simp [ChipCut.step, hact]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c
      exact execInv_xtLt_step s pin hinv hact c
    · intro c hx
      by_cases hf : s.freeze.frz = true
      · exact (execInv_exec_step_frz s pin hinv hact hf c hx).1
      · exact (execInv_exec_step s pin hinv hact (by simpa using hf) c hx).1
    · intro c hx
      by_cases hf : s.freeze.frz = true
      · exact (execInv_exec_step_frz s pin hinv hact hf c hx).2
      · exact (execInv_exec_step s pin hinv hact (by simpa using hf) c hx).2
    · intro c c' hne hx hx'
      exact execInv_sep_step s pin hinv hact c c' hne hx hx'
  · have hstep : ChipCut.step s pin = ChipCut.resetChip s pin := by simp [ChipCut.step, hact]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c
      simp [ChipCut.resetChip, ChipCut.resetState]
    · intro c h
      simp [ChipCut.resetChip, ChipCut.resetState] at h
    · intro c h
      simp [ChipCut.resetChip, ChipCut.resetState] at h
    · intro c c' _ h
      simp [ChipCut.resetChip, ChipCut.resetState] at h

/-- A thread the cut dispatches this cycle is `READY` (either core). -/
theorem threadIn_disp_ready (s : State) (pin : Machine.PinIn) (t : Nat)
    (h : (threadIn s pin t).disp = true) : (threadAt s t).ready = true := by
  have h' := h
  simp only [threadIn, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨hd, he⟩ | ⟨hd, he⟩
  · rw [← he]
    exact disp_ready_cut s pin 0 hd
  · rw [← he]
    exact disp_ready_cut s pin 1 hd

/-- **`WireAgree.pauseDisp` from `ExecInv` alone.**  No `ChipRel`, no `Inv` and
no wiring hypothesis is needed: a paused thread is the executing thread of the
pausing core (`pause_pse`) and so not `READY` (`ExecInv.ready`), while a
dispatched thread is `READY` (`disp_ready_cut`); the two exclude each other. -/
theorem ccw_pauseDisp_cut (s : State) (pin : Machine.PinIn) (hinv : ExecInv s) :
    ∀ t : Fin 6,
      Not ((threadIn s pin t.val).pause = true ∧ (threadIn s pin t.val).disp = true) := by
  intro t hcon
  obtain ⟨hpause, hdisp⟩ := hcon
  have hnf : (threadAt s t.val).ready = false := pause_not_ready hinv t.val hpause
  have htr : (threadAt s t.val).ready = true := threadIn_disp_ready s pin t.val hdisp
  rw [hnf] at htr
  exact absurd htr (by decide)

/-- **`ExecInv` along the cut trace from reset** (unconditional). -/
theorem execInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, ExecInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact execInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact execInv_step _ _ ih

/-- **`WireAgree.pauseDisp` at every cycle of the cut trace.**  From
`execInv_trace` (`execInv_step`) and the `WireAgree.pauseDisp` discharge
`ccw_pauseDisp`; the remaining hypotheses are the ones `ccw_pauseDisp` names. -/
theorem ccw_pauseDisp_trace (pins : Nat → Machine.PinIn) (cont : Contents) (n : Nat)
    (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel (cutStateAt pins (resetState cont) n) m)
    (hinv : Inv (cutStateAt pins (resetState cont) n))
    (hbus : ∀ c : Fin 2,
      CoreInputBus (cutStateAt pins (resetState cont) n) m pin c
        (sIr (cutStateAt pins (resetState cont) n) m c))
    (hJGTab : ∀ n' : Nat,
      Machine.Util.jumpGuardIdx.getD n' Machine.Tables.guardNames.size = Core.JG_TABLE.getD n' 62) :
    ∀ t : Fin 6,
      Not ((threadIn (cutStateAt pins (resetState cont) n) pin t.val).pause = true ∧
        (threadIn (cutStateAt pins (resetState cont) n) pin t.val).disp = true) :=
  ccw_pauseDisp _ _ _ hrel (execInv_trace pins cont n) hinv hbus hJGTab

/-- **`WireAgree.pauseDisp` at every cycle of the cut trace, from `ExecInv`
alone** (no relation to a machine state and no wiring hypothesis). -/
theorem ccw_pauseDisp_trace_cut (pins : Nat → Machine.PinIn) (cont : Contents) (n : Nat)
    (pin : Machine.PinIn) :
    ∀ t : Fin 6,
      Not ((threadIn (cutStateAt pins (resetState cont) n) pin t.val).pause = true ∧
        (threadIn (cutStateAt pins (resetState cont) n) pin t.val).disp = true) :=
  ccw_pauseDisp_cut _ _ (execInv_trace pins cont n)

/-! ## 10. The contents congruence against the canonical abstraction

`Premises.contents` (`MemHostCfg.lean`) compares the machine's own memory/config
path at a related state `m` with the **same path at the canonical abstraction**
`absChip s` (`contentsNext` is literally `runStep (absChip s)`).  The three
open inputs of `premise_contents` are `contents_open_cbs`, `contents_open_req`
and `contents_open_served`.

`absChip` is the canonical representative of `ChipRel`, so the readings that
`mhcServed`/`mhcReq`/`mhcCbs` use are the cut's (the projections below are
`rfl`).  Consequently the arbiter argument can be replayed verbatim at
`absChip s` (`machServed_abs`) and the two served/request congruence theorems
follow from instantiating `ccw_served` twice.  `contents_open_req` needs one
cut-side capture-buffer invariant, `hwv : PV → WV` on the two streams, to read
the guarded `WB` slot of `BufRel` (mode-2 `wrWord`); nothing else is assumed.
-/

theorem streamAt_fin (s : State) (k : Fin 2) : streamAt s k.val = s.streams[k] := by
  rcases k with ⟨kv, hk⟩
  have h : kv = 0 ∨ kv = 1 := by omega
  rcases h with rfl | rfl <;> rfl

theorem absChip_cfg (s : State) : (absChip s).cfg = s.cont.cfg := rfl

theorem absChip_streams (s : State) (k : Fin 2) :
    (absChip s).streams[k] = Bridge.StreamB.abs (streamAt s k.val) := by
  rw [streamAt_fin]
  have hvec : (absChip s).streams = Vector.ofFn fun i : Fin 2 =>
      Bridge.StreamB.abs s.streams[i.val] := rfl
  rw [hvec]
  simp

/-- The cut's stream-input mode bit is the decoded configuration bit. -/
theorem streamIn_cfgMode (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    (streamIn s pin k.val).cfgMode = ((Machine.cfgView s.cont.cfg).streams[k]).rx := by
  show ((Machine.cfgView s.cont.cfg).streams[k.val]!).rx = _
  rw [vec_get!_eq_get _ _ k.isLt]

/-- The machine's mode at the canonical abstraction is the bridge's `modeOf`. -/
theorem absMode_eq (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    machMode (absChip s) k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) := by
  have hL : machMode (absChip s) k = (if k.val == 0 && s.dbgCtrl.replay then 3
      else if k.val == 0 && s.dbgCtrl.cen then 2
      else if ((Machine.cfgView s.cont.cfg).streams[k]).rx then 1 else 0) := rfl
  have h1 : (streamIn s pin k.val).replayEn = s.dbgCtrl.replay := rfl
  have h2 : (streamIn s pin k.val).capEn = (s.dbgCtrl.cen && !s.dbgCtrl.replay) := rfl
  have hR : Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) =
      (if k.val == 0 && s.dbgCtrl.replay then 3
       else if k.val == 0 && (s.dbgCtrl.cen && !s.dbgCtrl.replay) then 2
       else if ((Machine.cfgView s.cont.cfg).streams[k]).rx then 1 else 0) := by
    show (if k.val == 0 && (streamIn s pin k.val).replayEn then 3
        else if k.val == 0 && (streamIn s pin k.val).capEn then 2
        else if (streamIn s pin k.val).cfgMode then 1 else 0) = _
    rw [streamIn_cfgMode s pin k, h1, h2]
  rw [hL, hR]
  by_cases hr : s.dbgCtrl.replay = true
  · by_cases hk : (k.val == 0) = true
    · simp [hr, hk]
    · have hk' : (k.val == 0) = false := by simpa using hk
      simp [hr, hk']
  · have hr' : s.dbgCtrl.replay = false := by simpa using hr
    simp [hr']

/-- `mhcServed` is the machine's arbiter (`machServed`). -/
theorem mhcServed_eq_machServed (m : Machine.State) (pin : Machine.PinIn) :
    mhcServed m pin = machServed m := by
  have e0 : (mhcModesReq m pin)[0] = machSreq m 0 := by
    simp [mhcModesReq, machSreq, mhcModes, machMode]
  have e1 : (mhcModesReq m pin)[1] = machSreq m 1 := by
    simp [mhcModesReq, machSreq, mhcModes, machMode]
  rw [mhcServed, machServed, e0, e1]

/-- `mhcCbs` is the machine's combinational bundle (`machCbs`). -/
theorem mhcCbs_eq_machCbs (m : Machine.State) (pin : Machine.PinIn) :
    mhcCbs m pin = machCbs m := by
  simp only [mhcCbs, machCbs]

/-! ### The request congruence -/

/-- `streamReq` depends only on the mode and four stream fields (and `WB` only
while a word is pending). -/
theorem streamReq_congr (mode : Nat) (a b : Machine.StreamSt)
    (hba : a.ba = b.ba) (hrq : a.rq = b.rq) (hpv : a.pv = b.pv)
    (hpend : a.pend = b.pend) (hwb : a.pv = true → a.wb = b.wb) :
    Machine.streamReq mode a = Machine.streamReq mode b := by
  rcases mode with _ | _ | _ | _ | n
  · simp [Machine.streamReq, hba, hrq]
  · simp [Machine.streamReq, hba, hpv, hpend]
  · simp only [Machine.streamReq, hpv]
    by_cases hp : b.pv = true
    · rw [if_pos hp, if_pos hp, hba, hwb (by rw [hpv]; exact hp)]
    · rw [if_neg hp, if_neg hp]
  · simp [Machine.streamReq, hba, hrq]
  · simp [Machine.streamReq, hba, hrq]

/-- `p0Req` depends only on the pointer and its request. -/
theorem p0Req_congr (a b : Machine.P0St) (hreq : a.req = b.req) (hptr : a.ptr = b.ptr) :
    Machine.p0Req a = Machine.p0Req b := by
  rw [Machine.p0Req, Machine.p0Req, hreq, hptr]

/-- `hostReq` depends only on its request. -/
theorem hostReq_congr (a b : Machine.HostSt) (hreq : a.req = b.req) :
    Machine.hostReq a = Machine.hostReq b := by
  rw [Machine.hostReq, Machine.hostReq, hreq]

theorem mhcModesReq_abs (s : State) (m : Machine.State) (pin : Machine.PinIn) (k : Fin 2)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwv : (streamAt s k.val).pv = true → (streamAt s k.val).wv = true) :
    (mhcModesReq m pin)[k] = (mhcModesReq (absChip s) pin)[k] := by
  obtain ⟨_, _, hba, _, _, hrq, _, hpend, hpv, _, hbuf⟩ := hrel.streams k
  have hL : (mhcModesReq m pin)[k] = Machine.streamReq (machMode m k) m.streams[k] := by
    simp [mhcModesReq, mhcModes, machMode]
  have hR : (mhcModesReq (absChip s) pin)[k] =
      Machine.streamReq (machMode (absChip s) k) ((absChip s).streams[k]) := by
    simp [mhcModesReq, mhcModes, machMode]
  rw [hL, hR, absChip_streams, hmode k, absMode_eq s pin k]
  refine streamReq_congr _ _ _ ?_ ?_ ?_ ?_ ?_
  · show m.streams[k].ba = (streamAt s k.val).ba
    exact hba.symm
  · show m.streams[k].rq = (streamAt s k.val).rq
    exact hrq.symm
  · show m.streams[k].pv = (streamAt s k.val).pv
    exact hpv.symm
  · show m.streams[k].pend = (streamAt s k.val).pend
    exact hpend.symm
  · intro hpvM
    have hpvS : (streamAt s k.val).pv = true := by rw [hpv]; exact hpvM
    have hw := hwv hpvS
    have hwb := Bridge.StreamB.BufRel.wb_of_wv hbuf hw
    show m.streams[k].wb = (streamAt s k.val).wb
    exact hwb.symm

theorem mhcModesReq_abs0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwv : (streamAt s (0 : Fin 2).val).pv = true → (streamAt s (0 : Fin 2).val).wv = true) :
    (mhcModesReq m pin)[0] = (mhcModesReq (absChip s) pin)[0] :=
  mhcModesReq_abs s m pin 0 hrel hmode hwv

theorem mhcModesReq_abs1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwv : (streamAt s (1 : Fin 2).val).pv = true → (streamAt s (1 : Fin 2).val).wv = true) :
    (mhcModesReq m pin)[1] = (mhcModesReq (absChip s) pin)[1] :=
  mhcModesReq_abs s m pin 1 hrel hmode hwv

/-! ### Presence facts at `absChip` -/

theorem has_p0_abs (s : State) (hinv : Inv s) :
    hasReq (Machine.p0Req (absChip s).p0) = Mem.pending s.p0 := by
  rcases Bridge.Mem.req_cases s.p0 hinv.reqNeThree with h | h | h <;>
    simp [hasReq, Machine.p0Req, Mem.pending, absChip, Bridge.Mem.absP0, Bridge.Mem.reqOf, h,
      Mem.RQ_NONE]

theorem has_host_abs (s : State) :
    hasReq (Machine.hostReq (absChip s).host) = s.p0.hostQ := by
  rw [Machine.hostReq]
  cases hq : s.p0.hostQ <;> cases hw : s.p0.hostWr <;>
    simp [hasReq, Bridge.Mem.absSlot, absChip, hq, hw]

theorem has_sreq_zero_abs (s : State) (pin : Machine.PinIn) :
    hasReq (machSreq (absChip s) 0) = Mem.s0Req (memIn s pin) := by
  have hrq : (absChip s).streams[(0 : Fin 2)].rq = (streamAt s (0 : Fin 2).val).rq := by
    rw [absChip_streams]; rfl
  have hpv : (absChip s).streams[(0 : Fin 2)].pv = (streamAt s (0 : Fin 2).val).pv := by
    rw [absChip_streams]; rfl
  rw [machSreq, absMode_eq s pin 0]
  rw [has_streamReq_mode _ (absChip s).streams[(0 : Fin 2)]
    (Bridge.StreamB.abs (streamAt s (0 : Fin 2).val)) hrq hpv]
  rw [has_streamReq]
  have hcap : ((↑(0 : Fin 2) : Nat) == 0) = true := by decide
  rw [hcap]
  rw [show Stream.req true (streamAt s (↑(0 : Fin 2))) (streamIn s pin (↑(0 : Fin 2)))
      = (streamReq s 0).req from (sReq_zero s pin).symm]
  exact (s0Req_memIn s pin).symm

theorem has_sreq_one_abs (s : State) (pin : Machine.PinIn) :
    hasReq (machSreq (absChip s) 1) = Mem.s1Req (memIn s pin) := by
  have hrq : (absChip s).streams[(1 : Fin 2)].rq = (streamAt s (1 : Fin 2).val).rq := by
    rw [absChip_streams]; rfl
  have hpv : (absChip s).streams[(1 : Fin 2)].pv = (streamAt s (1 : Fin 2).val).pv := by
    rw [absChip_streams]; rfl
  rw [machSreq, absMode_eq s pin 1]
  rw [has_streamReq_mode _ (absChip s).streams[(1 : Fin 2)]
    (Bridge.StreamB.abs (streamAt s (1 : Fin 2).val)) hrq hpv]
  rw [has_streamReq]
  have hcap : ((↑(1 : Fin 2) : Nat) == 0) = false := by decide
  rw [hcap]
  rw [show Stream.req false (streamAt s (↑(1 : Fin 2))) (streamIn s pin (↑(1 : Fin 2)))
      = (streamReq s 1).req from (sReq_one s pin).symm]
  exact (s1Req_memIn s pin).symm

/-- **The machine's arbiter at the canonical abstraction** is the cut's grant
priority (the `ccw_served` argument at `absChip s`). -/
theorem machServed_abs (s : State) (pin : Machine.PinIn) (hinv : Inv s) :
    machServed (absChip s) = Bridge.Mem.servedIndex s.p0 (memIn s pin) := by
  have hfrz : (absChip s).dbg.frz = (memIn s pin).frz := rfl
  have h0 := has_sreq_zero_abs s pin
  have h1 := has_sreq_one_abs s pin
  have h2 := has_p0_abs s hinv
  have h3 := has_host_abs s
  rw [machServed, arbiter_has, hfrz, h0, h1, h2, h3, ← Bridge.Mem.arbiter_eq, arbiter_has]
  simp [has_someReq]

/-- **`contents_open_served`.** -/
theorem contents_open_served (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) :
    mhcServed m pin = mhcServed (absChip s) pin := by
  rw [mhcServed_eq_machServed, mhcServed_eq_machServed,
    ccw_served s m pin hrel hinv hmode, machServed_abs s pin hinv]

/-- The served index is at most four. -/
theorem servedIndex_le_four (s : State) (pin : Machine.PinIn) :
    Bridge.Mem.servedIndex s.p0 (memIn s pin) ≤ 4 := by
  unfold Bridge.Mem.servedIndex
  repeat' split
  all_goals omega

/-- **`contents_open_req`.** -/
theorem contents_open_req (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwv : ∀ k : Fin 2, (streamAt s k.val).pv = true → (streamAt s k.val).wv = true) :
    mhcReq m pin = mhcReq (absChip s) pin := by
  have hserved := contents_open_served s m pin hrel hinv hmode
  have h0 := mhcModesReq_abs0 s m pin hrel hmode (hwv 0)
  have h1 := mhcModesReq_abs1 s m pin hrel hmode (hwv 1)
  have h2 : Machine.p0Req m.p0 = Machine.p0Req (absChip s).p0 :=
    p0Req_congr _ _ hrel.p0.req hrel.p0.ptr
  have h3 : Machine.hostReq m.host = Machine.hostReq (absChip s).host := by
    refine hostReq_congr _ _ ?_
    rw [hrel.hostReq]; rfl
  have hlist : ∀ j : Nat, j < 4 →
      (mhcReqs m pin).getD j .none = (mhcReqs (absChip s) pin).getD j .none := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> simp [mhcReqs, h0, h1, h2, h3]
  have hsle : Bridge.Mem.servedIndex s.p0 (memIn s pin) ≤ 4 := servedIndex_le_four s pin
  have hserved' : mhcServed (absChip s) pin = Bridge.Mem.servedIndex s.p0 (memIn s pin) := by
    rw [mhcServed_eq_machServed]; exact machServed_abs s pin hinv
  simp only [mhcReq]
  rw [hserved, hserved']
  by_cases hz : (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 0) = true
  · simp only [hz, if_true]
  · simp only [hz, Bool.false_eq_true, if_false]
    exact hlist _ (by omega)

/-! ## 11. The stream invariants that the contents congruence needs

The remaining inputs of the contents congruence are two stream facts.  Both are
**false** at the `Stream` cut (so no chip-level proof of them exists), which is
why the sharpened request theorem carries the `WB` agreement directly:

* `pv → wv` (the round-d `hwv`): a capture `push` sets `PV` while `WV` is only
  held in capture mode (`Stream.wvNext`'s last branch), so one push from reset
  gives `PV = 1, WV = 0` (`streamInv_pv_wv_false`);
* `ld → mode ∈ {0,3}`: `LD` is set on a served read in transmit/replay and is
  *held* in the receive/capture branches (`Stream.ldNext`), while the mode is
  live (the configuration byte and `CEN`/`RPL` are current-cycle registers), so
  a receive cycle right after a served transmit read has `LD = 1` with mode 1
  (`streamInv_ld_mode_false`, a two-cycle trace from `Stream.resetState`).

What the mode-2 (`capture`) `wrWord` request actually needs is the `WB` word
itself; `BufRel` relates `WB` only while `WV`, so the sharpened statement below
takes the unguarded `WB` agreement as its premise.  It is strictly stronger
than the round-d `contents_open_req` (which derives it from `hwv` + `BufRel`).
-/


/-- A stream input record with the given control fields (everything else quiet). -/
def sIn (resetN frz capEn capPush replayEn cfgMode gnt : Bool) (cfgLen : BitVec 12) :
    Stream.Input :=
  { resetN := resetN, frz := frz, frzd := false, capEn := capEn, capPush := capPush,
    capRec := 0, replayEn := replayEn, replayApply := false, replayLate := false,
    cfgMode := cfgMode, cfgMsb := false, cfgStart := 0, cfgLen := cfgLen, cfgMark := 0,
    adv := false, rxWe := false, rxBit := false, rewind := false, flush := false,
    clrStarved := false, gnt := gnt, rdata := 0 }

/-- One capture push from reset leaves `PV` high with no word in `WV`. -/
theorem streamInv_pv_wv_false :
    ∃ (i : Stream.Input), (Stream.step true Stream.resetState i).pv = true ∧
      (Stream.step true Stream.resetState i).wv = false := by
  refine ⟨sIn true false true true false false false 1, ?_, ?_⟩ <;>
    decide

/-- The three-cycle transmit/receive switch: a served transmit read sets `LD`, and
the following receive cycle holds it, so `LD` is true in a receive cycle. -/
def ldSeq : Nat → Stream.Input
  | 0 => sIn true false false false false false false 1
  | 1 => sIn true false false false false false true 1
  | _ => sIn true false false false false true false 1

theorem streamInv_ld_mode_false :
    (Stream.stateAt true ldSeq Stream.resetState 2).ld = true ∧
      (ldSeq 2).cfgMode = true ∧ Stream.cen true (ldSeq 2) = false ∧
      Stream.rpl true (ldSeq 2) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


theorem mhcModesReq_abs_wb (s : State) (m : Machine.State) (pin : Machine.PinIn) (k : Fin 2)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : (streamAt s k.val).pv = true → m.streams[k].wb = (streamAt s k.val).wb) :
    (mhcModesReq m pin)[k] = (mhcModesReq (absChip s) pin)[k] := by
  obtain ⟨_, _, hba, _, _, hrq, _, hpend, hpv, _, _⟩ := hrel.streams k
  have hL : (mhcModesReq m pin)[k] = Machine.streamReq (machMode m k) m.streams[k] := by
    simp [mhcModesReq, mhcModes, machMode]
  have hR : (mhcModesReq (absChip s) pin)[k] =
      Machine.streamReq (machMode (absChip s) k) ((absChip s).streams[k]) := by
    simp [mhcModesReq, mhcModes, machMode]
  rw [hL, hR, absChip_streams, hmode k, absMode_eq s pin k]
  refine streamReq_congr _ _ _ ?_ ?_ ?_ ?_ ?_
  · show m.streams[k].ba = (streamAt s k.val).ba
    exact hba.symm
  · show m.streams[k].rq = (streamAt s k.val).rq
    exact hrq.symm
  · show m.streams[k].pv = (streamAt s k.val).pv
    exact hpv.symm
  · show m.streams[k].pend = (streamAt s k.val).pend
    exact hpend.symm
  · intro hpvM
    have hpvS : (streamAt s k.val).pv = true := by rw [hpv]; exact hpvM
    show m.streams[k].wb = (streamAt s k.val).wb
    exact hwb hpvS

theorem mhcModesReq_abs_wb0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : (streamAt s (0 : Fin 2).val).pv = true → m.streams[(0 : Fin 2)].wb =
      (streamAt s (0 : Fin 2).val).wb) :
    (mhcModesReq m pin)[0] = (mhcModesReq (absChip s) pin)[0] :=
  mhcModesReq_abs_wb s m pin 0 hrel hmode hwb

theorem mhcModesReq_abs_wb1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : (streamAt s (1 : Fin 2).val).pv = true → m.streams[(1 : Fin 2)].wb =
      (streamAt s (1 : Fin 2).val).wb) :
    (mhcModesReq m pin)[1] = (mhcModesReq (absChip s) pin)[1] :=
  mhcModesReq_abs_wb s m pin 1 hrel hmode hwb

/-- **`contents_open_req'`**: the request congruence with the sharp `WB` premise
(the unguarded `WB` slot that `BufRel` leaves free while `WV` is low). -/
theorem contents_open_req_wb (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : ∀ k : Fin 2, (streamAt s k.val).pv = true → m.streams[k].wb = (streamAt s k.val).wb) :
    mhcReq m pin = mhcReq (absChip s) pin := by
  have hserved := contents_open_served s m pin hrel hinv hmode
  have h0 := mhcModesReq_abs_wb0 s m pin hrel hmode (hwb 0)
  have h1 := mhcModesReq_abs_wb1 s m pin hrel hmode (hwb 1)
  have h2 : Machine.p0Req m.p0 = Machine.p0Req (absChip s).p0 :=
    p0Req_congr _ _ hrel.p0.req hrel.p0.ptr
  have h3 : Machine.hostReq m.host = Machine.hostReq (absChip s).host := by
    refine hostReq_congr _ _ ?_
    rw [hrel.hostReq]; rfl
  have hlist : ∀ j : Nat, j < 4 →
      (mhcReqs m pin).getD j .none = (mhcReqs (absChip s) pin).getD j .none := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> simp [mhcReqs, h0, h1, h2, h3]
  have hsle : Bridge.Mem.servedIndex s.p0 (memIn s pin) ≤ 4 := servedIndex_le_four s pin
  have hserved' : mhcServed (absChip s) pin = Bridge.Mem.servedIndex s.p0 (memIn s pin) := by
    rw [mhcServed_eq_machServed]; exact machServed_abs s pin hinv
  simp only [mhcReq]
  rw [hserved, hserved']
  by_cases hz : (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 0) = true
  · simp only [hz, if_true]
  · simp only [hz, Bool.false_eq_true, if_false]
    exact hlist _ (by omega)

/-- `ccw_served` with `StreamWire`'s first field as the mode hypothesis. -/
theorem ccw_served_of_wire (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hwire : StreamWire s m pin) :
    machServed m = Bridge.Mem.servedIndex s.p0 (memIn s pin) :=
  ccw_served s m pin hrel hinv hwire.mode

/-- `contents_open_served` from a full `StreamWire`. -/
theorem contents_open_served_of_wire (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hwire : StreamWire s m pin) :
    mhcServed m pin = mhcServed (absChip s) pin :=
  contents_open_served s m pin hrel hinv hwire.mode

/-! ## 12. The P0 half of `LandingRel` on every trace cycle

`LandingRel`'s stream clause is not an invariant (see §11's `ld` witness: `LD` is
held into a receive/capture cycle, while `ramOwner` records only the served
`.rd`), so `landingRel_step` cannot be proved as stated.  The P0 clause is a
genuine invariant and is closed here, together with its trace form:

* `mhcOwner_three` — the machine's output owner is 3 exactly when the served
  entry is a read (with `arbiter_le_four` to enumerate the served index);
* `p0_open_served_abs`, `p0Req_fetch_iff`, `landingP0_abs` — at `absChip s` the
  owner-3 output is `grantP0 && fetching`;
* `LandingP0` (`(ramOwner == 3) = (land && !FRZD)`) at reset, after every
  active/frozen/reset cycle, and along `cutStateAt` (`landingP0_trace`), hence
  `p0_open_land_trace`: `p0_open_land` on every cycle of the trace.
-/

/-- A RAM request is a read. -/
def isRdReq : Machine.RamReq → Bool
  | .rd _ _ => true
  | _ => false

/-- The machine's arbiter never returns more than four. -/
theorem arbiter_le_four (a0 a1 a2 a3 : Machine.RamReq) (f : Bool) :
    Machine.arbiter a0 a1 a2 a3 f ≤ 4 := by
  rw [arbiter_has]
  repeat' split
  all_goals omega

/-- The output owner is 3 exactly when the served entry is P0's read. -/
theorem mhcOwner_three (m : Machine.State) (pin : Machine.PinIn) :
    (mhcOwner m pin == 3) =
      (mhcServed m pin == 3 && isRdReq ((mhcReqs m pin).getD 2 .none)) := by
  simp only [mhcOwner, mhcReq, isRdReq]
  by_cases h0 : mhcServed m pin = 0
  · have h0b : ((mhcServed m pin == 0) = true) := by simp [h0]
    rw [if_pos h0b]
    have h3b : (mhcServed m pin == 3) = false := by simp [h0]
    rw [h3b]
    rfl
  · rw [if_neg (by simp [h0])]
    by_cases h3 : mhcServed m pin = 3
    · rw [h3]
      have hsub : (3 : Nat) - 1 = 2 := rfl
      rw [hsub]
      cases hq : (mhcReqs m pin).getD 2 .none <;> simp
    · have h3b : (mhcServed m pin == 3) = false := by simp [h3]
      rw [h3b]
      simp only [Bool.false_and]
      cases hq : (mhcReqs m pin).getD (mhcServed m pin - 1) .none <;> simp_all

/-- The arbiter's grant of P0 at the canonical abstraction is `grantP0`. -/
theorem p0_open_served_abs (s : State) (pin : Machine.PinIn) (hinv : Inv s) :
    (machServed (absChip s) == 3) = Mem.grantP0 s.p0 (memIn s pin) := by
  rw [machServed_abs s pin hinv]
  obtain ⟨h01, h0p, h0h, h1p, h1h, hph⟩ := Mem.grants_exclusive s.p0 (memIn s pin)
  simp only [Bridge.Mem.servedIndex]
  cases h0 : Mem.grantS0 (memIn s pin) <;> cases h1 : Mem.grantS1 (memIn s pin) <;>
    cases hp : Mem.grantP0 s.p0 (memIn s pin) <;>
    cases hh : Mem.grantHost s.p0 (memIn s pin)
  all_goals simp_all

/-- P0's request at the canonical abstraction is a read exactly when a fetch is
pending. -/
theorem p0Req_fetch_iff (s : State) (hinv : Inv s) :
    isRdReq (Machine.p0Req (absChip s).p0) = Mem.fetching s.p0 := by
  have hp : (absChip s).p0 = Bridge.Mem.absP0 s.p0 := rfl
  rw [hp]
  rcases Bridge.Mem.req_cases s.p0 hinv.reqNeThree with h | h | h
  · have h1 : (Bridge.Mem.absP0 s.p0).req = .none := by
      simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, h]
    have h2 : Mem.fetching s.p0 = false := by simp [Mem.fetching, h]
    rw [Machine.p0Req, h1, h2]
    rfl
  · have h1 : (Bridge.Mem.absP0 s.p0).req = .fetch := by
      simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, h]
    have h2 : Mem.fetching s.p0 = true := by simp [Mem.fetching, h]
    rw [Machine.p0Req, h1, h2]
    rfl
  · have h1 : (Bridge.Mem.absP0 s.p0).req = .write s.p0.reqAddr s.p0.reqData := by
      simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, h]
    have h2 : Mem.fetching s.p0 = false := by simp [Mem.fetching, h]
    rw [Machine.p0Req, h1, h2]
    rfl

/-- The owner-3 output at the canonical abstraction is P0's served fetch. -/
theorem landingP0_abs (s : State) (pin : Machine.PinIn) (hinv : Inv s) :
    (mhcOwner (absChip s) pin == 3) =
      (Mem.grantP0 s.p0 (memIn s pin) && Mem.fetching s.p0) := by
  rw [mhcOwner_three, mhcServed_eq_machServed (absChip s) pin, p0_open_served_abs s pin hinv]
  have h2 : (mhcReqs (absChip s) pin).getD 2 .none = Machine.p0Req (absChip s).p0 := by
    simp [mhcReqs]
  rw [h2, p0Req_fetch_iff s hinv]

/-- The P0 landing clause of `LandingRel`. -/
def LandingP0 (s : State) : Prop :=
  (s.cont.ramOwner == 3) = (s.p0.land && !s.freeze.frzd)

theorem landingP0_reset (cont : Contents) (h0 : cont.ramOwner = 0) :
    LandingP0 (resetState cont) := by
  have h3 : (cont.ramOwner == 3) = false := by
    rw [h0]; rfl
  show ((resetState cont).cont.ramOwner == 3) = _
  simp [resetState, Mem.resetState, CoreCtl.freezeReset, h3]

/-- `LandingP0` on an active cycle. -/
theorem landingP0_active (s : State) (pin : Machine.PinIn) (hinv : Inv s)
    (hac : runRst s pin = true) :
    LandingP0 (activeStep s pin) := by
  have hq : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hac
  have hstep : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  have howner : (activeStep s pin).cont.ramOwner = mhcOwner (absChip s) pin := by
    show (contentsNext s pin).ramOwner = _
    simp only [contentsNext]
    rw [← hstep]
    exact (step_ram (absChip s) pin hq).2.2.1
  have hland : (activeStep s pin).p0.land = Mem.landNext s.p0 (memIn s pin) := rfl
  have hfr : (freezeIn s pin).resetN = true := hac
  have hfrzd : (activeStep s pin).freeze.frzd = s.freeze.frz := by
    show (CoreCtl.freezeStep s.freeze (freezeIn s pin)).frzd = s.freeze.frz
    rw [CoreCtl.frzd_next]
    simp [hfr]
  show ((activeStep s pin).cont.ramOwner == 3) =
    ((activeStep s pin).p0.land && !(activeStep s pin).freeze.frzd)
  rw [howner, hland, hfrzd, landingP0_abs s pin hinv]
  have hres : (memIn s pin).resetN = true := hac
  by_cases hf : (memIn s pin).frz = true
  · have hff : s.freeze.frz = true := hf
    simp [Mem.grantP0, Mem.landNext, hf, hres, hff]
  · have hf' : (memIn s pin).frz = false := by simpa using hf
    have hff : s.freeze.frz = false := hf'
    simp [Mem.landNext, hf, hres, hff]

/-- `LandingP0` after one product step (both branches). -/
theorem landingP0_step (s : State) (pin : Machine.PinIn) (hinv : Inv s) :
    LandingP0 (step s pin) := by
  by_cases hact : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hact]]
    exact landingP0_active s pin hinv hact
  · rw [show step s pin = resetChip s pin from by simp [step, hact]]
    show ((resetChip s pin).cont.ramOwner == 3) = _
    simp [resetChip, resetState, contentsReset, Mem.resetState, CoreCtl.freezeReset]

/-- `LandingP0` at every cycle of the cut trace. -/
theorem landingP0_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (h0 : cont.ramOwner = 0) :
    ∀ n, LandingP0 (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact landingP0_reset cont h0
  | succ n ih =>
    rw [cutStateAt_succ]
    exact landingP0_step _ _ (inv_trace pins cont n)

/-- **`p0_open_land` at every cycle of the cut trace.** -/
theorem p0_open_land_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (h0 : cont.ramOwner = 0) (n : Nat) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel (cutStateAt pins (resetState cont) n) m) :
    (m.ramOwner == 3) =
      ((cutStateAt pins (resetState cont) n).p0.land &&
        !(cutStateAt pins (resetState cont) n).freeze.frzd) := by
  have hland := landingP0_trace pins cont h0 n
  rw [hrel.ramOwner]
  exact hland

/-! ## 13. The stream mode-quiet premise and the `LD`-mode branch lemma

`LandingRel`'s stream clause needs `LD` to be set only in transmit (0) or replay
(3) cycles.  That is *not* true of the raw cut (§8's `streamInv_ld_mode_false`),
so it is carried by the single named premise `stream_mode_quiet`, which encodes
§9a.13 / §12.4 and is deliberately stricter than the SPEC (§13 docstring).

`modeOf_branch`/`absMode_branch` rewrite the mode into the `Stream` branch
predicates (`rpl`/`cen`/`txMode`), `ldNext_true` says a true `LD` transition is a
held `LD` or a served read in a transmit/replay branch, and `ldNext_mode`
combines those with `stream_mode_quiet` to keep the next mode out of {1,2}.
`ldModeInv` is the invariant (`LD → mode ∈ {0,3}`), proved at reset.
-/

theorem modeOf_branch (cap : Bool) (i : Stream.Input) :
    Bridge.StreamB.modeOf cap i =
      (if Stream.rpl cap i then 3
       else if Stream.cen cap i then 2
       else if Stream.txMode cap i then 0 else 1) := by
  have hr : Stream.rpl cap i = (cap && i.replayEn) := rfl
  have hc : Stream.cen cap i = (cap && i.capEn && !(cap && i.replayEn)) := rfl
  have ht : Stream.txMode cap i =
      (!i.cfgMode && !(cap && i.capEn && !(cap && i.replayEn)) && !(cap && i.replayEn)) := rfl
  rw [hr, hc, ht]
  simp only [Bridge.StreamB.modeOf]
  by_cases h1 : (cap && i.replayEn) = true
  · simp [h1]
  · have h1' : (cap && i.replayEn) = false := by simpa using h1
    by_cases h2 : (cap && i.capEn) = true
    · simp [h1', h2]
    · have h2' : (cap && i.capEn) = false := by simpa using h2
      by_cases h3 : i.cfgMode = true
      · simp [h1', h2', h3]
      · have h3' : i.cfgMode = false := by simpa using h3
        simp [h1', h2', h3']

theorem absMode_branch (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    machMode (absChip s) k =
      (if Stream.rpl (k.val == 0) (streamIn s pin k.val) then 3
       else if Stream.cen (k.val == 0) (streamIn s pin k.val) then 2
       else if Stream.txMode (k.val == 0) (streamIn s pin k.val) then 0 else 1) := by
  rw [absMode_eq]
  exact modeOf_branch _ _

theorem absChip_dbg_val (s : State) :
    (absChip s).dbg =
      { freeze := s.freeze.freeze, frz := s.freeze.frz, frzd := s.freeze.frzd,
        men := s.dbgDigest.men, misr := s.dbgDigest.misr, cen := s.dbgCtrl.cen,
        rpl := s.dbgCtrl.replay, emask := s.dbgCtrl.emask, dc := s.dbgCtrl.dc,
        rlv := s.dbgCtrl.rlv, rlvp := s.dbgCtrl.rlvPrev } := rfl

/-- The cut-side effective mode of stream `k`: the config `RX` bit and the debug
`CEN`/`RPL` registers, i.e. `machMode (absChip s) k` without the abstraction
(`absChip_cfg`/`absChip_dbg_val` keep the comparisons cheap). -/
def stateMode (s : State) (k : Fin 2) : Nat :=
  if k.val == 0 && s.dbgCtrl.replay then 3
  else if k.val == 0 && s.dbgCtrl.cen then 2
  else if ((Machine.cfgView s.cont.cfg).streams[k]).rx then 1 else 0

theorem stateMode_eq (s : State) (k : Fin 2) : stateMode s k = machMode (absChip s) k := by
  rw [machMode, absChip_cfg, absChip_dbg_val]
  simp only [stateMode, Machine.streamMode]

theorem stateMode_branch (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    stateMode s k =
      (if Stream.rpl (k.val == 0) (streamIn s pin k.val) then 3
       else if Stream.cen (k.val == 0) (streamIn s pin k.val) then 2
       else if Stream.txMode (k.val == 0) (streamIn s pin k.val) then 0 else 1) := by
  rw [stateMode_eq]
  exact absMode_branch s pin k

/-- The cut-side stream registers of a cycle-dominant mode: **the mode does not
change while the stream has a read in flight, a second replay slot, or a pending
byte** — `LD`, `RQ`, `NV` or `PV` set (§9a.13: changing `MODE`, `MSB` or `START`
without a rewind leaves the stream in an unspecified state until the next
rewind; §12.4: change `CEN` only together with a rewind of `S0`).

This is the one named premise of the stream landing/replay-buffer argument.

* The `LD`/`RQ` half is the SPEC's open case (a served read must not be
  observed by a mode switch).
* The `NV` half is **stricter than SPEC §9a.13** (orchestrator decision of
  2026-11-22b): it is what B1's `ShapeModeOK` invariant needs
  (`BRIDGE_STREAMBUF_NOTES.md` §9): a mode change while a replay-buffer slot is
  live is excluded, which rules out the `ShapeOK`-breaking mode excursion
  (`Bridge.StreamBuf.shapeOK_break_witness`).  With `LD = NV = 0` the next `NV`
  is `0` (`nv_step_zero` / `Bridge.StreamBuf.nv_step_cap_false`), which is what
  `Bridge.StreamBuf.shapeModeOK_step_nv` consumes.
* The `PV` half (both at the old and the new state) is the second orchestrator
  decision (2026-11-22c): a receive→capture switch with a pending byte makes the
  capture `WB` diverge (`Bridge.StreamBuf.capWb_reachable_witness`).

`WV` is **deliberately not required** (orchestrator decision of 2026-11-22d,
after the independent review finding): reset defaults to transmit and the
transmit branch prefetches with no `ADV` and length 0 (`src/md2_stream.v` ~130),
so a settle-at-startup TX stream has `WV = 1` (`Stream.wvNext`'s landing branch)
while nothing else is live.  Requiring `WV = 0` would make a normal startup
(cores stopped, host writes the stream config over SPI once the prefetch has
settled with `RQ = LD = 0`) violate the premise.  `WV = 1` cannot break
`ShapeOK` (`ShapeOK : WV = 0 → NV = 0`; the live slot is `NV`), so the relaxed
premise is still *stricter than SPEC §9a.13* — a mode change is only allowed
with no read in flight, no second replay slot and no pending byte — and it is
what `ASSEMBLY_NOTES.md` records as the limitation.

A host rewind coinciding with a served read is *not* excluded (and must not be):
the machine reads `i.landNow` only under the stream's own `s.ld`
(`Machine/Stream.lean` lines 86, 129, 155) and `Stream.ldNext` clears `LD` on a
rewind, so such a landing is unobservable and is handled by the `LD`-gated form
of the stream clause (`LandingStream`).

The mode is `stateMode`, a pure state function, so `stateMode (step s pin) k` is
the mode of the next cycle and the premise can be stated at the state level. -/
def stream_mode_quiet (s : State) (pin : Machine.PinIn) : Prop :=
  ∀ k : Fin 2,
    stateMode (step s pin) k ≠ stateMode s k →
      (streamAt s k.val).ld = false ∧ (streamAt s k.val).rq = false ∧
        (streamAt s k.val).nv = false ∧
        (streamAt s k.val).pv = false ∧ (streamAt (step s pin) k.val).pv = false

/-- `LD` is only ever set in a transmit (0) or replay (3) cycle. -/
def ldModeInv (s : State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true → stateMode s k ≠ 1 ∧ stateMode s k ≠ 2

/-- A true `LD` transition comes from a held `LD` or from a served read in a
transmit/replay branch. -/
theorem ldNext_true (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (h : Stream.ldNext cap st i = true) :
    st.ld = true ∨ ((Stream.rpl cap i = true ∨ Stream.txMode cap i = true) ∧ st.rq = true) := by
  unfold Stream.ldNext at h
  repeat' split at h
  all_goals simp_all

/-- The `LD` transition keeps the mode out of the receive (1) and capture (2)
codes, given the invariant at the cycle and the mode-quiet premise. -/
theorem ldNext_mode (cap : Bool) (st : Stream.State) (i : Stream.Input) (m m' : Nat)
    (hm : m = (if Stream.rpl cap i then 3 else if Stream.cen cap i then 2
      else if Stream.txMode cap i then 0 else 1))
    (hih : st.ld = true → m ≠ 1 ∧ m ≠ 2)
    (hq : m' ≠ m → st.ld = false ∧ st.rq = false)
    (h : Stream.ldNext cap st i = true) : m' ≠ 1 ∧ m' ≠ 2 := by
  rcases ldNext_true cap st i h with hld | ⟨hbranch, hrq⟩
  · by_cases hmm : m = m'
    · rw [← hmm]; exact hih hld
    · have h0 := (hq (by omega)).1
      rw [h0] at hld
      exact absurd hld (by decide)
  · by_cases hmm : m = m'
    · rcases hbranch with hr | ht
      · have hm3 : m = 3 := by rw [hm]; simp [hr]
        rw [← hmm, hm3]; omega
      · have hall : (i.cfgMode = false ∧ Stream.cen cap i = false) ∧
            Stream.rpl cap i = false := by simpa [Stream.txMode] using ht
        have hr' : Stream.rpl cap i = false := hall.2
        have hc' : Stream.cen cap i = false := hall.1.2
        have hm0 : m = 0 := by rw [hm]; simp [hr', hc', ht]
        rw [← hmm, hm0]; omega
    · have h0 := (hq (by omega)).2
      rw [h0] at hrq
      exact absurd hrq (by decide)

theorem ldModeInv_reset (cont : Contents) : ldModeInv (resetState cont) := by
  intro k h
  rw [streamAt_fin, resetState] at h
  simp [Stream.resetState] at h

/-! ## 14. The P0 landing lane on every trace cycle

`p0_open_lane`'s *unguarded* statement (`land = true → ramLane = landLane`) is not
an invariant: in a frozen cycle `land` is held (`Mem.landNext`'s frozen branch)
while `contentsNext` overwrites `ramLane` with the frozen cycle's served read
(the host's), and `landLane` is held.  The guard `!FRZD` is exactly the one the
consumer has (`p0Next` reads the lane only when `ramOwner == 3`, which implies
`grantP0` and hence `!FRZ`), so the invariant is stated with it:

* `mhcLaneN_abs` — when P0's fetch is served, the abstraction's served lane is
  `PTR % 4`; `lane_bv` is the bit-vector identity `bv 2 (PTR % 4) = PTR[1:0]`;
* `laneInv` — `land → !FRZD → ramLane = landLane`, at reset, after every step and
  along `cutStateAt` (`laneInv_trace`);
* `p0_open_lane_trace` — the guarded `p0_open_lane` at every trace cycle.
-/

/-- The pointer's byte lane is the word-read lane. -/
theorem lane_bv (x : BitVec 11) :
    Machine.Util.bv 2 (x.toNat % 4) = BitVec.truncate 2 x := by
  revert x
  decide

/-- The served lane of the canonical abstraction is P0's pointer lane when P0's
fetch is served. -/
theorem mhcLaneN_abs (s : State) (pin : Machine.PinIn) (hinv : Inv s)
    (hgp : Mem.grantP0 s.p0 (memIn s pin) = true) (hft : Mem.fetching s.p0 = true) :
    mhcLaneN (absChip s) pin = s.p0.ptr.toNat % 4 := by
  have hs3 : Bridge.Mem.servedIndex s.p0 (memIn s pin) = 3 := by
    have h1 : (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 3) = true := by
      rw [← machServed_abs s pin hinv, p0_open_served_abs s pin hinv]
      exact hgp
    simpa using h1
  have hsv : mhcServed (absChip s) pin = 3 := by
    rw [mhcServed_eq_machServed]; rw [machServed_abs s pin hinv]; exact hs3
  have hreq : mhcReq (absChip s) pin = Machine.p0Req (absChip s).p0 := by
    simp only [mhcReq]
    rw [hsv]
    simp [mhcReqs]
  have hreq1 : s.p0.req = 1 := by simpa [Mem.fetching, Mem.RQ_FETCH] using hft
  have hrd : Machine.p0Req (absChip s).p0 =
      Machine.RamReq.rd (s.p0.ptr.toNat / 4) (s.p0.ptr.toNat % 4) := by
    simp [Machine.p0Req, absChip, Bridge.Mem.absP0, Bridge.Mem.reqOf, hreq1]
  simp only [mhcLaneN]
  rw [hreq, hrd]

/-- The P0 landing lane clause, guarded by the landing itself (`land && !FRZD`):
this is what `p0Next` reads (`landNow = ramOwner == 3` implies `!FRZD`). -/
def laneInv (s : State) : Prop :=
  s.p0.land = true → s.freeze.frzd = false → s.cont.ramLane = s.p0.landLane

theorem laneInv_reset (cont : Contents) (h0 : cont.ramOwner = 0) :
    laneInv (resetState cont) := by
  intro h _
  simp [resetState, Mem.resetState] at h

theorem laneInv_active (s : State) (pin : Machine.PinIn) (hinv : Inv s)
    (hac : runRst s pin = true) : laneInv (activeStep s pin) := by
  intro hland hfrzd
  have hq : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hac
  have hstep : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hq]
  have hlane : (activeStep s pin).cont.ramLane =
      Machine.Util.bv 2 (mhcLaneN (absChip s) pin) := by
    show (contentsNext s pin).ramLane = _
    simp only [contentsNext]
    rw [← hstep]
    exact (step_ram (absChip s) pin hq).2.2.2
  have hfrzd' : (activeStep s pin).freeze.frzd = s.freeze.frz := by
    show (CoreCtl.freezeStep s.freeze (freezeIn s pin)).frzd = s.freeze.frz
    rw [CoreCtl.frzd_next]
    have hfr : (freezeIn s pin).resetN = true := hac
    simp [hfr]
  have hfrze : (memIn s pin).frz = false := by
    have h := hfrzd
    rw [hfrzd'] at h
    exact h
  have hres : (memIn s pin).resetN = true := hac
  have hland' : (activeStep s pin).p0.land = Mem.landNext s.p0 (memIn s pin) := rfl
  have hboth : (Mem.grantP0 s.p0 (memIn s pin) && Mem.fetching s.p0) = true := by
    have h := hland
    rw [hland', Mem.landNext, hres, hfrze] at h
    simpa using h
  have hgp : Mem.grantP0 s.p0 (memIn s pin) = true := (Bool.and_eq_true_iff.mp hboth).1
  have hft : Mem.fetching s.p0 = true := (Bool.and_eq_true_iff.mp hboth).2
  have hptrlane : (activeStep s pin).p0.landLane = BitVec.truncate 2 s.p0.ptr := by
    have : (activeStep s pin).p0.landLane = Mem.landLaneNext s.p0 (memIn s pin) := rfl
    rw [this, Mem.landLaneNext, hres, hfrze]
    rfl
  rw [hlane, mhcLaneN_abs s pin hinv hgp hft, hptrlane, lane_bv]

theorem laneInv_step (s : State) (pin : Machine.PinIn) (hinv : Inv s) :
    laneInv (step s pin) := by
  by_cases hact : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hact]]
    exact laneInv_active s pin hinv hact
  · rw [show step s pin = resetChip s pin from by simp [step, hact]]
    intro h _
    simp [resetChip, resetState, Mem.resetState] at h

theorem laneInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (h0 : cont.ramOwner = 0) :
    ∀ n, laneInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact laneInv_reset cont h0
  | succ n ih =>
    rw [cutStateAt_succ]
    exact laneInv_step _ _ (inv_trace pins cont n)

/-- **`p0_open_lane` at every cycle of the cut trace**, in the guarded form the
consumer reads (`p0Next` takes the lane only when `ramOwner == 3`, which implies
`!FRZD`). -/
theorem p0_open_lane_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (h0 : cont.ramOwner = 0) (n : Nat) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel (cutStateAt pins (resetState cont) n) m) :
    (cutStateAt pins (resetState cont) n).p0.land = true →
      (cutStateAt pins (resetState cont) n).freeze.frzd = false →
      m.ramLane = (cutStateAt pins (resetState cont) n).p0.landLane := by
  intro hl hf
  rw [hrel.ramLane]
  exact laneInv_trace pins cont h0 n hl hf

theorem ldModeInv_step (s : State) (pin : Machine.PinIn) (hinv : ldModeInv s)
    (hq : stream_mode_quiet s pin) : ldModeInv (step s pin) := by
  intro k hk
  by_cases hact : runRst s pin = true
  · have hstep : step s pin = activeStep s pin := by simp [step, hact]
    have hq' : stateMode (activeStep s pin) k ≠ stateMode s k →
        (streamAt s k.val).ld = false ∧ (streamAt s k.val).rq = false := by
      intro hch
      have hch' : stateMode (step s pin) k ≠ stateMode s k := by
        rw [hstep]; exact hch
      obtain ⟨h1, h2, -, -, -⟩ := hq k hch'
      exact ⟨h1, h2⟩
    rw [hstep] at hk ⊢
    have hstr : (streamAt (activeStep s pin) k.val).ld
        = Stream.ldNext (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) := by
      rw [streamAt_fin]
      have hvec : (activeStep s pin).streams = Vector.ofFn fun i : Fin 2 =>
          Stream.step (i.val == 0) (streamAt s i.val) (streamIn s pin i.val) := rfl
      rw [hvec]
      simp only [vec_get_ofFn']
      rfl
    rw [hstr] at hk
    exact ldNext_mode (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
      (stateMode s k) (stateMode (activeStep s pin) k)
      (stateMode_branch s pin k) (hinv k) hq' hk
  · rw [show step s pin = resetChip s pin from by simp [step, hact]] at hk
    rw [streamAt_fin, resetChip, resetState] at hk
    simp [Stream.resetState] at hk

/-- `ldModeInv` at every cycle of the cut trace, with the mode-quiet premise
assumed at every cycle. -/
theorem ldModeInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, ldModeInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact ldModeInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact ldModeInv_step _ _ ih (hq n)

/-! ## 15. The LD-gated stream clause of `LandingRel`

The raw stream clause `(ramOwner == k+1) = (ld && !FRZD)` is false (a rewind
clears `LD` while the machine still records the served `.rd`, and a mode switch
holds `LD`); §8/§9.  The machine reads `i.landNow` only under the stream's own
`s.ld` (`Machine/Stream.lean` 86/129/155), so the clause is stated with that
gate (`LandingStream`), which is exactly what `Machine.streamNext` consumes:

* `mhcOwner_eq` — the owner is `j` exactly when the served entry is a read
  (`mhcOwner_three` generalised to `k + 1`), and `servedIndex_gnt` — the grant
  of stream `k` is the served index at `k + 1`;
* `machSreq_isRd` — a machine stream request is a read exactly in the
  transmit/replay modes with `RQ` up;
* the five `ldNext_*` projections of `Stream.ldNext` (frozen hold, capture hold,
  receive hold, replay set, transmit set);
* `landingStream_active`/`_step`/`_trace` — the clause at reset, after every
  cycle and along `cutStateAt`, using `ldModeInv` (§11) to kill the receive/
  capture hold branches;
* `stream_landNow_ld`/`stream_landNow_ld_trace` — the restated
  `stream_landNow`: with `LD` up, `(m.ramOwner == k+1) = !FRZD` on every cycle.
-/

theorem mhcOwner_eq (m : Machine.State) (pin : Machine.PinIn) (k : Nat) :
    (mhcOwner m pin == k + 1) =
      (mhcServed m pin == k + 1 && isRdReq ((mhcReqs m pin).getD k .none)) := by
  simp only [mhcOwner, mhcReq, isRdReq]
  by_cases h0 : mhcServed m pin = 0
  · have h0b : ((mhcServed m pin == 0) = true) := by simp [h0]
    rw [if_pos h0b]
    have h3b : (mhcServed m pin == k + 1) = false := by simp [h0]
    rw [h3b]
    rfl
  · rw [if_neg (by simp [h0])]
    by_cases h3 : mhcServed m pin = k + 1
    · rw [h3]
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub]
      cases hq : (mhcReqs m pin).getD k .none <;> simp
    · have h3b : (mhcServed m pin == k + 1) = false := by simp [h3]
      rw [h3b]
      simp only [Bool.false_and]
      cases hq : (mhcReqs m pin).getD (mhcServed m pin - 1) .none <;> simp_all

theorem machSreq_isRd (mode : Nat) (st : Machine.StreamSt) :
    isRdReq (Machine.streamReq mode st) = ((mode != 1) && (mode != 2) && st.rq) := by
  rcases mode with _ | _ | _ | _ | n
  · simp only [Machine.streamReq]; cases st.rq <;> simp [isRdReq]
  · simp only [Machine.streamReq]; cases st.pv <;> simp [isRdReq]
  · simp only [Machine.streamReq]; cases st.pv <;> simp [isRdReq]
  · simp only [Machine.streamReq]; cases st.rq <;> simp [isRdReq]
  · simp only [Machine.streamReq]; cases st.rq <;> simp [isRdReq]

theorem mhcModesReq_absChip (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    (mhcModesReq (absChip s) pin)[k] = machSreq (absChip s) k := by
  simp [mhcModesReq, machSreq, mhcModes, machMode]

theorem ldNext_frz (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hf : i.frz = true) :
    Stream.ldNext cap st i = (if i.rewind then false else st.ld) := by
  unfold Stream.ldNext
  simp [hres, hf]

theorem ldNext_cen (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hrw : i.rewind = false) (hf : i.frz = false)
    (hc : Stream.cen cap i = true) : Stream.ldNext cap st i = st.ld := by
  have hr : Stream.rpl cap i = false := by
    cases h : Stream.rpl cap i
    · rfl
    · exfalso
      simp only [Stream.rpl] at h
      simp only [Stream.cen] at hc
      rw [h] at hc
      simp at hc
  unfold Stream.ldNext
  simp [hres, hrw, hf, hr, hc]

theorem ldNext_rx (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hrw : i.rewind = false) (hf : i.frz = false)
    (hr : Stream.rpl cap i = false) (hc : Stream.cen cap i = false)
    (ht : Stream.txMode cap i = false) : Stream.ldNext cap st i = st.ld := by
  unfold Stream.ldNext
  simp [hres, hrw, hf, hr, hc, ht]

theorem ldNext_rpl (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hrw : i.rewind = false) (hf : i.frz = false)
    (hr : Stream.rpl cap i = true) : Stream.ldNext cap st i = (st.rq && i.gnt) := by
  unfold Stream.ldNext
  simp [hres, hrw, hf, hr]

theorem ldNext_tx (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hrw : i.rewind = false) (hf : i.frz = false)
    (hc : Stream.cen cap i = false) (ht : Stream.txMode cap i = true) :
    Stream.ldNext cap st i = (st.rq && i.gnt) := by
  unfold Stream.ldNext
  simp [hres, hrw, hf, hc, ht]

theorem servedIndex_gnt (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    (Bridge.Mem.servedIndex s.p0 (memIn s pin) == k.val + 1) = streamGnt s pin k.val := by
  rcases k with ⟨kv, hk⟩
  have h01 : kv = 0 ∨ kv = 1 := by omega
  rcases h01 with rfl | rfl
  · show (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 1) = streamGnt s pin 0
    rw [servedIndex_s0]
    rfl
  · show (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 1 + 1) = streamGnt s pin 1
    rw [servedIndex_s1]
    rfl

def LandingStream (s : State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true →
    ((s.cont.ramOwner == k.val + 1) = !s.freeze.frzd)

theorem landingStream_active (s : State) (pin : Machine.PinIn) (hinv : Inv s)
    (hldm : ldModeInv s) (hac : runRst s pin = true) :
    LandingStream (activeStep s pin) := by
  intro k hk
  have hqabs : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hac
  have hstep : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hqabs]
  have howner : (activeStep s pin).cont.ramOwner = mhcOwner (absChip s) pin := by
    show (contentsNext s pin).ramOwner = _
    simp only [contentsNext]
    rw [← hstep]
    exact (step_ram (absChip s) pin hqabs).2.2.1
  have hfrzd' : (activeStep s pin).freeze.frzd = s.freeze.frz := by
    show (CoreCtl.freezeStep s.freeze (freezeIn s pin)).frzd = s.freeze.frz
    rw [CoreCtl.frzd_next]
    have hfr : (freezeIn s pin).resetN = true := hac
    simp [hfr]
  have hstr : (streamAt (activeStep s pin) k.val).ld
      = Stream.ldNext (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) := by
    rw [streamAt_fin]
    have hvec : (activeStep s pin).streams = Vector.ofFn fun i : Fin 2 =>
        Stream.step (i.val == 0) (streamAt s i.val) (streamIn s pin i.val) := rfl
    rw [hvec]
    simp only [vec_get_ofFn']
    rfl
  rw [hstr] at hk
  rw [howner, hfrzd']
  have hsv : (mhcServed (absChip s) pin == k.val + 1) = streamGnt s pin k.val := by
    rw [mhcServed_eq_machServed, machServed_abs s pin hinv, servedIndex_gnt]
  have hgetd : (mhcReqs (absChip s) pin).getD k.val .none = machSreq (absChip s) k := by
    rcases k with ⟨kv, hklt⟩
    have h01 : kv = 0 ∨ kv = 1 := by omega
    rcases h01 with rfl | rfl
    · have h0 : (mhcReqs (absChip s) pin).getD 0 .none =
          (mhcModesReq (absChip s) pin)[(0 : Fin 2)] := rfl
      rw [h0]
      exact mhcModesReq_absChip s pin (0 : Fin 2)
    · have h1 : (mhcReqs (absChip s) pin).getD 1 .none =
          (mhcModesReq (absChip s) pin)[(1 : Fin 2)] := rfl
      rw [h1]
      exact mhcModesReq_absChip s pin (1 : Fin 2)
  by_cases hfrz : s.freeze.frz = true
  · have hfrzm : (memIn s pin).frz = true := hfrz
    have hgnt : streamGnt s pin k.val = false := by
      rcases k with ⟨kv, hklt⟩
      have h01 : kv = 0 ∨ kv = 1 := by omega
      rcases h01 with rfl | rfl
      · show Mem.grantS0 (memIn s pin) = false
        simp [Mem.grantS0, hfrzm]
      · show Mem.grantS1 (memIn s pin) = false
        simp [Mem.grantS1, hfrzm]
    rw [hfrz, mhcOwner_eq, hsv, hgnt]
    simp
  · have hfrz' : s.freeze.frz = false := by simpa using hfrz
    have hrw : (streamIn s pin k.val).rewind = false := by
      cases h : (streamIn s pin k.val).rewind
      · rfl
      · exfalso
        unfold Stream.ldNext at hk
        simp [h] at hk
    have hgntset : streamGnt s pin k.val = (streamIn s pin k.val).gnt := rfl
    rw [hfrz', mhcOwner_eq, hsv, Bool.not_false]
    by_cases hrpl : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
    · rw [ldNext_rpl _ _ _ hac hrw hfrz' hrpl] at hk
      obtain ⟨hrq, hgnt⟩ := Bool.and_eq_true_iff.mp hk
      have hm3 : machMode (absChip s) k = 3 := by
        rw [← stateMode_eq, stateMode_branch s pin k]
        simp [hrpl]
      have hisrd : isRdReq ((mhcReqs (absChip s) pin).getD k.val .none) = true := by
        rw [hgetd, machSreq, machSreq_isRd, hm3, absChip_streams]
        simp [Bridge.StreamB.abs, hrq]
      rw [hgntset, hgnt, hisrd]
      simp
    · have hrpl' : Stream.rpl (k.val == 0) (streamIn s pin k.val) = false := by
        simpa using hrpl
      by_cases hcen : Stream.cen (k.val == 0) (streamIn s pin k.val) = true
      · rw [ldNext_cen _ _ _ hac hrw hfrz' hcen] at hk
        have hm2 : stateMode s k = 2 := by
          rw [stateMode_branch s pin k]
          simp [hrpl', hcen]
        exact absurd hm2 (hldm k hk).2
      · have hcen' : Stream.cen (k.val == 0) (streamIn s pin k.val) = false := by
          simpa using hcen
        by_cases htx : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
        · rw [ldNext_tx _ _ _ hac hrw hfrz' hcen' htx] at hk
          obtain ⟨hrq, hgnt⟩ := Bool.and_eq_true_iff.mp hk
          have hm0 : machMode (absChip s) k = 0 := by
            rw [← stateMode_eq, stateMode_branch s pin k]
            simp [hrpl', hcen', htx]
          have hisrd : isRdReq ((mhcReqs (absChip s) pin).getD k.val .none) = true := by
            rw [hgetd, machSreq, machSreq_isRd, hm0, absChip_streams]
            simp [Bridge.StreamB.abs, hrq]
          rw [hgntset, hgnt, hisrd]
          simp
        · have htx' : Stream.txMode (k.val == 0) (streamIn s pin k.val) = false := by
            simpa using htx
          rw [ldNext_rx _ _ _ hac hrw hfrz' hrpl' hcen' htx'] at hk
          have hm1 : stateMode s k = 1 := by
            rw [stateMode_branch s pin k]
            simp [hrpl', hcen', htx']
          exact absurd hm1 (hldm k hk).1

theorem landingStream_reset (cont : Contents) : LandingStream (resetState cont) := by
  intro k hk
  rw [streamAt_fin, resetState] at hk
  simp [Stream.resetState] at hk

theorem landingStream_step (s : State) (pin : Machine.PinIn) (hinv : Inv s)
    (hldm : ldModeInv s) : LandingStream (step s pin) := by
  by_cases hact : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hact]]
    exact landingStream_active s pin hinv hldm hact
  · rw [show step s pin = resetChip s pin from by simp [step, hact]]
    intro k hk
    rw [streamAt_fin, resetChip, resetState] at hk
    simp [Stream.resetState] at hk

/-- The LD-gated stream clause at every cycle of the cut trace. -/
theorem landingStream_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, LandingStream (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact landingStream_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact landingStream_step _ _ (inv_trace pins cont n) (ldModeInv_trace pins cont hq n)

/-- **The restated `stream_landNow`**: with `LD` up, the machine's owner is this
stream exactly in an unfrozen cycle.  (`Machine.streamNext` reads `i.landNow`
only under `s.ld`, so this is the form it consumes.) -/
theorem stream_landNow_ld (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hland : LandingStream s) (k : Fin 2)
    (hld : (streamAt s k.val).ld = true) :
    (m.ramOwner == k.val + 1) = !(memIn s pin).frzd := by
  rw [hrel.ramOwner]
  exact hland k hld

/-- The same on every cycle of the cut trace. -/
theorem stream_landNow_ld_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n))
    (n : Nat) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel (cutStateAt pins (resetState cont) n) m) (k : Fin 2)
    (hld : (streamAt (cutStateAt pins (resetState cont) n) k.val).ld = true) :
    (m.ramOwner == k.val + 1) = !(memIn (cutStateAt pins (resetState cont) n) pin).frzd := by
  rw [hrel.ramOwner]
  exact landingStream_trace pins cont hq n k hld

/-! ## The mode branches of `LD` (used by the last stream residual)

`ldModeInv` says a stream with a read outstanding is in transmit or replay, so
the cycle's `txMode`/`rpl` is determined by `stateMode`.  These live here (not in
`Assembly.lean`) because the discharge's stream bridge consumes them. -/

/-- `stateMode = 0` is the transmit branch. -/
theorem stateMode_zero_txMode (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : stateMode s k = 0) : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true := by
  rw [stateMode_branch s pin k] at h
  by_cases hr : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · rw [ite_eq_left hr] at h
    exact absurd h (by decide)
  · rw [ite_eq_right hr] at h
    by_cases hc : Stream.cen (k.val == 0) (streamIn s pin k.val) = true
    · rw [ite_eq_left hc] at h
      exact absurd h (by decide)
    · rw [ite_eq_right hc] at h
      by_cases ht : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
      · exact ht
      · rw [ite_eq_right ht] at h
        exact absurd h (by decide)

/-- `stateMode = 3` is the replay branch. -/
theorem stateMode_three_rpl (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : stateMode s k = 3) : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true := by
  rw [stateMode_branch s pin k] at h
  by_cases hr : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · exact hr
  · rw [ite_eq_right hr] at h
    by_cases hc : Stream.cen (k.val == 0) (streamIn s pin k.val) = true
    · rw [ite_eq_left hc] at h
      exact absurd h (by decide)
    · rw [ite_eq_right hc] at h
      by_cases ht : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
      · rw [ite_eq_left ht] at h
        exact absurd h (by decide)
      · rw [ite_eq_right ht] at h
        exact absurd h (by decide)

/-- `ldModeInv` puts a stream with a read outstanding in the transmit or replay
branch. -/
theorem ldMode_branch (s : State) (pin : Machine.PinIn) (k : Fin 2) (hm : ldModeInv s)
    (hld : (streamAt s k.val).ld = true) :
    Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
      Stream.rpl (k.val == 0) (streamIn s pin k.val) = true := by
  have h := hm k hld
  rw [stateMode_branch s pin k] at h
  by_cases hrpl : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · exact Or.inr hrpl
  · by_cases htx : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
    · exact Or.inl htx
    · simp [hrpl, htx] at h

end Metronome.ChipCut.Discharge
