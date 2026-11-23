/-
# W2: the core guard and source vectors (`CoreInputBus.guards`, `CoreInputBus.srcs`)

Round b: after the `Wire.lean` fix (`sourcesOf.sBit`/`sByte`/`guardsOf.sBit` use
`Stream.bitOut (k == 0)`), the two `CoreInputBus` fields are discharged from
`ChipRel`, `Inv`, `runRst s pin = true` and the global string-table facts
(`GuardTable`, `SrcTable`).

Layers (as recorded in `DISCHARGE_COREUNITS_NOTES.md` §2):

1. **leaf equalities** — `sourcesOf`, `guardsOf` and `lineGuardsOf` of the cut
   (`Wire.lean`) against `Bridge.Glue.{sources,guards,lineGuards}Of` of the
   machine `Env` built from the related state, including the pin-vector leaf
   (`Debug.Pins.pinVec` vs `Machine.Util.protoPins` with the `RPL`/`EMASK`/`RLV`
   overlay) and `Env.hlvl`;
2. the **`g_line` byte step** — `bitOf (lineSlot gLine ln) j = bitAt
   (lineGuard ln (lineGuardsOf s)) j`;
3. the **`srcVec`** substitutions — the four `withSlot` core-local ports and the
   `lowMask 512 (8 * 39)` tail;

then `CoreUnits.guardVec_bit` / `guardV_global` / `Bridge.Glue.lineGuard_bridge`
and `srcV_global` / `Glue.src_slot_*` finish both fields.

Evidence: `data/raw/lean_chipcut_wire_guardsrc_v4_20261121b/`.
-/

import Metronome.ChipCut.Discharge.CoreUnits

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2048

namespace Metronome.ChipCut.Discharge

open Metronome Metronome.ChipCut
open Metronome.Machine.Util

/-! ## 1. Selector bridges (`Nat`-matched `Wire.lean` selectors) -/

theorem lineAt_get (s : State) (l : Fin 4) : lineAt s l.val = s.lines[l.val] := by
  rcases l with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem streamAt_get (s : State) (k : Fin 2) : streamAt s k.val = s.streams[k.val] := by
  rcases k with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl

theorem cntAt_get (s : State) (k : Fin 3) : cntAt s k.val = s.cnt[k.val] := by
  rcases k with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> rfl

theorem shAt_get (s : State) (k : Fin 2) : shAt s k.val = s.sh[k.val] := by
  rcases k with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl

theorem lfAt_get (s : State) (k : Fin 2) : lfAt s k.val = s.lf[k.val] := by
  rcases k with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl

/-- `vget` at an in-range index is the `Fin`-indexed component. -/
theorem vget_fin {a : Type} {n : Nat} [Inhabited a] (v : Vector a n) (e : Nat) (he : e < n) :
    Machine.Util.vget v e = v[(⟨e, he⟩ : Fin n)] := vec_get!_eq_get v e he

/-! ## 2. Packing helpers (cut concatenations vs the machine's `bv`) -/

/-- One cut bit as the machine's `bv 1` of `b2n`. -/
theorem b1_eq (b : Bool) : (if b then (1 : BitVec 1) else 0) = Machine.Util.bv 1 (b2n b) := by
  cases b <;> rfl

/-- Two cut bits (high first) as the machine's `bv 2`. -/
theorem b2_eq (a b : Bool) :
    (if a then (1 : BitVec 1) else 0) ++ (if b then (1 : BitVec 1) else 0) =
      Machine.Util.bv 2 (b2n a * 2 + b2n b) := by
  cases a <;> cases b <;> rfl

/-- Three cut bits in `x ++ (y ++ z)` shape as the machine's `bv 3`. -/
theorem b3_eq (a b c : Bool) :
    (if a then (1 : BitVec 1) else 0) ++ ((if b then (1 : BitVec 1) else 0) ++
      (if c then (1 : BitVec 1) else 0)) =
      Machine.Util.bv 3 (b2n a * 4 + b2n b * 2 + b2n c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Four cut bits in `a ++ (b ++ (c ++ d))` shape as the machine's `bv 4`. -/
theorem b4_eq (a b c d : Bool) :
    (if a then (1 : BitVec 1) else 0) ++ ((if b then (1 : BitVec 1) else 0) ++
      ((if c then (1 : BitVec 1) else 0) ++ (if d then (1 : BitVec 1) else 0))) =
      Machine.Util.bv 4 (b2n a * 8 + b2n b * 4 + b2n c * 2 + b2n d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- `(x ++ y).toNat` as `x.toNat * 2 ^ y.width + y.toNat`. -/
theorem cat_toNat {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.or_comm,
    Bridge.Glue.or_shift y.toNat x.toNat n y.isLt]

/-- Four two-bit values in `x3 ++ (x2 ++ (x1 ++ x0))` shape as the machine's `bv 8`. -/
theorem b4x2_eq (x3 x2 x1 x0 : BitVec 2) :
    x3 ++ (x2 ++ (x1 ++ x0)) =
      Machine.Util.bv 8 (x3.toNat * 64 + x2.toNat * 16 + x1.toNat * 4 + x0.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [cat_toNat, cat_toNat, cat_toNat, Machine.Util.bv, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  have h0 := x0.isLt
  have h1 := x1.isLt
  have h2 := x2.isLt
  have h3 := x3.isLt
  show x3.toNat * 2 ^ (2 + (2 + 2)) + (x2.toNat * 2 ^ (2 + 2) +
    (x1.toNat * 2 ^ 2 + x0.toNat)) = x3.toNat * 64 + x2.toNat * 16 + x1.toNat * 4 + x0.toNat
  rw [show 2 ^ (2 + (2 + 2)) = 64 from by decide,
    show 2 ^ (2 + 2) = 16 from by decide, show 2 ^ 2 = 4 from by decide]
  omega

/-- The four bytes of a 32-bit word (high byte first) reassemble it. -/
theorem accR_pack (r : BitVec 32) :
    ((BitVec.truncate 8 (BitVec.ushiftRight r (8 * 3)) ++
          BitVec.truncate 8 (BitVec.ushiftRight r (8 * 2))) ++
        BitVec.truncate 8 (BitVec.ushiftRight r (8 * 1))) ++
      BitVec.truncate 8 (BitVec.ushiftRight r (8 * 0)) = r := by
  bv_decide

/-- The sticky `SHk.OUT` bit: `D & 0x80 != 0` is bit 7. -/
theorem and80_ne (d : BitVec 8) : ((d &&& (0x80 : BitVec 8)) != 0) = d.getLsbD 7 := by
  bv_decide

/-- The `SHk.OUT` bit: `D & 1 != 0` is bit 0. -/
theorem and01_ne (d : BitVec 8) : ((d &&& (0x01 : BitVec 8)) != 0) = d.getLsbD 0 := by
  bv_decide

/-! ## 2b. Accessors for the conjunction-valued relation fields -/

theorem sync_s2 {s : State} {m : Machine.State} (h : ChipRel s m) :
    s.sync.s2 = m.sync.ui2 ++ m.sync.uio2 := by
  obtain ⟨-, h, -⟩ := h.sync
  exact h

theorem dbg_cen {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.dbg.cen = s.dbgCtrl.cen := by
  obtain ⟨-, -, -, -, -, h, -, -, -, -, -⟩ := h.dbg
  exact h

theorem dbg_rpl {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.dbg.rpl = s.dbgCtrl.replay := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -, -⟩ := h.dbg
  exact h

theorem dbg_emask {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.dbg.emask = s.dbgCtrl.emask := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -⟩ := h.dbg
  exact h

theorem dbg_rlv {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.dbg.rlv = s.dbgCtrl.rlv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := h.dbg
  exact h

theorem gs_ctrl_inv {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.ctrl.inv = s.glue.inv := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -, -, -⟩ := h.ctrl
  exact h

theorem ctrl_outv {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.ctrl.outv = s.glue.outv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -, -⟩ := h.ctrl
  exact h

theorem ctrl_inb {s : State} {m : Machine.State} (h : ChipRel s m) :
    m.ctrl.inb = s.glue.inB := by
  obtain ⟨-, -, -, -, -, h, -, -, -, -, -, -⟩ := h.ctrl
  exact h

/-! ## 3. The pin-vector leaf

`Wire.pinLvl` (`Debug.Pins.level (Debug.Pins.pinVec s2) RLV EMASK RPL`) against
`Machine.pinView`'s `Nat` level (`protoPins` with the `RPL`/`EMASK`/`RLV`
overlay). -/

/-- `protoPins` splits a synchroniser word into a low byte and five high pins. -/
theorem protoPins_eq (ui uio : BitVec 8) :
    Machine.Util.protoPins ui uio = uio.toNat + (ui.toNat >>> 3) * 256 := rfl

/-- `Debug.Pins.pinVec` of `ui ++ uio` is the machine's `protoPins` value. -/
theorem pinVec_toNat (ui uio : BitVec 8) :
    (Debug.Pins.pinVec (ui ++ uio)).toNat = Machine.Util.protoPins ui uio := by
  have hraw : (ui ++ uio).toNat = uio.toNat + ui.toNat * 2 ^ 8 := by
    rw [cat_toNat]; omega
  have hlow : Machine.Util.nbits (ui ++ uio).toNat 0 8 = uio.toNat := by
    rw [hraw, Bridge.Glue.nbits_low (m := 8) ui.toNat uio.toNat 0 8 (by omega) (by omega)]
    simp [Machine.Util.nbits, Nat.mod_eq_of_lt uio.isLt]
  have hhi : Machine.Util.nbits (ui ++ uio).toNat 11 5 = ui.toNat >>> 3 := by
    rw [hraw,
      Bridge.Glue.nbits_high (m := 8) (A := ui.toNat) (B := uio.toNat) 3 5 (by omega)]
    rw [Machine.Util.nbits, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by have := ui.isLt; omega)
  unfold Debug.Pins.pinVec
  rw [cat_toNat, Bridge.Debug.slice_toNat, Bridge.Debug.slice_toNat, protoPins_eq]
  rw [hlow, hhi]
  omega

/-- `Machine.pinView`'s level, in the form `Bridge.Debug.level_toNat` produces. -/
theorem pinView_lvl (sy : Machine.SyncSt) (d : Machine.DbgSt) :
    (Machine.pinView sy d).lvl =
      (Machine.Util.protoPins sy.ui2 sy.uio2 &&&
          (2 ^ 13 - 1 - (if d.rpl then d.emask.toNat else 0))) |||
        (d.rlv.toNat &&& (if d.rpl then d.emask.toNat else 0)) := by
  unfold Machine.pinView
  simp [Machine.Tables.N_IN_PINS]

/-- The cut's synchronised level equals the machine's `pinView` level. -/
theorem pinLvl_toNat (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (pinLvl s).toNat = (Machine.pinView m.sync m.dbg).lvl := by
  have hrpl : s.dbgCtrl.replay = m.dbg.rpl := (dbg_rpl hrel).symm
  have hemask : s.dbgCtrl.emask = m.dbg.emask := (dbg_emask hrel).symm
  have hrlv : s.dbgCtrl.rlv = m.dbg.rlv := (dbg_rlv hrel).symm
  have hs2 : s.sync.s2 = m.sync.ui2 ++ m.sync.uio2 := sync_s2 hrel
  unfold pinLvl
  rw [Bridge.Debug.level_toNat, hs2, hrpl, hemask, hrlv, pinVec_toNat, pinView_lvl]

/-- `Env.hlvl`: the machine pin vector is 13 bits wide. -/
theorem pinLvl_lt (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (Machine.pinView m.sync m.dbg).lvl < 2 ^ 13 := by
  rw [← pinLvl_toNat s m hrel]
  exact (pinLvl s).isLt

/-- `Machine.pinView`'s level reads `ui2`, `uio2`, `RPL`, `EMASK`, `RLV`. -/
theorem pinView_lvl_congr {sy sy' : Machine.SyncSt} {d d' : Machine.DbgSt}
    (h1 : sy.ui2 = sy'.ui2) (h2 : sy.uio2 = sy'.uio2)
    (h4 : d.rpl = d'.rpl) (h5 : d.emask = d'.emask) (h6 : d.rlv = d'.rlv) :
    (Machine.pinView sy d).lvl = (Machine.pinView sy' d').lvl := by
  rw [pinView_lvl, pinView_lvl, h1, h2, h4, h5, h6]

/-- A pin select reads only the level. -/
theorem pinView_pin_congr {sy sy' : Machine.SyncSt} {d d' : Machine.DbgSt}
    (h : (Machine.pinView sy d).lvl = (Machine.pinView sy' d').lvl) (k : Nat) :
    (Machine.pinView sy d).pin k = (Machine.pinView sy' d').pin k := by
  simp [Machine.PinView.pin, h]

/-- The cut's line pin vectors are the machine's `pinView` of the related state. -/
theorem gs_pinView_abs (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (Machine.pinView (absChip s).sync (absChip s).dbg).lvl =
      (Machine.pinView m.sync m.dbg).lvl := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, h10, -⟩ := hrel.dbg
  have hs2 : s.sync.s2 = m.sync.ui2 ++ m.sync.uio2 := sync_s2 hrel
  refine pinView_lvl_congr ?_ ?_ ?_ ?_ ?_
  · show BitVec.truncate 8 (BitVec.ushiftRight s.sync.s2 8) = m.sync.ui2
    rw [hs2]
    bv_decide
  · show BitVec.truncate 8 s.sync.s2 = m.sync.uio2
    rw [hs2]
    bv_decide
  · show s.dbgCtrl.replay = m.dbg.rpl
    exact h7.symm
  · show s.dbgCtrl.emask = m.dbg.emask
    exact h8.symm
  · show s.dbgCtrl.rlv = m.dbg.rlv
    exact h10.symm

/-! ## 4. Unit leaves (`UnitsRel` + the cut's output functions) -/

/-- `SHk.DONE` against the machine's `doneK`. -/
theorem shDone_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Units.Shifter.done (shAt s k.val) = Bridge.Glue.doneK m.units k.val := by
  obtain ⟨-, -, -, -, -, -, -, hush, -, -⟩ := hrel.units
  show Units.Shifter.done (shAt s k.val) =
    ((Machine.Util.vget m.units.sh k.val).cnt.toNat == 0)
  rw [vget_fin m.units.sh k.val k.isLt, hush k]
  rw [Units.Shifter.done, Bridge.StreamB.beq_nat]
  rfl

/-- `SHk.OUT` against the machine's `shOut`. -/
theorem shOut_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Units.Shifter.out (shAt s k.val) = Bridge.Glue.shOk m.units k.val := by
  obtain ⟨-, -, -, -, -, -, -, hush, -, -⟩ := hrel.units
  show Units.Shifter.out (shAt s k.val) = Machine.shOut (vget m.units.sh k.val)
  rw [vget_fin m.units.sh k.val k.isLt, hush k]
  simp only [Units.Shifter.out, Machine.shOut, Machine.Util.bit]
  by_cases h : (shAt s k.val).msb = true
  · rw [if_pos h, if_pos h]
    exact and80_ne _
  · rw [if_neg h, if_neg h]
    exact and01_ne _

/-- `CNTk.Z` against the machine's `(V == 0)`. -/
theorem cntZ_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 3) :
    Units.Counter.zOut (cntAt s k.val) =
      ((Machine.Util.vget m.units.cnt k.val).toNat == 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, hucnt, -⟩ := hrel.units
  rw [vget_fin m.units.cnt k.val k.isLt, hucnt k]
  rw [Units.Counter.zOut, Bridge.StreamB.beq_nat]
  rfl

/-- The accumulator scratch word against the machine's four `R` bytes. -/
theorem accR_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    s.acc.r = ((Machine.Util.vget m.units.r 3 ++ Machine.Util.vget m.units.r 2) ++
      Machine.Util.vget m.units.r 1) ++ Machine.Util.vget m.units.r 0 := by
  obtain ⟨-, -, -, -, -, -, hur, -, -, -⟩ := hrel.units
  rw [vget_fin m.units.r 3 (by decide), vget_fin m.units.r 2 (by decide),
    vget_fin m.units.r 1 (by decide), vget_fin m.units.r 0 (by decide),
    hur ⟨3, by decide⟩, hur ⟨2, by decide⟩, hur ⟨1, by decide⟩, hur ⟨0, by decide⟩]
  exact (accR_pack s.acc.r).symm

/-- The shifter data bytes. -/
theorem shD_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (shAt s 1).dr ++ (shAt s 0).dr =
      (Machine.Util.vget m.units.sh 1).d ++ (Machine.Util.vget m.units.sh 0).d := by
  obtain ⟨-, -, -, -, -, -, -, hush, -, -⟩ := hrel.units
  rw [vget_fin m.units.sh 1 (by decide), vget_fin m.units.sh 0 (by decide),
    hush ⟨1, by decide⟩, hush ⟨0, by decide⟩]

/-- The two shifter output bits. -/
theorem shO_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (if Units.Shifter.out (shAt s 1) then (1 : BitVec 1) else 0) ++
        (if Units.Shifter.out (shAt s 0) then (1 : BitVec 1) else 0) =
      Machine.Util.bv 2 (Machine.Util.b2n (Bridge.Glue.shOk m.units 1) * 2 +
        Machine.Util.b2n (Bridge.Glue.shOk m.units 0)) := by
  rw [b2_eq, shOut_eq s m hrel ⟨1, by decide⟩, shOut_eq s m hrel ⟨0, by decide⟩]

/-- The three counter values. -/
theorem cnV_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    ((cntAt s 2).v ++ (cntAt s 1).v) ++ (cntAt s 0).v =
      (Machine.Util.vget m.units.cnt 2 ++ Machine.Util.vget m.units.cnt 1) ++
        Machine.Util.vget m.units.cnt 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hucnt, -⟩ := hrel.units
  rw [vget_fin m.units.cnt 2 (by decide), vget_fin m.units.cnt 1 (by decide),
    vget_fin m.units.cnt 0 (by decide),
    hucnt ⟨2, by decide⟩, hucnt ⟨1, by decide⟩, hucnt ⟨0, by decide⟩]

/-- The two LFSR states. -/
theorem lfS_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (lfAt s 1).s ++ (lfAt s 0).s =
      Machine.Util.vget m.units.lf 1 ++ Machine.Util.vget m.units.lf 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hulf⟩ := hrel.units
  rw [vget_fin m.units.lf 1 (by decide), vget_fin m.units.lf 0 (by decide),
    hulf ⟨1, by decide⟩, hulf ⟨0, by decide⟩]

/-! ## 5. Stream leaves (`AbsRelB` + the cut's stream outputs) -/

/-- A `nbits` window is below `2^w`. -/
theorem nbits_lt (x l w : Nat) : Machine.Util.nbits x l w < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

/-- `ofNat 11` round-trips below `2^11`. -/
theorem ofNat11_toNat (x : Nat) (hx : x < 2 ^ 11) : (BitVec.ofNat 11 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hx

/-- `ofNat 12` round-trips below `2^12`. -/
theorem ofNat12_toNat (x : Nat) (hx : x < 2 ^ 12) : (BitVec.ofNat 12 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hx

/-- The machine's stream configuration of the cut's `cfgView`. -/
theorem cfgView_streams (c : Machine.Config) (k : Nat) (hk : k < 2) :
    Machine.Util.vget (Machine.cfgView c).streams k = Machine.Config.stream c k := by
  rw [vget_fin _ k hk]
  simp only [Machine.cfgView]
  rw [vec_get_ofFn']

/-- Build a `StreamCfg` equality from its five fields. -/
theorem streamCfg_eq (a b : Machine.StreamCfg) (h1 : a.rx = b.rx) (h2 : a.msb = b.msb)
    (h3 : a.start = b.start) (h4 : a.len = b.len) (h5 : a.mark = b.mark) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp_all

/-- The cut's `streamViewIn` configuration is the machine's `cfgView` stream. -/
theorem cfgOf_streamViewIn (s : State) (k : Fin 2) :
    Bridge.StreamB.cfgOf (streamViewIn s k.val) =
      Machine.Util.vget (Machine.cfgView s.cont.cfg).streams k.val := by
  rw [vget_fin (Machine.cfgView s.cont.cfg).streams k.val k.isLt]
  simp only [Machine.cfgView]
  rw [vec_get_ofFn']
  have hcf : (Machine.cfgView s.cont.cfg).streams[k.val]! =
      Machine.Config.stream s.cont.cfg k.val := by
    rw [show (Machine.cfgView s.cont.cfg).streams[k.val]! =
      Machine.Util.vget (Machine.cfgView s.cont.cfg).streams k.val from rfl,
      vget_fin _ k.val k.isLt]
    simp only [Machine.cfgView]
    rw [vec_get_ofFn']
  simp only [Bridge.StreamB.cfgOf, streamViewIn, hcf, Machine.Config.stream]
  apply streamCfg_eq
  · rfl
  · rfl
  · exact ofNat11_toNat _ (nbits_lt _ _ _)
  · exact ofNat12_toNat _ (nbits_lt _ _ _)
  · exact ofNat12_toNat _ (nbits_lt _ _ _)

/-- S0's mode: the cut's `CEN`/`RPL` gating is the machine's `streamMode` slot 0. -/
theorem streamMode_zero_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Machine.streamMode (Bridge.StreamB.cfgOf (streamViewIn s 0)) 0
        (Bridge.StreamB.dbgOfCap true (streamViewIn s 0)) =
      Machine.streamMode (Machine.Util.vget (Machine.cfgView m.cfg).streams 0) 0 m.dbg := by
  have hcen : m.dbg.cen = s.dbgCtrl.cen := dbg_cen hrel
  have hrpl : m.dbg.rpl = s.dbgCtrl.replay := dbg_rpl hrel
  have hrep : (streamViewIn s 0).replayEn = m.dbg.rpl := by
    show s.dbgCtrl.replay = m.dbg.rpl
    exact hrpl.symm
  have hcap : (streamViewIn s 0).capEn = (m.dbg.cen && !(m.dbg.rpl)) := by
    show (s.dbgCtrl.cen && !(s.dbgCtrl.replay)) = (m.dbg.cen && !(m.dbg.rpl))
    rw [hcen, hrpl]
  have hcf : (Bridge.StreamB.cfgOf (streamViewIn s 0)).rx =
      (Machine.Util.vget (Machine.cfgView m.cfg).streams 0).rx := by
    rw [cfgOf_streamViewIn s ⟨0, by decide⟩, hrel.cfg]
  simp only [Machine.streamMode, Bridge.StreamB.dbgOfCap, Stream.cen, Stream.rpl,
    hrep, hcap, hcf]
  by_cases hr : m.dbg.rpl = true <;> by_cases hc : m.dbg.cen = true <;>
    by_cases hx : (Machine.Util.vget (Machine.cfgView m.cfg).streams 0).rx = true <;>
    simp_all

/-- The cut's `Sk.BIT` at `CAP = 0` (S1) is the machine's slot-1 bit. -/
theorem bitOut_k1 (st : Stream.State) (i : Stream.Input) (d : Machine.DbgSt) :
    Stream.bitOut false st i =
      Machine.streamBit (Bridge.StreamB.cfgOf i) 1 d (Bridge.StreamB.abs st) := by
  unfold Stream.bitOut Machine.streamBit Machine.streamEnd Stream.endC
  rw [Bridge.StreamB.beq_nat, Bridge.StreamB.stream_bitAt_eq, Bridge.StreamB.bsel_toNat]
  have hmode : Stream.txMode false i =
      (Machine.streamMode (Bridge.StreamB.cfgOf i) 1 d == 0) := by
    unfold Stream.txMode Stream.cen Stream.rpl Machine.streamMode Bridge.StreamB.cfgOf
    by_cases h : i.cfgMode = true <;> simp [h]
  rw [hmode]
  simp [Bridge.StreamB.abs, Bridge.StreamB.cfgOf]

/-- `Machine.streamBit` at slot 1 reads only `RX`, `MSB`, `LEN` and four state fields. -/
theorem streamBit_congr_1 {c c' : Machine.StreamCfg} {d d' : Machine.DbgSt}
    {st st' : Machine.StreamSt}
    (hrx : c.rx = c'.rx) (hmsb : c.msb = c'.msb) (hlen : c.len = c'.len)
    (hpos : st.pos = st'.pos) (hbidx : st.bidx = st'.bidx) (hcv : st.cv = st'.cv)
    (hcur : st.cur = st'.cur) :
    Machine.streamBit c 1 d st = Machine.streamBit c' 1 d' st' := by
  simp [Machine.streamBit, Machine.streamMode, Machine.streamB, Machine.streamEnd,
    hrx, hmsb, hlen, hpos, hbidx, hcv, hcur]

/-- `Machine.streamBit` with equal modes and four equal state fields. -/
theorem streamBit_congr_mode {c c' : Machine.StreamCfg} {d d' : Machine.DbgSt}
    {st st' : Machine.StreamSt} (k k' : Nat)
    (hmode : Machine.streamMode c k d = Machine.streamMode c' k' d')
    (hmsb : c.msb = c'.msb) (hlen : c.len = c'.len)
    (hpos : st.pos = st'.pos) (hbidx : st.bidx = st'.bidx) (hcv : st.cv = st'.cv)
    (hcur : st.cur = st'.cur) :
    Machine.streamBit c k d st = Machine.streamBit c' k' d' st' := by
  simp [Machine.streamBit, hmode, Machine.streamB, Machine.streamEnd,
    hmsb, hlen, hpos, hbidx, hcv, hcur]

/-- The stream fields the guard/source leaves read, from `ChipRel.streams`. -/
theorem stream_fields (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    (streamAt s k.val).pos = (Machine.Util.vget m.streams k.val).pos ∧
    (streamAt s k.val).bidx = (Machine.Util.vget m.streams k.val).bidx ∧
    (streamAt s k.val).cur = (Machine.Util.vget m.streams k.val).cur ∧
    (streamAt s k.val).cv = (Machine.Util.vget m.streams k.val).cv ∧
    (streamAt s k.val).pend = (Machine.Util.vget m.streams k.val).pend := by
  obtain ⟨hp, hb, -, hc, hcv, -, -, hpd, -, -, -⟩ := hrel.streams k
  rw [vget_fin m.streams k.val k.isLt]
  exact ⟨hp, hb, hc, hcv, hpd⟩

/-- `Sk.END`, cut vs machine. -/
theorem streamEnd_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Stream.gEnd (streamAt s k.val) (streamViewIn s k.val) =
      Machine.streamEnd (Machine.Util.vget (Machine.cfgView m.cfg).streams k.val)
        (Machine.Util.vget m.streams k.val) := by
  obtain ⟨hpos, -, -, -, -⟩ := stream_fields s m hrel k
  have hcfg : Machine.Util.vget (Machine.cfgView m.cfg).streams k.val =
      Bridge.StreamB.cfgOf (streamViewIn s k.val) := by
    rw [cfgOf_streamViewIn s k, hrel.cfg]
  show ((streamAt s k.val).pos == (streamViewIn s k.val).cfgLen) = _
  rw [Bridge.StreamB.beq_nat]
  unfold Machine.streamEnd
  rw [hcfg, hpos]
  rfl

/-- `Sk.MARK`, cut vs machine. -/
theorem streamMark_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Stream.gMark (streamAt s k.val) (streamViewIn s k.val) =
      Machine.streamMark (Machine.Util.vget (Machine.cfgView m.cfg).streams k.val)
        (Machine.Util.vget m.streams k.val) := by
  obtain ⟨hpos, hbidx, -, -, -⟩ := stream_fields s m hrel k
  have hcfg : Machine.Util.vget (Machine.cfgView m.cfg).streams k.val =
      Bridge.StreamB.cfgOf (streamViewIn s k.val) := by
    rw [cfgOf_streamViewIn s k, hrel.cfg]
  show ((streamAt s k.val).pos == (streamViewIn s k.val).cfgMark &&
    ((streamAt s k.val).bidx == 0)) = _
  rw [Bridge.StreamB.beq_nat, Bridge.StreamB.beq_nat]
  unfold Machine.streamMark
  rw [hcfg, hpos, hbidx]
  rfl

/-- `Sk.BYTE` (guard), cut vs machine. -/
theorem streamAtByte_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Stream.gByte (streamAt s k.val) (streamViewIn s k.val) =
      Machine.streamAtByte (Machine.Util.vget m.streams k.val) := by
  obtain ⟨-, hbidx, -, -, -⟩ := stream_fields s m hrel k
  show ((streamAt s k.val).bidx == 0) = _
  rw [Bridge.StreamB.beq_nat]
  unfold Machine.streamAtByte
  rw [hbidx]
  rfl

/-- `Sk.BIT` of S1 (`CAP = 0`): the cut's `bitOut false` against the machine's slot 1. -/
theorem streamBit_1_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Stream.bitOut false (streamAt s 1) (streamViewIn s 1) =
      Machine.streamBit (Machine.Util.vget (Machine.cfgView m.cfg).streams 1) 1 m.dbg
        (Machine.Util.vget m.streams 1) := by
  obtain ⟨hpos, hbidx, hcur, hcv, -⟩ := stream_fields s m hrel ⟨1, by decide⟩
  have hcfg : Machine.Util.vget (Machine.cfgView m.cfg).streams 1 =
      Bridge.StreamB.cfgOf (streamViewIn s 1) := by
    rw [cfgOf_streamViewIn s ⟨1, by decide⟩, hrel.cfg]
  refine Eq.trans (bitOut_k1 (streamAt s 1) (streamViewIn s 1) m.dbg) ?_
  rw [hcfg]
  exact streamBit_congr_1 rfl rfl rfl hpos hbidx hcv hcur

/-- `Sk.BIT` of S0 (`CAP = 1`): the cut's `bitOut true` against the machine's slot 0. -/
theorem streamBit_0_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    Stream.bitOut true (streamAt s 0) (streamViewIn s 0) =
      Machine.streamBit (Machine.Util.vget (Machine.cfgView m.cfg).streams 0) 0 m.dbg
        (Machine.Util.vget m.streams 0) := by
  obtain ⟨hpos, hbidx, hcur, hcv, -⟩ := stream_fields s m hrel ⟨0, by decide⟩
  have hcfg : Machine.Util.vget (Machine.cfgView m.cfg).streams 0 =
      Bridge.StreamB.cfgOf (streamViewIn s 0) := by
    rw [cfgOf_streamViewIn s ⟨0, by decide⟩, hrel.cfg]
  refine Eq.trans (Bridge.StreamB.bit_eq true (streamAt s 0) (streamViewIn s 0)) ?_
  rw [hcfg]
  refine streamBit_congr_mode 0 0 ?_ rfl rfl hpos hbidx hcv hcur
  rw [streamMode_zero_eq s m hrel, hcfg]

/-- `Machine.streamByte` reads `RX`, `CUR` and `PEND` only. -/
theorem streamByte_congr {c c' : Machine.StreamCfg} {st st' : Machine.StreamSt}
    (hrx : c.rx = c'.rx) (hcur : st.cur = st'.cur) (hpend : st.pend = st'.pend) :
    Machine.streamByte c st = Machine.streamByte c' st' := by
  simp [Machine.streamByte, hrx, hcur, hpend]

/-- Source `Sk.BYTE`, cut vs machine. -/
theorem streamByte_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Stream.byteOut (k.val == 0) (streamAt s k.val) (streamViewIn s k.val) =
      Machine.Util.bv 8 (Machine.streamByte
        (Machine.Util.vget (Machine.cfgView m.cfg).streams k.val)
        (Machine.Util.vget m.streams k.val)) := by
  obtain ⟨-, -, hcur, -, hpend⟩ := stream_fields s m hrel k
  have hcfg : Machine.Util.vget (Machine.cfgView m.cfg).streams k.val =
      Bridge.StreamB.cfgOf (streamViewIn s k.val) := by
    rw [cfgOf_streamViewIn s k, hrel.cfg]
  show (if (streamViewIn s k.val).cfgMode then (streamAt s k.val).pend
    else (streamAt s k.val).cur) = _
  rw [hcfg]
  have hbyte : Machine.streamByte (Bridge.StreamB.cfgOf (streamViewIn s k.val))
      (Machine.Util.vget m.streams k.val) =
      (if (streamViewIn s k.val).cfgMode then (streamAt s k.val).pend
        else (streamAt s k.val).cur).toNat := by
    simp only [Machine.streamByte, Bridge.StreamB.cfgOf, hpend.symm, hcur.symm]
    by_cases hm : (streamViewIn s k.val).cfgMode <;> simp [hm]
  rw [hbyte, Bridge.Glue.bv_toNat]

/-! ## 6. Line leaves -/

/-- The machine's line configuration of the cut's `cfgView`. -/
theorem cfgView_lines (c : Machine.Config) (l : Nat) (hl : l < 4) :
    Machine.Util.vget (Machine.cfgView c).lines l = c.line l := by
  rw [vget_fin _ l hl]
  simp only [Machine.cfgView]
  rw [vec_get_ofFn']

/-- Line LUT words are 32 bits, so `ofNat 32` round-trips. -/
theorem cfgLine_lut0_lt (c : Machine.Config) (l : Nat) : (c.line l).lut0 < 2 ^ 32 := by
  simp only [Machine.Config.line, Machine.Util.cfgLE]
  exact bgetLE_lt _ _ _

theorem cfgLine_lut1_lt (c : Machine.Config) (l : Nat) : (c.line l).lut1 < 2 ^ 32 := by
  simp only [Machine.Config.line, Machine.Util.cfgLE]
  exact bgetLE_lt _ _ _

theorem lines_lut0_lt (c : Machine.Config) (l : Nat) (hl : l < 4) :
    ((Machine.cfgView c).lines[l]!).lut0 < 2 ^ 32 := by
  rw [show (Machine.cfgView c).lines[l]! = Machine.Util.vget (Machine.cfgView c).lines l
    from rfl, cfgView_lines c l hl]
  exact cfgLine_lut0_lt c l

theorem lines_lut1_lt (c : Machine.Config) (l : Nat) (hl : l < 4) :
    ((Machine.cfgView c).lines[l]!).lut1 < 2 ^ 32 := by
  rw [show (Machine.cfgView c).lines[l]! = Machine.Util.vget (Machine.cfgView c).lines l
    from rfl, cfgView_lines c l hl]
  exact cfgLine_lut1_lt c l

/-- `L.IN` (the two-bit input symbol), cut vs machine. -/
theorem lineInSym_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) (hl : l < 4) :
    (Line.inSym s.lines[l] (lineStaticIn s l)).toNat =
      Machine.inSym (Machine.Util.vget (Machine.cfgView m.cfg).lines l)
        (Machine.Util.vget m.lines l) := by
  rw [Bridge.Line.inSym_toNat]
  have hst : Bridge.Line.absSt s.lines[l] = Machine.Util.vget m.lines l := by
    rw [← lineAt_get s ⟨l, hl⟩, vget_fin m.lines l hl, hrel.lines ⟨l, hl⟩]
  have hc0 : (Bridge.Line.absCfg (lineStaticIn s l).cfg).lut0 =
      (Machine.Util.vget (Machine.cfgView m.cfg).lines l).lut0 := by
    rw [Bridge.Line.absCfg_lut0]
    show (lineCfgOf ((Machine.cfgView s.cont.cfg).lines[l]!)).lut0.toNat = _
    rw [hrel.cfg]
    simp only [lineCfgOf, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lines_lut0_lt s.cont.cfg l hl)]
    rfl
  have hc1 : (Bridge.Line.absCfg (lineStaticIn s l).cfg).lut1 =
      (Machine.Util.vget (Machine.cfgView m.cfg).lines l).lut1 := by
    rw [Bridge.Line.absCfg_lut1]
    show (lineCfgOf ((Machine.cfgView s.cont.cfg).lines[l]!)).lut1.toNat = _
    rw [hrel.cfg]
    simp only [lineCfgOf, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lines_lut1_lt s.cont.cfg l hl)]
    rfl
  rw [hst]
  unfold Machine.inSym
  rw [hc0, hc1]

/-- Line `SP`, cut vs machine. -/
theorem lineSp_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) (hl : l < 4) :
    s.lines[l].sp = (Machine.Util.vget m.lines l).sp := by
  rw [show s.lines[l] = lineAt s l from (lineAt_get s ⟨l, hl⟩).symm,
    vget_fin m.lines l hl, hrel.lines ⟨l, hl⟩]
  rfl

/-- Line `RUN`, cut vs machine. -/
theorem lineRun_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat)
    (hl : l < 4) : s.lines[l].run = (Machine.Util.vget m.lines l).run := by
  rw [show s.lines[l] = lineAt s l from (lineAt_get s ⟨l, hl⟩).symm,
    vget_fin m.lines l hl, hrel.lines ⟨l, hl⟩]
  rfl

/-- Line `PINA`, cut vs machine. -/
theorem linePinA_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) (hl : l < 4) :
    (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pina =
      (Machine.pinView m.sync m.dbg).pin
        (Machine.Util.vget (Machine.cfgView m.cfg).lines l).pina := by
  rw [pinView_pin_congr (gs_pinView_abs s m hrel)]
  rw [show Machine.Util.vget (Machine.cfgView m.cfg).lines l
    = Machine.Util.vget (Machine.cfgView s.cont.cfg).lines l from by rw [hrel.cfg],
    show Machine.Util.vget (Machine.cfgView s.cont.cfg).lines l
      = (Machine.cfgView s.cont.cfg).lines[l]! from rfl]

/-- Line `PINB`, cut vs machine. -/
theorem linePinB_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) (hl : l < 4) :
    (Machine.pinView (absChip s).sync (absChip s).dbg).pin
        ((Machine.cfgView s.cont.cfg).lines[l]!).pinb =
      (Machine.pinView m.sync m.dbg).pin
        (Machine.Util.vget (Machine.cfgView m.cfg).lines l).pinb := by
  rw [pinView_pin_congr (gs_pinView_abs s m hrel)]
  rw [show Machine.Util.vget (Machine.cfgView m.cfg).lines l
    = Machine.Util.vget (Machine.cfgView s.cont.cfg).lines l from by rw [hrel.cfg],
    show Machine.Util.vget (Machine.cfgView s.cont.cfg).lines l
      = (Machine.cfgView s.cont.cfg).lines[l]! from rfl]

/-! ## 7. The `Env` and the three leaf-record equalities -/

/-- The `Bridge.Glue.Env` of the guard/source leaves at line `l`. -/
def envG (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) : Bridge.Glue.Env :=
  { ms := m, cv := Machine.cfgView m.cfg, p := Machine.pinView m.sync m.dbg, l := l, imm := 0,
    hlvl := pinLvl_lt s m hrel }

/-- The same `Env` at the core's executing line and immediate field. -/
def envS (s : State) (m : Machine.State) (hrel : ChipRel s m) (c : Fin 2) : Bridge.Glue.Env :=
  { ms := m, cv := Machine.cfgView m.cfg, p := Machine.pinView m.sync m.dbg,
    l := (sIr s m c).xl.toNat,
    imm := Machine.insnField (sIr s m c).ir Machine.Tables.FIELD_imm,
    hlvl := pinLvl_lt s m hrel }

/-- The cut's `pins` leaf: `pinLvl` is the machine's `bv 13` level. -/
theorem pinLvl_bv (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    pinLvl s = Machine.Util.bv 13 (Machine.pinView m.sync m.dbg).lvl := by
  apply BitVec.eq_of_toNat_eq
  rw [pinLvl_toNat s m hrel, Machine.Util.bv, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (pinLvl_lt s m hrel)]

theorem sources_ext (a b : Glue.Sources)
    (h1 : a.fl = b.fl) (h2 : a.pins = b.pins) (h3 : a.accA = b.accA) (h4 : a.accR = b.accR)
    (h5 : a.shD = b.shD) (h6 : a.shO = b.shO) (h7 : a.cnV = b.cnV) (h8 : a.lfS = b.lfS)
    (h9 : a.pDat = b.pDat) (h10 : a.sBit = b.sBit) (h11 : a.sByte = b.sByte)
    (h12 : a.inB = b.inB) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := b
  simp_all

theorem guards_ext (a b : Glue.Guards)
    (h1 : a.fl = b.fl) (h2 : a.shDone = b.shDone) (h3 : a.shOut = b.shOut)
    (h4 : a.cntZ = b.cntZ) (h5 : a.accZ = b.accZ) (h6 : a.accC = b.accC)
    (h7 : a.accN = b.accN) (h8 : a.lfS = b.lfS) (h9 : a.inv = b.inv) (h10 : a.outv = b.outv)
    (h11 : a.pRdy = b.pRdy) (h12 : a.sEnd = b.sEnd) (h13 : a.sMark = b.sMark)
    (h14 : a.sByte = b.sByte) (h15 : a.sBit = b.sBit) (h16 : a.pins = b.pins)
    (h17 : a.lRun = b.lRun) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17⟩ := b
  simp_all

theorem lineGuards_ext (a b : Glue.LineGuards)
    (h1 : a.inn = b.inn) (h2 : a.sp = b.sp) (h3 : a.pinA = b.pinA) (h4 : a.pinB = b.pinB) :
    a = b := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  simp_all

/-- The cut's `sourcesOf` is `Bridge.Glue.sourcesOf` of the related machine. -/
theorem sourcesOf_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) :
    sourcesOf s = Bridge.Glue.sourcesOf (envG s m hrel l) := by
  have hfl : s.glue.fl = m.units.f := by
    obtain ⟨h, -, -, -, -, -, -, -, -, -⟩ := hrel.units
    exact h.symm
  have haccA : s.acc.a = m.units.a := by
    obtain ⟨-, -, h, -, -, -, -, -, -, -⟩ := hrel.units
    exact h.symm
  have hpDat : s.p0.dat = m.p0.d := hrel.p0.d.symm
  refine sources_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [sourcesOf, Bridge.Glue.sourcesOf, envG]
  · exact hfl
  · exact pinLvl_bv s m hrel
  · exact haccA
  · exact accR_eq s m hrel
  · exact shD_eq s m hrel
  · exact shO_eq s m hrel
  · exact cnV_eq s m hrel
  · exact lfS_eq s m hrel
  · exact hpDat
  · rw [b2_eq, streamBit_1_eq s m hrel, streamBit_0_eq s m hrel]
  · have h1 : Stream.byteOut false (streamAt s 1) (streamViewIn s 1) =
        Machine.Util.bv 8 (Machine.streamByte
          (Machine.Util.vget (Machine.cfgView m.cfg).streams 1)
          (Machine.Util.vget m.streams 1)) := by
      simpa using streamByte_eq s m hrel ⟨1, by decide⟩
    have h0 : Stream.byteOut true (streamAt s 0) (streamViewIn s 0) =
        Machine.Util.bv 8 (Machine.streamByte
          (Machine.Util.vget (Machine.cfgView m.cfg).streams 0)
          (Machine.Util.vget m.streams 0)) := by
      simpa using streamByte_eq s m hrel ⟨0, by decide⟩
    rw [h1, h0]
  · exact (ctrl_inb hrel).symm

/-- The same `sourcesOf` equality at the core's line and immediate (`envS`), which
`sourcesOf` ignores. -/
theorem sourcesOf_envS (s : State) (m : Machine.State) (hrel : ChipRel s m) (c : Fin 2) :
    sourcesOf s = Bridge.Glue.sourcesOf (envS s m hrel c) :=
  (sourcesOf_eq s m hrel (sIr s m c).xl.toNat).trans
    (show Bridge.Glue.sourcesOf (envG s m hrel (sIr s m c).xl.toNat) =
      Bridge.Glue.sourcesOf (envS s m hrel c) from rfl)

/-- The cut's `guardsOf` is `Bridge.Glue.guardsOf` of the related machine. -/
theorem guardsOf_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) :
    guardsOf s = Bridge.Glue.guardsOf (envG s m hrel l) := by
  obtain ⟨hfl, -, -, huz, huc, hun, -, -, -, -⟩ := hrel.units
  refine guards_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [guardsOf, Bridge.Glue.guardsOf, envG]
  · exact hfl.symm
  · rw [b2_eq, shDone_eq s m hrel ⟨1, by decide⟩, shDone_eq s m hrel ⟨0, by decide⟩]
  · rw [b2_eq, shOut_eq s m hrel ⟨1, by decide⟩, shOut_eq s m hrel ⟨0, by decide⟩]
  · rw [b3_eq, cntZ_eq s m hrel ⟨2, by decide⟩, cntZ_eq s m hrel ⟨1, by decide⟩,
      cntZ_eq s m hrel ⟨0, by decide⟩]
  · exact huz.symm
  · exact huc.symm
  · exact hun.symm
  · exact lfS_eq s m hrel
  · exact (gs_ctrl_inv hrel).symm
  · exact (ctrl_outv hrel).symm
  · exact (hrel.p0.rdy).symm
  · rw [b2_eq, streamEnd_eq s m hrel ⟨1, by decide⟩, streamEnd_eq s m hrel ⟨0, by decide⟩]
  · rw [b2_eq, streamMark_eq s m hrel ⟨1, by decide⟩, streamMark_eq s m hrel ⟨0, by decide⟩]
  · rw [b2_eq, streamAtByte_eq s m hrel ⟨1, by decide⟩, streamAtByte_eq s m hrel ⟨0, by decide⟩]
  · rw [b2_eq, streamBit_1_eq s m hrel, streamBit_0_eq s m hrel]
  · exact pinLvl_bv s m hrel
  · rw [b4_eq, lineRun_eq s m hrel 3 (by decide), lineRun_eq s m hrel 2 (by decide),
      lineRun_eq s m hrel 1 (by decide), lineRun_eq s m hrel 0 (by decide)]

/-- The cut's `lineGuardsOf` is `Bridge.Glue.lineGuardsOf` of the related machine. -/
theorem lineGuardsOf_eq (s : State) (m : Machine.State) (hrel : ChipRel s m) (l : Nat) :
    lineGuardsOf s = Bridge.Glue.lineGuardsOf (envG s m hrel l) := by
  refine lineGuards_ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [lineGuardsOf, Bridge.Glue.lineGuardsOf, envG]
  · rw [b4x2_eq, lineInSym_eq s m hrel 3 (by decide), lineInSym_eq s m hrel 2 (by decide),
      lineInSym_eq s m hrel 1 (by decide), lineInSym_eq s m hrel 0 (by decide)]
  · rw [b4_eq, lineSp_eq s m hrel 3 (by decide), lineSp_eq s m hrel 2 (by decide),
      lineSp_eq s m hrel 1 (by decide), lineSp_eq s m hrel 0 (by decide)]
  · rw [b4_eq, linePinA_eq s m hrel 3 (by decide), linePinA_eq s m hrel 2 (by decide),
      linePinA_eq s m hrel 1 (by decide), linePinA_eq s m hrel 0 (by decide)]
  · rw [b4_eq, linePinB_eq s m hrel 3 (by decide), linePinB_eq s m hrel 2 (by decide),
      linePinB_eq s m hrel 1 (by decide), linePinB_eq s m hrel 0 (by decide)]

/-! ## 8. The machine's table tails and small bit plumbing -/

/-- `guardOp` past the 62-entry table is `invalid`. -/
theorem guardOp_ge (k : Nat) (h : 62 ≤ k) : Machine.guardOp k = Machine.GuardOp.invalid := by
  rw [Bridge.Glue.guardOp_eq]
  have hlen : Machine.Tables.guardNames.size = 62 := by decide
  have hnone : Machine.Tables.guardNames[k]? = none := by
    rw [Array.getElem?_eq_none_iff]
    omega
  rw [hnone]
  rfl

/-- `srcOp` past the 39-entry table is `zero`. -/
theorem srcOp_ge (k : Nat) (h : 39 ≤ k) : Machine.srcOp k = Machine.SrcOp.zero := by
  rw [Bridge.Glue.srcOp_eq]
  have hlen : Machine.Tables.srcNames.size = 39 := by decide
  have hnone : Machine.Tables.srcNames[k]? = none := by
    rw [Array.getElem?_eq_none_iff]
    omega
  rw [hnone]
  rfl

/-- Bit `k ≥ w` of a `w`-bit vector is false. -/
theorem bitOf_ge' {w : Nat} (v : BitVec w) (k : Nat) (h : w ≤ k) : Core.bitOf v k = false := by
  rw [Bridge.Core.bitOf_eq_getLsbD, BitVec.getLsbD_of_ge v k h]

/-- `Core.slice` as bits of the value. -/
theorem bitOf_slice {w : Nat} (v : BitVec w) (lo n k : Nat) (hk : k < n) :
    Core.bitOf (Core.slice v lo n) k = Core.bitOf v (lo + k) := by
  rw [Bridge.Core.bitOf_eq_getLsbD, Bridge.Core.bitOf_eq_getLsbD, slice_getLsbD _ _ _ _ hk]

/-- `ofNat 2` round-trips below `4`. -/
theorem ofNat2_toNat (x : Nat) (hx : x < 4) : (BitVec.ofNat 2 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hx

/-- The `lineSlot` index is five bits per line. -/
theorem lineSlot_index (ln : BitVec 2) :
    BitVec.toNat (5 * BitVec.setWidth 32 ln) = 5 * ln.toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth,
    show ((5 : BitVec 32)).toNat = 5 from rfl,
    Nat.mod_eq_of_lt (by omega : ln.toNat < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by have := ln.isLt; omega)

/-- **The `g_line` byte step**: bit `j` of line `ln`'s bundle in the core's
`gLine` bus is bit `j` of the line's `lineGuard`. -/
theorem lineSlot_bit (s : State) (pin : Machine.PinIn) (c : Nat) (ln : Nat) (j : Nat)
    (hl : ln < 4) (hj : j < 5) :
    Core.bitOf (Core.lineSlot (coreIn s pin c).gLine (BitVec.ofNat 2 ln)) j =
      Glue.bitAt (Glue.lineGuard ln (lineGuardsOf s)) j := by
  unfold Core.lineSlot
  rw [lineSlot_index, ofNat2_toNat ln hl, bitOf_slice _ _ _ _ hj]
  show Core.bitOf (ChipCut.packBools 20 fun i =>
      Glue.bitAt (Glue.lineGuard (i / 5) (lineGuardsOf s)) (i % 5)) (5 * ln + j) = _
  rw [packBools_bit 20 _ (5 * ln + j) (by omega),
    show (5 * ln + j) / 5 = ln from by omega,
    show (5 * ln + j) % 5 = j from by omega]

/-! ## 9. The `srcVec` slot lemmas (`withSlot` and the `lowMask` tail) -/

/-- A shift-in's bit below the window is clear. -/
theorem getLsbD_shiftLeft_lt {m : Nat} (y : BitVec m) (n i : Nat) (hi : i < n) :
    (BitVec.shiftLeft y n).getLsbD i = false := by
  rw [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
  simp [hi]

/-- A shift-in's bit above the window repeats the source bit. -/
theorem getLsbD_shiftLeft_ge {m : Nat} (y : BitVec m) (n i : Nat) (hi : n ≤ i)
    (hy : y.getLsbD (i - n) = false) : (BitVec.shiftLeft y n).getLsbD i = false := by
  rw [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
  by_cases hm : i < m
  · simp [hm, hy]
  · simp [hm]

/-- A `lowMask` bit below the mask window is set. -/
theorem lowMask_getLsbD_lt {w : Nat} (n t : Nat) (ht : t < n) (hw : t < w) :
    (Core.lowMask w n).getLsbD t = true := by
  unfold Core.lowMask
  rw [BitVec.getLsbD_not, BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes]
  simp [ht, hw]

/-- A `lowMask` bit at or above the mask window is clear. -/
theorem lowMask_getLsbD_ge {w : Nat} (n t : Nat) (ht : n ≤ t) :
    (Core.lowMask w n).getLsbD t = false := by
  unfold Core.lowMask
  rw [BitVec.getLsbD_not, BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes]
  by_cases hw : t < w
  · simp [ht, hw, show t - n < w from by omega]
  · simp [hw]

/-- Bits 8 and above of the `withSlot` mask value are clear. -/
theorem maskVal_false (t : Nat) (ht : 8 ≤ t) :
    (BitVec.setWidth 512 (BitVec.allOnes 8) : BitVec 512).getLsbD t = false := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  have h8 : ¬ (t < 8) := by omega
  by_cases h5 : t < 512 <;> simp [h5, h8]

/-- Bits below 8 of the `withSlot` mask value are set. -/
theorem maskVal_true (b : Nat) (hb : b < 8) :
    (BitVec.setWidth 512 (BitVec.allOnes 8) : BitVec 512).getLsbD b = true := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp [hb, show b < 512 from by omega]

/-- A byte value zero-extended to 512 bits reads its own bits below 8. -/
theorem setWidth8_getLsbD (x : BitVec 8) (b : Nat) (hb : b < 8) :
    (BitVec.setWidth 512 x).getLsbD b = x.getLsbD b := by
  rw [BitVec.getLsbD_setWidth]
  by_cases h5 : b < 512
  · simp [h5]
  · omega

/-- Bits 8 and above of a byte zero-extended to 512 bits are clear. -/
theorem setWidth8_getLsbD_ge (x : BitVec 8) (t : Nat) (ht : 8 ≤ t) :
    (BitVec.setWidth 512 x).getLsbD t = false := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge x t ht]
  simp

/-- A `withSlot` write is invisible outside its own slot. -/
theorem withSlot_slice_ne (v : BitVec 512) (j k : Nat) (x : BitVec 8)
    (hjk : k ≠ j) (hk : k < 64) :
    Core.slice (Core.withSlot v j x) (8 * k) 8 = Core.slice v (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [slice_getLsbD _ _ _ _ hb, slice_getLsbD _ _ _ _ hb]
  show (Core.withSlot v j x).getLsbD (8 * k + b) = v.getLsbD (8 * k + b)
  have hkj : k < j ∨ j < k := by omega
  have hM : (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.allOnes 8)) (8 * j)).getLsbD
      (8 * k + b) = false := by
    rcases hkj with h | h
    · exact getLsbD_shiftLeft_lt _ _ _ (by omega)
    · exact getLsbD_shiftLeft_ge _ _ _ (by omega) (maskVal_false _ (by omega))
  have hx : (BitVec.shiftLeft (BitVec.setWidth 512 x) (8 * j)).getLsbD (8 * k + b) = false := by
    rcases hkj with h | h
    · exact getLsbD_shiftLeft_lt _ _ _ (by omega)
    · have hge : 8 ≤ 8 * k + b - 8 * j := by
        have h1 : 8 * j + 8 ≤ 8 * k + b := by omega
        omega
      exact getLsbD_shiftLeft_ge _ _ _ (by omega) (setWidth8_getLsbD_ge x _ hge)
  unfold Core.withSlot
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hM, hx]
  have h5 : 8 * k + b < 512 := by omega
  simp [h5]

/-- A `withSlot` write is read back at its own slot. -/
theorem withSlot_slice_same (v : BitVec 512) (j : Nat) (x : BitVec 8) (hj : j < 64) :
    Core.slice (Core.withSlot v j x) (8 * j) 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [slice_getLsbD _ _ _ _ hb]
  show (Core.withSlot v j x).getLsbD (8 * j + b) = x.getLsbD b
  have hM : (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.allOnes 8)) (8 * j)).getLsbD
      (8 * j + b) = true := by
    rw [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
      show 8 * j + b - 8 * j = b from by omega, maskVal_true b hb]
    simp [show 8 * j + b < 512 from by omega, show ¬ (8 * j + b < 8 * j) from by omega]
  have hx : (BitVec.shiftLeft (BitVec.setWidth 512 x) (8 * j)).getLsbD (8 * j + b) =
      x.getLsbD b := by
    rw [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
      show 8 * j + b - 8 * j = b from by omega, setWidth8_getLsbD x b hb]
    simp [show 8 * j + b < 512 from by omega, show ¬ (8 * j + b < 8 * j) from by omega]
  unfold Core.withSlot
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hM, hx]
  have h5 : 8 * j + b < 512 := by omega
  simp [h5]

/-- The `lowMask 512 (8 * 39)` tail leaves slots below 39 untouched. -/
theorem mask_slice_lt (v : BitVec 512) (k : Nat) (hk : k < 39) :
    Core.slice (v &&& Core.lowMask 512 (8 * 39)) (8 * k) 8 = Core.slice v (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [slice_getLsbD _ _ _ _ hb, slice_getLsbD _ _ _ _ hb, BitVec.getLsbD_and,
    lowMask_getLsbD_lt (w := 512) (n := 8 * 39) (t := 8 * k + b) (by omega) (by omega)]
  simp

/-- The `lowMask 512 (8 * 39)` tail clears slots 39 and above. -/
theorem mask_slice_ge (v : BitVec 512) (k : Nat) (hk : 39 ≤ k) :
    Core.slice (v &&& Core.lowMask 512 (8 * 39)) (8 * k) 8 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [slice_getLsbD _ _ _ _ hb, BitVec.getLsbD_and,
    lowMask_getLsbD_ge (w := 512) (n := 8 * 39) (t := 8 * k + b) (by omega)]
  simp

/-- A non-substituted slot of `srcVec` is the `srcs` bus slot. -/
theorem srcVec_slice_ne (x : Core.State) (i : Core.Input) (k : Nat) (hk : k < 39)
    (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    Core.slice (Core.srcVec x i) (8 * k) 8 = Core.slice i.srcs (8 * k) 8 := by
  unfold Core.srcVec
  rw [mask_slice_lt _ k hk,
    withSlot_slice_ne _ 3 k _ h3 (by omega), withSlot_slice_ne _ 2 k _ h2 (by omega),
    withSlot_slice_ne _ 1 k _ h1 (by omega), withSlot_slice_ne _ 0 k _ h0 (by omega)]

/-- `srcVec` slot 0 is the core-local `ZERO`. -/
theorem srcVec_slice_0 (x : Core.State) (i : Core.Input) :
    Core.slice (Core.srcVec x i) (8 * 0) 8 = 0 := by
  unfold Core.srcVec
  rw [mask_slice_lt _ 0 (by omega),
    withSlot_slice_ne _ 3 0 _ (by decide) (by omega),
    withSlot_slice_ne _ 2 0 _ (by decide) (by omega),
    withSlot_slice_ne _ 1 0 _ (by decide) (by omega),
    withSlot_slice_same _ 0 _ (by omega)]

/-- `srcVec` slot 1 is the core-local `IMM`. -/
theorem srcVec_slice_1 (x : Core.State) (i : Core.Input) :
    Core.slice (Core.srcVec x i) (8 * 1) 8 = Core.i_imm x := by
  unfold Core.srcVec
  rw [mask_slice_lt _ 1 (by omega),
    withSlot_slice_ne _ 3 1 _ (by decide) (by omega),
    withSlot_slice_ne _ 2 1 _ (by decide) (by omega),
    withSlot_slice_same _ 1 _ (by omega)]

/-- `srcVec` slot 2 is the core-local `L.IN`. -/
theorem srcVec_slice_2 (x : Core.State) (i : Core.Input) :
    Core.slice (Core.srcVec x i) (8 * 2) 8 =
      BitVec.setWidth 8 (Core.slice i.lIn (BitVec.toNat (2 * BitVec.setWidth 32 x.xl)) 2) := by
  unfold Core.srcVec
  rw [mask_slice_lt _ 2 (by omega),
    withSlot_slice_ne _ 3 2 _ (by decide) (by omega),
    withSlot_slice_same _ 2 _ (by omega)]

/-- `srcVec` slot 3 is the core-local `L.CAP`. -/
theorem srcVec_slice_3 (x : Core.State) (i : Core.Input) :
    Core.slice (Core.srcVec x i) (8 * 3) 8 =
      BitVec.setWidth 8 (Core.slice i.lCap (BitVec.toNat (5 * BitVec.setWidth 32 x.xl)) 5) := by
  unfold Core.srcVec
  rw [mask_slice_lt _ 3 (by omega), withSlot_slice_same _ 3 _ (by omega)]

/-- `srcVec` slots 39 and above are cleared by the mask. -/
theorem srcVec_slice_ge (x : Core.State) (i : Core.Input) (k : Nat) (hk : 39 ≤ k) :
    Core.slice (Core.srcVec x i) (8 * k) 8 = 0 := by
  unfold Core.srcVec
  rw [mask_slice_ge _ k hk]

/-- `Core.slice`'s `Nat` value. -/
theorem slice_toNat' {w : Nat} (v : BitVec w) (lo n : Nat) :
    (Core.slice v lo n).toNat = Machine.Util.nbits v.toNat lo n := by
  simp [Core.slice, Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

/-- The core's `IMM` field is the machine's `FIELD_imm`. -/
theorem i_imm_toNat (x : Core.State) :
    (Core.i_imm x).toNat = Machine.insnField x.ir Machine.Tables.FIELD_imm := by
  show (Core.slice x.ir 3 8).toNat = Machine.Util.nbits x.ir.toNat 3 8
  rw [slice_toNat']

/-! ## 10. The two `CoreInputBus` fields -/

/-- **`CoreInputBus.guards`**: the cut's effective guard vector is the machine's
`guardVal`, slot by slot, for every line and every guard index. -/
theorem coreInputBus_guards (hG : Bridge.Glue.GuardTable) (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (c : Fin 2) (hrel : ChipRel s m) (hinv : Inv s)
    (hact : runRst s pin = true) :
    ∀ (ln : Nat), ln < 4 → ∀ k : Nat,
      Core.bitOf (Core.guardVec (coreIn s pin c.val).guards (coreIn s pin c.val).gLine
        (BitVec.ofNat 2 ln)) k =
      Machine.guardVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) ln
        (Machine.guardOp k) := by
  intro ln hl k
  by_cases hk : k < 64
  · rw [guardVec_bit _ _ _ k hk]
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos rfl,
        show Machine.guardOp 0 = Machine.GuardOp.true_ from by rw [hG.eq 0]; rfl]
      rfl
    · rw [if_neg h0]
      by_cases h27 : 27 ≤ k ∧ k ≤ 31
      · rw [if_pos h27, lineSlot_bit s pin c.val ln (k - 27) hl (by omega),
          lineGuardsOf_eq s m hrel ln]
        have hbridge := Bridge.Glue.lineGuard_bridge hG (envG s m hrel ln) hl (k - 27) (by omega)
        have hk : Machine.guardOp k = Machine.guardOp (27 + (k - 27)) := by
          congr 1
          omega
        rw [hk]
        simpa [envG, Bridge.Glue.guardV] using hbridge.symm
      · rw [if_neg h27]
        by_cases h62 : k < 62
        · rw [if_pos h62, guards_bit s pin c.val k hk, guardsOf_eq s m hrel ln]
          exact (guardV_global hG (envG s m hrel ln) k hk
            (by omega) (by omega) (by omega) (by omega) (by omega)).symm
        · rw [if_neg h62,
            show Machine.guardOp k = Machine.GuardOp.invalid from guardOp_ge k (by omega)]
          rfl
  · rw [show Core.bitOf (Core.guardVec (coreIn s pin c.val).guards
        (coreIn s pin c.val).gLine (BitVec.ofNat 2 ln)) k = false from
      bitOf_ge' _ k (by omega),
      show Machine.guardOp k = Machine.GuardOp.invalid from guardOp_ge k (by omega)]
    rfl

/-- `setWidth 8` of a two-bit value keeps its `Nat` value. -/
theorem setWidth8_toNat2 (w : BitVec 2) : (BitVec.setWidth 8 w).toNat = w.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := w.isLt; omega)]

/-- `setWidth 8` of a five-bit value keeps its `Nat` value. -/
theorem setWidth8_toNat5 (w : BitVec 5) : (BitVec.setWidth 8 w).toNat = w.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := w.isLt; omega)]

/-- The `L.IN` slot index is two bits per line. -/
theorem two_xl_index (zl : BitVec 2) :
    BitVec.toNat (2 * BitVec.setWidth 32 zl) = 2 * zl.toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth,
    show ((2 : BitVec 32)).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega : zl.toNat < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by have := zl.isLt; omega)

/-- The core's `lIn` bus at the executing line is the machine's `IN`. -/
theorem lIn_slot (s : State) (pin : Machine.PinIn) (m : Machine.State) (hrel : ChipRel s m)
    (c : Nat) (zl : BitVec 2) :
    (Core.slice (coreIn s pin c).lIn (BitVec.toNat (2 * BitVec.setWidth 32 zl)) 2).toNat =
      Machine.inSym (Machine.Util.vget (Machine.cfgView m.cfg).lines zl.toNat)
        (Machine.Util.vget m.lines zl.toNat) := by
  have hl : zl.toNat < 4 := by have := zl.isLt; omega
  show (Core.slice (coreIn s pin c).lIn (BitVec.toNat (2 * BitVec.setWidth 32 zl)) 2).toNat = _
  rw [two_xl_index]
  rw [show Core.slice (coreIn s pin c).lIn (2 * zl.toNat) 2 =
      Line.inSym (lineAt s zl.toNat) (lineStaticIn s zl.toNat) from by
    rw [show (coreIn s pin c).lIn =
        ChipCut.packNs 2 4 (fun l => Line.inSym (lineAt s l) (lineStaticIn s l)) from rfl]
    exact packNs_slice 2 4 _ zl.toNat hl]
  rw [lineAt_get s ⟨zl.toNat, hl⟩]
  exact lineInSym_eq s m hrel zl.toNat hl

/-- The core's `lCap` bus at the executing line is the machine's `L.CAP`. -/
theorem lCap_slot (s : State) (pin : Machine.PinIn) (m : Machine.State) (hrel : ChipRel s m)
    (c : Nat) (zl : BitVec 2) :
    (BitVec.setWidth 8 (Core.slice (coreIn s pin c).lCap
        (BitVec.toNat (5 * BitVec.setWidth 32 zl)) 5)).toNat =
      Machine.Util.b2n (Machine.Util.vget m.lines zl.toNat).rem * 16 +
        (Machine.Util.vget m.lines zl.toNat).sn.toNat := by
  have hl : zl.toNat < 4 := by have := zl.isLt; omega
  rw [setWidth8_toNat5, lineSlot_index zl]
  rw [show Core.slice (coreIn s pin c).lCap (5 * zl.toNat) 5 =
      Line.cap (lineAt s zl.toNat) from by
    rw [show (coreIn s pin c).lCap = ChipCut.packNs 5 4 (fun l => Line.cap (lineAt s l)) from rfl]
    exact packNs_slice 5 4 _ zl.toNat hl]
  rw [Bridge.Line.cap_toNat, ← hrel.lines ⟨zl.toNat, hl⟩, vget_fin m.lines zl.toNat hl]

/-- **`CoreInputBus.srcs`**: each source slot of the core's substituted source
vector is the machine's `srcVal` of that port. -/
theorem coreInputBus_srcs (hS : Bridge.Glue.SrcTable) (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (c : Fin 2) (hrel : ChipRel s m) (hinv : Inv s)
    (hact : runRst s pin = true) :
    ∀ k : Nat,
      (Core.slice (Core.srcVec (sIr s m c) (coreIn s pin c.val)) (8 * k) 8).toNat =
      Machine.srcVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (sIr s m c).xl.toNat (Machine.insnField (sIr s m c).ir Machine.Tables.FIELD_imm)
        (Machine.srcOp k) := by
  intro k
  generalize hx : sIr s m c = x
  by_cases hk39 : k < 39
  · by_cases h0 : k = 0
    · subst h0
      rw [srcVec_slice_0]
      rw [show Machine.srcOp 0 = Machine.SrcOp.zero from by rw [hS.eq 0]; rfl]
      rfl
    · by_cases h1 : k = 1
      · subst h1
        rw [srcVec_slice_1, i_imm_toNat,
          show Machine.srcOp 1 = Machine.SrcOp.imm from by rw [hS.eq 1]; rfl]
        simp [Machine.srcVal, Nat.mod_eq_of_lt (by
          show Machine.insnField x.ir Machine.Tables.FIELD_imm < 256
          rw [← i_imm_toNat x]
          exact (Core.i_imm x).isLt)]
      · by_cases h2 : k = 2
        · subst h2
          rw [srcVec_slice_2, setWidth8_toNat2, lIn_slot s pin m hrel c.val x.xl,
            show Machine.srcOp 2 = Machine.SrcOp.lIn from by rw [hS.eq 2]; rfl]
          rfl
        · by_cases h3 : k = 3
          · subst h3
            rw [srcVec_slice_3, lCap_slot s pin m hrel c.val x.xl,
              show Machine.srcOp 3 = Machine.SrcOp.lCap from by rw [hS.eq 3]; rfl]
            rfl
          · rw [srcVec_slice_ne x (coreIn s pin c.val) k hk39 h0 h1 h2 h3,
              srcs_byte s pin c.val k (by omega), sourcesOf_envS s m hrel c]
            simpa [hx, Bridge.Glue.srcV, envS] using
              (srcV_global hS (envS s m hrel c) k (by omega) h1 h2 h3).symm
  · rw [srcVec_slice_ge x (coreIn s pin c.val) k (by omega),
      show Machine.srcOp k = Machine.SrcOp.zero from srcOp_ge k (by omega)]
    rfl

/-- **The `CoreInputBus` witness.** -/
theorem coreInputBus (hG : Bridge.Glue.GuardTable) (hS : Bridge.Glue.SrcTable)
    (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    CoreInputBus s m pin c (sIr s m c) :=
  { guards := coreInputBus_guards hG s m pin c hrel hinv hact
    srcs := coreInputBus_srcs hS s m pin c hrel hinv hact }

/-- **`Premises.cores` with no `CoreInputBus` hypothesis**: the one-line adapter
from `coreInputBus` to `premise_cores`. -/
theorem premise_cores_of (hG : Bridge.Glue.GuardTable) (hS : Bridge.Glue.SrcTable)
    (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62) :
    ∀ c : Fin 2, CoreRegsRel ((activeStep s pin).cores[c]) ((Machine.step m pin).cores[c]) :=
  premise_cores s m pin hrel hinv hact hJGTab
    (fun c => coreInputBus hG hS s m pin c hrel hinv hact)


