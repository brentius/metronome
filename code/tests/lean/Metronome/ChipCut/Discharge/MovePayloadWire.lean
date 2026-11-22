/-
# ChipCut wiring: the payload rows and the two control-sticky events

This module closes the five remaining `OpenWiring` fields that reduce to the move
fabric, the pointer move and the configuration-write queue:

| `OpenWiring` field | theorem |
|---|---|
| `unitFlagPQ` | `unitFlagPQ` (the `FLAGS` payload row) |
| `p0Move` | `p0Move` |
| `cwMove` | `cwMove` |
| `ctrlMemhaz` | `ctrlMemhaz` |
| `ctrlCwovr` | `ctrlCwovr` |

The three payload instances are the `hPQ` shape `pickScan_mWs` needs
(`MoveFabric.unitInputs_flag_low4`, `MoveFabricKeyed.p0_open_move` and the new
`cwMove`).  Two of them (`FLAGS`, `P0`) are derived from
`MoveFabric.DstPayloadTable`'s group membership; the third (`CW`) needs the
group's *code set*, which the payload table does not carry (there is no `Fam.cw`,
and the payload table is not this module's to edit).  All three are derived from
one new global table hypothesis, `DstFlagP0CwTable`, in the
`DstKindTable`/`DstPayloadTable` style: the destination code of each of the nine
fixed ports.  `decode_check_flagp0cw.lean` in the evidence directory checks every
row for all 64 codes by compiled evaluation.

`ctrlMemhaz` is the machine's `pdHaz || p0haz` against the cut's
`Moves.memhazEvent`: the `P0.D` read scan (`MoveBus.src` + the source table, the
`hostInRead` argument of `MoveFabricKeyed`) and the pointer hazard
(`Bridge.Mem`'s `haz`, `Mem.haz`).  `ctrlCwovr` is the machine's `cwNext` overrun
(`CW.D` dropped while the queue is busy) against the cut's queue drop event
(`CoreQueue.writeData && !CoreQueue.accept`), through the machine's internal
drain condition and `Glue.cwovr_step`.

No `sorry`, no `native_decide`, no `admit`.
-/
import Metronome.ChipCut.Discharge.MoveFabric
import Metronome.ChipCut.Discharge.MoveFabricKeyed
import Metronome.ChipCut.Discharge.Glue
import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.MovePayloadWire

open Metronome
open Metronome.ChipCut.Discharge
open Metronome.ChipCut.Discharge.MoveFabric

/-! ## 1. The fixed-port code table

`Machine.dstOp` cannot be evaluated in the kernel on the generated table's parsed
names (`String.splitOnAux` is irreducible), so the `FLAGS`/`P0`/`CW` codes are one
more global table hypothesis of the `DstKindTable` class.  `FLAGS.SET`/`CLR` and
the four `P0` ports are also covered by `DstPayloadTable`'s `famIn`; the `CW`
group is not a payload family, which is why the group's code set is a row here. -/

/-- The destination codes of the `FLAGS`, `P0` and `CW` ports. -/
structure DstFlagP0CwTable : Prop where
  /-- `FLAGS.SET` is code 5 -/
  fset : ∀ d, d < 64 → Machine.dstOp d = .fset → d = 5
  /-- `FLAGS.CLR` is code 6 -/
  fclr : ∀ d, d < 64 → Machine.dstOp d = .fclr → d = 6
  /-- `P0.AL` is code 43 -/
  pAl : ∀ d, d < 64 → Machine.dstOp d = .pAl → d = 43
  /-- `P0.AH` is code 44 -/
  pAh : ∀ d, d < 64 → Machine.dstOp d = .pAh → d = 44
  /-- `P0.W` is code 45 -/
  pW : ∀ d, d < 64 → Machine.dstOp d = .pW → d = 45
  /-- `P0.R` is code 46 -/
  pR : ∀ d, d < 64 → Machine.dstOp d = .pR → d = 46
  /-- `CW.AL` is code 58 -/
  cwAl : ∀ d, d < 64 → Machine.dstOp d = .cwAl → d = 58
  /-- `CW.AH` is code 59 -/
  cwAh : ∀ d, d < 64 → Machine.dstOp d = .cwAh → d = 59
  /-- `CW.D` is code 60 -/
  cwD : ∀ d, d < 64 → Machine.dstOp d = .cwD → d = 60
  /-- the `CW` write group holds exactly the three `CW` ports (its id is the
  group of code 58) -/
  cwGroup : ∀ d, d < 64 →
    (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 58) = true →
    Machine.dstOp d = .cwAl ∨ Machine.dstOp d = .cwAh ∨ Machine.dstOp d = .cwD

/-! ## 2. The `FLAGS` payload row: `OpenWiring.unitFlagPQ`

`UnitInputs.flag` (`MoveFabric.unitInputs_flag_low4`) needs the `FLAGS` group's
`hPQ`: `FLAGS.SET` → flag `true`, `FLAGS.CLR` → `false`, and the cut's payload is
the picked word's code test against `flagsSetDst` (code 5). -/

/-- **`OpenWiring.unitFlagPQ`**, the `FLAGS` payload row. -/
theorem unitFlagPQ (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    ∀ d, d < 64 →
      (match Machine.dstOp d with | .fset => some true | .fclr => some false | _ => none) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 5) then
        some (BitVec.ofNat 6 d == Metronome.Glue.flagsSetDst) else none) := by
  intro d hd
  have hpay := hT.payload Fam.flags d hd
  rw [show famG Fam.flags = Moves.dgTable 5 from rfl] at hpay
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 5) = true
  · rw [if_pos hg]
    have hfam : famIn Fam.flags (Machine.dstOp d) = true := by rw [← hpay, hg]
    cases h : Machine.dstOp d with
    | fset => have h5 : d = 5 := hF.fset d hd h; subst h5; decide
    | fclr => have h6 : d = 6 := hF.fclr d hd h; subst h6; decide
    | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
  · rw [if_neg (by simpa using hg)]
    cases h : Machine.dstOp d with
    | fset => have h5 : d = 5 := hF.fset d hd h; subst h5; exact absurd hg (by decide)
    | fclr => have h6 : d = 6 := hF.fclr d hd h; subst h6; exact absurd hg (by decide)
    | _ => rfl

/-! ## 3. The `P0` payload row and `OpenWiring.p0Move` -/

/-- The machine's pointer-move decode as the payload of the `P0` write group. -/
def p0MoveOf : Machine.DstOp → Option Nat
  | .pAl => some 0
  | .pAh => some 1
  | .pW => some 2
  | .pR => some 3
  | _ => none

/-- The `P0` payload row: the machine's four pointer decodes are the cut's code
test of the `P0` write group, and the port code is `Strobes.p0Sel`. -/
theorem hPQ_p0 (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    ∀ d, d < 64 → p0MoveOf (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 43) then
        some ((Strobes.p0Sel (BitVec.ofNat 6 d)).toNat) else none) := by
  intro d hd
  have hpay := hT.payload Fam.p0 d hd
  rw [show famG Fam.p0 = Moves.dgTable 43 from rfl] at hpay
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 43) = true
  · rw [if_pos hg]
    have hfam : famIn Fam.p0 (Machine.dstOp d) = true := by rw [← hpay, hg]
    cases h : Machine.dstOp d with
    | pAl => have h43 : d = 43 := hF.pAl d hd h; subst h43; decide
    | pAh => have h44 : d = 44 := hF.pAh d hd h; subst h44; decide
    | pW => have h45 : d = 45 := hF.pW d hd h; subst h45; decide
    | pR => have h46 : d = 46 := hF.pR d hd h; subst h46; decide
    | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
  · rw [if_neg (by simpa using hg)]
    cases h : Machine.dstOp d with
    | pAl => have h43 : d = 43 := hF.pAl d hd h; subst h43; exact absurd hg (by decide)
    | pAh => have h44 : d = 44 := hF.pAh d hd h; subst h44; exact absurd hg (by decide)
    | pW => have h45 : d = 45 := hF.pW d hd h; subst h45; exact absurd hg (by decide)
    | pR => have h46 : d = 46 := hF.pR d hd h; subst h46; exact absurd hg (by decide)
    | _ => rfl

/-- **The pointer move scan, `isSome` form**: the machine's `P0` winner exists
exactly when the cut's pointer-move strobe is up.  This is the `p0haz` half of
`ctrlMemhaz`, and it is one `pickScan_mWs` instance (`hPQ_p0`). -/
theorem mhcP0Move_isSome (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    (mhcP0Move m pin).isSome = (memIn s pin).pWe := by
  have hGb : (Moves.dgTable 43 == Moves.dgNone) = false := by decide
  have hG0 : (Moves.dgTable 43 == Moves.dgLSym) = false := by decide
  have hG1 : (Moves.dgTable 43 == Moves.dgTStop) = false := by decide
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    p0MoveOf (fun dst => some ((Strobes.p0Sel dst).toNat)) (fun v => v) (Moves.dgTable 43)
    hGb hG0 hG1 (hPQ_p0 hT hF)
  have h1 : (mhcP0Move m pin).isSome =
      ((mhcWs m pin).findSome? (fun mv => (p0MoveOf (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v)))).isSome := by
    rw [show mhcP0Move m pin = (mhcWs m pin).findSome? (fun mm =>
        match Machine.dstOp mm.dst with
        | .pAl => some ⟨0, mm.v⟩ | .pAh => some ⟨1, mm.v⟩
        | .pW => some ⟨2, mm.v⟩ | .pR => some ⟨3, mm.v⟩ | _ => none) from rfl]
    have hfun : (fun mm : Machine.Move => match Machine.dstOp mm.dst with
        | .pAl => some ⟨0, mm.v⟩ | .pAh => some ⟨1, mm.v⟩
        | .pW => some ⟨2, mm.v⟩ | .pR => some ⟨3, mm.v⟩ | _ => none) =
        (fun mv => (p0MoveOf (Machine.dstOp mv.dst)).map
          (fun a => (⟨a, mv.v⟩ : Machine.P0Move))) :=
      funext (fun x => by cases Machine.dstOp x.dst <;> rfl)
    rw [hfun]
    exact MoveFabricKeyed.findSome?_isSome_congr' _ _ _ (fun mv => by
      rw [Option.isSome_map, Option.isSome_map])
  rw [h1, MoveFabricKeyed.mhcWs_eq_mWs, hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 43))
      (mvDst s pin) (mvDat s pin) = gw s pin 43 from rfl]
  rw [show (memIn s pin).pWe = (gw s pin 43).we from rfl]
  cases (gw s pin 43).we <;> rfl

/-- **`OpenWiring.p0Move`**: the machine's `P0` winner is the cut's pointer port
of write group 17 (codes 43..46).  This is `MoveFabricKeyed.p0_open_move` with the
payload instance supplied by the table (`hPQ_p0`). -/
theorem p0Move (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hF : DstFlagP0CwTable) :
    mhcP0Move m pin = Bridge.Mem.mvOf (memIn s pin) :=
  MoveFabricKeyed.p0_open_move s m pin hrel hinv hJGTab hbus hgrp hkind (hPQ_p0 hT hF)

/-! ## 4. The `CW` port row and `OpenWiring.cwMove`

The cut reads the `CW` write group through one packed word (`Wire.cwWord =
gw s pin 58`): `CoreQueue.writeData`/`writeLow`/`writeHigh` are the word's `we`
with the destination code test `== 60/58/59`, and the data byte is the word's
data.  The machine's `mhcCwMove` scans the winners for the three `CW` decodes.
One `pickScan_mWs` instance with `Q = cwSel` (the port of the word's code, in the
cut's `CW.D > CW.AL > CW.AH` priority) identifies them. -/

/-- The machine's configuration-write decode as the payload of the `CW` group. -/
def cwMoveOf : Machine.DstOp → Option Nat
  | .cwAl => some 0
  | .cwAh => some 1
  | .cwD => some 2
  | _ => none

/-- The cut's `CW` port of a picked destination code (its priority order). -/
def cwSel (dst : BitVec 6) : Option Nat :=
  if dst == (60 : BitVec 6) then some 2
  else if dst == (58 : BitVec 6) then some 0
  else if dst == (59 : BitVec 6) then some 1 else none

/-- The `CW` payload row. -/
theorem hPQ_cw (hF : DstFlagP0CwTable) :
    ∀ d, d < 64 → cwMoveOf (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 58) then
        cwSel (BitVec.ofNat 6 d) else none) := by
  intro d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 58) = true
  · rw [if_pos hg]
    rcases hF.cwGroup d hd hg with h | h | h
    · have h58 : d = 58 := hF.cwAl d hd h
      subst h58
      rw [h]
      decide
    · have h59 : d = 59 := hF.cwAh d hd h
      subst h59
      rw [h]
      decide
    · have h60 : d = 60 := hF.cwD d hd h
      subst h60
      rw [h]
      decide
  · rw [if_neg (by simpa using hg)]
    cases h : Machine.dstOp d with
    | cwAl => have h58 : d = 58 := hF.cwAl d hd h; subst h58; exact absurd hg (by decide)
    | cwAh => have h59 : d = 59 := hF.cwAh d hd h; subst h59; exact absurd hg (by decide)
    | cwD => have h60 : d = 60 := hF.cwD d hd h; subst h60; exact absurd hg (by decide)
    | _ => rfl

/-- The cut's packed `CW` word: its code, data and move-hit bits. -/
theorem cwWord_code (s : State) (pin : Machine.PinIn) :
    CoreQueue.cwCode (cwWord s pin) = (gw s pin 58).dst := by
  simp only [cwWord, CoreQueue.cwCode, CoreCtl.GroupWord.pack]
  exact slice_makeWord_8_6 _ _ _

theorem cwWord_data (s : State) (pin : Machine.PinIn) :
    CoreQueue.cwData (cwWord s pin) = (gw s pin 58).data := by
  simp only [cwWord, CoreQueue.cwData, CoreCtl.GroupWord.pack]
  exact slice_makeWord_0_8 _ _ _

theorem cwWord_we (s : State) (pin : Machine.PinIn) :
    CoreQueue.bitAt (cwWord s pin) 14 = (gw s pin 58).we := by
  simp only [cwWord, CoreQueue.bitAt, CoreCtl.GroupWord.pack]
  exact bitAt_makeWord_14 _ _ _

/-- **`OpenWiring.cwMove`**: the machine's `CW` winner is the cut's configuration
queue word (`cwWord = gw 58`). -/
theorem cwMove (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hF : DstFlagP0CwTable) :
    mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin) := by
  have hGb : (Moves.dgTable 58 == Moves.dgNone) = false := by decide
  have hG0 : (Moves.dgTable 58 == Moves.dgLSym) = false := by decide
  have hG1 : (Moves.dgTable 58 == Moves.dgTStop) = false := by decide
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    cwMoveOf cwSel (fun v => v) (Moves.dgTable 58) hGb hG0 hG1 (hPQ_cw hF)
  have h1 : mhcCwMove m pin =
      (((mhcWs m pin).findSome? (fun mv => (cwMoveOf (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v)))).map (fun p : Nat × Nat => (⟨p.1, p.2⟩ : Machine.CwMove))) := by
    rw [show mhcCwMove m pin = (mhcWs m pin).findSome? (fun mm =>
        match Machine.dstOp mm.dst with
        | .cwAl => some ⟨0, mm.v⟩ | .cwAh => some ⟨1, mm.v⟩
        | .cwD => some ⟨2, mm.v⟩ | _ => none) from rfl]
    have hfun : (fun mm : Machine.Move => match Machine.dstOp mm.dst with
        | .cwAl => some ⟨0, mm.v⟩ | .cwAh => some ⟨1, mm.v⟩
        | .cwD => some ⟨2, mm.v⟩ | _ => none) =
        (fun mv => (cwMoveOf (Machine.dstOp mv.dst)).map
          (fun a => (⟨a, mv.v⟩ : Machine.CwMove))) :=
      funext (fun x => by cases Machine.dstOp x.dst <;> rfl)
    rw [hfun]
    exact (MoveFabricKeyed.findSome?_map_pair (mhcWs m pin)
      (fun mv => cwMoveOf (Machine.dstOp mv.dst)) (fun mv => mv.v)
      (fun a b => (⟨a, b⟩ : Machine.CwMove))).symm
  rw [h1, MoveFabricKeyed.mhcWs_eq_mWs, hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 58))
      (mvDst s pin) (mvDat s pin) = gw s pin 58 from rfl]
  have hcut : Bridge.CfgWrite.mvOf (cqIn s pin) =
      (if (gw s pin 58).we && ((gw s pin 58).dst == (60 : BitVec 6)) then
        some (⟨2, (gw s pin 58).data.toNat⟩ : Machine.CwMove)
      else if (gw s pin 58).we && ((gw s pin 58).dst == (58 : BitVec 6)) then
        some (⟨0, (gw s pin 58).data.toNat⟩ : Machine.CwMove)
      else if (gw s pin 58).we && ((gw s pin 58).dst == (59 : BitVec 6)) then
        some (⟨1, (gw s pin 58).data.toNat⟩ : Machine.CwMove)
      else none) := by
    simp only [Bridge.CfgWrite.mvOf, cqIn, CoreQueue.writeData, CoreQueue.writeLow,
      CoreQueue.writeHigh, cwWord_we s pin, cwWord_code s pin, cwWord_data s pin]
  rw [hcut]
  cases hw : (gw s pin 58).we
  · simp only [hw, Bool.false_and, if_false, if_true, cwSel, Option.map_none]
    rfl
  · simp only [hw, Bool.true_and, cwSel]
    cases h60 : ((gw s pin 58).dst == (60 : BitVec 6)) <;>
      cases h58 : ((gw s pin 58).dst == (58 : BitVec 6)) <;>
      cases h59 : ((gw s pin 58).dst == (59 : BitVec 6)) <;>
      simp only [h60, h58, h59, if_true, if_false, Option.map_some, Option.map_none] <;>
      rfl

/-! ## 5. The `P0.D` read scan and `OpenWiring.ctrlMemhaz`

The machine's `memhaz` is `pdHaz || p0haz`: some enabled move reads `P0.D` while
the pointer data is not ready (`pdHaz`), or a pointer request is replaced while
unserved (`p0haz`, the `p0Next` hazard).  The cut's `Moves.memhazEvent` is the
same conjunction read through the enabled-source mask
(`Moves.readsOf en src srcP0D`) and `Mem.haz`. -/

/-- The machine's `p0Next` hazard component. -/
theorem p0Next_haz (p : Machine.P0St) (mv : Option Machine.P0Move) (served landNow : Bool)
    (ramOut lane : Nat) (frz : Bool) :
    (Machine.p0Next p mv served landNow ramOut lane frz).2 =
      (mv.isSome && (match p.req with | .none => false | _ => true) && !served) := rfl

/-- The host slot's `pending` bit is the pointer request. -/
theorem pending_req (b : Mem.State) (h : b.req ≠ (3 : BitVec 2)) :
    (match (Bridge.Mem.absP0 b).req with | .none => false | _ => true) = Mem.pending b := by
  rcases Bridge.Mem.req_cases b h with h0 | h1 | h2
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h0]
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h1]
  · simp [Bridge.Mem.absP0, Bridge.Mem.reqOf, Mem.pending, h2]

/-- The machine's `P0.D` source decode. -/
def isPD : Machine.SrcOp → Bool
  | .pD => true
  | _ => false

/-- `isPD` is source class 1. -/
theorem isPD_class (o : Machine.SrcOp) : isPD o = (Bridge.Moves.srcClassNat o == 1) := by
  cases o <;> rfl

/-- The source table's `P0.D` code is `33` alone (a 64-code kernel check on the
total `srcOpOf`). -/
theorem srcOpOf_pD_all :
    (List.range 64).all (fun d => ((Bridge.Moves.srcClassNat (Bridge.Glue.srcOpOf d) == 1) ==
      ((BitVec.ofNat 6 d) == Moves.srcP0D))) = true := by
  decide

/-- **The `P0.D` decode is the cut's source code 33.** -/
theorem srcPD_iff (hsrc : Bridge.Glue.SrcTable) {d : Nat} (hd : d < 64) :
    isPD (Machine.srcOp d) = (BitVec.ofNat 6 d == Moves.srcP0D) := by
  rw [isPD_class, hsrc.eq d]
  have h := List.all_eq_true.1 srcOpOf_pD_all d (by simpa [List.mem_range] using hd)
  exact beq_iff_eq.1 h

/-- The per-slot `P0.D` read identity on a live slot. -/
theorem pdSlot (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (hsrc : Bridge.Glue.SrcTable) (q : Nat) (hq : q < 6)
    {mv : Machine.Move} (hmv : machSlot m pin q = some mv)
    (hen : ((movBundle s pin).get q).enabled = true) :
    isPD (Machine.srcOp mv.src) =
      (CoreCtl.bitAt (mvEn s pin) q &&
        (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcP0D)) := by
  have hsrcq : mv.src = (Core.slice (mvSrc s pin) (6 * q) 6).toNat :=
    hbus.src q hq mv hmv
  have hlt : (Core.slice (mvSrc s pin) (6 * q) 6).toNat < 64 := by
    simpa using (Core.slice (mvSrc s pin) (6 * q) 6).isLt
  rw [hsrcq, srcPD_iff hsrc hlt, Bridge.Moves.ofNat_toNat_6]
  have hbit : CoreCtl.bitAt (mvEn s pin) q = true := by
    rw [hbus.en q hq, hmv]
    rfl
  rw [hbit]
  rfl

/-- The six-slot `P0.D` scan is the cut's enabled-source mask. -/
theorem pdScan (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz)
    (hbus : MoveBus s m pin) (hsrc : Bridge.Glue.SrcTable) :
    (ltAllMoves m).any (fun mv => isPD (Machine.srcOp mv.src)) =
      (List.range 6).any (fun q =>
        (CoreCtl.bitAt (mvEn s pin) q &&
          (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcP0D))) := by
  rw [MoveFabricKeyed.mAllMoves_ltAllMoves, mAllMoves_enum s m pin hcore hfrz]
  refine MoveFabricKeyed.any_filterMap_split (List.range 6) (machSlot m pin) _
    (fun q => CoreCtl.bitAt (mvEn s pin) q &&
      (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcP0D)) ?_ ?_
  · intro q hq mv hmv
    rw [List.mem_range] at hq
    have hen : ((movBundle s pin).get q).enabled = true := by
      rw [← machSlot_isSome s m pin hbus q hq, hmv]
      rfl
    exact pdSlot s m pin hbus hsrc q hq hmv hen
  · intro q hq hnone
    rw [List.mem_range] at hq
    have hbit : CoreCtl.bitAt (mvEn s pin) q = false := by
      have hs : (machSlot m pin q).isSome = false := by rw [hnone]; rfl
      rw [← hbus.en q hq] at hs
      exact hs
    rw [hbit]
    rfl

/-- The cut's `readsOf` mask is the six-slot disjunction. -/
theorem readsOf_any (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) :
    (!(Moves.readsOf en src s == 0)) =
      (List.range 6).any (fun q => Moves.readAt en src s q) := by
  rw [Moves.readsOf_ne_zero, ← MoveFabricKeyed.anySix_eq_any]
  rfl

/-- **`ctrlInTrue.memhaz`, unfolded** to the two machine hazard terms. -/
theorem ctrlInTrue_memhaz_unfold (m : Machine.State) (pin : Machine.PinIn) :
    (ctrlInTrue m pin).memhaz =
      ((!m.p0.rdy && (ltAllMoves m).any (fun mv => isPD (Machine.srcOp mv.src))) ||
        (Machine.p0Next m.p0 (mhcP0Move m pin) (machineServed m pin == 3) (m.ramOwner == 3)
          m.ramOut.toNat m.ramLane.toNat m.dbg.frz).2) := by
  simp only [ctrlInTrue, ltAllMoves, ltCbs]
  rfl

/-- The machine's `p0Next` hazard is the cut's `Mem.haz`. -/
theorem p0Haz_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hF : DstFlagP0CwTable)
    (hserved : (machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin)) :
    (Machine.p0Next m.p0 (mhcP0Move m pin) (machineServed m pin == 3) (m.ramOwner == 3)
      m.ramOut.toNat m.ramLane.toNat m.dbg.frz).2 = Mem.haz s.p0 (memIn s pin) := by
  rw [p0Next_haz]
  rw [show (mhcP0Move m pin).isSome = (memIn s pin).pWe from
    mhcP0Move_isSome s m pin hrel hinv hJGTab hbus hgrp hkind hT hF]
  rw [show m.p0.req = (Bridge.Mem.absP0 s.p0).req from hrel.p0.req]
  rw [show (match (Bridge.Mem.absP0 s.p0).req with | .none => false | _ => true) =
      Mem.pending s.p0 from pending_req s.p0 hinv.reqNeThree]
  rw [hserved]
  rfl

/-- **`OpenWiring.ctrlMemhaz`**: the machine's `MEMHAZ` event (the `P0.D` read
scan and the pointer hazard) is the cut's `memhazEvent`. -/
theorem ctrlMemhaz (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hsrc : Bridge.Glue.SrcTable) (hT : DstPayloadTable) (hF : DstFlagP0CwTable)
    (hserved : (machineServed m pin == 3) = Mem.grantP0 s.p0 (memIn s pin)) :
    (ctrlInTrue m pin).memhaz =
      Moves.memhazEvent (mvEn s pin) (mvSrc s pin) (Mem.haz s.p0 (memIn s pin)) s.p0.rdy := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val) :=
    fun c => rel_of_bus s m pin c hrel hinv (hbus c)
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := fun c => by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hscan := pdScan s m pin hcore hfrz hbusM hsrc
  have hcut : (!(Moves.readsOf (mvEn s pin) (mvSrc s pin) Moves.srcP0D == 0)) =
      (List.range 6).any (fun q =>
        (CoreCtl.bitAt (mvEn s pin) q &&
          (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcP0D))) := by
    rw [readsOf_any]
    rfl
  rw [ctrlInTrue_memhaz_unfold]
  rw [show (ltAllMoves m).any (fun mv => isPD (Machine.srcOp mv.src)) =
      !(Moves.readsOf (mvEn s pin) (mvSrc s pin) Moves.srcP0D == 0)
    from hscan.trans hcut.symm]
  rw [p0Haz_eq s m pin hrel hinv hJGTab hbus hgrp hkind hT hF hserved]
  rw [Moves.memhazEvent]
  simp only [Moves.memhazEventOf]
  rw [hrel.p0.rdy]
  conv =>
    lhs
    rw [Bool.and_comm]
  exact Bool.or_comm _ _

/-! ## 6. The configuration-queue overrun and `OpenWiring.ctrlCwovr`

The machine's `cwNext` overrun is `CW.D` dropped while the queue holds
(`cw.cwv && !drains`); the cut's is `writeData && !accept`, which is
`writeData && pending && !drain`.  The two agree through the `CW` move
(`cwMove`), `CwRel` and the machine's internal drain condition. -/

/-- The arbiter's `coreIssue` is "the grant is `.core`", in boolean form. -/
theorem step_coreIssue (st : Config.State) (inp : Config.Input) (c : Config.Write) :
    (match Config.grant st inp with
      | .host w => (true, false, w)
      | .core w => (true, true, w)
      | .idle => (false, false, c)).2.fst =
    (!st.heldValid && !st.previousWrite && !inp.hostValid && inp.coreValid) := by
  unfold Config.grant
  by_cases hh : st.heldValid = true <;> by_cases hp : st.previousWrite = true <;>
    by_cases hv : inp.hostValid = true <;> by_cases hc : inp.coreValid = true <;>
    simp [hh, hp, hv, hc]

/-- The arbiter cut's `coreIssue` in closed form. -/
theorem arbIn_coreIssue (s : State) :
    (arbStep s).coreIssue =
      (!s.arb.heldValid && !s.arb.previousWrite && !(hostCfgOf s).isSome &&
        ((s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) && !s.freeze.frz)) := by
  have h := step_coreIssue (Config.beforeEdge s.arb (arbIn s)) (arbIn s) (arbIn s).core
  simp only [arbStep, Config.step]
  refine h.trans ?_
  simp [Config.beforeEdge, arbIn, Bridge.CfgWrite.cfgIn]

/-- The cut's queue overrun event, in `pending`/`drain` form. -/
theorem accept_not (st : CoreQueue.State) (i : CoreQueue.Input) :
    (CoreQueue.writeData i && !CoreQueue.accept st i) =
      (CoreQueue.writeData i && st.pending && !CoreQueue.drain st i) := by
  unfold CoreQueue.accept
  by_cases hw : CoreQueue.writeData i = true <;>
    by_cases hp : st.pending = true <;>
    by_cases hd : CoreQueue.drain st i = true <;>
    simp [hw, hp, hd]

/-- The machine's internal queue-drain condition of `cwNext`. -/
def mhcDrains (m : Machine.State) (pin : Machine.PinIn) : Bool :=
  !m.dbg.frz && m.cw.cwv &&
    (if (m.cw.cwv && Machine.Config.isCfgAddr m.cw.cwqa.toNat) then
      (!m.cw.hh && (mhcHostCfg m pin).isNone && !m.dbg.frz && m.cw.cwv &&
        Machine.Config.isCfgAddr m.cw.cwqa.toNat && !m.cw.bwp)
    else true)

/-- The machine's core-drain component of `cwNext`'s bank-port let (the fifth
element of the `perf0` tuple). -/
theorem cwNext_coreDrain_val (cw : Machine.CwSt) (hostCfg : Option (Nat × Nat)) (frozen : Bool) :
    (if cw.hh then
        (match hostCfg with
         | some (a, v) => (some (cw.hha.toNat, cw.hhd.toNat), true, a, v, false)
         | none => (some (cw.hha.toNat, cw.hhd.toNat), false, 0, 0, false))
      else
        match hostCfg with
        | some (a, v) =>
          if cw.bwp then (none, true, a, v, false) else (some (a, v), false, 0, 0, false)
        | none =>
          if (!frozen && cw.cwv && (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) &&
              !cw.bwp) = true then
            (some (cw.cwqa.toNat, cw.cwqd.toNat), false, 0, 0, true)
          else (none, false, 0, 0, false)).2.2.2.snd =
      (!cw.hh && hostCfg.isNone && !frozen && cw.cwv &&
        (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) && !cw.bwp) := by
  cases hh : cw.hh
  · cases hc : hostCfg
    · by_cases hd : (!frozen && cw.cwv && (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) &&
          !cw.bwp) = true <;> simp [hh, hc, hd]
    · cases hb : cw.bwp <;> simp [hh, hc, hb]
  · cases hc : hostCfg <;> simp [hh, hc]

/-- The machine's drain condition is the cut's queue drain
(`CoreQueue.drain`, with the arbiter's `coreIssue`). -/
theorem mhcDrains_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) :
    mhcDrains m pin = CoreQueue.drain s.cq (cqIn s pin) := by
  have hhost := cw_open_hostCfg s m pin hinv hrel
  have hci := arbIn_coreIssue s
  rw [show CoreQueue.drain s.cq (cqIn s pin) = cwDrain s from rfl, cwDrain, hci]
  unfold mhcDrains
  rw [hhost, hrel.cw.cwv, hrel.cw.cwqa, hrel.cw.bwp, hrel.cw.hh, dbgRel_frz hrel.dbg]
  by_cases hf : s.freeze.frz = true
  · simp [hf]
  · have hf2 : s.freeze.frz = false := by
      cases hfb : s.freeze.frz
      · rfl
      · exact absurd hfb hf
    clear hf
    by_cases hp : s.cq.pending = true <;>
      by_cases hic : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat = true <;>
      by_cases hl : s.arb.heldValid = true <;>
      by_cases hw : s.arb.previousWrite = true <;>
      (cases hostCfgOf s <;> simp [hf2, hp, hic, hl, hw])

/-- The machine's `cwNext` overrun for a computed `CW` move. -/
theorem mhcCwo_ovr_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hcw : mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin)) :
    (mhcCwo m pin).ovr =
      (CoreQueue.writeData (cqIn s pin) && s.cq.pending &&
        !CoreQueue.drain s.cq (cqIn s pin)) := by
  have hhost := cw_open_hostCfg s m pin hinv hrel
  have hfrz := dbgRel_frz hrel.dbg
  have hci := arbIn_coreIssue s
  simp only [mhcCwo, Machine.cwNext, hcw, Bridge.CfgWrite.mvOf]
  cases hf : s.freeze.frz <;>
  by_cases hD : CoreQueue.writeData (cqIn s pin) = true <;>
  by_cases hL : CoreQueue.writeLow (cqIn s pin) = true <;>
  by_cases hH : CoreQueue.writeHigh (cqIn s pin) = true <;>
  by_cases hic : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat = true <;>
  by_cases hp : s.cq.pending = true <;>
  by_cases hl : s.arb.heldValid = true <;>
  by_cases hb : s.arb.previousWrite = true <;>
  cases ho : hostCfgOf s <;>
  simp_all [cqIn, hrel.cw.cwv, hrel.cw.cwqa, hrel.cw.bwp, hrel.cw.hh, hhost, hf, hci,
    CoreQueue.drain, CoreQueue.accept]

/-- **`OpenWiring.ctrlCwovr`**: the machine's `cwNext` overrun is the cut's
configuration-queue drop event. -/
theorem ctrlCwovr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : MoveFabricKeyed.JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : MoveFabricKeyed.GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hF : DstFlagP0CwTable) :
    (ctrlInTrue m pin).cwovr =
      (CoreQueue.writeData (cqIn s pin) && !CoreQueue.accept s.cq (cqIn s pin)) := by
  rw [show (ctrlInTrue m pin).cwovr = (mhcCwo m pin).ovr from rfl]
  rw [mhcCwo_ovr_eq s m pin hrel hinv (cwMove s m pin hrel hinv hJGTab hbus hgrp hkind hF)]
  rw [accept_not s.cq (cqIn s pin)]

end Metronome.ChipCut.Discharge.MovePayloadWire
