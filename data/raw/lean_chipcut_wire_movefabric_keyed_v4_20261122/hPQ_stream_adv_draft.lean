import Metronome.ChipCut.Discharge.MoveFabricKeyed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.MoveFabricKeyed

open Metronome
open Metronome.ChipCut.Discharge.MoveFabric

/-- **The `Fam.stream k` payload instance for `S*.ADV`**: the machine's
`.sAdv k` test is the cut's group test conjoined with the code test
`dst == 47 + k`.  This is the `hPQ` that `pickScan_mWs` needs. -/
theorem hPQ_stream_adv (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    ∀ d, d < 64 → sAdvUnit k (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) then
        (if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (47 + k.val) then some () else none)
       else none) := by
  intro d hd
  have hpay := hT.payload (.stream k.val) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = true
  · have hfam : famIn (.stream k.val) (Machine.dstOp d) = true := by rw [← hpay, hg]
    rw [if_pos hg]
    cases h : Machine.dstOp d with
    | sAdv j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd47 : d = 47 + k.val := by simpa [hj] using hC.sAdv d hd j h
      rw [hd47]
      simp [sAdvUnit, hj]
    | sRx j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd49 : d = 49 + k.val := by simpa [hj] using hC.sRx d hd j h
      rw [hd49, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sAdvUnit]
    | sCtl j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd51 : d = 51 + k.val := by simpa [hj] using hC.sCtl d hd j h
      rw [hd51, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sAdvUnit]
    | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
  · rw [if_neg (by simpa using hg)]
    by_cases hP : sAdvUnit k (Machine.dstOp d) = some ()
    · exfalso
      cases h : Machine.dstOp d with
      | sAdv j =>
        rw [h] at hP
        have hj : j = k.val := by
          by_cases hjk : j = k.val
          · exact hjk
          · simp [sAdvUnit, hjk] at hP
        have hd47 : d = 47 + k.val := by simpa [hj] using hC.sAdv d hd j h
        rw [hd47] at hg
        rw [show Moves.dgTable (BitVec.ofNat 6 (47 + k.val)) = famG (.stream k.val) from rfl] at hg
        exact absurd hg (by simp)
      | _ => rw [h] at hP; exact absurd hP (by simp [sAdvUnit])
    · cases h : sAdvUnit k (Machine.dstOp d) with
      | none => rfl
      | some u => cases u; exact absurd h hP

/-- **`StreamWire.input`'s `adv` component is exact**: the machine's
`(machStreamIn m k).adv` is the cut's `Sk.ADV` strobe `opg(DG_SK, 47+k)`. -/
theorem streams_adv (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    (machStreamIn m k).adv = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).adv := by
  have hpq := hPQ_stream_adv hT hC k
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (sAdvUnit k) (fun dst => if dst == BitVec.ofNat 6 (47 + k.val) then some () else none)
    (fun v => v) (famG (.stream k.val))
    (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq
  have hmach : (machStreamIn m k).adv =
      ((mWs m pin).findSome? (fun mv => (sAdvUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v)))).isSome := by
    rw [machStreamIn_adv, machWs_eq_mWs']
    exact findSome?_isSome_congr _ _ (fun mv => by
      rw [Option.isSome_map, Option.isSome_map]
      exact sAdv_isSome_eq k (Machine.dstOp mv.dst))
  rw [hmach, hscan]
  have hwe : (if (gw s pin (BitVec.ofNat 6 (47 + k.val))).we then
      ((if (gw s pin (BitVec.ofNat 6 (47 + k.val))).dst == BitVec.ofNat 6 (47 + k.val)
        then some () else none).map
        (fun a => (a, (gw s pin (BitVec.ofNat 6 (47 + k.val))).data.toNat))) else none).isSome
      = ((gw s pin (BitVec.ofNat 6 (47 + k.val))).we &&
        ((gw s pin (BitVec.ofNat 6 (47 + k.val))).dst == BitVec.ofNat 6 (47 + k.val))) := by
    cases (gw s pin (BitVec.ofNat 6 (47 + k.val))).we <;>
      cases ((gw s pin (BitVec.ofNat 6 (47 + k.val))).dst ==
        BitVec.ofNat 6 (47 + k.val)) <;> rfl
  rw [hwe]
  show _ = strobe s pin (BitVec.ofNat 6 (47 + k.val))
  rw [show strobe s pin (BitVec.ofNat 6 (47 + k.val)) = Strobes.opg (mvEn s pin)
      (mvGrp s pin) (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (47 + k.val)))
      (BitVec.ofNat 6 (47 + k.val)) from rfl,
    Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (Moves.dgTable (BitVec.ofNat 6 (47 + k.val))) (BitVec.ofNat 6 (47 + k.val))]
  rw [show Moves.dgTable (BitVec.ofNat 6 (47 + k.val)) = famG (.stream k.val) from rfl,
    show gw s pin (BitVec.ofNat 6 (47 + k.val)) = Moves.pickWord (Moves.hitsMask (mvEn s pin)
      (mvGrp s pin) (famG (.stream k.val))) (mvDst s pin) (mvDat s pin) from rfl]
  rfl

end Metronome.ChipCut.Discharge.MoveFabricKeyed
