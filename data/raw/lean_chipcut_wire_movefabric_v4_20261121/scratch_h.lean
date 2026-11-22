import Metronome.ChipCut.Discharge.MoveFabric

open Metronome

namespace Metronome.ChipCut.Discharge.MoveFabric

/-- `findSome?` commutes with a projection of its value. -/
theorem findSome?_map_value {α : Type} {β : Type} {γ : Type} (l : List α)
    (f : α → Option β) (T : β → γ) :
    (l.findSome? f).map T = l.findSome? (fun x => (f x).map T) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases h : f a with
    | none => simpa only [h, Option.map_none] using ih
    | some b => rfl

theorem unitInputs_shCfg_low5_probe (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) :
    ∀ k : Fin 2, ((mUnitsIn m pin).shCfg[k]).map (fun v => v % 32) =
      Bridge.ShifterB.absCfg (shIn s pin k.val) := by
  intro k
  have huniq : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).we = true →
      ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).dst == BitVec.ofNat 6 (22 + k.val)) = true := by
    intro hw
    obtain ⟨j, hj, hhit, hfirst⟩ := pickWord_we_exists (mvEn s pin) (mvGrp s pin)
      (famG (.shCfg k.val)) (mvDst s pin) (mvDat s pin) hw
    have hpw := Bridge.Moves.pickWord_eq_word (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s) (famG (.shCfg k.val)) j hj hhit hfirst
    rw [show (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).dst = ((movBundle s pin).get j).dst from
      congrArg CoreCtl.GroupWord.dst hpw]
    have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
    have hgrp' : (Moves.dgTable ((movBundle s pin).get j).dst == famG (.shCfg k.val)) = true := by
      have h2 := hhit
      rw [hitAt_bundle s pin (famG (.shCfg k.val)) (famG_nonkeyed hT).1 j hj,
        Bool.and_eq_true] at h2
      rw [hbusM.grp j hj] at h2
      exact h2.2
    have hlt : ((movBundle s pin).get j).dst.toNat < 64 := by
      simpa using ((movBundle s pin).get j).dst.isLt
    have hfam : famIn (.shCfg k.val) (Machine.dstOp ((movBundle s pin).get j).dst.toNat)
        = true := by
      rw [← hT.payload (.shCfg k.val) _ hlt, Bridge.Moves.ofNat_toNat_6]
      exact hgrp'
    have hcode : ((movBundle s pin).get j).dst = BitVec.ofNat 6 (22 + k.val) := by
      cases h : Machine.dstOp ((movBundle s pin).get j).dst.toNat with
      | shCfg j' =>
        rw [h] at hfam
        have h' : j' = k.val := by simpa [famIn] using hfam
        rw [← Bridge.Moves.ofNat_toNat_6 ((movBundle s pin).get j).dst,
          (hT.codeOf _ hlt j').2.1 h, h']
      | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
    rw [hcode, beq_iff_eq]
  have hpq := hPQ_of_payload (famIn (.shCfg k.val))
    (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
    (fun _ => some ()) (famG (.shCfg k.val)) (hT.payload (.shCfg k.val))
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | shCfg j =>
        rw [h] at hp
        have h' : (j == k.val) = true := by simpa using hp
        rw [beq_iff_eq] at h'
        subst h'
        simp
      | _ => rw [h] at hp; simp at hp)
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | shCfg j =>
        rw [h] at hp
        have h' : (j == k.val) = false := by simpa using hp
        simp [h']
      | _ => simp [h] at *)
  have hpack : (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
      | .shCfg j => if j == k.val then some mv.v else none
      | _ => none) =
      (if (gw s pin (BitVec.ofNat 6 (22 + k.val))).we then
        some (gw s pin (BitVec.ofNat 6 (22 + k.val))).data.toNat else none) := by
    have hpt : ∀ mv : Machine.Move,
        (match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some mv.v else none
          | _ => none) =
        ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none
          | _ => none).map (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2) := by
      intro mv
      cases h : Machine.dstOp mv.dst <;> simp [h]
    rw [findSome?_congr (fun mv => hpt mv),
      findSome?_snd_map (mWs m pin)
        (fun mv => match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none | _ => none)
        (fun mv => mv.v),
      pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
        (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
        (fun _ => some ()) (fun v => v) (famG (.shCfg k.val))
        (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
    rw [show gw s pin (BitVec.ofNat 6 (22 + k.val)) =
        Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
          (mvDst s pin) (mvDat s pin) from rfl]
    cases (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
      (mvDst s pin) (mvDat s pin)).we <;> rfl
  rw [show (mUnitsIn m pin).shCfg[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .shCfg j => if (j == k.val) = true then some mv.v else none
      | _ => none) from Discharge.vec_get_ofFn' _ k,
    findSome?_map_value (mWs m pin)
      (fun mv => match Machine.dstOp mv.dst with
        | .shCfg j => if (j == k.val) = true then some mv.v else none
        | _ => none) (fun v => v % 32)]
  have hstep : ∀ mv : Machine.Move,
      ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some mv.v else none
          | _ => none).map (fun v => v % 32)) =
      ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none
          | _ => none).map (fun a => (a, mv.v % 32))).map (fun p : Unit × Nat => p.2) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> simp [h]
  rw [findSome?_congr (fun mv => hstep mv),
    findSome?_snd_map (mWs m pin)
      (fun mv => match Machine.dstOp mv.dst with
        | .shCfg j => if j == k.val then some () else none | _ => none)
      (fun mv => mv.v % 32),
    pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
      (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
      (fun _ => some ()) (fun v => v % 32) (famG (.shCfg k.val))
      (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
  have hcut : Bridge.ShifterB.absCfg (shIn s pin k.val) =
      (if (gw s pin (BitVec.ofNat 6 (22 + k.val))).we then
        some ((gw s pin (BitVec.ofNat 6 (22 + k.val))).data.toNat % 32) else none) := by
    have hstr : strobe s pin (BitVec.ofNat 6 (22 + k.val)) =
        (gw s pin (BitVec.ofNat 6 (22 + k.val))).we := by
      rw [show strobe s pin (BitVec.ofNat 6 (22 + k.val)) = Strobes.opg (mvEn s pin)
          (mvGrp s pin) (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (22 + k.val)))
          (BitVec.ofNat 6 (22 + k.val)) from rfl, Strobes.opg_eq_pick]
      rw [show Moves.dgTable (BitVec.ofNat 6 (22 + k.val)) = famG (.shCfg k.val) from rfl] at *
      by_cases hw : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
          (famG (.shCfg k.val))) (mvDst s pin) (mvDat s pin)).we = true
      · rw [show gw s pin (BitVec.ofNat 6 (22 + k.val)) = Moves.pickWord
            (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
            (mvDst s pin) (mvDat s pin) from rfl]
        simp [hw, huniq hw]
      · have hf : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
            (famG (.shCfg k.val))) (mvDst s pin) (mvDat s pin)).we = false := by
          simpa using hw
        rw [hf]
        rfl
    rw [show Bridge.ShifterB.absCfg (shIn s pin k.val) =
        (if (shIn s pin k.val).cfgWe then some ((shIn s pin k.val).cfgD).toNat else none)
        from rfl,
      show (shIn s pin k.val).cfgWe = strobe s pin (BitVec.ofNat 6 (22 + k.val)) from rfl,
      hstr,
      show (shIn s pin k.val).cfgD =
        BitVec.truncate 5 (gw s pin (BitVec.ofNat 6 (22 + k.val))).data from rfl,
      truncate_five_toNat]
  rw [hcut]

end Metronome.ChipCut.Discharge.MoveFabric
