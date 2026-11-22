/-
# ChipCut discharge: the stream move picks and the combined stream control

`StreamWire.input` (`Discharge/StreamDbg.lean`) compares the machine's whole
`StreamIn` record with `Bridge.StreamB.absIn`.  Two of its fields are the stream
move fabric's:

* `rx` — the machine reads the winning `Sk.RX k` move's bus byte, while the cut
  reads **bit 0 of stream `k`'s whole write-group winner** (`Wire.streamIn.rxBit`,
  RTL `w[0]` of `PICKG(DG_Sk)`, `src/project.v:471`).  The group has one winner and
  `Sk.ADV k`/`Sk.RX k`/`Sk.CTL k` share the group (`47+k`, `49+k`, `51+k`), so the
  two agree on the low bit only: `streams_rx_low1` proves the `% 2` form (the exact
  form is false, `MoveFabricKeyed.stream_rx_data_witness`).
* `ctlMove`/`hCtl` — the machine keeps the `Sk.CTL` move byte and the host
  `SRT.CTL` byte apart and combines them inside `Machine.streamNext`, while the cut
  folds them into `Stream.Input.rewind`/`flush`/`clrStarved`
  (`Strobes.streamCtlOf`).  `streams_ctl_combined` proves that the three booleans
  `streamNext` computes are the cut's three inputs.  (The field equality itself is
  false: with no move the machine has `none` and the cut still has `some 0`;
  `MoveFabricKeyed.stream_ctl_absent_witness`.)

Both targets are one `pickScan_mWs` instance for the stream family `Fam.stream k`
with the payload `Sk.RX k` (resp. the plain move byte for `Sk.CTL`), plus the
group identity `dgTable (49+k) = dgTable (47+k)` (`dgTable_stream_*`) and the
width lemma `byte_mod_two`.

Hypotheses are exactly `pickScan_mWs`'s (`ChipRel`, `Inv`, the jump-guard table,
`CoreInputBus`, `hgrp`, `DstKindTable`) plus the two global destination tables
`DstPayloadTable` and `DstStreamLineTable`.

## Round 2: the three side hypotheses of the control statement

`streams_ctl_combined` takes the `Sk.CTL` pick (`hmove`), the host `CTL` byte
(`hhost`) and the freeze sample (`hfrz`) as hypotheses.  All three are discharged
here:

* `streams_ctlMove_pick` — the pick, one `pickScan_mWs` for `Fam.stream k`
  (`S*.CTL`, code `51+k`; the `streams_adv` pattern);
* `streams_hCtl` — the host byte, through the host link (`ltHw m = hwOf s`,
  `hwByte_eq`), re-derived locally because `HostPinWire` cannot be imported
  alongside `CoreUnits` (duplicate `bgetLE_lt`);
* `streams_frz` — `ChipRel.dbg`'s `frz` projection.

`streams_ctl_combined'` is the resulting statement with only the standard
hypotheses.
-/
import Metronome.ChipCut.Discharge.MoveFabricKeyed
import Metronome.ChipCut.Discharge.StreamDbg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.StreamMoveWire

open Metronome
open Metronome.ChipCut.Discharge.MoveFabric
open Metronome.ChipCut.Discharge.MoveFabricKeyed

/-! ## 0. Bit plumbing -/

/-- The cut's `CoreCtl.bitAt` is the machine's `nbit` of the value (the
`CoreCtl` twin of `Bridge.Glue.bitAt_eq_nbit`, which `Strobes` uses). -/
theorem core_bitAt_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    CoreCtl.bitAt x i = Machine.Util.nbit x.toNat i := by
  rw [Bool.eq_iff_iff]
  simp only [CoreCtl.bitAt, Machine.Util.nbit, BitVec.getLsbD, bne_iff_ne, ne_eq,
    BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow,
    BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  rw [show BitVec.ushiftRight x i = (x >>> i) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show ((0 : BitVec 1)).toNat = 0 from by decide]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ i) with h | h <;> simp [h]

/-- `getD 0` of a guarded control bus: the machine's `ctlMove`/`hCtl` read. -/
theorem getD_ite_some (c : Bool) (x : Nat) :
    (if c then some x else (none : Option Nat)).getD 0 = if c then x else 0 := by
  cases c <;> rfl

/-! ## 1. The machine's stream move fields as the plain winner scans

`machStreamIn`'s `sel` maps the scan's payload to `mm.v`; these two lemmas move
that `Option.map` inside the scan, which is the shape `pickScan_mWs` consumes. -/

/-- The machine's `rx` field, as the winner scan over `.sRx k` moves. -/
theorem machStreamIn_rx (m : Machine.State) (k : Fin 2) :
    (machStreamIn m k).rx =
      (machWs m).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .sRx j => if j == k.val then some mv.v else none
        | _ => none) := by
  show (machWs m).findSome? (fun mm => (match Machine.dstOp mm.dst with
      | .sRx j => if j == k.val then some 0 else none
      | _ => none).map (fun _ => mm.v)) = _
  rw [findSome?_congr (g := fun mv => match Machine.dstOp mv.dst with
      | .sRx j => if j == k.val then some mv.v else none
      | _ => none) (fun mv => ?_)]
  cases h : Machine.dstOp mv.dst with
  | sRx j =>
    by_cases hj : (j == k.val) = true <;> simp [hj]
  | _ => simp

/-- The machine's `ctlMove` field, as the winner scan over `.sCtl k` moves. -/
theorem machStreamIn_ctlMove (m : Machine.State) (k : Fin 2) :
    (machStreamIn m k).ctlMove =
      (machWs m).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .sCtl j => if j == k.val then some mv.v else none
        | _ => none) := by
  show (machWs m).findSome? (fun mm => (match Machine.dstOp mm.dst with
      | .sCtl j => if j == k.val then some 0 else none
      | _ => none).map (fun _ => mm.v)) = _
  rw [findSome?_congr (g := fun mv => match Machine.dstOp mv.dst with
      | .sCtl j => if j == k.val then some mv.v else none
      | _ => none) (fun mv => ?_)]
  cases h : Machine.dstOp mv.dst with
  | sCtl j =>
    by_cases hj : (j == k.val) = true <;> simp [hj]
  | _ => simp

/-! ## 2. Stream `k`'s write group

Codes `47+k` (`Sk.ADV`), `49+k` (`Sk.RX`) and `51+k` (`Sk.CTL`) all lie in the
group `Fam.stream k` (`famG (.stream k)`), so `gw` reads the same word at all
three — which is what makes the cut's `rxBit` the RX winner's low bit. -/

/-- The picked word of stream `k`'s write group (`Sk.ADV`/`RX`/`CTL`). -/
def streamPick (s : State) (pin : Machine.PinIn) (k : Fin 2) : CoreCtl.GroupWord :=
  Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.stream k.val)))
    (mvDst s pin) (mvDat s pin)

/-- The `Sk.ADV` code's group is the stream group. -/
theorem dgTable_stream_adv (k : Fin 2) :
    Moves.dgTable (BitVec.ofNat 6 (47 + k.val)) = famG (.stream k.val) := rfl

/-- The `Sk.RX` code's group is the stream group. -/
theorem dgTable_stream_rx (k : Fin 2) :
    Moves.dgTable (BitVec.ofNat 6 (49 + k.val)) = famG (.stream k.val) := by
  have hk : k.val = 0 ∨ k.val = 1 := by have := k.isLt; omega
  rcases hk with hk | hk <;> rw [hk] <;> decide

/-- The `Sk.CTL` code's group is the stream group. -/
theorem dgTable_stream_ctl (k : Fin 2) :
    Moves.dgTable (BitVec.ofNat 6 (51 + k.val)) = famG (.stream k.val) := by
  have hk : k.val = 0 ∨ k.val = 1 := by have := k.isLt; omega
  rcases hk with hk | hk <;> rw [hk] <;> decide

/-- `gw` at the `Sk.ADV` code is the stream group's pick. -/
theorem gw_stream_adv (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    gw s pin (BitVec.ofNat 6 (47 + k.val)) = streamPick s pin k := rfl

/-- `gw` at the `Sk.RX` code is the stream group's pick (same group as `ADV`). -/
theorem gw_stream_rx (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    gw s pin (BitVec.ofNat 6 (49 + k.val)) = streamPick s pin k := by
  unfold gw streamPick
  rw [dgTable_stream_rx k]

/-- `gw` at the `Sk.CTL` code is the stream group's pick. -/
theorem gw_stream_ctl (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    gw s pin (BitVec.ofNat 6 (51 + k.val)) = streamPick s pin k := by
  unfold gw streamPick
  rw [dgTable_stream_ctl k]

/-- The `Sk.RX k` payload test on the decoded destination. -/
def sRxUnit (k : Fin 2) : Machine.DstOp → Option Unit
  | .sRx j => if j == k.val then some () else none
  | _ => none

/-- The group-code test of one destination code. -/
def codeUnit (code : Nat) : BitVec 6 → Option Unit :=
  fun d => if d == BitVec.ofNat 6 code then some () else none

/-! ## 3. `rx`: the low bit of the stream group's winner

Machine: the `.sRx k` winner's bus byte.  Cut: `if rxWe then some rxBit`, with
`rxWe` the `Sk.RX k` strobe and `rxBit` bit 0 of the *group* winner's data.

One `pickScan_mWs` for `Fam.stream k` gives the winner's byte; the payload test
`Q` must return `none` off the `Sk.RX` code (an `ADV`/`CTL` winner gives the same
group, so a naked `Bool` payload `Q d = some (d == 49+k)` would demand
`none = some false` and fail `hPQ`).  Then
`strobe = we && dst == code` (`Strobes.opg_eq_pick`) and `% 2` of a byte is its
bit 0 (`byte_mod_two`). -/
theorem streams_rx_low1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) (hC : DstStreamLineTable) :
    ∀ k : Fin 2, (machStreamIn m k).rx.map (fun v => v % 2) =
      (absInOf k (streamAt s k.val) (streamIn s pin k.val)).rx := by
  intro k
  have hcode : 49 + k.val < 64 := by have := k.isLt; omega
  have hc47 : 47 + k.val < 64 := by have := k.isLt; omega
  have hc51 : 51 + k.val < 64 := by have := k.isLt; omega
  -- the payload-table instance for the stream group
  have hPQ : ∀ d, d < 64 → sRxUnit k (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) then
        codeUnit (49 + k.val) (BitVec.ofNat 6 d) else none) := by
    intro d hd
    have hpg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) =
        famIn (.stream k.val) (Machine.dstOp d) := hT.payload (.stream k.val) d hd
    by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = true
    · have hfam : famIn (.stream k.val) (Machine.dstOp d) = true := by
        rw [← hpg, hg]
      rw [hg]
      cases h : Machine.dstOp d with
      | sRx j =>
        rw [h] at hfam
        have hj : j = k.val := by simpa [famIn] using hfam
        subst hj
        have hdcode : d = 49 + k.val := hC.sRx d hd k.val h
        simp [sRxUnit, codeUnit, hdcode, ofNat6_beq_self (49 + k.val) hcode]
      | sAdv j =>
        rw [h] at hfam
        have hj : j = k.val := by simpa [famIn] using hfam
        subst hj
        have hdcode : d = 47 + k.val := hC.sAdv d hd k.val h
        simp [sRxUnit, codeUnit, hdcode,
          ofNat6_beq_of_ne (a := 47 + k.val) (b := 49 + k.val) hc47 hcode (by omega)]
      | sCtl j =>
        rw [h] at hfam
        have hj : j = k.val := by simpa [famIn] using hfam
        subst hj
        have hdcode : d = 51 + k.val := hC.sCtl d hd k.val h
        simp [sRxUnit, codeUnit, hdcode,
          ofNat6_beq_of_ne (a := 51 + k.val) (b := 49 + k.val) hc51 hcode (by omega)]
      | _ => rw [h] at hfam; simp [famIn] at hfam
    · have hgf : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = false := by
        by_cases hh : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = true
        · exact absurd hh hg
        · simpa using hh
      rw [hgf]
      cases h : Machine.dstOp d with
      | sRx j =>
        have hf : famIn (.stream k.val) (Machine.dstOp d) = false := by rw [← hpg, hgf]
        rw [h] at hf
        have hj : (j == k.val) = false := by
          by_cases hh : (j == k.val) = true
          · have ht : famIn (.stream k.val) (.sRx j) = true := by simp [famIn, hh]
            rw [ht] at hf
            exact absurd hf (by simp)
          · simpa using hh
        simp [sRxUnit, hj]
      | _ => simp [sRxUnit]
  -- the group pick IS the machine's `.sRx k` winner
  have hscan : (mWs m pin).findSome? (fun mv => (sRxUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v))) =
      (if (streamPick s pin k).we then
        (codeUnit (49 + k.val) (streamPick s pin k).dst).map
          (fun a => (a, (streamPick s pin k).data.toNat)) else none) :=
    pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
      (sRxUnit k) (codeUnit (49 + k.val)) (fun v => v) (famG (.stream k.val))
      (famG_nonkeyed (f := .stream k.val) hT).1
      (famG_nonkeyed (f := .stream k.val) hT).2.1
      (famG_nonkeyed (f := .stream k.val) hT).2.2 hPQ
  -- the scan's value (the `dst == code` test is folded out of the payload)
  have hval : (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .sRx j => if j == k.val then some mv.v else none
        | _ => none) =
      (if (streamPick s pin k).we &&
          ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val))
        then some (streamPick s pin k).data.toNat else none) := by
    rw [findSome?_congr (g := fun mv => ((sRxUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2)) (fun mv => ?_)]
    · rw [findSome?_snd_map, hscan]
      by_cases hw : (streamPick s pin k).we = true <;>
        by_cases hb : ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val)) = true <;>
        simp [codeUnit, hw, hb]
    · cases h : Machine.dstOp mv.dst with
      | sRx j =>
        by_cases hj : (j == k.val) = true <;> simp [sRxUnit, hj]
      | _ => simp [sRxUnit]
  -- the cut's field
  have hcut : (absInOf k (streamAt s k.val) (streamIn s pin k.val)).rx =
      (if (streamPick s pin k).we &&
          ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val))
        then some (if Machine.Util.bit (streamPick s pin k).data 0 then 1 else 0) else none) := by
    rw [show (absInOf k (streamAt s k.val) (streamIn s pin k.val)).rx =
        (if (streamIn s pin k.val).rxWe then
          some (if (streamIn s pin k.val).rxBit then 1 else 0) else none) from rfl]
    rw [show (streamIn s pin k.val).rxWe = strobe s pin (BitVec.ofNat 6 (49 + k.val)) from rfl]
    rw [show (streamIn s pin k.val).rxBit =
        Machine.Util.bit (gw s pin (BitVec.ofNat 6 (47 + k.val))).data 0 from rfl]
    rw [show strobe s pin (BitVec.ofNat 6 (49 + k.val)) = Strobes.opg (mvEn s pin) (mvGrp s pin)
        (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (49 + k.val)))
        (BitVec.ofNat 6 (49 + k.val)) from rfl,
      Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (Moves.dgTable (BitVec.ofNat 6 (49 + k.val))) (BitVec.ofNat 6 (49 + k.val)),
      dgTable_stream_rx k]
    rfl
  -- assemble
  calc (machStreamIn m k).rx.map (fun v => v % 2)
      = ((mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
            | .sRx j => if j == k.val then some mv.v else none
            | _ => none)).map (fun v => v % 2) := by
          rw [machStreamIn_rx, machWs_eq_mWs']
    _ = (if (streamPick s pin k).we &&
            ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val))
          then some (streamPick s pin k).data.toNat else none).map (fun v => v % 2) := by
          rw [hval]
    _ = (if (streamPick s pin k).we &&
            ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val))
          then some ((streamPick s pin k).data.toNat % 2) else none) := by
          by_cases h : ((streamPick s pin k).we &&
              ((streamPick s pin k).dst == BitVec.ofNat 6 (49 + k.val))) = true <;> simp [h]
    _ = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).rx := by
          rw [hcut, byte_mod_two]

/-! ## 4. The combined stream control bits

The cut folds the host `SRT.CTL` byte into the same three control inputs
(`Strobes.streamCtlOf`: rewind = move bit 0 OR host bit 0, flush = move bit 1 OR
host bit 1, `clrStarved` = host bit 7), while the machine keeps the move byte
(`StreamIn.ctlMove`), the host byte (`StreamIn.hCtl`) and the cycle's freeze flag
separate and combines them in `Machine.streamNext`:

```
rewind   := nbit mctl 0 || nbit hctl 0
flushReq := nbit mctl 1 || (!frozen && nbit hctl 1)
clr      := nbit hctl 7
```

`streamCtl_combine` is the pure boolean identity; `streams_ctl_combined` states it
for the actual records, with the two wiring hypotheses (`hmove`: the machine's
`ctlMove` is the `Sk.CTL` winner's byte, i.e. `gw (51+k)`'s `we && dst == 51+k`
and data; `hhost`: its `hCtl` is the host `CTL` byte) and the freeze sample. -/

/-- The three control bits of one cycle from the machine's two bus readings and
the cut's combined strobing.  The flush conjunct is the **consumed** flush:
`streamNext` passes `flushReq` to `streamAuto` only in its unfrozen branch, so the
host-flush gate `!frozen` is applied on both sides — which is also `Stream.fl`'s
`!FRZ` gate (SPEC_V2 §12.3: a host stream flush is ignored while frozen). -/
theorem streamCtl_combine (data : BitVec 8) (hm hh : Bool) (hd : BitVec 8)
    (frozen : Bool) :
    ((Machine.Util.nbit (if hm then data.toNat else 0) 0 ||
        Machine.Util.nbit (if hh then hd.toNat else 0) 0) =
        (Strobes.streamCtlOf data hm hh hd).rewind)
      ∧ (((Machine.Util.nbit (if hm then data.toNat else 0) 1 ||
          (!frozen && Machine.Util.nbit (if hh then hd.toNat else 0) 1)) && !frozen) =
        ((Strobes.streamCtlOf data hm hh hd).flush && !frozen))
      ∧ (Machine.Util.nbit (if hh then hd.toNat else 0) 7 =
        (Strobes.streamCtlOf data hm hh hd).clrStarved) := by
  unfold Strobes.streamCtlOf
  simp only [core_bitAt_eq_nbit]
  cases hm <;> cases hh <;> cases frozen <;> simp [Machine.Util.nbit]

/-- **The stream control inputs are the machine's combined control bus.**  The
three booleans `Machine.streamNext` computes from `(ctlMove, hCtl, frozen)` are
the cut's `rewind`, `flush` and `clrStarved` inputs.  Hypotheses: the `Sk.CTL`
pick (`hmove`) and the host `SRT.CTL` byte (`hhost`), plus the freeze sample.

The `flush` conjunct is the *effective* flush: on a frozen cycle the machine's
`flushReq` is not consumed (the frozen branch of `streamNext` never calls
`streamAuto`) and the cut's `Stream.fl` gates by `!FRZ`, so both sides carry
`… && !frozen`.  On an unfrozen cycle the plain `flushReq = flush` form is
`streams_flush_live`. -/
theorem streams_ctl_combined (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (k : Fin 2)
    (hmove : (machStreamIn m k).ctlMove =
      (if strobe s pin (BitVec.ofNat 6 (51 + k.val))
        then some (gw s pin (BitVec.ofNat 6 (51 + k.val))).data.toNat else none))
    (hhost : (machStreamIn m k).hCtl =
      (if hwIsSome s "SRT" k.val "CTL" then some (hwData s).toNat else none))
    (hfrz : m.dbg.frz = (streamIn s pin k.val).frz) :
    ((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 0 ||
        Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 0) =
      (streamIn s pin k.val).rewind)
      ∧ (((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
          (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) && !m.dbg.frz) =
        ((streamIn s pin k.val).flush && !(streamIn s pin k.val).frz))
      ∧ (Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 7 =
        (streamIn s pin k.val).clrStarved) := by
  simp only [hmove, hhost, getD_ite_some, hfrz]
  exact streamCtl_combine (gw s pin (BitVec.ofNat 6 (51 + k.val))).data
    (strobe s pin (BitVec.ofNat 6 (51 + k.val))) (hwIsSome s "SRT" k.val "CTL")
    (hwData s) (streamIn s pin k.val).frz

/-- On an unfrozen cycle the machine's `flushReq` is the cut's `flush` (the
`!frozen` gate of `streamNext` and `Stream.fl`'s `!FRZ` are both inert). -/
theorem streams_flush_live (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (k : Fin 2)
    (hmove : (machStreamIn m k).ctlMove =
      (if strobe s pin (BitVec.ofNat 6 (51 + k.val))
        then some (gw s pin (BitVec.ofNat 6 (51 + k.val))).data.toNat else none))
    (hhost : (machStreamIn m k).hCtl =
      (if hwIsSome s "SRT" k.val "CTL" then some (hwData s).toNat else none))
    (hfrz : m.dbg.frz = (streamIn s pin k.val).frz)
    (hlive : m.dbg.frz = false) :
    (Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
        (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) =
      (streamIn s pin k.val).flush := by
  have h := (streams_ctl_combined s m pin k hmove hhost hfrz).2.1
  have hf : (streamIn s pin k.val).frz = false := by rw [← hfrz, hlive]
  rw [hlive, hf] at h
  simp only [Bool.not_false, Bool.true_and, Bool.and_true] at h
  rw [hlive]
  simp only [Bool.not_false, Bool.true_and]
  exact h

/-! ## 5. Round 2: the three side hypotheses of `streams_ctl_combined`

`HostPinWire.ltHw_eq`/`hwByte_eq` state the host-write bridge used below, but
that module cannot be imported here (it redeclares `bgetLE_lt`, already in
`CoreUnits`, which `MoveFabric` imports).  The three steps are re-derived
locally from `MemHostCfg.linkRel_cut`. -/

/-- The machine's host write of the cycle is the cut's `hwOf` (§9). -/
theorem ltHw_eq' (s : State) (m : Machine.State) (hrel : ChipRel s m) (hinv : Inv s) :
    ltHw m = hwOf s := by
  have hl := linkRel_cut s m hinv hrel
  simp only [ltHw, hwOf]
  rw [← hl.wr, ← hl.addr]
  by_cases hw : s.hostCmd.wr = true
  · rw [if_pos hw, if_pos hw, hl.wdata hw]
  · rw [if_neg hw, if_neg hw]

/-- The value of a located host write byte is the write data byte. -/
theorem hwAt_val' (s : State) (blk : String) (inst : Nat) (reg : String) (j v : Nat)
    (h : Machine.Util.hwAt (hwOf s) blk inst reg = some (j, v)) :
    v = s.hostCmd.wdata.toNat := by
  cases hw : s.hostCmd.wr
  · simp [hwOf, hw, Machine.Util.hwAt] at h
  · simp only [hwOf, hw, if_pos rfl] at h
    unfold Machine.Util.hwAt at h
    cases hl : Machine.hostLocate s.hostCmd.addr.toNat with
    | none => simp [hl] at h
    | some loc =>
      rw [hl] at h
      simp only [if_true] at h
      by_cases hc : (loc.blk == blk && loc.inst == inst && loc.reg == reg) = true
      · rw [if_pos hc] at h
        have h2 := congrArg Prod.snd (Option.some.inj h)
        exact h2.symm
      · rw [if_neg hc] at h
        exact absurd h (by simp)

/-- A one-byte host write read through `hwByte` is `some` exactly under its
`hwAt` locator test, with the write data byte. -/
theorem hwByte_eq' (s : State) (blk : String) (inst : Nat) (reg : String) :
    Machine.Util.hwByte (hwOf s) blk inst reg =
      (if (Machine.Util.hwAt (hwOf s) blk inst reg).isSome then
        some s.hostCmd.wdata.toNat else none) := by
  unfold Machine.Util.hwByte
  cases h : Machine.Util.hwAt (hwOf s) blk inst reg with
  | none => simp
  | some pv =>
    obtain ⟨j, v⟩ := pv
    rw [show v = s.hostCmd.wdata.toNat from hwAt_val' s blk inst reg j v h]
    simp

/-- The `Sk.CTL k` payload test on the decoded destination. -/
def sCtlUnit (k : Fin 2) : Machine.DstOp → Option Unit
  | .sCtl j => if j == k.val then some () else none
  | _ => none

/-- **The `Fam.stream k` payload instance for `S*.CTL`** (the `S*.ADV` twin):
the machine's `.sCtl k` test is the cut's group test conjoined with the code test
`dst == 51 + k`. -/
theorem hPQ_stream_ctl (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    ∀ d, d < 64 → sCtlUnit k (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) then
        (if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (51 + k.val) then some () else none)
       else none) := by
  intro d hd
  have hpay := hT.payload (.stream k.val) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = true
  · have hfam : famIn (.stream k.val) (Machine.dstOp d) = true := by rw [← hpay, hg]
    rw [if_pos hg]
    cases h : Machine.dstOp d with
    | sCtl j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd51 : d = 51 + k.val := by simpa [hj] using hC.sCtl d hd j h
      rw [hd51]
      simp [sCtlUnit, hj]
    | sAdv j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd47 : d = 47 + k.val := by simpa [hj] using hC.sAdv d hd j h
      rw [hd47, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sCtlUnit]
    | sRx j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd49 : d = 49 + k.val := by simpa [hj] using hC.sRx d hd j h
      rw [hd49, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sCtlUnit]
    | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
  · rw [if_neg (by simpa using hg)]
    by_cases hP : sCtlUnit k (Machine.dstOp d) = some ()
    · exfalso
      cases h : Machine.dstOp d with
      | sCtl j =>
        rw [h] at hP
        have hj : j = k.val := by
          by_cases hjk : j = k.val
          · exact hjk
          · simp [sCtlUnit, hjk] at hP
        have hd51 : d = 51 + k.val := by simpa [hj] using hC.sCtl d hd j h
        rw [hd51] at hg
        rw [show Moves.dgTable (BitVec.ofNat 6 (51 + k.val)) = famG (.stream k.val) from by
          rcases (by have := k.isLt; omega : k.val = 0 ∨ k.val = 1) with hk | hk <;>
            rw [hk] <;> decide] at hg
        exact absurd hg (by simp)
      | _ => rw [h] at hP; exact absurd hP (by simp [sCtlUnit])
    · cases h : sCtlUnit k (Machine.dstOp d) with
      | none => rfl
      | some u => cases u; exact absurd h hP

/-- **`StreamWire.input`'s `ctlMove` field is the `Sk.CTL` group pick.**  The
machine's move byte is `gw (51+k)`'s data when the `Sk.CTL k` strobe fires and
`none` otherwise. -/
theorem streams_ctlMove_pick (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    (machStreamIn m k).ctlMove =
      (if strobe s pin (BitVec.ofNat 6 (51 + k.val))
        then some (gw s pin (BitVec.ofNat 6 (51 + k.val))).data.toNat else none) := by
  have hpq := hPQ_stream_ctl hT hC k
  have hscan : (mWs m pin).findSome? (fun mv => (sCtlUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v))) =
      (if (streamPick s pin k).we then
        (if (streamPick s pin k).dst == BitVec.ofNat 6 (51 + k.val) then some () else none).map
          (fun a => (a, (streamPick s pin k).data.toNat)) else none) :=
    pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
      (sCtlUnit k) (fun dst => if dst == BitVec.ofNat 6 (51 + k.val) then some () else none)
      (fun v => v) (famG (.stream k.val))
      (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq
  have hmach : (machStreamIn m k).ctlMove =
      (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .sCtl j => if j == k.val then some mv.v else none
        | _ => none) := by
    rw [machStreamIn_ctlMove m k, machWs_eq_mWs' m pin]
  rw [hmach]
  have hval : (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .sCtl j => if j == k.val then some mv.v else none
        | _ => none) =
      (if (streamPick s pin k).we &&
          ((streamPick s pin k).dst == BitVec.ofNat 6 (51 + k.val))
        then some (streamPick s pin k).data.toNat else none) := by
    rw [findSome?_congr (g := fun mv => ((sCtlUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2)) (fun mv => ?_)]
    · rw [findSome?_snd_map, hscan]
      by_cases hw : (streamPick s pin k).we = true <;>
        by_cases hb : ((streamPick s pin k).dst == BitVec.ofNat 6 (51 + k.val)) = true <;>
        simp [hw, hb]
    · cases h : Machine.dstOp mv.dst with
      | sCtl j =>
        by_cases hj : (j == k.val) = true <;> simp [sCtlUnit, hj]
      | _ => simp [sCtlUnit]
  rw [hval]
  rw [show strobe s pin (BitVec.ofNat 6 (51 + k.val)) = Strobes.opg (mvEn s pin) (mvGrp s pin)
      (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (51 + k.val)))
      (BitVec.ofNat 6 (51 + k.val)) from rfl,
    Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (Moves.dgTable (BitVec.ofNat 6 (51 + k.val))) (BitVec.ofNat 6 (51 + k.val)),
    dgTable_stream_ctl k, gw_stream_ctl s pin k]
  rfl

/-- **`StreamWire.input`'s `hCtl` field is the cut's host decode.**  The
machine's `hwByte` of the host write is the cut's `SRT.CTL` byte strobe/value
pair (`hwIsSome`/`hwData`), through the host link (`ltHw_eq'`) and the canonical
abstraction (`hwByte_eq'`). -/
theorem streams_hCtl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (k : Fin 2) :
    (machStreamIn m k).hCtl =
      (if hwIsSome s "SRT" k.val "CTL" then some (hwData s).toNat else none) := by
  show Machine.Util.hwByte (machHw m) "SRT" k.val "CTL" = _
  have hhw : machHw m = hwOf s := by
    rw [machHw, hostNext_hw]
    exact ltHw_eq' s m hrel hinv
  rw [hhw, hwByte_eq']
  rfl

/-- **The cycle's freeze sample.**  `ChipRel`'s debug relation gives
`m.dbg.frz = s.freeze.frz`, which is the cut's `streamIn.frz`. -/
theorem streams_frz (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    m.dbg.frz = (streamIn s pin k.val).frz := by
  rw [dbgRel_frz hrel.dbg]
  rfl

/-- **The stream control inputs are the machine's combined control bus** (no
side hypotheses: the pick, the host byte and the freeze sample are discharged
above).  See `streams_ctl_combined` for the statement's reading and the
frozen-flush note. -/
theorem streams_ctl_combined' (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) :
    ∀ k : Fin 2,
    ((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 0 ||
        Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 0) =
      (streamIn s pin k.val).rewind)
      ∧ (((Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
          (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) && !m.dbg.frz) =
        ((streamIn s pin k.val).flush && !(streamIn s pin k.val).frz))
      ∧ (Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 7 =
        (streamIn s pin k.val).clrStarved) := by
  intro k
  exact streams_ctl_combined s m pin k
    (streams_ctlMove_pick s m pin hrel hinv hJGTab hbus hgrp hkind hT hC k)
    (streams_hCtl s m pin hrel hinv k)
    (streams_frz s m pin hrel k)

/-- The unfrozen-cycle form of `streams_ctl_combined'`. -/
theorem streams_flush_live' (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2)
    (hlive : m.dbg.frz = false) :
    (Machine.Util.nbit ((machStreamIn m k).ctlMove.getD 0) 1 ||
        (!m.dbg.frz && Machine.Util.nbit ((machStreamIn m k).hCtl.getD 0) 1)) =
      (streamIn s pin k.val).flush :=
  streams_flush_live s m pin k
    (streams_ctlMove_pick s m pin hrel hinv hJGTab hbus hgrp hkind hT hC k)
    (streams_hCtl s m pin hrel hinv k)
    (streams_frz s m pin hrel k) hlive

end Metronome.ChipCut.Discharge.StreamMoveWire
