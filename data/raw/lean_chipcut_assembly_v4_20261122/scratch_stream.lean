import Metronome.Stream
import Metronome.CoreCtl

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open Metronome

def szIn2 (gnt frz : Bool) : Stream.Input where
  resetN := true
  frz := frz
  frzd := false
  capEn := false
  capPush := false
  capRec := 0
  replayEn := false
  replayApply := false
  replayLate := false
  cfgMode := false
  cfgMsb := false
  cfgStart := 0
  cfgLen := 1
  cfgMark := 0
  adv := false
  rxWe := false
  rxBit := false
  rewind := false
  flush := false
  clrStarved := false
  gnt := gnt
  rdata := 0

example : (Stream.rqNext true Stream.resetState (szIn2 false false)) = true := by decide

example : (Stream.step true Stream.resetState (szIn2 false false)).rq = true := by decide

example : (Stream.step true Stream.resetState (szIn2 false false)).rq = true := by rfl

example : (Stream.step true Stream.resetState (szIn2 false false)).rq = true := by
  simp [Stream.step, Stream.rqNext]
