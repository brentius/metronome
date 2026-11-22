import Metronome.Stream

-- Generated from Yosys RTLIL by `stream_check.py`.  Both instantiations of
-- `src/md2_stream.v` are cut: S0 (`CAP = 1`, edge capture and edge replay) and
-- S1 (`CAP = 0`).  Every state register and every output cone is extracted
-- fail-closed from the elaborated cells; `gnt`, the RAM read word, the
-- capture/replay control signals and `frz`/`frzd` are per-cycle inputs.
-- RTL snapshot SHA-256: 609a4cbf0639094eaf786eb60d07b372ae58a79b5e5803c28a8225964c44287f

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Metronome.Stream

namespace CapOne

-- g_s[0].u: the elaborated `md2_stream` with CAP = true.
-- Register states and combinational cells: 14 registers, 268 gates.
-- RTL snapshot SHA-256: 609a4cbf0639094eaf786eb60d07b372ae58a79b5e5803c28a8225964c44287f

/-- The `CAP` argument of this variant. -/
abbrev capValue : Bool := true

/-- Next state of `pos`. -/
def rtlPos (state : State) (input : Input) : BitVec 12 :=
  let rtlPos0 := state.rq && input.gnt
  let rtlPos1 := (state.pos + (4 : BitVec 12))
  let rtlPos2 := if rtlPos0 then rtlPos1 else state.pos
  let rtlPos3 := !input.replayEn
  let rtlPos4 := input.capEn && rtlPos3
  let rtlPos5 := rtlPos4 && input.capPush
  let rtlPos6 := (state.pos == input.cfgLen)
  let rtlPos7 := !rtlPos6
  let rtlPos8 := rtlPos5 && rtlPos7
  let rtlPos9 := !input.gnt
  let rtlPos10 := state.pv && rtlPos9
  let rtlPos11 := !rtlPos10
  let rtlPos12 := rtlPos8 && rtlPos11
  let rtlPos13 := (state.pos + (4 : BitVec 12))
  let rtlPos14 := if rtlPos12 then rtlPos13 else state.pos
  let rtlPos15 := !input.cfgMode
  let rtlPos16 := !rtlPos4
  let rtlPos17 := rtlPos15 && rtlPos16
  let rtlPos18 := !input.replayEn
  let rtlPos19 := rtlPos17 && rtlPos18
  let rtlPos20 := !state.cv
  let rtlPos21 := rtlPos20 && state.wv
  let rtlPos22 := rtlPos19 && input.adv
  let rtlPos23 := !rtlPos6
  let rtlPos24 := rtlPos22 && rtlPos23
  let rtlPos25 := rtlPos24 && state.cv
  let rtlPos26 := (state.bidx == (7 : BitVec 3))
  let rtlPos27 := (state.pos + (1 : BitVec 12))
  let rtlPos28 := if rtlPos26 then rtlPos27 else state.pos
  let rtlPos29 := if rtlPos25 then rtlPos28 else state.pos
  let rtlPos30 := if rtlPos21 then state.pos else rtlPos29
  let rtlPos31 := !rtlPos4
  let rtlPos32 := input.cfgMode && rtlPos31
  let rtlPos33 := !input.replayEn
  let rtlPos34 := rtlPos32 && rtlPos33
  let rtlPos35 := rtlPos34 && input.rxWe
  let rtlPos36 := !rtlPos6
  let rtlPos37 := rtlPos35 && rtlPos36
  let rtlPos38 := rtlPos37 && rtlPos26
  let rtlPos39 := rtlPos34 && input.flush
  let rtlPos40 := !rtlPos6
  let rtlPos41 := rtlPos39 && rtlPos40
  let rtlPos42 := !input.frz
  let rtlPos43 := rtlPos41 && rtlPos42
  let rtlPos44 := (state.bidx != 0)
  let rtlPos45 := rtlPos44 || rtlPos37
  let rtlPos46 := rtlPos43 && rtlPos45
  let rtlPos47 := rtlPos38 || rtlPos46
  let rtlPos48 := (state.pos + (1 : BitVec 12))
  let rtlPos49 := if rtlPos47 then rtlPos48 else state.pos
  let rtlPos50 := if rtlPos19 then rtlPos30 else rtlPos49
  let rtlPos51 := if rtlPos4 then rtlPos14 else rtlPos50
  let rtlPos52 := if input.replayEn then rtlPos2 else rtlPos51
  let rtlPos53 := if input.frz then state.pos else rtlPos52
  let rtlPos54 := if input.rewind then (0 : BitVec 12) else rtlPos53
  let rtlPos55 := if input.resetN then rtlPos54 else (0 : BitVec 12)
  rtlPos55

/-- Next state of `bidx`. -/
def rtlBidx (state : State) (input : Input) : BitVec 3 :=
  let rtlBidx0 := !input.replayEn
  let rtlBidx1 := input.capEn && rtlBidx0
  let rtlBidx2 := !input.cfgMode
  let rtlBidx3 := !rtlBidx1
  let rtlBidx4 := rtlBidx2 && rtlBidx3
  let rtlBidx5 := !input.replayEn
  let rtlBidx6 := rtlBidx4 && rtlBidx5
  let rtlBidx7 := !state.cv
  let rtlBidx8 := rtlBidx7 && state.wv
  let rtlBidx9 := rtlBidx6 && input.adv
  let rtlBidx10 := (state.pos == input.cfgLen)
  let rtlBidx11 := !rtlBidx10
  let rtlBidx12 := rtlBidx9 && rtlBidx11
  let rtlBidx13 := rtlBidx12 && state.cv
  let rtlBidx14 := (state.bidx == (7 : BitVec 3))
  let rtlBidx15 := (state.bidx + (1 : BitVec 3))
  let rtlBidx16 := if rtlBidx14 then (0 : BitVec 3) else rtlBidx15
  let rtlBidx17 := if rtlBidx13 then rtlBidx16 else state.bidx
  let rtlBidx18 := if rtlBidx8 then state.bidx else rtlBidx17
  let rtlBidx19 := !rtlBidx1
  let rtlBidx20 := input.cfgMode && rtlBidx19
  let rtlBidx21 := !input.replayEn
  let rtlBidx22 := rtlBidx20 && rtlBidx21
  let rtlBidx23 := rtlBidx22 && input.rxWe
  let rtlBidx24 := !rtlBidx10
  let rtlBidx25 := rtlBidx23 && rtlBidx24
  let rtlBidx26 := rtlBidx25 && rtlBidx14
  let rtlBidx27 := rtlBidx22 && input.flush
  let rtlBidx28 := !rtlBidx10
  let rtlBidx29 := rtlBidx27 && rtlBidx28
  let rtlBidx30 := !input.frz
  let rtlBidx31 := rtlBidx29 && rtlBidx30
  let rtlBidx32 := (state.bidx != 0)
  let rtlBidx33 := rtlBidx32 || rtlBidx25
  let rtlBidx34 := rtlBidx31 && rtlBidx33
  let rtlBidx35 := rtlBidx26 || rtlBidx34
  let rtlBidx36 := !rtlBidx35
  let rtlBidx37 := rtlBidx25 && rtlBidx36
  let rtlBidx38 := (state.bidx + (1 : BitVec 3))
  let rtlBidx39 := if rtlBidx37 then rtlBidx38 else state.bidx
  let rtlBidx40 := if rtlBidx35 then (0 : BitVec 3) else rtlBidx39
  let rtlBidx41 := if rtlBidx6 then rtlBidx18 else rtlBidx40
  let rtlBidx42 := if rtlBidx1 then state.bidx else rtlBidx41
  let rtlBidx43 := if input.replayEn then state.bidx else rtlBidx42
  let rtlBidx44 := if input.frz then state.bidx else rtlBidx43
  let rtlBidx45 := if input.rewind then (0 : BitVec 3) else rtlBidx44
  let rtlBidx46 := if input.resetN then rtlBidx45 else (0 : BitVec 3)
  rtlBidx46

/-- Next state of `ba`. -/
def rtlBa (state : State) (input : Input) : BitVec 11 :=
  let rtlBa0 := state.rq && input.gnt
  let rtlBa1 := (state.ba + (4 : BitVec 11))
  let rtlBa2 := if rtlBa0 then rtlBa1 else state.ba
  let rtlBa3 := !input.replayEn
  let rtlBa4 := input.capEn && rtlBa3
  let rtlBa5 := state.pv && input.gnt
  let rtlBa6 := (state.ba + (1 : BitVec 11))
  let rtlBa7 := if rtlBa5 then rtlBa6 else state.ba
  let rtlBa8 := !input.cfgMode
  let rtlBa9 := !rtlBa4
  let rtlBa10 := rtlBa8 && rtlBa9
  let rtlBa11 := !input.replayEn
  let rtlBa12 := rtlBa10 && rtlBa11
  let rtlBa13 := !state.cv
  let rtlBa14 := rtlBa13 && state.wv
  let rtlBa15 := (state.ba + (1 : BitVec 11))
  let rtlBa16 := rtlBa12 && input.adv
  let rtlBa17 := (state.pos == input.cfgLen)
  let rtlBa18 := !rtlBa17
  let rtlBa19 := rtlBa16 && rtlBa18
  let rtlBa20 := rtlBa19 && state.cv
  let rtlBa21 := (state.bidx == (7 : BitVec 3))
  let rtlBa22 := (state.ba + (1 : BitVec 11))
  let rtlBa23 := if state.wv then rtlBa22 else state.ba
  let rtlBa24 := if rtlBa21 then rtlBa23 else state.ba
  let rtlBa25 := if rtlBa20 then rtlBa24 else state.ba
  let rtlBa26 := if rtlBa14 then rtlBa15 else rtlBa25
  let rtlBa27 := state.pv && input.gnt
  let rtlBa28 := (state.ba + (1 : BitVec 11))
  let rtlBa29 := if rtlBa27 then rtlBa28 else state.ba
  let rtlBa30 := if rtlBa12 then rtlBa26 else rtlBa29
  let rtlBa31 := if rtlBa4 then rtlBa7 else rtlBa30
  let rtlBa32 := if input.replayEn then rtlBa2 else rtlBa31
  let rtlBa33 := if input.frz then state.ba else rtlBa32
  let rtlBa34 := if input.rewind then input.cfgStart else rtlBa33
  let rtlBa35 := if input.resetN then rtlBa34 else (0 : BitVec 11)
  rtlBa35

/-- Next state of `cur`. -/
def rtlCur (state : State) (input : Input) : BitVec 8 :=
  let rtlCur0 := !input.replayEn
  let rtlCur1 := input.capEn && rtlCur0
  let rtlCur2 := !input.cfgMode
  let rtlCur3 := !rtlCur1
  let rtlCur4 := rtlCur2 && rtlCur3
  let rtlCur5 := !input.replayEn
  let rtlCur6 := rtlCur4 && rtlCur5
  let rtlCur7 := !state.cv
  let rtlCur8 := rtlCur7 && state.wv
  let rtlCur9 := (BitVec.truncate 8 (BitVec.ushiftRight state.wb ((8 * ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0))).toNat) + 0)))
  let rtlCur10 := rtlCur6 && input.adv
  let rtlCur11 := (state.pos == input.cfgLen)
  let rtlCur12 := !rtlCur11
  let rtlCur13 := rtlCur10 && rtlCur12
  let rtlCur14 := rtlCur13 && state.cv
  let rtlCur15 := (state.bidx == (7 : BitVec 3))
  let rtlCur16 := (BitVec.truncate 8 (BitVec.ushiftRight state.wb ((8 * ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0))).toNat) + 0)))
  let rtlCur17 := if state.wv then rtlCur16 else state.cur
  let rtlCur18 := if rtlCur15 then rtlCur17 else state.cur
  let rtlCur19 := if rtlCur14 then rtlCur18 else state.cur
  let rtlCur20 := if rtlCur8 then rtlCur9 else rtlCur19
  let rtlCur21 := !rtlCur1
  let rtlCur22 := input.cfgMode && rtlCur21
  let rtlCur23 := !input.replayEn
  let rtlCur24 := rtlCur22 && rtlCur23
  let rtlCur25 := rtlCur24 && input.rxWe
  let rtlCur26 := !rtlCur11
  let rtlCur27 := rtlCur25 && rtlCur26
  let rtlCur28 := rtlCur27 && rtlCur15
  let rtlCur29 := rtlCur24 && input.flush
  let rtlCur30 := !rtlCur11
  let rtlCur31 := rtlCur29 && rtlCur30
  let rtlCur32 := !input.frz
  let rtlCur33 := rtlCur31 && rtlCur32
  let rtlCur34 := (state.bidx != 0)
  let rtlCur35 := rtlCur34 || rtlCur27
  let rtlCur36 := rtlCur33 && rtlCur35
  let rtlCur37 := rtlCur28 || rtlCur36
  let rtlCur38 := !rtlCur37
  let rtlCur39 := rtlCur27 && rtlCur38
  let rtlCur40 := (~~~state.bidx)
  let rtlCur41 := if input.cfgMsb then rtlCur40 else state.bidx
  let rtlCur42 := rtlCur27 && input.rxBit
  let rtlCur43 := (((if rtlCur42 then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) <<< (rtlCur41).toNat)
  let rtlCur44 := (state.cur ||| rtlCur43)
  let rtlCur45 := if rtlCur39 then rtlCur44 else state.cur
  let rtlCur46 := if rtlCur37 then (0 : BitVec 8) else rtlCur45
  let rtlCur47 := if rtlCur6 then rtlCur20 else rtlCur46
  let rtlCur48 := if rtlCur1 then state.cur else rtlCur47
  let rtlCur49 := if input.replayEn then state.cur else rtlCur48
  let rtlCur50 := if input.frz then state.cur else rtlCur49
  let rtlCur51 := if input.rewind then (0 : BitVec 8) else rtlCur50
  let rtlCur52 := if input.resetN then rtlCur51 else (0 : BitVec 8)
  rtlCur52

/-- Next state of `cv`. -/
def rtlCv (state : State) (input : Input) : Bool :=
  let rtlCv0 := !input.replayEn
  let rtlCv1 := input.capEn && rtlCv0
  let rtlCv2 := !input.cfgMode
  let rtlCv3 := !rtlCv1
  let rtlCv4 := rtlCv2 && rtlCv3
  let rtlCv5 := !input.replayEn
  let rtlCv6 := rtlCv4 && rtlCv5
  let rtlCv7 := !state.cv
  let rtlCv8 := rtlCv7 && state.wv
  let rtlCv9 := rtlCv6 && input.adv
  let rtlCv10 := (state.pos == input.cfgLen)
  let rtlCv11 := !rtlCv10
  let rtlCv12 := rtlCv9 && rtlCv11
  let rtlCv13 := rtlCv12 && state.cv
  let rtlCv14 := (state.bidx == (7 : BitVec 3))
  let rtlCv15 := if state.wv then state.cv else false
  let rtlCv16 := if rtlCv14 then rtlCv15 else state.cv
  let rtlCv17 := if rtlCv13 then rtlCv16 else state.cv
  let rtlCv18 := if rtlCv8 then true else rtlCv17
  let rtlCv19 := if rtlCv6 then rtlCv18 else state.cv
  let rtlCv20 := if rtlCv1 then state.cv else rtlCv19
  let rtlCv21 := if input.replayEn then state.cv else rtlCv20
  let rtlCv22 := if input.frz then state.cv else rtlCv21
  let rtlCv23 := if input.rewind then false else rtlCv22
  let rtlCv24 := if input.resetN then rtlCv23 else false
  rtlCv24

/-- Next state of `wb`. -/
def rtlWb (state : State) (input : Input) : BitVec 32 :=
  let rtlWb0 := !input.replayEn
  let rtlWb1 := input.capEn && rtlWb0
  let rtlWb2 := rtlWb1 && input.capPush
  let rtlWb3 := (state.pos == input.cfgLen)
  let rtlWb4 := !rtlWb3
  let rtlWb5 := rtlWb2 && rtlWb4
  let rtlWb6 := rtlWb1 && rtlWb5
  let rtlWb7 := !input.gnt
  let rtlWb8 := state.pv && rtlWb7
  let rtlWb9 := !rtlWb8
  let rtlWb10 := rtlWb6 && rtlWb9
  let rtlWb11 := !input.frz
  let rtlWb12 := rtlWb10 && rtlWb11
  let rtlWb13 := !input.cfgMode
  let rtlWb14 := !rtlWb1
  let rtlWb15 := rtlWb13 && rtlWb14
  let rtlWb16 := !input.replayEn
  let rtlWb17 := rtlWb15 && rtlWb16
  let rtlWb18 := rtlWb17 && state.ld
  let rtlWb19 := !input.frzd
  let rtlWb20 := rtlWb18 && rtlWb19
  let rtlWb21 := if rtlWb20 then input.rdata else state.wb
  let rtlWb22 := if rtlWb12 then input.capRec else rtlWb21
  let rtlWb23 := if input.replayApply then state.nv else state.wv
  let rtlWb24 := if input.replayApply then state.nb else rtlWb22
  let rtlWb25 := if input.frzd then state.nb else input.rdata
  let rtlWb26 := if rtlWb23 then rtlWb24 else rtlWb25
  let rtlWb27 := if state.ld then rtlWb26 else rtlWb24
  let rtlWb28 := if input.replayEn then rtlWb27 else rtlWb22
  let rtlWb29 := if input.frz then rtlWb22 else rtlWb28
  let rtlWb30 := if input.resetN then rtlWb29 else (0 : BitVec 32)
  rtlWb30

/-- Next state of `wv`. -/
def rtlWv (state : State) (input : Input) : Bool :=
  let rtlWv0 := if input.replayApply then state.nv else state.wv
  let rtlWv1 := if input.replayApply then state.nv else state.wv
  let rtlWv2 := if rtlWv0 then rtlWv1 else true
  let rtlWv3 := if state.ld then rtlWv2 else rtlWv1
  let rtlWv4 := !input.replayEn
  let rtlWv5 := input.capEn && rtlWv4
  let rtlWv6 := !input.cfgMode
  let rtlWv7 := !rtlWv5
  let rtlWv8 := rtlWv6 && rtlWv7
  let rtlWv9 := !input.replayEn
  let rtlWv10 := rtlWv8 && rtlWv9
  let rtlWv11 := !state.cv
  let rtlWv12 := rtlWv11 && state.wv
  let rtlWv13 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0)) == (3 : BitVec 2))
  let rtlWv14 := if state.ld then true else state.wv
  let rtlWv15 := if rtlWv13 then false else rtlWv14
  let rtlWv16 := rtlWv10 && input.adv
  let rtlWv17 := (state.pos == input.cfgLen)
  let rtlWv18 := !rtlWv17
  let rtlWv19 := rtlWv16 && rtlWv18
  let rtlWv20 := rtlWv19 && state.cv
  let rtlWv21 := (state.bidx == (7 : BitVec 3))
  let rtlWv22 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0)) == (3 : BitVec 2))
  let rtlWv23 := if rtlWv22 then false else rtlWv14
  let rtlWv24 := if state.wv then rtlWv23 else rtlWv14
  let rtlWv25 := if rtlWv21 then rtlWv24 else rtlWv14
  let rtlWv26 := if rtlWv20 then rtlWv25 else rtlWv14
  let rtlWv27 := if rtlWv12 then rtlWv15 else rtlWv26
  let rtlWv28 := if rtlWv10 then rtlWv27 else state.wv
  let rtlWv29 := if rtlWv5 then state.wv else rtlWv28
  let rtlWv30 := if input.replayEn then rtlWv3 else rtlWv29
  let rtlWv31 := if input.frz then state.wv else rtlWv30
  let rtlWv32 := if input.rewind then false else rtlWv31
  let rtlWv33 := if input.resetN then rtlWv32 else false
  rtlWv33

/-- Next state of `rq`. -/
def rtlRq (state : State) (input : Input) : Bool :=
  let rtlRq0 := state.rq && input.gnt
  let rtlRq1 := !state.rq
  let rtlRq2 := !state.ld
  let rtlRq3 := rtlRq1 && rtlRq2
  let rtlRq4 := (state.pos == input.cfgLen)
  let rtlRq5 := !rtlRq4
  let rtlRq6 := rtlRq3 && rtlRq5
  let rtlRq7 := state.wv && state.nv
  let rtlRq8 := !rtlRq7
  let rtlRq9 := rtlRq6 && rtlRq8
  let rtlRq10 := if rtlRq9 then true else state.rq
  let rtlRq11 := if rtlRq0 then false else rtlRq10
  let rtlRq12 := !input.replayEn
  let rtlRq13 := input.capEn && rtlRq12
  let rtlRq14 := !input.cfgMode
  let rtlRq15 := !rtlRq13
  let rtlRq16 := rtlRq14 && rtlRq15
  let rtlRq17 := !input.replayEn
  let rtlRq18 := rtlRq16 && rtlRq17
  let rtlRq19 := state.rq && input.gnt
  let rtlRq20 := !state.wv
  let rtlRq21 := !state.rq
  let rtlRq22 := rtlRq20 && rtlRq21
  let rtlRq23 := !state.ld
  let rtlRq24 := rtlRq22 && rtlRq23
  let rtlRq25 := if rtlRq24 then true else state.rq
  let rtlRq26 := if rtlRq19 then false else rtlRq25
  let rtlRq27 := if rtlRq18 then rtlRq26 else state.rq
  let rtlRq28 := if rtlRq13 then state.rq else rtlRq27
  let rtlRq29 := if input.replayEn then rtlRq11 else rtlRq28
  let rtlRq30 := if input.frz then state.rq else rtlRq29
  let rtlRq31 := if input.rewind then false else rtlRq30
  let rtlRq32 := if input.resetN then rtlRq31 else false
  rtlRq32

/-- Next state of `ld`. -/
def rtlLd (state : State) (input : Input) : Bool :=
  let rtlLd0 := state.rq && input.gnt
  let rtlLd1 := if state.ld then false else state.ld
  let rtlLd2 := if rtlLd0 then true else rtlLd1
  let rtlLd3 := !input.replayEn
  let rtlLd4 := input.capEn && rtlLd3
  let rtlLd5 := !input.cfgMode
  let rtlLd6 := !rtlLd4
  let rtlLd7 := rtlLd5 && rtlLd6
  let rtlLd8 := !input.replayEn
  let rtlLd9 := rtlLd7 && rtlLd8
  let rtlLd10 := state.rq && input.gnt
  let rtlLd11 := if state.ld then false else state.ld
  let rtlLd12 := if rtlLd10 then true else rtlLd11
  let rtlLd13 := if rtlLd9 then rtlLd12 else state.ld
  let rtlLd14 := if rtlLd4 then state.ld else rtlLd13
  let rtlLd15 := if input.replayEn then rtlLd2 else rtlLd14
  let rtlLd16 := if input.frz then state.ld else rtlLd15
  let rtlLd17 := if input.rewind then false else rtlLd16
  let rtlLd18 := if input.resetN then rtlLd17 else false
  rtlLd18

/-- Next state of `pend`. -/
def rtlPend (state : State) (input : Input) : BitVec 8 :=
  let rtlPend0 := !input.replayEn
  let rtlPend1 := input.capEn && rtlPend0
  let rtlPend2 := !input.cfgMode
  let rtlPend3 := !rtlPend1
  let rtlPend4 := rtlPend2 && rtlPend3
  let rtlPend5 := !input.replayEn
  let rtlPend6 := rtlPend4 && rtlPend5
  let rtlPend7 := !rtlPend1
  let rtlPend8 := input.cfgMode && rtlPend7
  let rtlPend9 := !input.replayEn
  let rtlPend10 := rtlPend8 && rtlPend9
  let rtlPend11 := rtlPend10 && input.rxWe
  let rtlPend12 := (state.pos == input.cfgLen)
  let rtlPend13 := !rtlPend12
  let rtlPend14 := rtlPend11 && rtlPend13
  let rtlPend15 := (state.bidx == (7 : BitVec 3))
  let rtlPend16 := rtlPend14 && rtlPend15
  let rtlPend17 := rtlPend10 && input.flush
  let rtlPend18 := !rtlPend12
  let rtlPend19 := rtlPend17 && rtlPend18
  let rtlPend20 := !input.frz
  let rtlPend21 := rtlPend19 && rtlPend20
  let rtlPend22 := (state.bidx != 0)
  let rtlPend23 := rtlPend22 || rtlPend14
  let rtlPend24 := rtlPend21 && rtlPend23
  let rtlPend25 := rtlPend16 || rtlPend24
  let rtlPend26 := !input.gnt
  let rtlPend27 := state.pv && rtlPend26
  let rtlPend28 := (~~~state.bidx)
  let rtlPend29 := if input.cfgMsb then rtlPend28 else state.bidx
  let rtlPend30 := rtlPend14 && input.rxBit
  let rtlPend31 := (((if rtlPend30 then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) <<< (rtlPend29).toNat)
  let rtlPend32 := (state.cur ||| rtlPend31)
  let rtlPend33 := if rtlPend27 then state.pend else rtlPend32
  let rtlPend34 := if rtlPend25 then rtlPend33 else state.pend
  let rtlPend35 := if rtlPend6 then state.pend else rtlPend34
  let rtlPend36 := if rtlPend1 then state.pend else rtlPend35
  let rtlPend37 := if input.replayEn then state.pend else rtlPend36
  let rtlPend38 := if input.frz then state.pend else rtlPend37
  let rtlPend39 := if input.resetN then rtlPend38 else (0 : BitVec 8)
  rtlPend39

/-- Next state of `pv`. -/
def rtlPv (state : State) (input : Input) : Bool :=
  let rtlPv0 := !input.replayEn
  let rtlPv1 := input.capEn && rtlPv0
  let rtlPv2 := rtlPv1 && input.capPush
  let rtlPv3 := (state.pos == input.cfgLen)
  let rtlPv4 := !rtlPv3
  let rtlPv5 := rtlPv2 && rtlPv4
  let rtlPv6 := !input.gnt
  let rtlPv7 := state.pv && rtlPv6
  let rtlPv8 := !rtlPv7
  let rtlPv9 := rtlPv5 && rtlPv8
  let rtlPv10 := state.pv && input.gnt
  let rtlPv11 := if rtlPv10 then false else state.pv
  let rtlPv12 := if rtlPv9 then true else rtlPv11
  let rtlPv13 := !input.cfgMode
  let rtlPv14 := !rtlPv1
  let rtlPv15 := rtlPv13 && rtlPv14
  let rtlPv16 := !input.replayEn
  let rtlPv17 := rtlPv15 && rtlPv16
  let rtlPv18 := !rtlPv1
  let rtlPv19 := input.cfgMode && rtlPv18
  let rtlPv20 := !input.replayEn
  let rtlPv21 := rtlPv19 && rtlPv20
  let rtlPv22 := rtlPv21 && input.rxWe
  let rtlPv23 := !rtlPv3
  let rtlPv24 := rtlPv22 && rtlPv23
  let rtlPv25 := (state.bidx == (7 : BitVec 3))
  let rtlPv26 := rtlPv24 && rtlPv25
  let rtlPv27 := rtlPv21 && input.flush
  let rtlPv28 := !rtlPv3
  let rtlPv29 := rtlPv27 && rtlPv28
  let rtlPv30 := !input.frz
  let rtlPv31 := rtlPv29 && rtlPv30
  let rtlPv32 := (state.bidx != 0)
  let rtlPv33 := rtlPv32 || rtlPv24
  let rtlPv34 := rtlPv31 && rtlPv33
  let rtlPv35 := rtlPv26 || rtlPv34
  let rtlPv36 := !input.gnt
  let rtlPv37 := state.pv && rtlPv36
  let rtlPv38 := state.pv && input.gnt
  let rtlPv39 := if rtlPv38 then false else state.pv
  let rtlPv40 := if rtlPv37 then rtlPv39 else true
  let rtlPv41 := if rtlPv35 then rtlPv40 else rtlPv39
  let rtlPv42 := if rtlPv17 then state.pv else rtlPv41
  let rtlPv43 := if rtlPv1 then rtlPv12 else rtlPv42
  let rtlPv44 := if input.replayEn then state.pv else rtlPv43
  let rtlPv45 := if input.frz then state.pv else rtlPv44
  let rtlPv46 := if input.rewind then false else rtlPv45
  let rtlPv47 := if input.resetN then rtlPv46 else false
  rtlPv47

/-- Next state of `starved`. -/
def rtlStarved (state : State) (input : Input) : Bool :=
  let rtlStarved0 := !input.cfgMode
  let rtlStarved1 := !input.replayEn
  let rtlStarved2 := input.capEn && rtlStarved1
  let rtlStarved3 := !rtlStarved2
  let rtlStarved4 := rtlStarved0 && rtlStarved3
  let rtlStarved5 := !input.replayEn
  let rtlStarved6 := rtlStarved4 && rtlStarved5
  let rtlStarved7 := rtlStarved6 && input.adv
  let rtlStarved8 := (state.pos == input.cfgLen)
  let rtlStarved9 := !rtlStarved8
  let rtlStarved10 := rtlStarved7 && rtlStarved9
  let rtlStarved11 := !state.cv
  let rtlStarved12 := (state.bidx == (7 : BitVec 3))
  let rtlStarved13 := !state.wv
  let rtlStarved14 := rtlStarved12 && rtlStarved13
  let rtlStarved15 := rtlStarved11 || rtlStarved14
  let rtlStarved16 := rtlStarved10 && rtlStarved15
  let rtlStarved17 := !rtlStarved2
  let rtlStarved18 := input.cfgMode && rtlStarved17
  let rtlStarved19 := !input.replayEn
  let rtlStarved20 := rtlStarved18 && rtlStarved19
  let rtlStarved21 := rtlStarved20 && input.rxWe
  let rtlStarved22 := !rtlStarved8
  let rtlStarved23 := rtlStarved21 && rtlStarved22
  let rtlStarved24 := rtlStarved23 && rtlStarved12
  let rtlStarved25 := rtlStarved20 && input.flush
  let rtlStarved26 := !rtlStarved8
  let rtlStarved27 := rtlStarved25 && rtlStarved26
  let rtlStarved28 := !input.frz
  let rtlStarved29 := rtlStarved27 && rtlStarved28
  let rtlStarved30 := (state.bidx != 0)
  let rtlStarved31 := rtlStarved30 || rtlStarved23
  let rtlStarved32 := rtlStarved29 && rtlStarved31
  let rtlStarved33 := rtlStarved24 || rtlStarved32
  let rtlStarved34 := rtlStarved20 && rtlStarved33
  let rtlStarved35 := rtlStarved34 && state.pv
  let rtlStarved36 := !input.gnt
  let rtlStarved37 := rtlStarved35 && rtlStarved36
  let rtlStarved38 := rtlStarved2 && input.capPush
  let rtlStarved39 := !rtlStarved8
  let rtlStarved40 := rtlStarved38 && rtlStarved39
  let rtlStarved41 := rtlStarved40 && state.pv
  let rtlStarved42 := !input.gnt
  let rtlStarved43 := rtlStarved41 && rtlStarved42
  let rtlStarved44 := rtlStarved37 || rtlStarved43
  let rtlStarved45 := rtlStarved16 || rtlStarved44
  let rtlStarved46 := input.replayEn && input.replayLate
  let rtlStarved47 := rtlStarved45 || rtlStarved46
  let rtlStarved48 := !input.clrStarved
  let rtlStarved49 := state.starved && rtlStarved48
  let rtlStarved50 := rtlStarved47 || rtlStarved49
  let rtlStarved51 := if input.resetN then rtlStarved50 else false
  rtlStarved51

/-- Next state of `nb`. -/
def rtlNb (state : State) (input : Input) : BitVec 32 :=
  let rtlNb0 := input.replayEn && state.ld
  let rtlNb1 := rtlNb0 && input.frz
  let rtlNb2 := !input.frzd
  let rtlNb3 := rtlNb1 && rtlNb2
  let rtlNb4 := if rtlNb3 then input.rdata else state.nb
  let rtlNb5 := if input.replayApply then state.nv else state.wv
  let rtlNb6 := if input.frzd then state.nb else input.rdata
  let rtlNb7 := if rtlNb5 then rtlNb6 else rtlNb4
  let rtlNb8 := if state.ld then rtlNb7 else rtlNb4
  let rtlNb9 := if input.replayEn then rtlNb8 else rtlNb4
  let rtlNb10 := if input.frz then rtlNb4 else rtlNb9
  let rtlNb11 := if input.resetN then rtlNb10 else (0 : BitVec 32)
  rtlNb11

/-- Next state of `nv`. -/
def rtlNv (state : State) (input : Input) : Bool :=
  let rtlNv0 := if input.replayApply then state.nv else state.wv
  let rtlNv1 := if input.replayApply then false else state.nv
  let rtlNv2 := if rtlNv0 then true else rtlNv1
  let rtlNv3 := if state.ld then rtlNv2 else rtlNv1
  let rtlNv4 := if input.replayEn then rtlNv3 else state.nv
  let rtlNv5 := if input.frz then state.nv else rtlNv4
  let rtlNv6 := if input.rewind then false else rtlNv5
  let rtlNv7 := if input.resetN then rtlNv6 else false
  rtlNv7

/-- Output `bit`. -/
def rtlBit (state : State) (input : Input) : Bool :=
  let rtlBit0 := !input.cfgMode
  let rtlBit1 := !input.replayEn
  let rtlBit2 := input.capEn && rtlBit1
  let rtlBit3 := !rtlBit2
  let rtlBit4 := rtlBit0 && rtlBit3
  let rtlBit5 := !input.replayEn
  let rtlBit6 := rtlBit4 && rtlBit5
  let rtlBit7 := rtlBit6 && state.cv
  let rtlBit8 := (state.pos == input.cfgLen)
  let rtlBit9 := !rtlBit8
  let rtlBit10 := rtlBit7 && rtlBit9
  let rtlBit11 := (~~~state.bidx)
  let rtlBit12 := if input.cfgMsb then rtlBit11 else state.bidx
  let rtlBit13 := (((BitVec.ushiftRight state.cur (rtlBit12).toNat) &&& (1 : BitVec 8)) != 0)
  let rtlBit14 := rtlBit10 && rtlBit13
  rtlBit14

/-- Output `byteOut`. -/
def rtlByteOut (state : State) (input : Input) : BitVec 8 :=
  let rtlByteOut0 := if input.cfgMode then state.pend else state.cur
  rtlByteOut0

/-- Output `gEnd`. -/
def rtlGEnd (state : State) (input : Input) : Bool :=
  let rtlGEnd0 := (state.pos == input.cfgLen)
  rtlGEnd0

/-- Output `gMark`. -/
def rtlGMark (state : State) (input : Input) : Bool :=
  let rtlGMark0 := (state.pos == input.cfgMark)
  let rtlGMark1 := (state.bidx == (0 : BitVec 3))
  let rtlGMark2 := rtlGMark0 && rtlGMark1
  rtlGMark2

/-- Output `gByte`. -/
def rtlGByte (state : State) (_input : Input) : Bool :=
  let rtlGByte0 := (state.bidx == (0 : BitVec 3))
  rtlGByte0

/-- Output `req`. -/
def rtlReq (state : State) (input : Input) : Bool :=
  let rtlReq0 := !input.replayEn
  let rtlReq1 := input.capEn && rtlReq0
  let rtlReq2 := input.cfgMode || rtlReq1
  let rtlReq3 := if rtlReq2 then state.pv else state.rq
  let rtlReq4 := if input.replayEn then state.rq else rtlReq3
  rtlReq4

/-- Output `reqWe`. -/
def rtlReqWe (_state : State) (input : Input) : Bool :=
  let rtlReqWe0 := !input.replayEn
  let rtlReqWe1 := input.capEn && rtlReqWe0
  let rtlReqWe2 := input.cfgMode || rtlReqWe1
  let rtlReqWe3 := !input.replayEn
  let rtlReqWe4 := rtlReqWe2 && rtlReqWe3
  rtlReqWe4

/-- Output `reqAddr`. -/
def rtlReqAddr (state : State) (_input : Input) : BitVec 11 :=
  state.ba

/-- Output `reqWdata`. -/
def rtlReqWdata (state : State) (_input : Input) : BitVec 8 :=
  state.pend

/-- Output `reqWord`. -/
def rtlReqWord (_state : State) (input : Input) : Bool :=
  let rtlReqWord0 := !input.replayEn
  let rtlReqWord1 := input.capEn && rtlReqWord0
  rtlReqWord1

/-- Output `reqWword`. -/
def rtlReqWword (state : State) (_input : Input) : BitVec 32 :=
  state.wb

/-- Output `replayValid`. -/
def rtlReplayValid (state : State) (input : Input) : Bool :=
  let rtlReplayValid0 := input.replayEn && state.wv
  rtlReplayValid0

/-- Output `replayWord`. -/
def rtlReplayWord (state : State) (_input : Input) : BitVec 32 :=
  state.wb

/-- The elaborated next state, field by field. -/
def rtlStep (state : State) (input : Input) : State :=
  ⟨rtlPos state input, rtlBidx state input, rtlBa state input, rtlCur state input, rtlCv state input, rtlWb state input, rtlWv state input, rtlRq state input, rtlLd state input, rtlPend state input, rtlPv state input, rtlStarved state input, rtlNb state input, rtlNv state input⟩

/-- The elaborated combinational outputs. -/
def rtlOut (state : State) (input : Input) : Out :=
  ⟨rtlBit state input, rtlByteOut state input, rtlGEnd state input, rtlGMark state input, rtlGByte state input, rtlReq state input, rtlReqWe state input, rtlReqAddr state input, rtlReqWdata state input, rtlReqWord state input, rtlReqWword state input, rtlReplayValid state input, rtlReplayWord state input⟩

/-! ## The extracted transition is the specification

`rtlStep` and `rtlOut` above are generated from the elaborated `md2_stream`
cells; the right-hand sides are `Metronome.Stream`'s equations at this variant's
`CAP` (true).  Each field is proved on its own cone, so `bv_decide` never sees
the whole state at once. -/

/-- Unfold the specification's equations and close the field equality.

The extracted definition is unfolded by each theorem first, so a proof only ever
sees its own cone.  The full `simp` after the unfolding normalises the `Bool`
guards (`true && x`, a negated `RESET_N`, an `if` with swapped branches) so that
`bv_decide` bit-blasts the residual instead of abstracting an `if` expression. -/
macro "spec_close" : tactic =>
  `(tactic| (simp only [step, out, posNext, bidxNext, baNext, curNext, cvNext,
    wbNext, wvNext, rqNext, ldNext, pendNext, pvNext, starvedNext, nbNext, nvNext,
    advT, starveTx, starveRx, starveEvent, push, done, bitin, fl, endC, last,
    txMode, rxMode, cen, rpl, occupied, landing, lb, bsel, nsh, bitAt, bitOut, byteOut,
    bitOut, gEnd, gMark, gByte, req, reqWe, reqAddr, reqWdata, reqWord, reqWword,
    replayValid, replayWord, State.mk.injEq, Out.mk.injEq] at * <;>
    ((try simp) <;>
     (repeat (first | rfl | bv_decide | (split <;> simp_all) | contradiction)))))

/-! ### Next state, field by field -/

/-- The extracted `POS` next state is §6.3's. -/
theorem rtlPos_eq (state : State) (input : Input) :
    (rtlStep state input).pos = (step capValue state input).pos := by
  simp only [rtlStep, rtlPos]
  spec_close

/-- The extracted `BIDX` next state is §6.3's. -/
theorem rtlBidx_eq (state : State) (input : Input) :
    (rtlStep state input).bidx = (step capValue state input).bidx := by
  simp only [rtlStep, rtlBidx]
  spec_close

/-- The extracted `BA` next state is §6.3's (byte address steps of 1, §12.4's
word write of 4 and §13.2's whole-word read of 4). -/
theorem rtlBa_eq (state : State) (input : Input) :
    (rtlStep state input).ba = (step capValue state input).ba := by
  simp only [rtlStep, rtlBa]
  spec_close

/-- The extracted `CUR` next state is §6.3's: `LB` from `WB` in transmit, the
assembly register in receive. -/
theorem rtlCur_eq (state : State) (input : Input) :
    (rtlStep state input).cur = (step capValue state input).cur := by
  simp only [rtlStep, rtlCur]
  spec_close

/-- The extracted `CV` next state is §6.3's. -/
theorem rtlCv_eq (state : State) (input : Input) :
    (rtlStep state input).cv = (step capValue state input).cv := by
  simp only [rtlStep, rtlCv]
  spec_close

/-- The extracted `WB` next state is §6.3's lookahead load, §12.3's landing
exception, §12.4's record and §13.2's two-deep buffer. -/
theorem rtlWb_eq (state : State) (input : Input) :
    (rtlStep state input).wb = (step capValue state input).wb := by
  simp only [rtlStep, rtlWb]
  spec_close

/-- The extracted `WV` next state is §6.3's. -/
theorem rtlWv_eq (state : State) (input : Input) :
    (rtlStep state input).wv = (step capValue state input).wv := by
  simp only [rtlStep, rtlWv]
  spec_close

/-- The extracted `RQ` next state is §6.3's request rule and §13.2's. -/
theorem rtlRq_eq (state : State) (input : Input) :
    (rtlStep state input).rq = (step capValue state input).rq := by
  simp only [rtlStep, rtlRq]
  spec_close

/-- The extracted `LD` next state is §6.3's. -/
theorem rtlLd_eq (state : State) (input : Input) :
    (rtlStep state input).ld = (step capValue state input).ld := by
  simp only [rtlStep, rtlLd]
  spec_close

/-- The extracted `PEND` next state is §6.3's, including the drop when a byte
still waits. -/
theorem rtlPend_eq (state : State) (input : Input) :
    (rtlStep state input).pend = (step capValue state input).pend := by
  simp only [rtlStep, rtlPend]
  spec_close

/-- The extracted `PV` next state is §6.3's. -/
theorem rtlPv_eq (state : State) (input : Input) :
    (rtlStep state input).pv = (step capValue state input).pv := by
  simp only [rtlStep, rtlPv]
  spec_close

/-- The extracted sticky `STARVED` next state is §6.3's, including §13.2's
`late`. -/
theorem rtlStarved_eq (state : State) (input : Input) :
    (rtlStep state input).starved = (step capValue state input).starved := by
  simp only [rtlStep, rtlStarved]
  spec_close

/-- The extracted second replay buffer slot `NB` is §13.2's (inert for a
`CAP = 0` stream). -/
theorem rtlNb_eq (state : State) (input : Input) :
    (rtlStep state input).nb = (step capValue state input).nb := by
  simp only [rtlStep, rtlNb]
  spec_close

/-- The extracted second replay buffer flag `NV` is §13.2's. -/
theorem rtlNv_eq (state : State) (input : Input) :
    (rtlStep state input).nv = (step capValue state input).nv := by
  simp only [rtlStep, rtlNv]
  spec_close

/-! ### Outputs, field by field -/

/-- `Sk.BIT` is §6.3's `CV && !END && CUR[b]`, disabled in receive, capture and
replay. -/
theorem rtlBit_eq (state : State) (input : Input) :
    rtlBit state input = bitOut capValue state input := by
  simp only [rtlBit]
  spec_close

/-- Source `Sk.BYTE` is `CUR` in transmit and `PEND` in receive. -/
theorem rtlByteOut_eq (state : State) (input : Input) :
    rtlByteOut state input = byteOut capValue state input := by
  simp only [rtlByteOut]
  spec_close

/-- Guard `Sk.END` compares `POS` with the live `LEN`. -/
theorem rtlGEnd_eq (state : State) (input : Input) :
    rtlGEnd state input = gEnd state input := by
  simp only [rtlGEnd]
  spec_close

/-- Guard `Sk.MARK` compares `POS` with the live `MARK` and requires `BIDX = 0`. -/
theorem rtlGMark_eq (state : State) (input : Input) :
    rtlGMark state input = gMark state input := by
  simp only [rtlGMark]
  spec_close

/-- Guard `Sk.BYTE` is `BIDX = 0`. -/
theorem rtlGByte_eq (state : State) (input : Input) :
    rtlGByte state input = gByte state input := by
  simp only [rtlGByte]
  spec_close

/-- The RAM request is `RQ`, `PV` or §12.4's whole-word write, by mode. -/
theorem rtlReq_eq (state : State) (input : Input) :
    rtlReq state input = req capValue state input := by
  simp only [rtlReq]
  spec_close

/-- The write flag is set in receive and capture mode only. -/
theorem rtlReqWe_eq (state : State) (input : Input) :
    rtlReqWe state input = reqWe capValue state input := by
  simp only [rtlReqWe]
  spec_close

/-- The request address is `BA`. -/
theorem rtlReqAddr_eq (state : State) (input : Input) :
    rtlReqAddr state input = reqAddr capValue state input := by
  simp only [rtlReqAddr]
  spec_close

/-- The write byte is `PEND`. -/
theorem rtlReqWdata_eq (state : State) (input : Input) :
    rtlReqWdata state input = reqWdata capValue state input := by
  simp only [rtlReqWdata]
  spec_close

/-- The whole-word write flag is `CEN` (§12.4). -/
theorem rtlReqWord_eq (state : State) (input : Input) :
    rtlReqWord state input = reqWord capValue state input := by
  simp only [rtlReqWord]
  spec_close

/-- The write word is `WB`. -/
theorem rtlReqWword_eq (state : State) (input : Input) :
    rtlReqWword state input = reqWword capValue state input := by
  simp only [rtlReqWword]
  spec_close

/-- §13.2's replay level may be updated exactly while replaying with a word. -/
theorem rtlReplayValid_eq (state : State) (input : Input) :
    rtlReplayValid state input = replayValid capValue state input := by
  simp only [rtlReplayValid]
  spec_close

/-- §13.2's replay record is `WB`; a `CAP = 0` stream presents nothing. -/
theorem rtlReplayWord_eq (state : State) (input : Input) :
    rtlReplayWord state input = replayWord capValue state input := by
  simp only [rtlReplayWord]
  spec_close

/-! ### The whole transition and the whole output word -/

/-- The extracted stream transition matches the independent SPEC_V2 §6.3 /
§12.3 / §12.4 / §13.2 specification for every state and input: all fourteen
register values. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step capValue state input := by
  simp only [rtlStep, step, State.mk.injEq]
  exact ⟨rtlPos_eq state input, rtlBidx_eq state input, rtlBa_eq state input,
    rtlCur_eq state input, rtlCv_eq state input, rtlWb_eq state input, rtlWv_eq state input,
    rtlRq_eq state input, rtlLd_eq state input, rtlPend_eq state input, rtlPv_eq state input,
    rtlStarved_eq state input, rtlNb_eq state input, rtlNv_eq state input⟩

/-- The extracted combinational outputs match the specification for every state
and input: the bit, byte, guards, request lines and replay presentation. -/
theorem rtlOut_eq_out (state : State) (input : Input) :
    rtlOut state input = out capValue state input := by
  simp only [rtlOut, out, Out.mk.injEq]
  exact ⟨rtlBit_eq state input, rtlByteOut_eq state input, rtlGEnd_eq state input,
    rtlGMark_eq state input, rtlGByte_eq state input, rtlReq_eq state input,
    rtlReqWe_eq state input, rtlReqAddr_eq state input, rtlReqWdata_eq state input,
    rtlReqWord_eq state input, rtlReqWword_eq state input, rtlReplayValid_eq state input,
    rtlReplayWord_eq state input⟩

/-! ### Trace lifting -/

/-- The extracted state during cycle `n`. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial (n + 1) = rtlStep (rtlStateAt inputs initial n) (inputs n) :=
  rfl

/-- The extracted trace is the specified trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt capValue inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_step (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step capValue (stateAt capValue inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-! ### Lifted safety facts -/

/-- A rewind in cycle `n` rewinds the extracted stream, whatever else happens. -/
theorem rtl_trace_rewind (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rewind = true) (hreset : (inputs n).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).pos = 0 ∧
      (rtlStateAt inputs initial (n + 1)).bidx = 0 ∧
      (rtlStateAt inputs initial (n + 1)).ba = (inputs n).cfgStart ∧
      (rtlStateAt inputs initial (n + 1)).cur = 0 ∧
      (rtlStateAt inputs initial (n + 1)).cv = false ∧
      (rtlStateAt inputs initial (n + 1)).wv = false ∧
      (rtlStateAt inputs initial (n + 1)).rq = false ∧
      (rtlStateAt inputs initial (n + 1)).ld = false ∧
      (rtlStateAt inputs initial (n + 1)).pv = false := by
  rw [rtlStateAt_eq]
  exact trace_rewind capValue inputs initial n h hreset

/-- A transmit advance with no byte sets `STARVED` and is ignored on the
extracted trace. -/
theorem rtl_trace_adv_without_cur (inputs : Nat → Input) (initial : State) (n : Nat)
    (hmode : txMode capValue (inputs n) = true) (hcv : (stateAt capValue inputs initial n).cv = false)
    (hadv : (inputs n).adv = true) (hend : endC (stateAt capValue inputs initial n) (inputs n) = false)
    (hfrz : (inputs n).frz = false) (hrew : (inputs n).rewind = false)
    (hreset : (inputs n).resetN = true) (hwv : (stateAt capValue inputs initial n).wv = false) :
    (rtlStateAt inputs initial (n + 1)).pos = (rtlStateAt inputs initial n).pos ∧
      (rtlStateAt inputs initial (n + 1)).bidx = (rtlStateAt inputs initial n).bidx ∧
      (rtlStateAt inputs initial (n + 1)).ba = (rtlStateAt inputs initial n).ba ∧
      (rtlStateAt inputs initial (n + 1)).cur = (rtlStateAt inputs initial n).cur ∧
      (rtlStateAt inputs initial (n + 1)).starved = true := by
  rw [rtlStateAt_succ, rtlStateAt_eq, rtlStep_eq_step]
  exact adv_without_cur capValue _ _ hmode hcv hadv hend hfrz hrew hreset hwv

/-- `STARVED`, once set on the extracted trace, stays set until a cycle clears
it (host `CTL` bit 7). -/
theorem rtl_trace_starved_persists (inputs : Nat → Input) (initial : State)
    (n m : Nat) (hnm : n ≤ m)
    (hset : (rtlStateAt inputs initial (n + 1)).starved = true)
    (hclear : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).clrStarved = false)
    (hreset : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).resetN = true) :
    (rtlStateAt inputs initial (m + 1)).starved = true := by
  have htrace : rtlStateAt inputs initial (m + 1) = stateAt capValue inputs initial (m + 1) :=
    rtlStateAt_eq inputs initial (m + 1)
  have hstart : (stateAt capValue inputs initial (n + 1)).starved = true := by
    rw [← rtlStateAt_eq inputs initial (n + 1)]
    exact hset
  rw [htrace]
  exact trace_starved_persists capValue inputs initial n m hnm hstart hclear hreset

/-! ## Axiom audit

`stream_check.py` records these records and fails the case if `sorryAx` appears.
The extracted equalities use `bv_decide`, so the large ones may carry a
per-theorem native certificate axiom in addition to `propext`,
`Classical.choice` and `Quot.sound`. -/

#print axioms rtlPos_eq
#print axioms rtlWb_eq
#print axioms rtlStarved_eq
#print axioms rtlBit_eq
#print axioms rtlReqWord_eq
#print axioms rtlStep_eq_step
#print axioms rtlOut_eq_out
#print axioms rtlStateAt_eq
#print axioms rtl_trace_rewind
#print axioms rtl_trace_adv_without_cur
#print axioms rtl_trace_starved_persists

end CapOne

namespace CapTwo

-- g_s[1].u: the elaborated `md2_stream` with CAP = false.
-- Register states and combinational cells: 12 registers, 159 gates.
-- RTL snapshot SHA-256: 609a4cbf0639094eaf786eb60d07b372ae58a79b5e5803c28a8225964c44287f

/-- The `CAP` argument of this variant. -/
abbrev capValue : Bool := false

/-- Next state of `pos`. -/
def rtlPos (state : State) (input : Input) : BitVec 12 :=
  let rtlPos0 := input.cfgMode && input.rxWe
  let rtlPos1 := (state.pos == input.cfgLen)
  let rtlPos2 := !rtlPos1
  let rtlPos3 := rtlPos0 && rtlPos2
  let rtlPos4 := (state.bidx == (7 : BitVec 3))
  let rtlPos5 := rtlPos3 && rtlPos4
  let rtlPos6 := input.cfgMode && input.flush
  let rtlPos7 := !rtlPos1
  let rtlPos8 := rtlPos6 && rtlPos7
  let rtlPos9 := !input.frz
  let rtlPos10 := rtlPos8 && rtlPos9
  let rtlPos11 := (state.bidx != 0)
  let rtlPos12 := rtlPos11 || rtlPos3
  let rtlPos13 := rtlPos10 && rtlPos12
  let rtlPos14 := rtlPos5 || rtlPos13
  let rtlPos15 := (state.pos + (1 : BitVec 12))
  let rtlPos16 := if rtlPos14 then rtlPos15 else state.pos
  let rtlPos17 := !state.cv
  let rtlPos18 := rtlPos17 && state.wv
  let rtlPos19 := !input.cfgMode
  let rtlPos20 := rtlPos19 && input.adv
  let rtlPos21 := !rtlPos1
  let rtlPos22 := rtlPos20 && rtlPos21
  let rtlPos23 := rtlPos22 && state.cv
  let rtlPos24 := (state.pos + (1 : BitVec 12))
  let rtlPos25 := if rtlPos4 then rtlPos24 else state.pos
  let rtlPos26 := if rtlPos23 then rtlPos25 else state.pos
  let rtlPos27 := if rtlPos18 then state.pos else rtlPos26
  let rtlPos28 := if input.cfgMode then rtlPos16 else rtlPos27
  let rtlPos29 := if input.frz then state.pos else rtlPos28
  let rtlPos30 := if input.rewind then (0 : BitVec 12) else rtlPos29
  let rtlPos31 := if input.resetN then rtlPos30 else (0 : BitVec 12)
  rtlPos31

/-- Next state of `bidx`. -/
def rtlBidx (state : State) (input : Input) : BitVec 3 :=
  let rtlBidx0 := input.cfgMode && input.rxWe
  let rtlBidx1 := (state.pos == input.cfgLen)
  let rtlBidx2 := !rtlBidx1
  let rtlBidx3 := rtlBidx0 && rtlBidx2
  let rtlBidx4 := (state.bidx == (7 : BitVec 3))
  let rtlBidx5 := rtlBidx3 && rtlBidx4
  let rtlBidx6 := input.cfgMode && input.flush
  let rtlBidx7 := !rtlBidx1
  let rtlBidx8 := rtlBidx6 && rtlBidx7
  let rtlBidx9 := !input.frz
  let rtlBidx10 := rtlBidx8 && rtlBidx9
  let rtlBidx11 := (state.bidx != 0)
  let rtlBidx12 := rtlBidx11 || rtlBidx3
  let rtlBidx13 := rtlBidx10 && rtlBidx12
  let rtlBidx14 := rtlBidx5 || rtlBidx13
  let rtlBidx15 := !rtlBidx14
  let rtlBidx16 := rtlBidx3 && rtlBidx15
  let rtlBidx17 := (state.bidx + (1 : BitVec 3))
  let rtlBidx18 := if rtlBidx16 then rtlBidx17 else state.bidx
  let rtlBidx19 := if rtlBidx14 then (0 : BitVec 3) else rtlBidx18
  let rtlBidx20 := !state.cv
  let rtlBidx21 := rtlBidx20 && state.wv
  let rtlBidx22 := !input.cfgMode
  let rtlBidx23 := rtlBidx22 && input.adv
  let rtlBidx24 := !rtlBidx1
  let rtlBidx25 := rtlBidx23 && rtlBidx24
  let rtlBidx26 := rtlBidx25 && state.cv
  let rtlBidx27 := (state.bidx + (1 : BitVec 3))
  let rtlBidx28 := if rtlBidx4 then (0 : BitVec 3) else rtlBidx27
  let rtlBidx29 := if rtlBidx26 then rtlBidx28 else state.bidx
  let rtlBidx30 := if rtlBidx21 then state.bidx else rtlBidx29
  let rtlBidx31 := if input.cfgMode then rtlBidx19 else rtlBidx30
  let rtlBidx32 := if input.frz then state.bidx else rtlBidx31
  let rtlBidx33 := if input.rewind then (0 : BitVec 3) else rtlBidx32
  let rtlBidx34 := if input.resetN then rtlBidx33 else (0 : BitVec 3)
  rtlBidx34

/-- Next state of `ba`. -/
def rtlBa (state : State) (input : Input) : BitVec 11 :=
  let rtlBa0 := state.pv && input.gnt
  let rtlBa1 := (state.ba + (1 : BitVec 11))
  let rtlBa2 := if rtlBa0 then rtlBa1 else state.ba
  let rtlBa3 := !state.cv
  let rtlBa4 := rtlBa3 && state.wv
  let rtlBa5 := (state.ba + (1 : BitVec 11))
  let rtlBa6 := !input.cfgMode
  let rtlBa7 := rtlBa6 && input.adv
  let rtlBa8 := (state.pos == input.cfgLen)
  let rtlBa9 := !rtlBa8
  let rtlBa10 := rtlBa7 && rtlBa9
  let rtlBa11 := rtlBa10 && state.cv
  let rtlBa12 := (state.bidx == (7 : BitVec 3))
  let rtlBa13 := (state.ba + (1 : BitVec 11))
  let rtlBa14 := if state.wv then rtlBa13 else state.ba
  let rtlBa15 := if rtlBa12 then rtlBa14 else state.ba
  let rtlBa16 := if rtlBa11 then rtlBa15 else state.ba
  let rtlBa17 := if rtlBa4 then rtlBa5 else rtlBa16
  let rtlBa18 := if input.cfgMode then rtlBa2 else rtlBa17
  let rtlBa19 := if input.frz then state.ba else rtlBa18
  let rtlBa20 := if input.rewind then input.cfgStart else rtlBa19
  let rtlBa21 := if input.resetN then rtlBa20 else (0 : BitVec 11)
  rtlBa21

/-- Next state of `cur`. -/
def rtlCur (state : State) (input : Input) : BitVec 8 :=
  let rtlCur0 := input.cfgMode && input.rxWe
  let rtlCur1 := (state.pos == input.cfgLen)
  let rtlCur2 := !rtlCur1
  let rtlCur3 := rtlCur0 && rtlCur2
  let rtlCur4 := (state.bidx == (7 : BitVec 3))
  let rtlCur5 := rtlCur3 && rtlCur4
  let rtlCur6 := input.cfgMode && input.flush
  let rtlCur7 := !rtlCur1
  let rtlCur8 := rtlCur6 && rtlCur7
  let rtlCur9 := !input.frz
  let rtlCur10 := rtlCur8 && rtlCur9
  let rtlCur11 := (state.bidx != 0)
  let rtlCur12 := rtlCur11 || rtlCur3
  let rtlCur13 := rtlCur10 && rtlCur12
  let rtlCur14 := rtlCur5 || rtlCur13
  let rtlCur15 := !rtlCur14
  let rtlCur16 := rtlCur3 && rtlCur15
  let rtlCur17 := (~~~state.bidx)
  let rtlCur18 := if input.cfgMsb then rtlCur17 else state.bidx
  let rtlCur19 := rtlCur3 && input.rxBit
  let rtlCur20 := (((if rtlCur19 then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) <<< (rtlCur18).toNat)
  let rtlCur21 := (state.cur ||| rtlCur20)
  let rtlCur22 := if rtlCur16 then rtlCur21 else state.cur
  let rtlCur23 := if rtlCur14 then (0 : BitVec 8) else rtlCur22
  let rtlCur24 := !state.cv
  let rtlCur25 := rtlCur24 && state.wv
  let rtlCur26 := (BitVec.truncate 8 (BitVec.ushiftRight state.wb ((8 * ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0))).toNat) + 0)))
  let rtlCur27 := !input.cfgMode
  let rtlCur28 := rtlCur27 && input.adv
  let rtlCur29 := !rtlCur1
  let rtlCur30 := rtlCur28 && rtlCur29
  let rtlCur31 := rtlCur30 && state.cv
  let rtlCur32 := (BitVec.truncate 8 (BitVec.ushiftRight state.wb ((8 * ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0))).toNat) + 0)))
  let rtlCur33 := if state.wv then rtlCur32 else state.cur
  let rtlCur34 := if rtlCur4 then rtlCur33 else state.cur
  let rtlCur35 := if rtlCur31 then rtlCur34 else state.cur
  let rtlCur36 := if rtlCur25 then rtlCur26 else rtlCur35
  let rtlCur37 := if input.cfgMode then rtlCur23 else rtlCur36
  let rtlCur38 := if input.frz then state.cur else rtlCur37
  let rtlCur39 := if input.rewind then (0 : BitVec 8) else rtlCur38
  let rtlCur40 := if input.resetN then rtlCur39 else (0 : BitVec 8)
  rtlCur40

/-- Next state of `cv`. -/
def rtlCv (state : State) (input : Input) : Bool :=
  let rtlCv0 := !state.cv
  let rtlCv1 := rtlCv0 && state.wv
  let rtlCv2 := !input.cfgMode
  let rtlCv3 := rtlCv2 && input.adv
  let rtlCv4 := (state.pos == input.cfgLen)
  let rtlCv5 := !rtlCv4
  let rtlCv6 := rtlCv3 && rtlCv5
  let rtlCv7 := rtlCv6 && state.cv
  let rtlCv8 := (state.bidx == (7 : BitVec 3))
  let rtlCv9 := if state.wv then state.cv else false
  let rtlCv10 := if rtlCv8 then rtlCv9 else state.cv
  let rtlCv11 := if rtlCv7 then rtlCv10 else state.cv
  let rtlCv12 := if rtlCv1 then true else rtlCv11
  let rtlCv13 := if input.cfgMode then state.cv else rtlCv12
  let rtlCv14 := if input.frz then state.cv else rtlCv13
  let rtlCv15 := if input.rewind then false else rtlCv14
  let rtlCv16 := if input.resetN then rtlCv15 else false
  rtlCv16

/-- Next state of `wb`. -/
def rtlWb (state : State) (input : Input) : BitVec 32 :=
  let rtlWb0 := !input.cfgMode
  let rtlWb1 := rtlWb0 && state.ld
  let rtlWb2 := !input.frzd
  let rtlWb3 := rtlWb1 && rtlWb2
  let rtlWb4 := if rtlWb3 then input.rdata else state.wb
  let rtlWb5 := if input.resetN then rtlWb4 else (0 : BitVec 32)
  rtlWb5

/-- Next state of `wv`. -/
def rtlWv (state : State) (input : Input) : Bool :=
  let rtlWv0 := !state.cv
  let rtlWv1 := rtlWv0 && state.wv
  let rtlWv2 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0)) == (3 : BitVec 2))
  let rtlWv3 := if state.ld then true else state.wv
  let rtlWv4 := if rtlWv2 then false else rtlWv3
  let rtlWv5 := !input.cfgMode
  let rtlWv6 := rtlWv5 && input.adv
  let rtlWv7 := (state.pos == input.cfgLen)
  let rtlWv8 := !rtlWv7
  let rtlWv9 := rtlWv6 && rtlWv8
  let rtlWv10 := rtlWv9 && state.cv
  let rtlWv11 := (state.bidx == (7 : BitVec 3))
  let rtlWv12 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ba 0)) == (3 : BitVec 2))
  let rtlWv13 := if rtlWv12 then false else rtlWv3
  let rtlWv14 := if state.wv then rtlWv13 else rtlWv3
  let rtlWv15 := if rtlWv11 then rtlWv14 else rtlWv3
  let rtlWv16 := if rtlWv10 then rtlWv15 else rtlWv3
  let rtlWv17 := if rtlWv1 then rtlWv4 else rtlWv16
  let rtlWv18 := if input.cfgMode then state.wv else rtlWv17
  let rtlWv19 := if input.frz then state.wv else rtlWv18
  let rtlWv20 := if input.rewind then false else rtlWv19
  let rtlWv21 := if input.resetN then rtlWv20 else false
  rtlWv21

/-- Next state of `rq`. -/
def rtlRq (state : State) (input : Input) : Bool :=
  let rtlRq0 := state.rq && input.gnt
  let rtlRq1 := !state.wv
  let rtlRq2 := !state.rq
  let rtlRq3 := rtlRq1 && rtlRq2
  let rtlRq4 := !state.ld
  let rtlRq5 := rtlRq3 && rtlRq4
  let rtlRq6 := if rtlRq5 then true else state.rq
  let rtlRq7 := if rtlRq0 then false else rtlRq6
  let rtlRq8 := if input.cfgMode then state.rq else rtlRq7
  let rtlRq9 := if input.frz then state.rq else rtlRq8
  let rtlRq10 := if input.rewind then false else rtlRq9
  let rtlRq11 := if input.resetN then rtlRq10 else false
  rtlRq11

/-- Next state of `ld`. -/
def rtlLd (state : State) (input : Input) : Bool :=
  let rtlLd0 := state.rq && input.gnt
  let rtlLd1 := if state.ld then false else state.ld
  let rtlLd2 := if rtlLd0 then true else rtlLd1
  let rtlLd3 := if input.cfgMode then state.ld else rtlLd2
  let rtlLd4 := if input.frz then state.ld else rtlLd3
  let rtlLd5 := if input.rewind then false else rtlLd4
  let rtlLd6 := if input.resetN then rtlLd5 else false
  rtlLd6

/-- Next state of `pend`. -/
def rtlPend (state : State) (input : Input) : BitVec 8 :=
  let rtlPend0 := input.cfgMode && input.rxWe
  let rtlPend1 := (state.pos == input.cfgLen)
  let rtlPend2 := !rtlPend1
  let rtlPend3 := rtlPend0 && rtlPend2
  let rtlPend4 := (state.bidx == (7 : BitVec 3))
  let rtlPend5 := rtlPend3 && rtlPend4
  let rtlPend6 := input.cfgMode && input.flush
  let rtlPend7 := !rtlPend1
  let rtlPend8 := rtlPend6 && rtlPend7
  let rtlPend9 := !input.frz
  let rtlPend10 := rtlPend8 && rtlPend9
  let rtlPend11 := (state.bidx != 0)
  let rtlPend12 := rtlPend11 || rtlPend3
  let rtlPend13 := rtlPend10 && rtlPend12
  let rtlPend14 := rtlPend5 || rtlPend13
  let rtlPend15 := !input.gnt
  let rtlPend16 := state.pv && rtlPend15
  let rtlPend17 := (~~~state.bidx)
  let rtlPend18 := if input.cfgMsb then rtlPend17 else state.bidx
  let rtlPend19 := rtlPend3 && input.rxBit
  let rtlPend20 := (((if rtlPend19 then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) <<< (rtlPend18).toNat)
  let rtlPend21 := (state.cur ||| rtlPend20)
  let rtlPend22 := if rtlPend16 then state.pend else rtlPend21
  let rtlPend23 := if rtlPend14 then rtlPend22 else state.pend
  let rtlPend24 := if input.cfgMode then rtlPend23 else state.pend
  let rtlPend25 := if input.frz then state.pend else rtlPend24
  let rtlPend26 := if input.resetN then rtlPend25 else (0 : BitVec 8)
  rtlPend26

/-- Next state of `pv`. -/
def rtlPv (state : State) (input : Input) : Bool :=
  let rtlPv0 := input.cfgMode && input.rxWe
  let rtlPv1 := (state.pos == input.cfgLen)
  let rtlPv2 := !rtlPv1
  let rtlPv3 := rtlPv0 && rtlPv2
  let rtlPv4 := (state.bidx == (7 : BitVec 3))
  let rtlPv5 := rtlPv3 && rtlPv4
  let rtlPv6 := input.cfgMode && input.flush
  let rtlPv7 := !rtlPv1
  let rtlPv8 := rtlPv6 && rtlPv7
  let rtlPv9 := !input.frz
  let rtlPv10 := rtlPv8 && rtlPv9
  let rtlPv11 := (state.bidx != 0)
  let rtlPv12 := rtlPv11 || rtlPv3
  let rtlPv13 := rtlPv10 && rtlPv12
  let rtlPv14 := rtlPv5 || rtlPv13
  let rtlPv15 := !input.gnt
  let rtlPv16 := state.pv && rtlPv15
  let rtlPv17 := state.pv && input.gnt
  let rtlPv18 := if rtlPv17 then false else state.pv
  let rtlPv19 := if rtlPv16 then rtlPv18 else true
  let rtlPv20 := if rtlPv14 then rtlPv19 else rtlPv18
  let rtlPv21 := if input.cfgMode then rtlPv20 else state.pv
  let rtlPv22 := if input.frz then state.pv else rtlPv21
  let rtlPv23 := if input.rewind then false else rtlPv22
  let rtlPv24 := if input.resetN then rtlPv23 else false
  rtlPv24

/-- Next state of `starved`. -/
def rtlStarved (state : State) (input : Input) : Bool :=
  let rtlStarved0 := !input.cfgMode
  let rtlStarved1 := rtlStarved0 && input.adv
  let rtlStarved2 := (state.pos == input.cfgLen)
  let rtlStarved3 := !rtlStarved2
  let rtlStarved4 := rtlStarved1 && rtlStarved3
  let rtlStarved5 := !state.cv
  let rtlStarved6 := (state.bidx == (7 : BitVec 3))
  let rtlStarved7 := !state.wv
  let rtlStarved8 := rtlStarved6 && rtlStarved7
  let rtlStarved9 := rtlStarved5 || rtlStarved8
  let rtlStarved10 := rtlStarved4 && rtlStarved9
  let rtlStarved11 := input.cfgMode && input.rxWe
  let rtlStarved12 := !rtlStarved2
  let rtlStarved13 := rtlStarved11 && rtlStarved12
  let rtlStarved14 := rtlStarved13 && rtlStarved6
  let rtlStarved15 := input.cfgMode && input.flush
  let rtlStarved16 := !rtlStarved2
  let rtlStarved17 := rtlStarved15 && rtlStarved16
  let rtlStarved18 := !input.frz
  let rtlStarved19 := rtlStarved17 && rtlStarved18
  let rtlStarved20 := (state.bidx != 0)
  let rtlStarved21 := rtlStarved20 || rtlStarved13
  let rtlStarved22 := rtlStarved19 && rtlStarved21
  let rtlStarved23 := rtlStarved14 || rtlStarved22
  let rtlStarved24 := input.cfgMode && rtlStarved23
  let rtlStarved25 := rtlStarved24 && state.pv
  let rtlStarved26 := !input.gnt
  let rtlStarved27 := rtlStarved25 && rtlStarved26
  let rtlStarved28 := rtlStarved10 || rtlStarved27
  let rtlStarved29 := !input.clrStarved
  let rtlStarved30 := state.starved && rtlStarved29
  let rtlStarved31 := rtlStarved28 || rtlStarved30
  let rtlStarved32 := if input.resetN then rtlStarved31 else false
  rtlStarved32

/-- Next state of `nb`. -/
def rtlNb (state : State) (_input : Input) : BitVec 32 :=
  -- a CAP = 0 stream has no §13.2 buffer slot: the field is inert
  state.nb

/-- Next state of `nv`. -/
def rtlNv (state : State) (_input : Input) : Bool :=
  -- a CAP = 0 stream has no §13.2 buffer slot: the field is inert
  state.nv

/-- Output `bit`. -/
def rtlBit (state : State) (input : Input) : Bool :=
  let rtlBit0 := !input.cfgMode
  let rtlBit1 := rtlBit0 && state.cv
  let rtlBit2 := (state.pos == input.cfgLen)
  let rtlBit3 := !rtlBit2
  let rtlBit4 := rtlBit1 && rtlBit3
  let rtlBit5 := (~~~state.bidx)
  let rtlBit6 := if input.cfgMsb then rtlBit5 else state.bidx
  let rtlBit7 := (((BitVec.ushiftRight state.cur (rtlBit6).toNat) &&& (1 : BitVec 8)) != 0)
  let rtlBit8 := rtlBit4 && rtlBit7
  rtlBit8

/-- Output `byteOut`. -/
def rtlByteOut (state : State) (input : Input) : BitVec 8 :=
  let rtlByteOut0 := if input.cfgMode then state.pend else state.cur
  rtlByteOut0

/-- Output `gEnd`. -/
def rtlGEnd (state : State) (input : Input) : Bool :=
  let rtlGEnd0 := (state.pos == input.cfgLen)
  rtlGEnd0

/-- Output `gMark`. -/
def rtlGMark (state : State) (input : Input) : Bool :=
  let rtlGMark0 := (state.pos == input.cfgMark)
  let rtlGMark1 := (state.bidx == (0 : BitVec 3))
  let rtlGMark2 := rtlGMark0 && rtlGMark1
  rtlGMark2

/-- Output `gByte`. -/
def rtlGByte (state : State) (_input : Input) : Bool :=
  let rtlGByte0 := (state.bidx == (0 : BitVec 3))
  rtlGByte0

/-- Output `req`. -/
def rtlReq (state : State) (input : Input) : Bool :=
  let rtlReq0 := if input.cfgMode then state.pv else state.rq
  rtlReq0

/-- Output `reqWe`. -/
def rtlReqWe (_state : State) (input : Input) : Bool :=
  input.cfgMode

/-- Output `reqAddr`. -/
def rtlReqAddr (state : State) (_input : Input) : BitVec 11 :=
  state.ba

/-- Output `reqWdata`. -/
def rtlReqWdata (state : State) (_input : Input) : BitVec 8 :=
  state.pend

/-- Output `reqWord`. -/
def rtlReqWord (_state : State) (_input : Input) : Bool :=
  false

/-- Output `reqWword`. -/
def rtlReqWword (state : State) (_input : Input) : BitVec 32 :=
  state.wb

/-- Output `replayValid`. -/
def rtlReplayValid (_state : State) (_input : Input) : Bool :=
  false

/-- Output `replayWord`. -/
def rtlReplayWord (_state : State) (_input : Input) : BitVec 32 :=
  (0 : BitVec 32)

/-- The elaborated next state, field by field. -/
def rtlStep (state : State) (input : Input) : State :=
  ⟨rtlPos state input, rtlBidx state input, rtlBa state input, rtlCur state input, rtlCv state input, rtlWb state input, rtlWv state input, rtlRq state input, rtlLd state input, rtlPend state input, rtlPv state input, rtlStarved state input, rtlNb state input, rtlNv state input⟩

/-- The elaborated combinational outputs. -/
def rtlOut (state : State) (input : Input) : Out :=
  ⟨rtlBit state input, rtlByteOut state input, rtlGEnd state input, rtlGMark state input, rtlGByte state input, rtlReq state input, rtlReqWe state input, rtlReqAddr state input, rtlReqWdata state input, rtlReqWord state input, rtlReqWword state input, rtlReplayValid state input, rtlReplayWord state input⟩

/-! ## The extracted transition is the specification

`rtlStep` and `rtlOut` above are generated from the elaborated `md2_stream`
cells; the right-hand sides are `Metronome.Stream`'s equations at this variant's
`CAP` (false).  Each field is proved on its own cone, so `bv_decide` never sees
the whole state at once. -/

/-- Unfold the specification's equations and close the field equality.

The extracted definition is unfolded by each theorem first, so a proof only ever
sees its own cone.  The full `simp` after the unfolding normalises the `Bool`
guards (`true && x`, a negated `RESET_N`, an `if` with swapped branches) so that
`bv_decide` bit-blasts the residual instead of abstracting an `if` expression. -/
macro "spec_close" : tactic =>
  `(tactic| (simp only [step, out, posNext, bidxNext, baNext, curNext, cvNext,
    wbNext, wvNext, rqNext, ldNext, pendNext, pvNext, starvedNext, nbNext, nvNext,
    advT, starveTx, starveRx, starveEvent, push, done, bitin, fl, endC, last,
    txMode, rxMode, cen, rpl, occupied, landing, lb, bsel, nsh, bitAt, bitOut, byteOut,
    bitOut, gEnd, gMark, gByte, req, reqWe, reqAddr, reqWdata, reqWord, reqWword,
    replayValid, replayWord, State.mk.injEq, Out.mk.injEq] at * <;>
    ((try simp) <;>
     (repeat (first | rfl | bv_decide | (split <;> simp_all) | contradiction)))))

/-! ### Next state, field by field -/

/-- The extracted `POS` next state is §6.3's. -/
theorem rtlPos_eq (state : State) (input : Input) :
    (rtlStep state input).pos = (step capValue state input).pos := by
  simp only [rtlStep, rtlPos]
  spec_close

/-- The extracted `BIDX` next state is §6.3's. -/
theorem rtlBidx_eq (state : State) (input : Input) :
    (rtlStep state input).bidx = (step capValue state input).bidx := by
  simp only [rtlStep, rtlBidx]
  spec_close

/-- The extracted `BA` next state is §6.3's (byte address steps of 1, §12.4's
word write of 4 and §13.2's whole-word read of 4). -/
theorem rtlBa_eq (state : State) (input : Input) :
    (rtlStep state input).ba = (step capValue state input).ba := by
  simp only [rtlStep, rtlBa]
  spec_close

/-- The extracted `CUR` next state is §6.3's: `LB` from `WB` in transmit, the
assembly register in receive. -/
theorem rtlCur_eq (state : State) (input : Input) :
    (rtlStep state input).cur = (step capValue state input).cur := by
  simp only [rtlStep, rtlCur]
  spec_close

/-- The extracted `CV` next state is §6.3's. -/
theorem rtlCv_eq (state : State) (input : Input) :
    (rtlStep state input).cv = (step capValue state input).cv := by
  simp only [rtlStep, rtlCv]
  spec_close

/-- The extracted `WB` next state is §6.3's lookahead load, §12.3's landing
exception, §12.4's record and §13.2's two-deep buffer. -/
theorem rtlWb_eq (state : State) (input : Input) :
    (rtlStep state input).wb = (step capValue state input).wb := by
  simp only [rtlStep, rtlWb]
  spec_close

/-- The extracted `WV` next state is §6.3's. -/
theorem rtlWv_eq (state : State) (input : Input) :
    (rtlStep state input).wv = (step capValue state input).wv := by
  simp only [rtlStep, rtlWv]
  spec_close

/-- The extracted `RQ` next state is §6.3's request rule and §13.2's. -/
theorem rtlRq_eq (state : State) (input : Input) :
    (rtlStep state input).rq = (step capValue state input).rq := by
  simp only [rtlStep, rtlRq]
  spec_close

/-- The extracted `LD` next state is §6.3's. -/
theorem rtlLd_eq (state : State) (input : Input) :
    (rtlStep state input).ld = (step capValue state input).ld := by
  simp only [rtlStep, rtlLd]
  spec_close

/-- The extracted `PEND` next state is §6.3's, including the drop when a byte
still waits. -/
theorem rtlPend_eq (state : State) (input : Input) :
    (rtlStep state input).pend = (step capValue state input).pend := by
  simp only [rtlStep, rtlPend]
  spec_close

/-- The extracted `PV` next state is §6.3's. -/
theorem rtlPv_eq (state : State) (input : Input) :
    (rtlStep state input).pv = (step capValue state input).pv := by
  simp only [rtlStep, rtlPv]
  spec_close

/-- The extracted sticky `STARVED` next state is §6.3's, including §13.2's
`late`. -/
theorem rtlStarved_eq (state : State) (input : Input) :
    (rtlStep state input).starved = (step capValue state input).starved := by
  simp only [rtlStep, rtlStarved]
  spec_close

/-- The extracted second replay buffer slot `NB` is §13.2's (inert for a
`CAP = 0` stream). -/
theorem rtlNb_eq (state : State) (input : Input) :
    (rtlStep state input).nb = (step capValue state input).nb := by
  simp only [rtlStep, rtlNb]
  spec_close

/-- The extracted second replay buffer flag `NV` is §13.2's. -/
theorem rtlNv_eq (state : State) (input : Input) :
    (rtlStep state input).nv = (step capValue state input).nv := by
  simp only [rtlStep, rtlNv]
  spec_close

/-! ### Outputs, field by field -/

/-- `Sk.BIT` is §6.3's `CV && !END && CUR[b]`, disabled in receive, capture and
replay. -/
theorem rtlBit_eq (state : State) (input : Input) :
    rtlBit state input = bitOut capValue state input := by
  simp only [rtlBit]
  spec_close

/-- Source `Sk.BYTE` is `CUR` in transmit and `PEND` in receive. -/
theorem rtlByteOut_eq (state : State) (input : Input) :
    rtlByteOut state input = byteOut capValue state input := by
  simp only [rtlByteOut]
  spec_close

/-- Guard `Sk.END` compares `POS` with the live `LEN`. -/
theorem rtlGEnd_eq (state : State) (input : Input) :
    rtlGEnd state input = gEnd state input := by
  simp only [rtlGEnd]
  spec_close

/-- Guard `Sk.MARK` compares `POS` with the live `MARK` and requires `BIDX = 0`. -/
theorem rtlGMark_eq (state : State) (input : Input) :
    rtlGMark state input = gMark state input := by
  simp only [rtlGMark]
  spec_close

/-- Guard `Sk.BYTE` is `BIDX = 0`. -/
theorem rtlGByte_eq (state : State) (input : Input) :
    rtlGByte state input = gByte state input := by
  simp only [rtlGByte]
  spec_close

/-- The RAM request is `RQ`, `PV` or §12.4's whole-word write, by mode. -/
theorem rtlReq_eq (state : State) (input : Input) :
    rtlReq state input = req capValue state input := by
  simp only [rtlReq]
  spec_close

/-- The write flag is set in receive and capture mode only. -/
theorem rtlReqWe_eq (state : State) (input : Input) :
    rtlReqWe state input = reqWe capValue state input := by
  simp only [rtlReqWe]
  spec_close

/-- The request address is `BA`. -/
theorem rtlReqAddr_eq (state : State) (input : Input) :
    rtlReqAddr state input = reqAddr capValue state input := by
  simp only [rtlReqAddr]
  spec_close

/-- The write byte is `PEND`. -/
theorem rtlReqWdata_eq (state : State) (input : Input) :
    rtlReqWdata state input = reqWdata capValue state input := by
  simp only [rtlReqWdata]
  spec_close

/-- The whole-word write flag is `CEN` (§12.4). -/
theorem rtlReqWord_eq (state : State) (input : Input) :
    rtlReqWord state input = reqWord capValue state input := by
  simp only [rtlReqWord]
  spec_close

/-- The write word is `WB`. -/
theorem rtlReqWword_eq (state : State) (input : Input) :
    rtlReqWword state input = reqWword capValue state input := by
  simp only [rtlReqWword]
  spec_close

/-- §13.2's replay level may be updated exactly while replaying with a word. -/
theorem rtlReplayValid_eq (state : State) (input : Input) :
    rtlReplayValid state input = replayValid capValue state input := by
  simp only [rtlReplayValid]
  spec_close

/-- §13.2's replay record is `WB`; a `CAP = 0` stream presents nothing. -/
theorem rtlReplayWord_eq (state : State) (input : Input) :
    rtlReplayWord state input = replayWord capValue state input := by
  simp only [rtlReplayWord]
  spec_close

/-! ### The whole transition and the whole output word -/

/-- The extracted stream transition matches the independent SPEC_V2 §6.3 /
§12.3 / §12.4 / §13.2 specification for every state and input: all fourteen
register values. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step capValue state input := by
  simp only [rtlStep, step, State.mk.injEq]
  exact ⟨rtlPos_eq state input, rtlBidx_eq state input, rtlBa_eq state input,
    rtlCur_eq state input, rtlCv_eq state input, rtlWb_eq state input, rtlWv_eq state input,
    rtlRq_eq state input, rtlLd_eq state input, rtlPend_eq state input, rtlPv_eq state input,
    rtlStarved_eq state input, rtlNb_eq state input, rtlNv_eq state input⟩

/-- The extracted combinational outputs match the specification for every state
and input: the bit, byte, guards, request lines and replay presentation. -/
theorem rtlOut_eq_out (state : State) (input : Input) :
    rtlOut state input = out capValue state input := by
  simp only [rtlOut, out, Out.mk.injEq]
  exact ⟨rtlBit_eq state input, rtlByteOut_eq state input, rtlGEnd_eq state input,
    rtlGMark_eq state input, rtlGByte_eq state input, rtlReq_eq state input,
    rtlReqWe_eq state input, rtlReqAddr_eq state input, rtlReqWdata_eq state input,
    rtlReqWord_eq state input, rtlReqWword_eq state input, rtlReplayValid_eq state input,
    rtlReplayWord_eq state input⟩

/-! ### Trace lifting -/

/-- The extracted state during cycle `n`. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial (n + 1) = rtlStep (rtlStateAt inputs initial n) (inputs n) :=
  rfl

/-- The extracted trace is the specified trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt capValue inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_step (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step capValue (stateAt capValue inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-! ### Lifted safety facts -/

/-- A rewind in cycle `n` rewinds the extracted stream, whatever else happens. -/
theorem rtl_trace_rewind (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rewind = true) (hreset : (inputs n).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).pos = 0 ∧
      (rtlStateAt inputs initial (n + 1)).bidx = 0 ∧
      (rtlStateAt inputs initial (n + 1)).ba = (inputs n).cfgStart ∧
      (rtlStateAt inputs initial (n + 1)).cur = 0 ∧
      (rtlStateAt inputs initial (n + 1)).cv = false ∧
      (rtlStateAt inputs initial (n + 1)).wv = false ∧
      (rtlStateAt inputs initial (n + 1)).rq = false ∧
      (rtlStateAt inputs initial (n + 1)).ld = false ∧
      (rtlStateAt inputs initial (n + 1)).pv = false := by
  rw [rtlStateAt_eq]
  exact trace_rewind capValue inputs initial n h hreset

/-- A transmit advance with no byte sets `STARVED` and is ignored on the
extracted trace. -/
theorem rtl_trace_adv_without_cur (inputs : Nat → Input) (initial : State) (n : Nat)
    (hmode : txMode capValue (inputs n) = true) (hcv : (stateAt capValue inputs initial n).cv = false)
    (hadv : (inputs n).adv = true) (hend : endC (stateAt capValue inputs initial n) (inputs n) = false)
    (hfrz : (inputs n).frz = false) (hrew : (inputs n).rewind = false)
    (hreset : (inputs n).resetN = true) (hwv : (stateAt capValue inputs initial n).wv = false) :
    (rtlStateAt inputs initial (n + 1)).pos = (rtlStateAt inputs initial n).pos ∧
      (rtlStateAt inputs initial (n + 1)).bidx = (rtlStateAt inputs initial n).bidx ∧
      (rtlStateAt inputs initial (n + 1)).ba = (rtlStateAt inputs initial n).ba ∧
      (rtlStateAt inputs initial (n + 1)).cur = (rtlStateAt inputs initial n).cur ∧
      (rtlStateAt inputs initial (n + 1)).starved = true := by
  rw [rtlStateAt_succ, rtlStateAt_eq, rtlStep_eq_step]
  exact adv_without_cur capValue _ _ hmode hcv hadv hend hfrz hrew hreset hwv

/-- `STARVED`, once set on the extracted trace, stays set until a cycle clears
it (host `CTL` bit 7). -/
theorem rtl_trace_starved_persists (inputs : Nat → Input) (initial : State)
    (n m : Nat) (hnm : n ≤ m)
    (hset : (rtlStateAt inputs initial (n + 1)).starved = true)
    (hclear : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).clrStarved = false)
    (hreset : ∀ j, n + 1 ≤ j → j ≤ m → (inputs j).resetN = true) :
    (rtlStateAt inputs initial (m + 1)).starved = true := by
  have htrace : rtlStateAt inputs initial (m + 1) = stateAt capValue inputs initial (m + 1) :=
    rtlStateAt_eq inputs initial (m + 1)
  have hstart : (stateAt capValue inputs initial (n + 1)).starved = true := by
    rw [← rtlStateAt_eq inputs initial (n + 1)]
    exact hset
  rw [htrace]
  exact trace_starved_persists capValue inputs initial n m hnm hstart hclear hreset

/-! ## Axiom audit

`stream_check.py` records these records and fails the case if `sorryAx` appears.
The extracted equalities use `bv_decide`, so the large ones may carry a
per-theorem native certificate axiom in addition to `propext`,
`Classical.choice` and `Quot.sound`. -/

#print axioms rtlPos_eq
#print axioms rtlWb_eq
#print axioms rtlStarved_eq
#print axioms rtlBit_eq
#print axioms rtlReqWord_eq
#print axioms rtlStep_eq_step
#print axioms rtlOut_eq_out
#print axioms rtlStateAt_eq
#print axioms rtl_trace_rewind
#print axioms rtl_trace_adv_without_cur
#print axioms rtl_trace_starved_persists

end CapTwo

end Metronome.Stream
