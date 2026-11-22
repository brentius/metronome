import Metronome.Machine.State

/-! §2 Pins: synchronisers, synchronised levels and edges; §13.2 replay overlay. -/

namespace Metronome.Machine

open Util Tables

/-- §2 Synchronised levels in cycle t. `lvl`/`prev` hold `PIN[12:0]` and the previous level (`sp`, P_k in bit k), after
the §13.2 overlay; `sck`, `csn`, `mosi` are the synchronised host pins and `sckRise` the synchronised rising edge of
SCK. -/
structure PinView where
  lvl : Nat
  prev : Nat
  sck : Bool
  csn : Bool
  mosi : Bool
  sckRise : Bool
deriving Repr, Inhabited

namespace Util
/-- §2 Pin numbering: P0..P7 are `uio_in[0..7]`, P8..P12 are `ui_in[3..7]`. -/
@[inline] def protoPins (ui uio : BitVec 8) : Nat := uio.toNat + (ui.toNat >>> 3) * 256
end Util

/-- §2 Synchronised level `PIN[k] = s2[k]` and previous level `sp[k]`, with the §13.2 overlay: while `RPL`, every pin in
`EMASK` reads `RLV` and its previous level is `RLV` of the previous cycle (`rlvp`). The host link pins (`ui_in[0..2]`) go
through the same synchronisers. -- AMBIG(6) the overlay of the previous level does not depend on the previous `RPL`. -/
def pinView (sy : SyncSt) (d : DbgSt) : PinView :=
  let raw2 := protoPins sy.ui2 sy.uio2
  let rawp := protoPins sy.uip sy.uiop
  let m := if d.rpl then d.emask.toNat else 0
  let keep := (2 ^ N_IN_PINS - 1) - m
  let lvl := (raw2 &&& keep) ||| (d.rlv.toNat &&& m)
  let prev := (rawp &&& keep) ||| (d.rlvp.toNat &&& m)
  { lvl, prev, sck := bit sy.ui2 0, csn := bit sy.ui2 1, mosi := bit sy.ui2 2,
    sckRise := bit sy.ui2 0 && !bit sy.uip 0 }

/-- §2 `PIN[k]`; a pin select of 13..15 reads constant 0. -/
@[inline] def PinView.pin (p : PinView) (k : Nat) : Bool := k < N_IN_PINS && nbit p.lvl k

/-- §2 `RISE[k] = s2 & !sp`; selects 13..15 have no edges. -/
@[inline] def PinView.rise (p : PinView) (k : Nat) : Bool := k < N_IN_PINS && nbit p.lvl k && !nbit p.prev k

/-- §2 `FALL[k] = !s2 & sp`; selects 13..15 have no edges. -/
@[inline] def PinView.fall (p : PinView) (k : Nat) : Bool := k < N_IN_PINS && !nbit p.lvl k && nbit p.prev k

/-- §3.2 polarity-selected RISE/FALL of `PIN[pin]` (0 none, 1 rise, 2 fall, 3 both; 0 if pin >= 13). -/
def PinView.edgeSel (p : PinView) (pin pol : Nat) : Bool :=
  match pol with
  | 1 => p.rise pin
  | 2 => p.fall pin
  | 3 => p.rise pin || p.fall pin
  | _ => false

/-- §2 Synchronisers: `s1' = raw`, `s2' = s1`, `sp' = s2`. -/
def syncNext (sy : SyncSt) (pin : PinIn) : SyncSt :=
  { ui1 := pin.ui, ui2 := sy.ui1, uip := sy.ui2, uio1 := pin.uio, uio2 := sy.uio1, uiop := sy.uio2 }

end Metronome.Machine
