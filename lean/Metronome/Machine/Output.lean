import Metronome.Machine.Thread

/-! §8 Output pins with §12.1 live-pin inputs; §12.2 execution digest; §9 `IRQ`; §2 pin outputs. -/

namespace Metronome.Machine

open Util Tables

/-- §8 / §12.1 Pin table index of output pin o, with `ln = LINE`, `cm = COMMITTED(ln)`:
`b0 = cm[SEL0]`, `b1 = LIVE[1] ? PIN[PINB(ln)] : cm[SEL1]`, `b2 = LIVE[0] ? PIN[PINA(ln)] : cm[SEL2]`,
`idx = BOUND ? {SEG(ln), b2, b1, b0} : 0`. -/
def outIdx (s : State) (cv : CfgView) (p : PinView) (o : Nat) : Nat :=
  let oc := vget cv.outs o
  let lc := vget cv.lines oc.line
  let ls := vget s.lines oc.line
  let cm := ls.committed
  let b0 := bit cm oc.sel0
  let b1 := if nbit oc.live 1 then p.pin lc.pinb else bit cm oc.sel1
  let b2 := if nbit oc.live 0 then p.pin lc.pina else bit cm oc.sel2
  if oc.bound then seg ls * 8 + b2n b2 * 4 + b2n b1 * 2 + b2n b0 else 0

/-- §8 / §12.3 `OUT[o]' = LUT[idx]; OEN[o]' = OE[idx]` (o < 8); both hold in a frozen cycle. -/
def outNext (s : State) (cv : CfgView) (p : PinView) (frozen : Bool) : BitVec 14 × BitVec 8 :=
  if frozen then (s.out, s.oen) else
  let idx := (List.range N_OUT_PINS).map (outIdx s cv p)
  let outs := (idx.zip (List.range N_OUT_PINS)).map fun (i, o) => nbit (vget cv.outs o).lut i
  let oens := ((idx.zip (List.range N_OUT_PINS)).take N_OE_PINS).map fun (i, o) => nbit (vget cv.outs o).oe i
  (bv 14 (packBits outs), bv 8 (packBits oens))

/-- §9 `ERR`: any of `CONFLICT`, `MEMHAZ`, `CWOVR` (§13.1), every thread's `LATE` and `OVR`, every line's
`TAPMISS` and every stream's `STARVED`. AMBIG(16) resolved 2026-11-21 (D46): SPEC §9 now lists `CWOVR`. -/
def errAny (s : State) : Bool :=
  s.ctrl.conflict || s.ctrl.memhaz || s.ctrl.cwovr || s.threads.toList.any (fun t => t.late || t.ovr) ||
    s.lines.toList.any (·.tapmiss) || s.streams.toList.any (·.starved)

/-- §9 `IRQ' = (IRQEN[0] && OUTV) || (IRQEN[1] && ERR)`. -/
def irqNext (s : State) : Bool := (bit s.ctrl.irqen 0 && s.ctrl.outv) || (bit s.ctrl.irqen 1 && errAny s)

/-- §12.2 Execution digest with `D = {OEN[7:0], OUT[13:0]}` of cycle t:
`M' = 0` on a host `MCTL` write with bit 1; elif `MEN && !FRZ`: `M' = ((M << 1) mod 2^32) ^ (M[31] ? 0x04C11DB7 : 0) ^ D`;
else `M' = M`. -/
def misrNext (s : State) (hClr : Bool) : BitVec 32 :=
  let m := s.dbg.misr.toNat
  let d := s.out.toNat + s.oen.toNat * 2 ^ N_OUT_PINS
  if hClr then 0
  else if s.dbg.men && !s.dbg.frz then bv 32 (((m * 2) % 2 ^ 32) ^^^ (if nbit m 31 then 0x04C11DB7 else 0) ^^^ d)
  else s.dbg.misr

/-- §2 / §8 / §9 Pins driven in a cycle: `uio_out[i] = OUT[i]`, `uio_oe[i] = OEN[i]` (O0..O7);
`uo_out[2..7] = OUT[8..13]`, `uo_out[0] = MISO = TX[7]`, `uo_out[1] = IRQ`. Returns `(uo_out, uio_out, uio_oe)`. -/
def pinsOut (s : State) : Nat × Nat × Nat :=
  let o := s.out.toNat
  ((o >>> 8) * 4 + b2n s.ctrl.irq * 2 + b2n (bit s.host.tx 7), o % 256, s.oen.toNat)

end Metronome.Machine
