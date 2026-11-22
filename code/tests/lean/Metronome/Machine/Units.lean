import Metronome.Machine.Moves

/-! §6.1 Units (flags, accumulator, scratch, shifters, counters, LFSR/CRC), as SPEC v1 6.1 and 9a.7. -/

namespace Metronome.Machine

open Util Tables

/-- §6.1 The winning move to each unit write group in cycle t (bus value `v`). -/
structure UnitsIn where
  /-- `FLAGS.SET` (true) or `FLAGS.CLR` (false) with bus value. -/
  flag : Option (Bool × Nat) := none
  /-- `ACC.*` op code (0 LD .. 6 CMP) with bus value. -/
  acc : Option (Nat × Nat) := none
  reg : Vector (Option Nat) 4 := Vector.replicate 4 none
  /-- `SHk.LD` (true) or `SHk.SH` (false) with bus value. -/
  sh : Vector (Option (Bool × Nat)) 2 := Vector.replicate 2 none
  shCfg : Vector (Option Nat) 2 := Vector.replicate 2 none
  /-- `CNTk.LO` (0), `.HI` (1), `.DEC` (2) with bus value. -/
  cnt : Vector (Option (Nat × Nat)) 3 := Vector.replicate 3 none
  /-- `LFk.ST` (`none` byte) or `LFk.Bb` (`some b`) with bus value. -/
  lf : Vector (Option (Option Nat × Nat)) 2 := Vector.replicate 2 none

/-- §6.1 / SPEC v1 6.1 / 9a.7 Accumulator. `LD: A'=v`. `ADD: r=A+v, A'=r[7:0], C'=r[8]`. `SUB: r=A-v, A'=r[7:0],
C'=(A>=v)`. `AND/OR/XOR: A'=A op v`. `CMP: r=A-v, C'=(A>=v)`, A unchanged. Every op sets `Z'=(result==0)` on the
8-bit result and `N'=result[7]`. Returns `(A', Z', C', N')`. -/
def accNext (a : Nat) (z c n : Bool) (op v : Nat) : Nat × Bool × Bool × Bool :=
  let fl (r : Nat) (c' : Bool) := (r % 256 == 0, c', nbit r 7)
  match op with
  | 0 => let r := v % 256; let (z', c', n') := fl r c; (r, z', c', n')
  | 1 => let r := a + v; let (z', c', n') := fl (r % 256) (nbit r 8); (r % 256, z', c', n')
  | 2 => let r := (a + 256 - v) % 256; let (z', c', n') := fl r (a ≥ v); (r, z', c', n')
  | 3 => let r := a &&& v; let (z', c', n') := fl r c; (r, z', c', n')
  | 4 => let r := a ||| v; let (z', c', n') := fl r c; (r, z', c', n')
  | 5 => let r := a ^^^ v; let (z', c', n') := fl r c; (r, z', c', n')
  | 6 => let r := (a + 256 - v) % 256; let (z', c', n') := fl r (a ≥ v); (a, z', c', n')
  | _ => (a, z, c, n)

/-- §6.1 / SPEC v1 6.1 Shifter. `LD: D'=v, CNT'=LEN?LEN:8`. `SH: D' = MSB ? {D[6:0],v[0]} : {v[0],D[7:1]},
CNT' = CNT ? CNT-1 : 0`. `CFG: LEN'=v[3:0], MSB'=v[4]`. -/
def shNext (s : ShSt) (op : Option (Bool × Nat)) (cfg : Option Nat) : ShSt :=
  let s1 : ShSt := match op with
    | some (true, v) => { s with d := bv 8 v, cnt := if s.len.toNat != 0 then s.len else 8 }
    | some (false, v) =>
      let d := s.d.toNat
      let d' := if s.msb then (d * 2) % 256 + v % 2 else (v % 2) * 128 + d / 2
      { s with d := bv 8 d', cnt := if s.cnt.toNat != 0 then s.cnt - 1 else 0 }
    | none => s
  match cfg with
  | some v => { s1 with len := bv 4 v, msb := nbit v 4 }
  | none => s1

/-- §6.1 / SPEC v1 6.1 Shifter out bit `O = MSB ? D[7] : D[0]`. -/
def shOut (s : ShSt) : Bool := if s.msb then bit s.d 7 else bit s.d 0

/-- §6.1 / SPEC v1 6.1 Counter. `LO: V[7:0]'=v`. `HI: V[15:8]'=v`. `DEC: V' = V ? V-1 : 0`. -/
def cntNext (x : BitVec 16) (op : Option (Nat × Nat)) : BitVec 16 :=
  match op with
  | some (0, v) => setByte x 0 v
  | some (1, v) => setByte x 1 v
  | some (2, _) => if x.toNat != 0 then x - 1 else 0
  | _ => x

/-- §6.1 / SPEC v1 6.1 LFSR/CRC. `ST: fb = S[0]^v[0]; S' = (S >> 1) ^ (fb ? POLY : 0)`. `Bk: S[8k+7:8k]' = v`. -/
def lfNext (s : BitVec 32) (poly : Nat) (op : Option (Option Nat × Nat)) : BitVec 32 :=
  match op with
  | some (none, v) =>
    let fb := bit s 0 != nbit v 0
    bv 32 ((s.toNat >>> 1) ^^^ (if fb then poly else 0))
  | some (some b, v) => setByte s b v
  | none => s

/-- §6.1 Units next state. Flags: `SET n: F[n]' = 1`, `CLR n: F[n]' = 0` (n = bus[3:0]); `FP' = F` every cycle
(held in a frozen cycle, §12.3). Scratch `Rk' = v`. -/
def unitsNext (cfg : Config) (u : UnitsSt) (i : UnitsIn) (frozen : Bool) : UnitsSt :=
  let f' := match i.flag with
    | some (b, v) => setBit u.f (v % 16) b
    | none => u.f
  let (a', z', c', n') := match i.acc with
    | some (op, v) => accNext u.a.toNat u.z u.c u.n op v
    | none => (u.a.toNat, u.z, u.c, u.n)
  { f := f', fp := if frozen then u.fp else u.f, a := bv 8 a', z := z', c := c', n := n',
    r := Vector.ofFn fun k => match i.reg[k] with
      | some v => bv 8 v
      | none => u.r[k]
    sh := Vector.ofFn fun k => shNext u.sh[k] i.sh[k] i.shCfg[k]
    cnt := Vector.ofFn fun k => cntNext u.cnt[k] i.cnt[k]
    lf := Vector.ofFn fun k => lfNext u.lf[k] (cfg.poly k.val) i.lf[k] }

end Metronome.Machine
