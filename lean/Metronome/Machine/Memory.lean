import Metronome.Machine.Units

/-! §6.2 Data RAM and arbiter; §6.1 pointer P0 (SPEC v1 6.1, 9a.2, 9a.3); §12.3 freeze and landing exception. -/

namespace Metronome.Machine

open Util Tables

/-- §6.2 A data RAM request: a word read (word address), a one-byte write (byte address), or a one-word write
(word address, §12.4). -/
inductive RamReq where
  | none
  | rd (word : Nat) (lane : Nat)
  | wrByte (a : Nat) (v : Nat)
  | wrWord (word : Nat) (v : Nat)
deriving Repr, Inhabited

/-- §6.2 / §12.3 Arbiter: one access per cycle; requesters in priority order S0, S1, P0, host. In a frozen cycle
only the host request is served. Returns the served requester (0 none, 1 S0, 2 S1, 3 P0, 4 host). -/
def arbiter (s0 s1 p0 host : RamReq) (frozen : Bool) : Nat :=
  let some_ : RamReq → Bool := fun r => match r with
    | .none => false
    | _ => true
  if !frozen && some_ s0 then 1
  else if !frozen && some_ s1 then 2
  else if !frozen && some_ p0 then 3
  else if some_ host then 4
  else 0

/-- §6.2 Data RAM word `w` (512 x 32, byte address a is lane `a[1:0]` of word `a[10:2]`, little-endian). -/
def ramWord (m : ByteArray) (w : Nat) : Nat := bgetLE m (4 * (w % 512)) 4

/-- §6.2 Perform a served request at the end of cycle s: writes update the RAM; a read's word appears at the RAM
output during s+1. Returns the new RAM, the RAM output and the byte addresses written. -/
def ramAccess (m : ByteArray) (out : Nat) (r : RamReq) : ByteArray × Nat × List Nat :=
  match r with
  | .none => (m, out, [])
  | .rd w _ => (m, ramWord m w, [])
  | .wrByte a v => (bset m (a % 2048) v, out, [a % 2048])
  | .wrWord w v =>
    let b := 4 * (w % 512)
    ((List.range 4).foldl (fun acc k => bset acc (b + k) (nbits v (8 * k) 8)) m, out,
      (List.range 4).map (b + ·))

/-- §6.1 / SPEC v1 6.1 P0's request to the arbiter: a fetch reads `mem[PTR]` with `PTR` as of the serving cycle; a
write request carries its address and data. -/
def p0Req (p : P0St) : RamReq :=
  match p.req with
  | .none => .none
  | .fetch => .rd (p.ptr.toNat / 4) (p.ptr.toNat % 4)
  | .write a v => .wrByte a.toNat v.toNat

/-- §6.1 The winning P0 move of cycle t: 0 `AL`, 1 `AH`, 2 `W`, 3 `R`, with bus value. -/
structure P0Move where
  op : Nat
  v : Nat
deriving Repr, Inhabited

/-- §6.1 / SPEC v1 6.1, 9a.2, 9a.3 and §12.3 P0 next state; also returns whether `MEMHAZ` is set by a request
overwrite.

* `AL: PTR[7:0]'=v`; `AH: PTR[10:8]'=v[2:0]`; both clear `RDY` and set `REQ = fetch`. `W: REQ = write(PTR, v);
  PTR' = PTR+1; RDY' = 0`. `R: PTR' = PTR+1; RDY' = 0; REQ = fetch`.
* 9a.2: `MEMHAZ` only when a request still unserved at the end of the cycle is replaced.
* A fetch served in s lands at the end of s+1: `D' =` the byte, `RDY' = 1` (visible from s+2), unless (9a.3) a
  request-setting move happened in the serving or landing cycle.
* §12.3: the landing byte is captured from the RAM output at the end of s+1 even if s+1 is frozen; `RDY` updates in
  the first unfrozen cycle (`land`). -/
def p0Next (p : P0St) (mv : Option P0Move) (served : Bool) (landNow : Bool) (ramOut : Nat) (lane : Nat)
    (frozen : Bool) : P0St × Bool :=
  let reqMove := mv.isSome
  let ptr := p.ptr.toNat
  let (ptr', req1) : Nat × PReq := match mv with
    | some ⟨0, v⟩ => ((ptr / 256) * 256 + v % 256, .fetch)
    | some ⟨1, v⟩ => ((v % 8) * 256 + ptr % 256, .fetch)
    | some ⟨2, v⟩ => (ptr + 1, .write p.ptr (bv 8 v))
    | some ⟨_, _⟩ => (ptr + 1, .fetch)
    | none => (ptr, if served then .none else p.req)
  let pending := match p.req with
    | .none => false
    | _ => true
  let haz := reqMove && pending && !served
  let servedFetch := served && (match p.req with
    | .fetch => true
    | _ => false)
  let process := p.land && !frozen
  let land' := servedFetch || (p.land && !process)
  let stale' := if servedFetch then reqMove else p.stale
  let d' := if landNow then bv 8 (nbits ramOut (8 * lane) 8) else p.d
  let rdy' := if reqMove then false else if process then !p.stale else p.rdy
  ({ ptr := bv 11 ptr', d := d', rdy := rdy', req := req1, land := land', stale := stale' }, haz)

end Metronome.Machine
