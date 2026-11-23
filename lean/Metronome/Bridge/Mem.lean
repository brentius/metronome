import Metronome.Machine
import Metronome.Mem

/-!
# Bridge: the data-RAM cut (`Metronome.Mem`) refines `Machine.Memory` / `Machine.Host` slots

`Metronome.Mem` specifies `md2_mem.v` (§6.2 arbiter, §6.1 pointer P0 and the
§9 host request slot) as an independent cut; `mem_check.py` proves the
elaborated registers implement it.  `Metronome.Machine` states the same
sections as `Machine.arbiter`, `Machine.ramAccess`, `Machine.p0Next` and the
host slot `HostSt.req`.  This file proves the cut's one-cycle transition is the
machine's, under an explicit map from the cut's state and inputs to the
machine's arguments.

## Abstraction map

State (`absP0`, `absSlot`):

* `ptr ↔ P0St.ptr`, `dat ↔ P0St.d`, `rdy ↔ P0St.rdy`, `land ↔ P0St.land`;
* `landRdy ↔ !P0St.stale`: the machine packs §9a.3's "no request move in the
  serve cycle" as the stale bit, the cut keeps the positive strobe.  The
  machine reads `stale` only when `land` is high; `stale_bridge` states the
  correspondence in exactly those cycles;
* the cut's `req : BitVec 2` plus its latches are the machine's `PReq`
  (`reqOf`): `0 → none`, `1 → fetch`, `2 → write reqAddr reqData`.  Code 3 is
  unreachable from reset (`Mem.reqNext_ne`); the bridge assumes `s.req ≠ 3`
  and the machine reads 3 as `none`;
* the host slot `(hostQ, hostWr, hostAddr, hostData)` is `absSlot : HReq`;
* `hLand`/`hLane` are the chip's `State.ramOwner`/`State.ramLane` of the
  served read (the machine keeps the landing strobe one level above P0).

Inputs: the pointer move is `mvOf i = some ⟨pSel.toNat, pData.toNat⟩` when
`pWe`; `served` is the cut's `grantP0`; `landNow`, `ramOut`, `lane` are the
chip's RAM-output plumbing, named in `dat_bridge` by `hlandNow`, `hramOut`,
`hlane`.

## Results

* `arbiter_eq` — the machine's priority arbiter (host only while frozen, §12.3)
  returns the cut's `servedIndex`.
* `p0_step_eq` — the observable P0 fields equal `Machine.p0Next`: `ptr`, `d`,
  `rdy`, `req` and `land`.  `stale_bridge` covers the machine's stale bit where
  it is read.  `reqAddr_bridge`/`reqData_bridge` cover the write latches.
* `slot_step` — the cut's host slot is the machine's `slotStep`, and
  `hostNext_slot` shows `Host.hostNext` uses that same update.
* `hLand_next`/`hLane_next` — the cut's host landing strobe and lane.

## Side conditions and one invariant

`req ≠ 3` is unreachable (`Mem.stateAt_req_ne_three`).  `hstaleRdy` — a
stale landing has `RDY = 0` — is the cut's own invariant: a request move in
the serve cycle already cleared `RDY` (§9a.3), and nothing else can set it
before the landing.  It is stated explicitly because the machine's
`p0Next` writes `RDY' = !stale` unconditionally while the cut holds `RDY`.

## No disagreement found

Every field maps onto `Machine.p0Next`, the slot update or the arbiter; the two
specs differ only in *where* the host slot and landing lane live.  No SPEC
clause is read two ways here.

No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Metronome.Bridge.Mem

/-! ## Numeric plumbing `BitVec` ↔ `Nat` -/

theorem bv_toNat {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv]

theorem append_toNat_8_3 (a : BitVec 3) (b : BitVec 8) :
    (a ++ b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append]
  have hb : b.toNat < 2 ^ 8 := by
    have := b.isLt
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem ptrHigh_toNat (p : BitVec 11) : (Metronome.Mem.ptrHigh p).toNat = p.toNat / 256 := by
  simp [Metronome.Mem.ptrHigh, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h := p.isLt
  omega

theorem ptrLow_toNat (p : BitVec 11) : (Metronome.Mem.ptrLow p).toNat = p.toNat % 256 := by
  simp [Metronome.Mem.ptrLow, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem trunc3_toNat (d : BitVec 8) : (BitVec.truncate 3 d).toNat = d.toNat % 8 := by
  simp [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem lane_toNat (a : BitVec 11) : (Metronome.Mem.lane a).toNat = a.toNat % 4 := by
  simp [Metronome.Mem.lane, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem wordAddr_toNat (a : BitVec 11) :
    (Metronome.Mem.wordAddr a).toNat = a.toNat / 4 := by
  simp [Metronome.Mem.wordAddr, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h := a.isLt
  omega

/-- The machine's `AL` address: `(PTR/256)*256 + pData % 256`. -/
theorem al_eq (p : BitVec 11) (d : BitVec 8) :
    Metronome.Mem.ptrHigh p ++ d =
      Machine.Util.bv 11 ((p.toNat / 256) * 256 + d.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat_8_3, ptrHigh_toNat, Machine.Util.bv, BitVec.toNat_ofNat]
  have hlt : p.toNat / 256 * 256 + d.toNat % 256 < 2 ^ (3 + 8) := by
    have hp := p.isLt
    have hd := d.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hd : d.toNat % 256 = d.toNat := Nat.mod_eq_of_lt d.isLt
  rw [hd]

theorem ah_eq (d : BitVec 8) (p : BitVec 11) :
    BitVec.truncate 3 d ++ Metronome.Mem.ptrLow p =
      Machine.Util.bv 11 ((d.toNat % 8) * 256 + p.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat_8_3, ptrLow_toNat, trunc3_toNat, Machine.Util.bv, BitVec.toNat_ofNat]
  have hlt : d.toNat % 8 * 256 + p.toNat % 256 < 2 ^ (3 + 8) := by
    have hp := p.isLt
    have hd := d.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]

theorem add_one_eq (p : BitVec 11) :
    p + 1 = Machine.Util.bv 11 (p.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Machine.Util.bv, BitVec.toNat_ofNat]
  simp

/-- Every 2-bit select is one of the four codes. -/
theorem pSel_cases (p : BitVec 2) : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by
  have h : p.toNat = 0 ∨ p.toNat = 1 ∨ p.toNat = 2 ∨ p.toNat = 3 := by
    have := p.isLt
    omega
  rcases h with h | h | h | h
  · left; apply BitVec.eq_of_toNat_eq; simpa using h
  · right; left; apply BitVec.eq_of_toNat_eq; simpa using h
  · right; right; left; apply BitVec.eq_of_toNat_eq; simpa using h
  · right; right; right; apply BitVec.eq_of_toNat_eq; simpa using h

/-- The cut's `streamReq` and the two individual request bits. -/
theorem streamReq_eq (i : Metronome.Mem.Input) :
    Metronome.Mem.streamReq i =
      (Metronome.Mem.bit0 i.sReq || Metronome.Mem.bit1 i.sReq) := by
  rcases pSel_cases i.sReq with h | h | h | h <;>
    simp [Metronome.Mem.streamReq, Metronome.Mem.bit0, Metronome.Mem.bit1, h]

theorem laneShift_eq (l : BitVec 2) : Metronome.Mem.laneShift l = 8 * l.toNat := by
  simp [Metronome.Mem.laneShift, Metronome.Mem.mulC, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h := l.isLt
  omega

theorem byteAt_toNat (w : BitVec 32) (l : BitVec 2) :
    (Metronome.Mem.byteAt w l).toNat = (w.toNat >>> (8 * l.toNat)) % 256 := by
  simp [Metronome.Mem.byteAt, laneShift_eq, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem byteAt_eq_bv (w : BitVec 32) (l : BitVec 2) :
    Metronome.Mem.byteAt w l =
      Machine.Util.bv 8 (Machine.Util.nbits w.toNat (8 * l.toNat) 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [byteAt_toNat, Machine.Util.bv, BitVec.toNat_ofNat, Machine.Util.nbits]
  have h : 2 ^ 8 = 256 := by decide
  rw [h]
  simp

/-! ## Abstraction maps -/

/-- The cut's request code and latches as the machine's `PReq`. -/
def reqOf (s : Metronome.Mem.State) : Machine.PReq :=
  if s.req = (2 : BitVec 2) then .write s.reqAddr s.reqData
  else if s.req = (1 : BitVec 2) then .fetch
  else .none

/-- The pointer part of the cut is the machine's P0 (the landing lane lives in
the chip state, see `hLane_next`). -/
def absP0 (s : Metronome.Mem.State) : Machine.P0St :=
  { ptr := s.ptr, d := s.dat, rdy := s.rdy, req := reqOf s, land := s.land,
    stale := !s.landRdy }

/-- The cut's host slot as the machine's `HReq`. -/
def absSlot (s : Metronome.Mem.State) : Machine.HReq :=
  if s.hostQ then (if s.hostWr then .write s.hostAddr s.hostData else .read s.hostAddr)
  else .none

/-- The pointer move the cut's input selects. -/
def mvOf (i : Metronome.Mem.Input) : Option Machine.P0Move :=
  if i.pWe then some ⟨i.pSel.toNat, i.pData.toNat⟩ else none

/-- Reachable states occupy codes 0, 1, 2 (`Mem.stateAt_req_ne_three`). -/
theorem req_cases (s : Metronome.Mem.State) (hneq : s.req ≠ (3 : BitVec 2)) :
    s.req = 0 ∨ s.req = 1 ∨ s.req = 2 := by
  have hne : s.req.toNat ≠ 3 := by
    intro h
    exact hneq (by apply BitVec.eq_of_toNat_eq; simpa using h)
  have h : s.req.toNat = 0 ∨ s.req.toNat = 1 ∨ s.req.toNat = 2 := by
    have := s.req.isLt
    omega
  rcases h with h | h | h
  · left; apply BitVec.eq_of_toNat_eq; simpa using h
  · right; left; apply BitVec.eq_of_toNat_eq; simpa using h
  · right; right; apply BitVec.eq_of_toNat_eq; simpa using h

/-- The machine's landed-fetch test on `reqOf` is the cut's `fetching`. -/
theorem fetchOf_reqOf (s : Metronome.Mem.State) (hneq : s.req ≠ (3 : BitVec 2)) :
    (match reqOf s with | .fetch => true | _ => false) = Metronome.Mem.fetching s := by
  rcases req_cases s hneq with h | h | h <;>
    simp [reqOf, Metronome.Mem.fetching, Metronome.Mem.RQ_FETCH, h]

/-- The same test on the abstracted pointer state. -/
theorem fetchOf_absP0 (s : Metronome.Mem.State) (hneq : s.req ≠ (3 : BitVec 2)) :
    (match (absP0 s).req with | .fetch => true | _ => false) = Metronome.Mem.fetching s := by
  simpa [absP0] using fetchOf_reqOf s hneq

theorem p0St_ext {a b : Machine.P0St} (hptr : a.ptr = b.ptr) (hd : a.d = b.d)
    (hrdy : a.rdy = b.rdy) (hreq : a.req = b.req) (hland : a.land = b.land)
    (hstale : a.stale = b.stale) : a = b := by
  cases a
  cases b
  simp_all

/-! ## Pointer state fields (`Machine.p0Next`)

The last three arguments are named like `p0Next`'s (`landNow`, `ramOut`,
`lane`); only `d` reads them. -/

/-- `PTR` agrees: `AL`/`AH` reload a byte, `W`/`R` step, otherwise hold. -/
theorem ptr_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (_landNow : Bool) (_ramOut _lane : Nat) :
    (absP0 (Metronome.Mem.step s i)).ptr =
      (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
        _landNow _ramOut _lane i.frz).1.ptr := by
  simp only [absP0, Metronome.Mem.step, Metronome.Mem.ptrNext, Machine.p0Next]
  by_cases h : i.pWe = true
  · rcases pSel_cases i.pSel with hsel | hsel | hsel | hsel
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR, al_eq]
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR, ah_eq]
    · simp only [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR, ite_true, ite_false, Bool.false_eq_true,
        Bool.not_true, Bool.true_and]
      exact add_one_eq s.ptr
    · simp only [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR, ite_true, ite_false, Bool.false_eq_true,
        Bool.not_true, Bool.true_and]
      exact add_one_eq s.ptr
  · simp [mvOf, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
      Metronome.Mem.opW, Metronome.Mem.opR, Machine.Util.bv]

/-- `REQ` agrees: every move sets a request (`W` a write, the others a fetch),
a served request clears, otherwise the slot holds. -/
theorem req_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (hneq : s.req ≠ (3 : BitVec 2))
    (_landNow : Bool) (_ramOut _lane : Nat) :
    reqOf (Metronome.Mem.step s i) =
      (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
        _landNow _ramOut _lane i.frz).1.req := by
  simp only [absP0, Metronome.Mem.step, Metronome.Mem.reqNext, Machine.p0Next, reqOf,
    Metronome.Mem.reqAddrNext, Metronome.Mem.reqDataNext]
  by_cases h : i.pWe = true
  · rcases pSel_cases i.pSel with hsel | hsel | hsel | hsel
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR]
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR]
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR, bv_toNat]
    · simp [mvOf, hsel, h, hreset, Metronome.Mem.opAl, Metronome.Mem.opAh,
        Metronome.Mem.opW, Metronome.Mem.opR]
  · rcases req_cases s hneq with hreq | hreq | hreq <;>
      by_cases hg : Metronome.Mem.grantP0 s i = true <;>
      simp [mvOf, h, hreset, hreq, hg, Metronome.Mem.opW]

/-- The write request's address latch: `W` latches `PTR`. -/
theorem reqAddr_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (h : Metronome.Mem.opW i = true) :
    (Metronome.Mem.step s i).reqAddr = s.ptr := by
  simp [Metronome.Mem.step, Metronome.Mem.reqAddrNext, hreset, h]

/-- The write request's data latch. -/
theorem reqData_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (h : Metronome.Mem.opW i = true) :
    (Metronome.Mem.step s i).reqData = i.pData := by
  simp [Metronome.Mem.step, Metronome.Mem.reqDataNext, hreset, h]

/-- `RDY` agrees: a move clears it, a landing sets it unless a move happened
in the serve cycle (`landRdy` / the machine's `!stale`), a frozen landing
waits, and a stale landing leaves the already-cleared `RDY` at zero. -/
theorem rdy_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true)
    (hstaleRdy : s.land = true → s.landRdy = false → s.rdy = false)
    (_landNow : Bool) (_ramOut _lane : Nat) :
    (absP0 (Metronome.Mem.step s i)).rdy =
      (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
        _landNow _ramOut _lane i.frz).1.rdy := by
  simp only [absP0, Metronome.Mem.step, Metronome.Mem.rdyNext, Machine.p0Next]
  by_cases h : i.pWe = true
  · simp [mvOf, h, hreset]
  · by_cases hl : s.land = true
    · by_cases hf : i.frz = true
      · by_cases hr : s.landRdy = true <;> simp [mvOf, h, hl, hf, hr, hreset]
      · by_cases hr : s.landRdy = true <;> simp [mvOf, h, hl, hf, hr, hreset, hstaleRdy hl]
    · by_cases hf : i.frz = true <;> simp [mvOf, h, hl, hf, hreset]

/-- `D` agrees, given the chip's RAM-output interface: the landing strobe, the
word the SRAM presents and its lane. -/
theorem dat_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (landNow : Bool) (ramOut : Nat) (lane : Nat)
    (hlandNow : landNow = (s.land && !i.frzd)) (hramOut : ramOut = i.ramWord.toNat)
    (hlane : lane = s.landLane.toNat) :
    (absP0 (Metronome.Mem.step s i)).d =
      (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
        landNow ramOut lane i.frz).1.d := by
  simp only [absP0, Metronome.Mem.step, Metronome.Mem.datNext, Machine.p0Next, hreset,
    Bool.not_true, Bool.false_eq_true, ite_false]
  rw [byteAt_eq_bv, hlandNow, ← hramOut, ← hlane]

/-- `land` agrees: a served P0 fetch records the landing (§9a.3), a frozen
cycle records nothing, and a landing outside its window is held. -/
theorem land_bridge (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (hneq : s.req ≠ (3 : BitVec 2))
    (_landNow : Bool) (_ramOut _lane : Nat) :
    (absP0 (Metronome.Mem.step s i)).land =
      (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
        _landNow _ramOut _lane i.frz).1.land := by
  simp only [absP0, Metronome.Mem.step, Metronome.Mem.landNext, Machine.p0Next]
  rcases req_cases s hneq with h | h | h
  all_goals
    simp only [reqOf, h, Metronome.Mem.fetching, Metronome.Mem.RQ_FETCH]
    by_cases hf : i.frz = true
    · have hg : Metronome.Mem.grantP0 s i = false := by
        simp [Metronome.Mem.grantP0, hf]
      by_cases hl : s.land = true <;> simp [hf, hg, hl, hreset]
    · by_cases hg : Metronome.Mem.grantP0 s i = true
      · simp [hf, hg, hreset]
      · by_cases hl : s.land = true <;> simp [hf, hg, hl, hreset]

/-- The observable pointer state (all fields but the don't-care stale bit) maps
onto `p0Next`. -/
theorem p0_step_eq (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) (hneq : s.req ≠ (3 : BitVec 2))
    (hstaleRdy : s.land = true → s.landRdy = false → s.rdy = false)
    (landNow : Bool) (ramOut : Nat) (lane : Nat)
    (hlandNow : landNow = (s.land && !i.frzd)) (hramOut : ramOut = i.ramWord.toNat)
    (hlane : lane = s.landLane.toNat) :
    (absP0 (Metronome.Mem.step s i)).ptr =
        (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
          landNow ramOut lane i.frz).1.ptr ∧
      (absP0 (Metronome.Mem.step s i)).d =
        (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
          landNow ramOut lane i.frz).1.d ∧
      (absP0 (Metronome.Mem.step s i)).rdy =
        (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
          landNow ramOut lane i.frz).1.rdy ∧
      reqOf (Metronome.Mem.step s i) =
        (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
          landNow ramOut lane i.frz).1.req ∧
      (absP0 (Metronome.Mem.step s i)).land =
        (Machine.p0Next (absP0 s) (mvOf i) (Metronome.Mem.grantP0 s i)
          landNow ramOut lane i.frz).1.land := by
  exact ⟨ptr_bridge s i hreset landNow ramOut lane,
    dat_bridge s i hreset landNow ramOut lane hlandNow hramOut hlane,
    rdy_bridge s i hreset hstaleRdy landNow ramOut lane,
    req_bridge s i hreset hneq landNow ramOut lane,
    land_bridge s i hreset hneq landNow ramOut lane⟩

/-- The cut's `resetState` maps to the machine's all-zero pointer, except that
`stale` reads `true` in the cut (its `landRdy` is low).  The machine reads
`stale` only when `land` is high, and at the first serve both models set it
consistently (`stale_bridge`), so the discrepancy is unobservable. -/
theorem absP0_reset :
    absP0 Metronome.Mem.resetState =
      ({ ptr := 0, d := 0, rdy := false, req := .none, land := false,
         stale := true } : Machine.P0St) := by
  simp [absP0, reqOf, Metronome.Mem.resetState]

/-! ## The arbiter (`Machine.arbiter`) -/

/-- The requester the cut grants, in the machine's 0/1/2/3/4 code. -/
def servedIndex (s : Metronome.Mem.State) (i : Metronome.Mem.Input) : Nat :=
  if Metronome.Mem.grantS0 i then 1
  else if Metronome.Mem.grantS1 i then 2
  else if Metronome.Mem.grantP0 s i then 3
  else if Metronome.Mem.grantHost s i then 4
  else 0

/-- Some-request encoding that isolates *whether* a requester asks (the arbiter
only tests presence). -/
def someReq (b : Bool) : Machine.RamReq := if b then .rd 0 0 else .none

/-- The machine's arbiter agrees with the cut's grant priority, including the
§12.3 rule that a frozen cycle serves only the host. -/
theorem arbiter_eq (s : Metronome.Mem.State) (i : Metronome.Mem.Input) :
    Machine.arbiter (someReq (Metronome.Mem.s0Req i)) (someReq (Metronome.Mem.s1Req i))
        (someReq (Metronome.Mem.pending s)) (someReq s.hostQ) i.frz =
      servedIndex s i := by
  simp only [streamReq_eq i, servedIndex, Machine.arbiter, someReq, Metronome.Mem.grantS0,
    Metronome.Mem.grantS1, Metronome.Mem.grantP0, Metronome.Mem.grantHost,
    Metronome.Mem.s0Req, Metronome.Mem.s1Req, Metronome.Mem.pending,
    Metronome.Mem.RQ_NONE]
  rcases pSel_cases i.sReq with h0 | h0 | h0 | h0 <;>
  rcases pSel_cases s.req with hr | hr | hr | hr <;>
  by_cases hq : s.hostQ = true <;> by_cases hf : i.frz = true <;>
  simp [servedIndex, Machine.arbiter, someReq, Metronome.Mem.grantS0,
    Metronome.Mem.grantS1, Metronome.Mem.grantP0, Metronome.Mem.grantHost,
    Metronome.Mem.s0Req, Metronome.Mem.s1Req, Metronome.Mem.streamReq,
    Metronome.Mem.pending, Metronome.Mem.RQ_NONE, h0, hr, hq, hf] <;> decide

/-! ## Host request slot (`Machine.Host.hostNext`'s `req`) -/

/-- One-cycle update of a `HReq` slot: a newly issued request overwrites an
unserved one (9a.4), a served request clears, otherwise hold. -/
def slotStep (h : Machine.HReq) (new : Option Machine.HReq) (served : Bool) : Machine.HReq :=
  match new with
  | some r => r
  | none => if served then .none else h

/-- The cut's host slot obeys exactly the machine's slot update. -/
theorem slot_step (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) :
    absSlot (Metronome.Mem.step s i) =
      slotStep (absSlot s)
        (if i.hSet then
          some (if i.hWr then Machine.HReq.write i.hAddr i.hData else Machine.HReq.read i.hAddr)
        else none)
        (Metronome.Mem.grantHost s i) := by
  simp only [absSlot, Metronome.Mem.step, Metronome.Mem.hostQNext, Metronome.Mem.hostWrNext,
    Metronome.Mem.hostAddrNext, Metronome.Mem.hostDataNext, slotStep]
  by_cases hs : i.hSet = true
  · by_cases hw : i.hWr = true <;> simp [hs, hw, hreset]
  · by_cases hg : Metronome.Mem.grantHost s i = true <;> simp [hs, hg, hreset]

/-- `Machine.Host.hostNext`'s slot field is the same `slotStep`, with the newly
issued request being `hostNext`'s read request or its pending host write. -/
theorem hostNext_slot (s : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (served : Bool) :
    (Machine.hostNext s cv p served).1.req =
      slotStep s.host.req
        (match (if s.host.rPend then some (Machine.hostRead s cv s.host.addr.toNat) else none) with
          | some (.inr a) => some (Machine.HReq.read (Machine.Util.bv 11 a))
          | _ => if s.host.wPend && Machine.Tables.DATA_BASE ≤ s.host.addr.toNat &&
                s.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES then
              some (Machine.HReq.write (Machine.Util.bv 11 (s.host.addr.toNat - Machine.Tables.DATA_BASE))
                s.host.wData)
            else none)
        served := by
  simp only [Machine.hostNext, slotStep]
  by_cases hr : s.host.rPend = true
  · rcases hrd : Machine.hostRead s cv s.host.addr.toNat with x | a
    · by_cases hw : (s.host.wPend && Machine.Tables.DATA_BASE ≤ s.host.addr.toNat &&
          s.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) = true <;>
        by_cases hs : served = true <;> simp [hr, hrd, hw, hs]
    · by_cases hs : served = true <;> simp [hr, hrd, hs]
  · by_cases hw : (s.host.wPend && Machine.Tables.DATA_BASE ≤ s.host.addr.toNat &&
        s.host.addr.toNat < Machine.Tables.DATA_BASE + Machine.Tables.DATA_BYTES) = true <;>
      by_cases hs : served = true <;> simp [hr, hw, hs]

/-- The cut's host landing strobe is "a host read was served": `grantHost` with
a read request (the machine's `ramOwner == 4` next cycle). -/
theorem hLand_next (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) :
    (Metronome.Mem.step s i).hLand = (Metronome.Mem.grantHost s i && !s.hostWr) := by
  simp [Metronome.Mem.step, Metronome.Mem.hLandNext, hreset]

/-- The cut's landing lane, when a landing is signalled, is the served host
address's lane (the machine stores that lane in `State.ramLane`). -/
theorem hLane_next (s : Metronome.Mem.State) (i : Metronome.Mem.Input)
    (hreset : i.resetN = true) :
    (Metronome.Mem.step s i).hLane = Metronome.Mem.lane s.hostAddr := by
  simp [Metronome.Mem.step, Metronome.Mem.hLaneNext, hreset]

/-! ## The served request in `Machine.ramAccess` coordinates -/

/-- A P0 fetch (`REQ = 1`) is the machine's `rd` of the cut's `mAddr` word in
the cut's `mBe` lane: `ramAccess` reads `mem[wordAddr PTR]` lane `PTR[1:0]`,
which is exactly `md2_mem`'s fetch port. -/
theorem p0_fetch_req (s : Metronome.Mem.State) (hreq : s.req = (1 : BitVec 2)) :
    Machine.p0Req (absP0 s) =
      Machine.RamReq.rd (Metronome.Mem.wordAddr s.ptr).toNat
        (Metronome.Mem.lane s.ptr).toNat := by
  have h12 : ((1 : BitVec 2) = 2) = False := by decide
  have h11 : ((1 : BitVec 2) = 1) = True := by decide
  simp only [Machine.p0Req, absP0, reqOf, hreq, h12, h11, ite_true, ite_false,
    Bool.false_eq_true]
  rw [wordAddr_toNat, lane_toNat]

/-- A P0 write request (`REQ = 2`) is the machine's `wrByte` of the latched
address and byte. -/
theorem p0_write_req (s : Metronome.Mem.State) (hreq : s.req = (2 : BitVec 2)) :
    Machine.p0Req (absP0 s) =
      Machine.RamReq.wrByte s.reqAddr.toNat s.reqData.toNat := by
  have h21 : ((2 : BitVec 2) = 1) = False := by decide
  have h22 : ((2 : BitVec 2) = 2) = True := by decide
  simp only [Machine.p0Req, absP0, reqOf, hreq, h21, h22, ite_true, ite_false,
    Bool.false_eq_true]

/-- The byte `ramAccess` writes is the byte the cut's `mAddr`/`mBe`/`mWd`
ports address: word `a/4` (mod 512) and lane `a%4`, for `a < 2048`. -/
theorem p0_write_addr (a : BitVec 11) :
    a.toNat % 2048 =
      4 * ((Metronome.Mem.wordAddr a).toNat % 512) + (Metronome.Mem.lane a).toNat := by
  rw [wordAddr_toNat, lane_toNat]
  have h := a.isLt
  omega

end Metronome.Bridge.Mem
