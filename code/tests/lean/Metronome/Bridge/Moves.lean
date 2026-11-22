import Metronome.Machine
import Metronome.Moves

/-!
# Bridge: the move-resolution cut (`Metronome.Moves`) refines `Machine.Moves`

`Metronome.Moves` is the independent statement of SPEC_V2 §6 used by
`moves_check.py`: the destination → write-group table, the six-slot priority
(`k = 3*core + m`), `sameKey`, `winAt`, the conflict event, the per-group
`pick`, and the sticky `CONFLICT`/`MEMHAZ` bits with the two source side
effects.

`Machine.Moves` is the whole-chip executable specification written from
SPEC_V2: `moveGroup` maps a move's destination to a write group *and* its key
(the executing line for `L.SYM`, the thread for `T.STOP`), and `resolveMoves`
folds the enabled moves in `(core, move index)` order, keeping the first move
per key and raising the conflict flag on a repeat.

This file proves:

* the **destination → group table**: for every 6-bit destination code, the
  cut's 5-bit `dgTable` entry is the index of the write group that contains
  that destination's name in `Machine.Tables.writeGroups` (`dgTable_matches`),
  and the machine's `dstGroup` array is that same list search
  (`dstGroup_getElem?`, and `dstGroup_all` for all 64 codes);
* the **sticky flags**: `Moves.stickyNext` is the machine's `ctrlNext` bit for
  `CONFLICT` and `MEMHAZ`, including the frozen-cycle behaviour (§12.3 gates
  the cores, not the sticky bits);
* the **`INV` mailbox** side effect and the **`MEMHAZ` event** shape;
* the **resolution**: `fold_prefix` is the invariant of `resolveMoves`' fold over
  the prefix of the first `n ≤ 6` slots (winners, seen keys, conflict), and at
  `n = 6` (`resolveMoves_winners`, `resolveMoves_conflict`) it gives exactly the
  cut's winner set (`winAt`), conflict event (`conflictEv`) and, for a non-keyed
  group, written word (`resolveMoves_pick` against `pickWord`).

## Side conditions

* `MoveAgree` (per cycle, field level): the machine move's `dst`, `line` and
  `thread` are the slot's, disabled slots are padded with `NULL`, and the slot's
  `group` is `dgTable` of its `dst`.  From this `moveTable_of_agree` proves the
  six-move key equality; padding is harmless (`resolveAux_pad`).
* `DstKindTable` (one global hypothesis, checked by compiled evaluation in
  `decode_check.lean`): the `L.SYM`/`T.STOP`/`NULL` kind of the 64 destination
  codes.  The group table and the 21 fixed names are kernel-checked
  (`dstGroup_all`, `dstClass_fixed`); the other 40 names need
  `Util.dstOfName`'s `String.splitOn`, whose worker `String.splitOnAux` is
  `@[irreducible]` in Lean 4.35.0 core.  This is a Lean-library reduction
  limitation, not a disagreement between the specifications.
* `SrcTable` is discharged in the kernel: `srcOp_cut` proves that the machine's
  `srcOp 33`/`srcOp 38` are `P0.D`/`HOST.IN`.

## Disagreements

None found in the parts bridged here.  The cut's `T.STOP` key is per thread
(`sameKey` tests `thread`), which is exactly the machine's `moveGroup`
(`.stop => (group, thread)`); `L.SYM` is per line in both.  SPEC §6's "two
enabled moves target one group" is read per key, not per group code;
`lsym_two_lines_witness` fixes that reading (two `L.SYM` moves on different lines
both win, with no conflict).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 1024

namespace Metronome.Bridge.Moves

open Metronome.Moves

/-! ## The destination → write-group table

`Machine.Tables.writeGroups` is the machine's own group table.  It is an
`Array (String × Array String)`; reading it through `toList` makes the search
kernel-reducible, so the cut's literal `dgMapLiteral` can be checked against it
by `decide`. -/

/-- The machine's write-group table, as a reducible list of lists. -/
def wgList : List (String × List String) :=
  [("L.SYM", ["L.SYM", "L.DBIT", "L.XOR"]),
   ("T.STOP", ["T.STOP"]),
   ("FLAGS", ["FLAGS.SET", "FLAGS.CLR"]),
   ("ACC", ["ACC.LD", "ACC.ADD", "ACC.SUB", "ACC.AND", "ACC.OR", "ACC.XOR", "ACC.CMP"]),
   ("R0", ["R0"]), ("R1", ["R1"]), ("R2", ["R2"]), ("R3", ["R3"]),
   ("SH0", ["SH0.LD", "SH0.SH"]), ("SH1", ["SH1.LD", "SH1.SH"]),
   ("SH0.CFG", ["SH0.CFG"]), ("SH1.CFG", ["SH1.CFG"]),
   ("CNT0", ["CNT0.LO", "CNT0.HI", "CNT0.DEC"]),
   ("CNT1", ["CNT1.LO", "CNT1.HI", "CNT1.DEC"]),
   ("CNT2", ["CNT2.LO", "CNT2.HI", "CNT2.DEC"]),
   ("LF0", ["LF0.ST", "LF0.B0", "LF0.B1", "LF0.B2", "LF0.B3"]),
   ("LF1", ["LF1.ST", "LF1.B0", "LF1.B1", "LF1.B2", "LF1.B3"]),
   ("P0", ["P0.AL", "P0.AH", "P0.W", "P0.R"]),
   ("S0", ["S0.ADV", "S0.RX", "S0.CTL"]),
   ("S1", ["S1.ADV", "S1.RX", "S1.CTL"]),
   ("L0.CTL", ["L0.CTL"]), ("L1.CTL", ["L1.CTL"]),
   ("L2.CTL", ["L2.CTL"]), ("L3.CTL", ["L3.CTL"]),
   ("HOST.OUT", ["HOST.OUT"]),
   ("CW", ["CW.AL", "CW.AH", "CW.D"])]

/-- `wgList` is the machine's table. -/
theorem wgList_eq :
    wgList = Metronome.Machine.Tables.writeGroups.toList.map
      (fun (g, ms) => (g, ms.toList)) := by
  decide

/-- The group index of a destination name in the machine's table. -/
def groupOfName (n : String) : Option Nat :=
  wgList.findIdx? (fun (_, ms) => ms.contains n)

/-- The cut's `dgTable` entry for code `d` is the group index of the `d`th
destination name in the machine's table, for all 64 codes (`31` is `DG_NONE`). -/
def groupCodeOf (d : Nat) : Nat :=
  ((Metronome.Machine.Tables.dstNames.toList[d]?).bind groupOfName).getD 31

theorem dgTable_matches_all :
    (List.range 64).all (fun d => (dgTable (BitVec.ofNat 6 d)).toNat ==
      groupCodeOf d) = true := by
  decide

/-- Per-code form of `dgTable_matches_all`. -/
theorem dgTable_matches (d : Nat) (hd : d < 64) :
    (dgTable (BitVec.ofNat 6 d)).toNat = groupCodeOf d := by
  have h := List.all_eq_true.1 dgTable_matches_all d (by simpa [List.mem_range] using hd)
  simpa using h

/-- `NULL` (code 0) has no group. -/
theorem dgTable_null_31 : (dgTable 0).toNat = 31 := by decide

/-- `Array.findIdx?` on a literal array is the list search. -/
theorem array_findIdx?_mk {α : Type} (p : α → Bool) (l : List α) :
    Array.findIdx? p (Array.mk l) = List.findIdx? p l :=
  List.findIdx?_toArray p l

/-- `Array.contains` is the list membership test. -/
theorem array_contains_eq {α : Type} [BEq α] (xs : Array α) (x : α) :
    xs.contains x = xs.toList.contains x :=
  (Array.contains_toList).symm

/-- The machine's `dstGroup` array is the list search of `dstGroup_getElem?`. -/
theorem dstGroup_getElem? (d : Nat) :
    Metronome.Machine.Util.dstGroup[d]? =
      (Metronome.Machine.Tables.dstNames.toList[d]?).map
        (fun n => Metronome.Machine.Tables.writeGroups.toList.findIdx?
          (fun (_, ms) => ms.toList.contains n)) := by
  simp only [Metronome.Machine.Util.dstGroup, Array.getElem?_map, Array.getElem?_toList,
    Function.comp_def, Metronome.Machine.Tables.writeGroups, array_findIdx?_mk,
    array_contains_eq]

/-- The machine's group array agrees with `wgList`. -/
theorem dstGroup_getElem?_wg (d : Nat) :
    Metronome.Machine.Util.dstGroup[d]? =
      (Metronome.Machine.Tables.dstNames.toList[d]?).map groupOfName := by
  rw [dstGroup_getElem?]
  congr 1

/-! ## The sticky flags

`CONFLICT` is `CTRL.STICKY` bit 0, `MEMHAZ` bit 1 (SPEC §6, §9, §13.1).  Both
are write-one-to-clear: an event (two valid moves with one key / a `P0.D` read
while `!RDY`) sets the bit, a host write of `STICKY` with the bit set clears it,
and an event in the same cycle wins.  `Machine.ctrlNext` is that equation for
the `CONFLICT` and `MEMHAZ` fields; `Moves.stickyNext` is the cut's.  A frozen
cycle gates neither (§12.3 lists the cores and the phase, not these bits). -/

/-- The `CONFLICT` next state is the cut's sticky step. -/
theorem ctrl_conflict_bridge (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (sticky : Nat)
    (hsticky : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "STICKY").getD 0 = sticky)
    (state event clear : Bool) (hst : s.ctrl.conflict = state)
    (hev : ci.conflict = event) (hclear : Metronome.Machine.Util.nbit sticky 0 = clear) :
    (Metronome.Machine.ctrlNext s hw ci frozen).conflict =
      Metronome.Moves.stickyNext state ⟨true, event, clear⟩ := by
  simp [Metronome.Machine.ctrlNext, hst, hev, hsticky, hclear, Metronome.Moves.stickyNext,
    Bool.or_comm]

/-- The `MEMHAZ` next state is the cut's sticky step (bit 1). -/
theorem ctrl_memhaz_bridge (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (sticky : Nat)
    (hsticky : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "STICKY").getD 0 = sticky)
    (state event clear : Bool) (hst : s.ctrl.memhaz = state)
    (hev : ci.memhaz = event) (hclear : Metronome.Machine.Util.nbit sticky 1 = clear) :
    (Metronome.Machine.ctrlNext s hw ci frozen).memhaz =
      Metronome.Moves.stickyNext state ⟨true, event, clear⟩ := by
  simp [Metronome.Machine.ctrlNext, hst, hev, hsticky, hclear, Metronome.Moves.stickyNext,
    Bool.or_comm]

/-- A frozen cycle does not change the sticky equation. -/
theorem ctrl_conflict_frozen (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) :
    (Metronome.Machine.ctrlNext s hw ci true).conflict =
      (Metronome.Machine.ctrlNext s hw ci false).conflict := rfl

/-- A clear-only cycle clears a set flag (the cut's `sticky_clear`). -/
theorem ctrl_conflict_clear_only (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (sticky : Nat)
    (hsticky : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "STICKY").getD 0 = sticky)
    (hc : s.ctrl.conflict = true) (he : ci.conflict = false)
    (hclear : Metronome.Machine.Util.nbit sticky 0 = true) :
    (Metronome.Machine.ctrlNext s hw ci frozen).conflict = false := by
  simp [Metronome.Machine.ctrlNext, hc, he, hsticky, hclear]

/-- An event sets the flag whatever the clear bit does. -/
theorem ctrl_conflict_event (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (he : ci.conflict = true) :
    (Metronome.Machine.ctrlNext s hw ci frozen).conflict = true := by
  simp [Metronome.Machine.ctrlNext, he]

/-! ## The mailbox `INV` side effect -/

/-- The machine's `INV` next state is the cut's `invNext` (host write beats a
same-cycle read). -/
theorem ctrl_inv_bridge (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (state hostWrite : Bool) (hst : s.ctrl.inv = state)
    (hin : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "HOSTIN").isSome = hostWrite) :
    (Metronome.Machine.ctrlNext s hw ci frozen).inv =
      Metronome.Moves.invNext state true hostWrite ci.hostInRead := by
  simp only [Metronome.Machine.ctrlNext, hst, hin, Metronome.Moves.invNext]
  by_cases h : hostWrite = true <;> by_cases hr : ci.hostInRead = true <;> simp [h, hr]

/-- A host `HOSTIN` write sets `INV` even with a same-cycle read. -/
theorem ctrl_inv_host_write_wins (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (state : Bool) (hst : s.ctrl.inv = state)
    (hin : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "HOSTIN").isSome = true) :
    (Metronome.Machine.ctrlNext s hw ci frozen).inv = true := by
  rw [ctrl_inv_bridge s hw ci frozen state true hst hin]
  simp [Metronome.Moves.invNext]

/-- A `HOST.IN` read with no host write clears `INV`. -/
theorem ctrl_inv_read_clears (s : Metronome.Machine.State)
    (hw : Option Metronome.Machine.HostWr) (ci : Metronome.Machine.CtrlIn) (frozen : Bool)
    (state : Bool) (hst : s.ctrl.inv = state)
    (hin : ((Metronome.Machine.Util.hwByte hw "CTRL" 0) "HOSTIN").isSome = false)
    (hr : ci.hostInRead = true) :
    (Metronome.Machine.ctrlNext s hw ci frozen).inv = false := by
  rw [ctrl_inv_bridge s hw ci frozen state false hst hin]
  simp [Metronome.Moves.invNext, hr]

/-! ## The `MEMHAZ` event shape -/

/-- The machine's `MEMHAZ` event is the cut's `memhazEventOf`. -/
theorem memhaz_event_bridge (rdPd : BitVec 6) (haz ready someRead : Bool)
    (hread : (!(rdPd == 0)) = someRead) :
    (haz || (someRead && !ready)) = Metronome.Moves.memhazEventOf rdPd haz ready := by
  rw [← hread]
  rfl

/-- A `P0.D` read while `!RDY` raises the event. -/
theorem memhaz_event_of_read (rdPd : BitVec 6) (haz : Bool)
    (h : (!(rdPd == 0)) = true) :
    (haz || (true && !false)) = Metronome.Moves.memhazEventOf rdPd haz false := by
  rw [← h]
  rfl

/-! ## The machine's decoders against the cut's tables

The machine's `dstOp`/`srcOp` are `Array.getD` lookups into `Array.map`ped name
tables, and its `dstGroup` is an `Array.findIdx?` search.  `Array.findIdx?.loop`
and `String.splitOnAux` are `@[irreducible]` in Lean 4.35.0 core, so the kernel
cannot evaluate all of them.  `dstOp_eq`/`srcOp_eq` rewrite the array lookups to
list-indexed form, which reduces the *fixed* names (21 of the 61 destination
names, and both source names of interest) to their constructors.  The group
table is fully checked in the kernel (`dstGroup_all`); the `L.SYM`/`T.STOP`/
`NULL` *kind* of the 40 parsed destination names is the single global hypothesis
`DstKindTable`, checked by compiled evaluation in `decode_check` (see
`commands.log`). -/

/-- The machine's `dstOp` is the name table's decoder of the code's entry. -/
theorem dstOp_eq (i : Nat) :
    Metronome.Machine.dstOp i =
      ((Metronome.Machine.Tables.dstNames[i]?).map
        Metronome.Machine.Util.dstOfName).getD .null := by
  simp only [Metronome.Machine.dstOp, Metronome.Machine.Util.dstOps,
    Array.getD_eq_getD_getElem?, Array.getElem?_map]

/-- The machine's `srcOp` is the name table's decoder of the code's entry. -/
theorem srcOp_eq (i : Nat) :
    Metronome.Machine.srcOp i =
      ((Metronome.Machine.Tables.srcNames[i]?).map
        Metronome.Machine.Util.srcOfName).getD .zero := by
  simp only [Metronome.Machine.srcOp, Metronome.Machine.Util.srcOps,
    Array.getD_eq_getD_getElem?, Array.getElem?_map]

/-- The class of a destination decoder value: 0 `NULL`, 1 `L.SYM`, 2 `T.STOP`,
3 anything else. -/
def dstClassNat : Metronome.Machine.DstOp → Nat
  | .null => 0
  | .lsym _ => 1
  | .stop => 2
  | _ => 3

/-- Constructor class of a source decoder value. -/
def srcClassNat : Metronome.Machine.SrcOp → Nat
  | .pD => 1
  | .hostIn => 2
  | _ => 0

/-- The cut group code of a destination code, as a `Nat` (31 = none). -/
def dgNat (d : Nat) : Nat := (dgTable (BitVec.ofNat 6 d)).toNat

/-- The machine's `dstGroup` array of every one of the 64 codes is the cut's
group code (31 = no group). -/
theorem dstGroup_all :
    (List.range 64).all (fun d => Metronome.Machine.Util.dstGroup.getD d none ==
      (if dgNat d == 31 then none else some (dgNat d))) = true := by
  simp only [Array.getD_eq_getD_getElem?, dstGroup_getElem?_wg, dgNat]
  decide

theorem dstGroup_of_code (d : Nat) (hd : d < 64) :
    Metronome.Machine.Util.dstGroup.getD d none =
      (if dgNat d == 31 then none else some (dgNat d)) := by
  have h := List.all_eq_true.1 dstGroup_all d (by simpa [List.mem_range] using hd)
  simpa using h

theorem ofNat_toNat_6 (v : BitVec 6) : BitVec.ofNat 6 v.toNat = v := by
  rw [BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq v

theorem dgNat_beq_zero (d : Nat) :
    (dgNat d == 0) = (dgTable (BitVec.ofNat 6 d) == dgLSym) := by
  rw [Bool.eq_iff_iff]
  unfold dgNat dgLSym
  rw [beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]
  simp

theorem dgNat_beq_one (d : Nat) :
    (dgNat d == 1) = (dgTable (BitVec.ofNat 6 d) == dgTStop) := by
  rw [Bool.eq_iff_iff]
  unfold dgNat dgTStop
  rw [beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]
  simp

theorem dgNat_beq_31 (d : Nat) :
    (dgNat d == 31) = (dgTable (BitVec.ofNat 6 d) == dgNone) := by
  rw [Bool.eq_iff_iff]
  unfold dgNat dgNone
  rw [beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]
  simp

/-- The machine's destination decoder kind, as the cut's group table implies it.
One global hypothesis, checked by compiled evaluation (`decode_check`).  The
kernel cannot reduce `String.splitOnAux` (`@[irreducible]` in Lean 4.35.0 core),
so the parsed destination names cannot be decoded in the kernel; the 21 fixed
names are kernel-checked in `dstClass_fixed`. -/
def DstKindTable : Prop :=
  ∀ d, d < 64 → dstClassNat (Metronome.Machine.dstOp d) =
    (if dgNat d == 0 then 1 else if dgNat d == 1 then 2 else if dgNat d == 31 then 0 else 3)

/-- The fixed-name part of the destination table is kernel-checked. -/
theorem dstClass_fixed :
    ([ "L.SYM", "L.DBIT", "L.XOR", "T.STOP", "FLAGS.SET", "FLAGS.CLR", "ACC.LD",
       "ACC.ADD", "ACC.SUB", "ACC.AND", "ACC.OR", "ACC.XOR", "ACC.CMP", "P0.AL",
       "P0.AH", "P0.W", "P0.R", "HOST.OUT", "CW.AL", "CW.AH", "CW.D" ].map
        (fun n => dstClassNat (Metronome.Machine.Util.dstOfName n))) =
      [1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] := by
  decide

/-- The cut's two source codes decode as `P0.D` and `HOST.IN`. -/
theorem srcOp_cut : srcClassNat (Metronome.Machine.srcOp 33) = 1 ∧
    srcClassNat (Metronome.Machine.srcOp 38) = 2 := by
  rw [srcOp_eq, srcOp_eq]
  constructor <;> decide

/-- Kind arithmetic: a class of `0` forces the `NULL` branch. -/
theorem kind_zero {c1 c2 c3 : Bool}
    (h : (if c1 then 1 else if c2 then 2 else if c3 then 0 else 3) = 0) :
    c3 = true := by
  revert h; cases c1 <;> cases c2 <;> cases c3 <;> decide

/-- Kind arithmetic: a class of `1` forces the `L.SYM` branch. -/
theorem kind_one {c1 c2 c3 : Bool}
    (h : (if c1 then 1 else if c2 then 2 else if c3 then 0 else 3) = 1) :
    c1 = true := by
  revert h; cases c1 <;> cases c2 <;> cases c3 <;> decide

/-- Kind arithmetic: a class of `2` forces the `T.STOP` branch. -/
theorem kind_two {c1 c2 c3 : Bool}
    (h : (if c1 then 1 else if c2 then 2 else if c3 then 0 else 3) = 2) :
    c1 = false ∧ c2 = true := by
  revert h; cases c1 <;> cases c2 <;> cases c3 <;> decide

/-- Kind arithmetic: a class of `3` forces all three branches away. -/
theorem kind_three {c1 c2 c3 : Bool}
    (h : (if c1 then 1 else if c2 then 2 else if c3 then 0 else 3) = 3) :
    c1 = false ∧ c2 = false ∧ c3 = false := by
  revert h; cases c1 <;> cases c2 <;> cases c3 <;> decide

/-! ## Keys

The cut keys a move by its write group, and for the two keyed groups also by the
executing line (`L.SYM`) or thread (`T.STOP`).  The key is a pair of `Nat`s, the
same shape as the machine's `moveGroup` key, so the fold's `seen` list can be
compared directly. -/

/-- The key discriminator: the executing line for `L.SYM`, the thread for
`T.STOP`, `0` otherwise. -/
def disc (s : Slot) : Nat :=
  if s.group == dgLSym then s.line.toNat
  else if s.group == dgTStop then s.thread.toNat else 0

/-- A key: write group and discriminator, both as `Nat`. -/
abbrev Key := Nat × Nat

/-- The cut key: no key for `NULL`, else the group and the discriminator. -/
def slotKey (s : Slot) : Option Key :=
  if s.group == dgNone then none else some (s.group.toNat, disc s)

/-- The machine key of a slot: no key for a disabled slot. -/
def slotKeyOf (s : Slot) : Option Key :=
  if s.enabled then slotKey s else none

theorem disc_lsym {s : Slot} (h : (s.group == dgLSym) = true) :
    disc s = s.line.toNat := by
  simp [disc, h]

theorem disc_tstop {s : Slot} (h : (s.group == dgTStop) = true) :
    disc s = s.thread.toNat := by
  have hne : (s.group == dgLSym) = false := by
    rw [beq_iff_eq] at h
    rw [h]
    decide
  simp [disc, hne, h]

/-- Two `NULL` slots never contend (neither has a write port). -/
theorem sameKey_none_key (a b : Slot) (ha : a.group = dgNone) (hb : b.group = dgNone) :
    sameKey a b = true := by
  have hgg : (a.group == b.group) = true := by rw [ha, hb]; decide
  have hgl : (!(a.group == dgLSym) || (a.line == b.line)) = true := by
    have h : (a.group == dgLSym) = false := by rw [ha]; decide
    rw [h]; simp
  have hgt : (!(a.group == dgTStop) || (a.thread == b.thread)) = true := by
    have h : (a.group == dgTStop) = false := by rw [ha]; decide
    rw [h]; simp
  rw [sameKey, hgg, hgl, hgt]
  rfl

/-- `sameKey` compares exactly the two slots' keys. -/
theorem sameKey_iff_slotKey (a b : Slot) : sameKey a b = true ↔ slotKey a = slotKey b := by
  constructor
  · intro h
    rw [sameKey, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hgg, hgl⟩, hgt⟩ := h
    have hg : a.group = b.group := by simpa using hgg
    have hdisc : disc a = disc b := by
      by_cases h1 : (a.group == dgLSym) = true
      · have h1' : (b.group == dgLSym) = true := by rw [← hg]; exact h1
        rw [disc_lsym h1, disc_lsym h1']
        have hl : (a.line == b.line) = true := by
          have hh := hgl
          rw [h1] at hh
          simpa using hh
        have hle : a.line = b.line := by simpa using hl
        rw [hle]
      · by_cases h2 : (a.group == dgTStop) = true
        · have h2' : (b.group == dgTStop) = true := by rw [← hg]; exact h2
          rw [disc_tstop h2, disc_tstop h2']
          have ht : (a.thread == b.thread) = true := by
            have hh := hgt
            rw [h2] at hh
            simpa using hh
          have hte : a.thread = b.thread := by simpa using ht
          rw [hte]
        · have hb1 : (b.group == dgLSym) = false := by rw [← hg]; simpa using h1
          have hb2 : (b.group == dgTStop) = false := by rw [← hg]; simpa using h2
          simp [disc, h1, h2, hb1, hb2]
    by_cases hn : (a.group == dgNone) = true
    · have hnb : (b.group == dgNone) = true := by rw [← hg]; exact hn
      simp [slotKey, hn, hnb]
    · have hnb : (b.group == dgNone) = false := by rw [← hg]; simpa using hn
      simp [slotKey, hn, hnb, hg, hdisc]
  · intro h
    by_cases hn : (a.group == dgNone) = true
    · have hga : a.group = dgNone := by simpa using hn
      have hka : slotKey a = none := by simp [slotKey, hn]
      rw [hka] at h
      have hb : slotKey b = none := h.symm
      have hnb : (b.group == dgNone) = true := by
        by_cases hbf : (b.group == dgNone) = true
        · exact hbf
        · have hbf' : (b.group == dgNone) = false := by simpa using hbf
          simp [slotKey, hbf'] at hb
      have hgb : b.group = dgNone := by simpa using hnb
      exact sameKey_none_key a b hga hgb
    · have hna : slotKey a = some (a.group.toNat, disc a) := by simp [slotKey, hn]
      rw [hna] at h
      have hbf : (b.group == dgNone) = false := by
        by_cases hbt : (b.group == dgNone) = true
        · have hbn : slotKey b = none := by simp [slotKey, hbt]
          rw [hbn] at h
          exact absurd h (by simp)
        · simpa using hbt
      have hb : slotKey b = some (b.group.toNat, disc b) := by simp [slotKey, hbf]
      rw [hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hgrp, hdisc⟩ := h
      have hgrpe : a.group = b.group := BitVec.eq_of_toNat_eq hgrp
      have hgg : (a.group == b.group) = true := by rw [beq_iff_eq]; exact hgrpe
      have hgl : (!(a.group == dgLSym) || (a.line == b.line)) = true := by
        by_cases h1 : (a.group == dgLSym) = true
        · have h1' : (b.group == dgLSym) = true := by rw [← hgrpe]; exact h1
          have hl : a.line.toNat = b.line.toNat := by
            rw [← disc_lsym h1, ← disc_lsym h1']
            exact hdisc
          have hle : a.line = b.line := BitVec.eq_of_toNat_eq hl
          rw [h1, hle]
          simp
        · have h1f : (a.group == dgLSym) = false := by simpa using h1
          rw [h1f]
          simp
      have hgt : (!(a.group == dgTStop) || (a.thread == b.thread)) = true := by
        by_cases h2 : (a.group == dgTStop) = true
        · have h2' : (b.group == dgTStop) = true := by rw [← hgrpe]; exact h2
          have ht : a.thread.toNat = b.thread.toNat := by
            rw [← disc_tstop h2, ← disc_tstop h2']
            exact hdisc
          have hte : a.thread = b.thread := BitVec.eq_of_toNat_eq ht
          rw [h2, hte]
          simp
        · have h2f : (a.group == dgTStop) = false := by simpa using h2
          rw [h2f]
          simp
      rw [sameKey, hgg, hgl, hgt]
      rfl

/-- The machine's move key for a destination code, line and thread. -/
def codeKey (d line thread : Nat) : Option Key :=
  if dgTable (BitVec.ofNat 6 d) == dgNone then none
  else some (dgNat d,
    if dgTable (BitVec.ofNat 6 d) == dgLSym then line
    else if dgTable (BitVec.ofNat 6 d) == dgTStop then thread else 0)

/-- The machine's `moveGroup` is the cut's code key.  The only non-kernel input
is `hkind`, the decoder kind table. -/
theorem moveGroup_eq_codeKey (hkind : DstKindTable) (m : Metronome.Machine.Move)
    (hd : m.dst < 64) :
    Metronome.Machine.moveGroup m = codeKey m.dst m.line m.thread := by
  have hgrp := dstGroup_of_code m.dst hd
  have hcl := hkind m.dst hd
  unfold Metronome.Machine.moveGroup
  cases hdt : Metronome.Machine.dstOp m.dst with
  | null =>
    rw [hdt] at hcl
    simp only [dstClassNat] at hcl
    have hz : (dgNat m.dst == 31) = true := kind_zero hcl.symm
    have hzt : (dgTable (BitVec.ofNat 6 m.dst) == dgNone) = true := by
      rw [← dgNat_beq_31]; exact hz
    simp [codeKey, hgrp, hz, hzt]
  | lsym k =>
    rw [hdt] at hcl
    simp only [dstClassNat] at hcl
    have h1 : (dgNat m.dst == 0) = true := kind_one hcl.symm
    have h1t : (dgTable (BitVec.ofNat 6 m.dst) == dgLSym) = true := by
      rw [← dgNat_beq_zero]; exact h1
    have hz : (dgNat m.dst == 31) = false := by
      rw [beq_iff_eq] at h1; rw [h1]; decide
    have hzt : (dgTable (BitVec.ofNat 6 m.dst) == dgNone) = false := by
      rw [← dgNat_beq_31]; exact hz
    simp [codeKey, hgrp, h1t, hz, hzt]
  | stop =>
    rw [hdt] at hcl
    simp only [dstClassNat] at hcl
    obtain ⟨h1f, h2t⟩ := kind_two hcl.symm
    have h1t : (dgTable (BitVec.ofNat 6 m.dst) == dgLSym) = false := by
      rw [← dgNat_beq_zero]; exact h1f
    have h2t' : (dgTable (BitVec.ofNat 6 m.dst) == dgTStop) = true := by
      rw [← dgNat_beq_one]; exact h2t
    have hz : (dgNat m.dst == 31) = false := by
      rw [beq_iff_eq] at h2t; rw [h2t]; decide
    have hzt : (dgTable (BitVec.ofNat 6 m.dst) == dgNone) = false := by
      rw [← dgNat_beq_31]; exact hz
    simp [codeKey, hgrp, h1t, h2t', hz, hzt]
  | fset | fclr | acc _ | reg _ | shLd _ | shSh _ | shCfg _ | cntLo _ | cntHi _ | cntDec _
  | lfSt _ | lfB _ _ | pAl | pAh | pW | pR | sAdv _ | sRx _ | sCtl _ | lCtl _ | hostOut
  | cwAl | cwAh | cwD =>
    rw [hdt] at hcl
    simp only [dstClassNat] at hcl
    obtain ⟨h1f, h2f, h3f⟩ := kind_three hcl.symm
    have h1t : (dgTable (BitVec.ofNat 6 m.dst) == dgLSym) = false := by
      rw [← dgNat_beq_zero]; exact h1f
    have h2t : (dgTable (BitVec.ofNat 6 m.dst) == dgTStop) = false := by
      rw [← dgNat_beq_one]; exact h2f
    have h3t : (dgTable (BitVec.ofNat 6 m.dst) == dgNone) = false := by
      rw [← dgNat_beq_31]; exact h3f
    simp [codeKey, hgrp, h1f, h2f, h3f, h1t, h2t, h3t]

/-- A padded (`NULL`) move has no key. -/
theorem moveGroup_null_of_dst_zero (hkind : DstKindTable) (m : Metronome.Machine.Move)
    (h : m.dst = 0) :
    Metronome.Machine.moveGroup m = none := by
  have hd0 : m.dst < 64 := by rw [h]; decide
  rw [moveGroup_eq_codeKey hkind m hd0, h]
  have h0 : (dgTable (BitVec.ofNat 6 0) == dgNone) = true := by
    rw [beq_iff_eq, ← BitVec.toNat_inj]
    simpa [dgNone] using dgTable_null_31
  simp [codeKey, h0]

/-- The machine key of a move is the cut key of the slot it executes. -/
theorem moveGroup_eq_slotKey (hkind : DstKindTable) (m : Metronome.Machine.Move)
    (s : Slot) (hd : m.dst = s.dst.toNat) (hgrp : s.group = dgTable s.dst)
    (hline : m.line = s.line.toNat) (hthread : m.thread = s.thread.toNat) :
    Metronome.Machine.moveGroup m = slotKey s := by
  have hdlt : m.dst < 64 := by rw [hd]; exact s.dst.isLt
  rw [moveGroup_eq_codeKey hkind m hdlt, hd]
  simp [codeKey, slotKey, disc, dgNat, ofNat_toNat_6, hgrp, hline, hthread]

/-! ## The per-cycle move table -/

/-- The six machine moves of a cycle, in slot order. -/
def six (m : Nat → Metronome.Machine.Move) : List Metronome.Machine.Move :=
  [m 0, m 1, m 2, m 3, m 4, m 5]

theorem six_get? (m : Nat → Metronome.Machine.Move) {k : Nat} (hk : k < 6) :
    (six m)[k]? = some (m k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem six_take_succ (m : Nat → Metronome.Machine.Move) {n : Nat} (hn : n < 6) :
    (six m).take (n + 1) = (six m).take n ++ [m n] := by
  rw [List.take_add_one, six_get? m hn]
  rfl

/-- The per-cycle move table: the six machine moves' keys are the slots' keys. -/
def MoveTable (b : Bundle) (ms : List Metronome.Machine.Move) : Prop :=
  ms.length = 6 ∧ ∀ k, k < 6 → ∀ mm, ms[k]? = some mm →
    Metronome.Machine.moveGroup mm = slotKeyOf (b.get k)

/-- The abstraction map: the machine's move fields are the slot's, disabled slots
are padded with `NULL`. -/
structure MoveAgree (b : Bundle) (m : Nat → Metronome.Machine.Move) : Prop where
  dst : ∀ k, k < 6 → (b.get k).enabled = true → (m k).dst = (b.get k).dst.toNat
  pad : ∀ k, k < 6 → (b.get k).enabled = false → (m k).dst = 0
  grp : ∀ k, k < 6 → (b.get k).group = dgTable (b.get k).dst
  line : ∀ k, k < 6 → (m k).line = (b.get k).line.toNat
  thread : ∀ k, k < 6 → (m k).thread = (b.get k).thread.toNat

/-- `MoveAgree` gives the move table. -/
theorem moveTable_of_agree (hkind : DstKindTable) (b : Bundle)
    (m : Nat → Metronome.Machine.Move) (h : MoveAgree b m) : MoveTable b (six m) := by
  refine ⟨rfl, ?_⟩
  intro k hk mm hmm
  rw [six_get? m hk] at hmm
  simp only [Option.some.injEq] at hmm
  subst hmm
  by_cases hen : (b.get k).enabled = true
  · rw [slotKeyOf, if_pos hen]
    exact moveGroup_eq_slotKey hkind (m k) (b.get k) (h.dst k hk hen) (h.grp k hk)
      (h.line k hk) (h.thread k hk)
  · have henf : (b.get k).enabled = false := by simpa using hen
    rw [slotKeyOf, if_neg (by simpa using hen)]
    exact moveGroup_null_of_dst_zero hkind (m k) (h.pad k hk henf)

/-! ## The fold invariant

`Machine.resolveMoves` folds the six enabled moves in `(core, move index)` order,
keeping the first move of each key and raising the conflict flag on a repeat.
The cut computes the same thing slot by slot (`winAt`, `conflictEv`).  The two
are bridged by a fold invariant over the prefix of processed slots: after `n`
slots, the winner list is `ws0 ++ winsFrom seen0 m n`, the `seen` list contains
exactly the keys `keySeen seen0 (keyAt m) n`, and the conflict flag is
`cf0 || dupFrom seen0 (keyAt m) n`.  `fold_prefix` proves the invariant for every
`n ≤ 6` by induction on `n`; `resolveMoves_winners`/`resolveMoves_conflict`
instantiate it at six. -/

/-- The machine key of slot `j` of a cycle. -/
def keyAt (m : Nat → Metronome.Machine.Move) (j : Nat) : Option Key :=
  Metronome.Machine.moveGroup (m j)

/-- The fold state: winners, seen keys, conflict flag. -/
abbrev St := List Metronome.Machine.Move × List Key × Bool

/-- One step of `Machine.resolveMoves`, as a function on the state. -/
def stepOn (st : St) (mm : Metronome.Machine.Move) : St :=
  let (ws, seen, cf) := st
  match Metronome.Machine.moveGroup mm with
  | none => st
  | some g => if seen.contains g then (ws, seen, true) else (ws ++ [mm], seen ++ [g], cf)

/-- The machine's fold, with an explicit accumulator. -/
def resolveAux (ms : List Metronome.Machine.Move) (acc : St) : St :=
  ms.foldl stepOn acc

/-- `resolveMoves` is `resolveAux` from the empty state. -/
theorem resolveMoves_eq (ms : List Metronome.Machine.Move) :
    Metronome.Machine.resolveMoves ms
      = ((resolveAux ms ([], [], false)).1, (resolveAux ms ([], [], false)).2.2) := rfl

theorem stepOn_triple (ws : List Metronome.Machine.Move) (seen : List Key) (cf : Bool)
    (mm : Metronome.Machine.Move) :
    stepOn (ws, seen, cf) mm =
      (match Metronome.Machine.moveGroup mm with
       | none => (ws, seen, cf)
       | some g => if seen.contains g then (ws, seen, true)
         else (ws ++ [mm], seen ++ [g], cf)) := rfl

theorem stepOn_none (st : St) (mm : Metronome.Machine.Move)
    (hg : Metronome.Machine.moveGroup mm = none) : stepOn st mm = st := by
  obtain ⟨a, b, c⟩ := st
  simp [stepOn, hg]

theorem stepOn_contains (st : St) (mm : Metronome.Machine.Move) (g : Key)
    (hg : Metronome.Machine.moveGroup mm = some g) (hc : st.2.1.contains g = true) :
    stepOn st mm = (st.1, st.2.1, true) := by
  obtain ⟨a, b, c⟩ := st
  have hc' : b.contains g = true := hc
  rw [stepOn_triple, hg]
  dsimp only
  rw [if_pos hc']

theorem stepOn_new (st : St) (mm : Metronome.Machine.Move) (g : Key)
    (hg : Metronome.Machine.moveGroup mm = some g) (hc : st.2.1.contains g = false) :
    stepOn st mm = (st.1 ++ [mm], st.2.1 ++ [g], st.2.2) := by
  obtain ⟨a, b, c⟩ := st
  have hc' : b.contains g = false := hc
  rw [stepOn_triple, hg]
  dsimp only
  rw [if_neg (by rw [hc']; decide)]

/-- The keys seen before slot `n`: the initial ones plus the prefix's keys. -/
def keySeen (seen0 : List Key) (g : Nat → Option Key) (n : Nat) (kk : Key) : Bool :=
  seen0.contains kk || (List.range n).any (fun j => g j == some kk)

/-- Slot `n` of the prefix wins its key. -/
def winFrom (seen0 : List Key) (g : Nat → Option Key) (n : Nat) : Bool :=
  match g n with
  | none => false
  | some kk => !(keySeen seen0 g n kk)

/-- A conflict occurred in the first `n` slots. -/
def dupFrom (seen0 : List Key) (g : Nat → Option Key) : Nat → Bool
  | 0 => false
  | n + 1 => dupFrom seen0 g n ||
      (match g n with
       | none => false
       | some kk => keySeen seen0 g n kk)

/-- The winners of the first `n` slots. -/
def winsFrom (seen0 : List Key) (m : Nat → Metronome.Machine.Move) (n : Nat) :
    List Metronome.Machine.Move :=
  (List.range n).filterMap (fun j => if winFrom seen0 (keyAt m) j then some (m j) else none)

theorem keySeen_zero (seen0 : List Key) (g : Nat → Option Key) (kk : Key) :
    keySeen seen0 g 0 kk = seen0.contains kk := by
  simp [keySeen]

theorem keySeen_succ (seen0 : List Key) (g : Nat → Option Key) (n : Nat) (kk : Key) :
    keySeen seen0 g (n + 1) kk = (keySeen seen0 g n kk || (g n == some kk)) := by
  unfold keySeen
  rw [List.range_succ, List.any_append]
  simp [List.any_cons, Bool.or_assoc]

theorem beq_comm_key (a b : Key) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]

theorem winsFrom_zero (seen0 : List Key) (m : Nat → Metronome.Machine.Move) :
    winsFrom seen0 m 0 = [] := by
  simp [winsFrom]

theorem winsFrom_succ (seen0 : List Key) (m : Nat → Metronome.Machine.Move) (n : Nat) :
    winsFrom seen0 m (n + 1) =
      winsFrom seen0 m n ++
        (if winFrom seen0 (keyAt m) n then [m n] else []) := by
  unfold winsFrom
  rw [List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, List.append_nil]
  cases h : winFrom seen0 (keyAt m) n <;> simp [h]

/-- `filterMap` over a `range` only depends on the values below the bound. -/
theorem filterMap_range_congr {α : Type} (f g : Nat → Option α) :
    ∀ (n : Nat), (∀ k, k < n → f k = g k) →
      (List.range n).filterMap f = (List.range n).filterMap g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.filterMap_append, List.filterMap_append,
      filterMap_range_congr f g n (fun k hk => h k (by omega))]
    simp only [List.filterMap_cons, List.filterMap_nil]
    rw [h n (by omega)]

/-- The fold invariant over the first `n ≤ 6` slots. -/
theorem fold_prefix (m : Nat → Metronome.Machine.Move) :
    ∀ (n : Nat), n ≤ 6 → ∀ (ws0 : List Metronome.Machine.Move) (seen0 : List Key) (cf0 : Bool),
      (resolveAux ((six m).take n) (ws0, seen0, cf0)).1 = ws0 ++ winsFrom seen0 m n ∧
      (∀ kk, (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk =
        keySeen seen0 (keyAt m) n kk) ∧
      (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.2 =
        (cf0 || dupFrom seen0 (keyAt m) n) := by
  intro n
  induction n with
  | zero =>
    intro _ ws0 seen0 cf0
    refine ⟨?_, ?_, ?_⟩
    · simp [resolveAux, winsFrom_zero]
    · intro kk; simp [resolveAux, keySeen_zero]
    · simp [resolveAux, dupFrom]
  | succ n ih =>
    intro hn ws0 seen0 cf0
    have hn6 : n < 6 := by omega
    have hnle : n ≤ 6 := by omega
    obtain ⟨hws, hseen, hcf⟩ := ih hnle ws0 seen0 cf0
    rw [six_take_succ m hn6]
    have hfold : resolveAux ((six m).take n ++ [m n]) (ws0, seen0, cf0)
        = stepOn (resolveAux ((six m).take n) (ws0, seen0, cf0)) (m n) := by
      simp only [resolveAux, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hfold]
    refine ⟨?_, ?_, ?_⟩
    · -- winners
      cases hg : keyAt m n with
      | none =>
        rw [stepOn_none _ _ (by simpa [keyAt] using hg), hws]
        rw [winsFrom_succ]
        have hw : winFrom seen0 (keyAt m) n = false := by simp [winFrom, hg]
        rw [hw]; simp
      | some kk =>
        by_cases hc : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = true
        · rw [stepOn_contains _ _ _ (by simpa [keyAt] using hg) hc, hws]
          rw [winsFrom_succ]
          have hks : keySeen seen0 (keyAt m) n kk = true := by
            rw [← hseen kk]; exact hc
          have hw : winFrom seen0 (keyAt m) n = false := by simp [winFrom, hg, hks]
          rw [hw]; simp
        · have hcf' : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = false := by
            simpa using hc
          rw [stepOn_new _ _ _ (by simpa [keyAt] using hg) hcf', hws]
          rw [winsFrom_succ]
          have hks : keySeen seen0 (keyAt m) n kk = false := by
            rw [← hseen kk]; exact hcf'
          have hw : winFrom seen0 (keyAt m) n = true := by simp [winFrom, hg, hks]
          rw [hw]
          simp [List.append_assoc]
    · -- seen
      intro kk'
      cases hg : keyAt m n with
      | none =>
        rw [stepOn_none _ _ (by simpa [keyAt] using hg), hseen kk', keySeen_succ]
        simp [hg]
      | some kk =>
        by_cases hc : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = true
        · rw [stepOn_contains _ _ _ (by simpa [keyAt] using hg) hc, hseen kk', keySeen_succ, hg]
          have hks : keySeen seen0 (keyAt m) n kk = true := by
            rw [← hseen kk]; exact hc
          by_cases hkk : kk' = kk
          · subst hkk
            rw [hks]; simp
          · have hbeq : (some kk == some kk') = false := by
              rw [Bool.eq_false_iff]
              intro h2
              rw [beq_iff_eq, Option.some.injEq] at h2
              exact hkk h2.symm
            rw [hbeq]; simp
        · have hcf' : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = false := by
            simpa using hc
          rw [stepOn_new _ _ _ (by simpa [keyAt] using hg) hcf']
          dsimp only
          rw [List.contains_append, List.contains_cons, List.contains_nil, beq_comm_key kk' kk,
            hseen kk', keySeen_succ, hg]
          simp
    · -- conflict
      cases hg : keyAt m n with
      | none =>
        rw [stepOn_none _ _ (by simpa [keyAt] using hg), hcf]
        simp [dupFrom, hg]
      | some kk =>
        by_cases hc : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = true
        · rw [stepOn_contains _ _ _ (by simpa [keyAt] using hg) hc]
          dsimp only
          have hks : keySeen seen0 (keyAt m) n kk = true := by
            rw [← hseen kk]; exact hc
          simp [dupFrom, hg, hks]
        · have hcf' : (resolveAux ((six m).take n) (ws0, seen0, cf0)).2.1.contains kk = false := by
            simpa using hc
          rw [stepOn_new _ _ _ (by simpa [keyAt] using hg) hcf']
          dsimp only
          rw [hcf]
          have hks : keySeen seen0 (keyAt m) n kk = false := by
            rw [← hseen kk]; exact hcf'
          simp [dupFrom, hg, hks]

/-! ## Instantiation at six slots -/

theorem six_take_six (m : Nat → Metronome.Machine.Move) : (six m).take 6 = six m := rfl

theorem keyAt_eq {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {k : Nat} (hk : k < 6) :
    keyAt m k = slotKeyOf (b.get k) :=
  hMT.2 k hk (m k) (six_get? m hk)

theorem slotKeyOf_none_iff (s : Slot) : slotKeyOf s = none ↔ validAt s = false := by
  unfold slotKeyOf slotKey validAt
  by_cases hen : s.enabled = true <;> by_cases hg : (s.group == dgNone) = true <;>
    simp [hen, hg]

theorem keyAt_valid_of_some {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {k : Nat} {kk : Key} (hk : k < 6)
    (h : keyAt m k = some kk) : validAt (b.get k) = true := by
  have hk' := keyAt_eq hMT hk
  rw [hk'] at h
  by_cases hv : validAt (b.get k) = true
  · exact hv
  · have hv' : validAt (b.get k) = false := by simpa using hv
    rw [(slotKeyOf_none_iff _).2 hv'] at h
    simp at h

theorem slotKey_of_valid {s : Slot} (hv : validAt s = true) :
    slotKey s = some (s.group.toNat, disc s) := by
  unfold slotKey
  have hg : (s.group == dgNone) = false := by
    have h := hv
    unfold validAt at h
    rw [Bool.and_eq_true] at h
    simpa using h.2
  rw [if_neg (by simpa using hg)]

theorem keyAt_of_valid {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {k : Nat} (hk : k < 6)
    (hv : validAt (b.get k) = true) :
    keyAt m k = some ((b.get k).group.toNat, disc (b.get k)) := by
  rw [keyAt_eq hMT hk, slotKeyOf]
  have hen : (b.get k).enabled = true := by
    have h := hv
    unfold validAt at h
    rw [Bool.and_eq_true] at h
    exact h.1
  rw [if_pos hen]
  exact slotKey_of_valid hv

/-- The fold's pointwise blocking test is the cut's `sameKey` test. -/
theorem sameKey_of_key {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {j k : Nat} (hj : j < 6) (hk : k < 6) {kk : Key}
    (hkk : keyAt m k = some kk) :
    (validAt (b.get j) && sameKey (b.get j) (b.get k)) = (keyAt m j == some kk) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hvj, hsk⟩ := h
    have hjkey : keyAt m j = some ((b.get j).group.toNat, disc (b.get j)) :=
      keyAt_of_valid hMT hj hvj
    have hkkey : keyAt m k = some ((b.get k).group.toNat, disc (b.get k)) :=
      keyAt_of_valid hMT hk (keyAt_valid_of_some hMT hk hkk)
    have hkk' : ((b.get k).group.toNat, disc (b.get k)) = kk := by
      rw [hkkey] at hkk
      simpa using hkk
    have hsk' := (sameKey_iff_slotKey _ _).1 hsk
    rw [slotKey_of_valid hvj, slotKey_of_valid (keyAt_valid_of_some hMT hk hkk)] at hsk'
    rw [beq_iff_eq, hjkey, ← hkk']
    exact hsk'
  · intro h
    rw [beq_iff_eq] at h
    have hvj := keyAt_valid_of_some hMT hj h
    have hvk := keyAt_valid_of_some hMT hk hkk
    have hjkey : keyAt m j = some ((b.get j).group.toNat, disc (b.get j)) :=
      keyAt_of_valid hMT hj hvj
    have hkkey : keyAt m k = some ((b.get k).group.toNat, disc (b.get k)) :=
      keyAt_of_valid hMT hk hvk
    rw [Bool.and_eq_true]
    refine ⟨hvj, ?_⟩
    rw [sameKey_iff_slotKey, slotKey_of_valid hvj, slotKey_of_valid hvk, ← hjkey, ← hkkey,
      h, hkk]

/-- The cut's `blocked` scan over the fold's keys. -/
theorem blocked_eq_any {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {k : Nat} (hk : k < 6) {kk : Key}
    (hkk : keyAt m k = some kk) :
    blocked b k = (List.range k).any (fun j => keyAt m j == some kk) := by
  unfold blocked
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [List.mem_range] at hj
    exact ⟨j, by simpa [List.mem_range] using hj,
      (sameKey_of_key (b := b) (m := m) hMT (j := j) (k := k) (by omega) hk hkk) ▸ h⟩
  · rintro ⟨j, hj, h⟩
    rw [List.mem_range] at hj
    exact ⟨j, by simpa [List.mem_range] using hj,
      (sameKey_of_key (b := b) (m := m) hMT (j := j) (k := k) (by omega) hk hkk).symm ▸ h⟩

/-- The fold's winner bit is the cut's `winAt`. -/
theorem winFrom_eq_winAt {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) {k : Nat} (hk : k < 6) :
    winFrom [] (keyAt m) k = winAt b k := by
  cases hg : keyAt m k with
  | none =>
    have hv : validAt (b.get k) = false :=
      (slotKeyOf_none_iff (b.get k)).1 (by rw [← keyAt_eq hMT hk]; exact hg)
    simp only [winFrom, hg, winAt, hv, Bool.false_and]
  | some kk =>
    have hv : validAt (b.get k) = true := keyAt_valid_of_some hMT hk hg
    have hblocked := blocked_eq_any hMT hk hg
    have hseen : keySeen [] (keyAt m) k kk = blocked b k := by
      rw [keySeen, hblocked]
      simp
    simp only [winFrom, hg, hseen, winAt, hv, Bool.true_and]

/-- `dupFrom` is the scan over the prefix. -/
theorem dupFrom_eq_any (seen0 : List Key) (g : Nat → Option Key) (n : Nat) :
    dupFrom seen0 g n =
      (List.range n).any (fun j => match g j with
        | none => false
        | some kk => keySeen seen0 g j kk) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show dupFrom seen0 g (n + 1) =
        (dupFrom seen0 g n || (match g n with
          | none => false
          | some kk => keySeen seen0 g n kk)) from rfl, ih]
    rw [List.range_succ, List.any_append]
    simp [List.any_cons]

/-- A `sameKey` pair has the same group code and discriminator. -/
theorem sameKey_fst {a b : Slot} (h : sameKey a b = true) :
    a.group.toNat = b.group.toNat ∧ disc a = disc b := by
  have hk := (sameKey_iff_slotKey _ _).1 h
  by_cases hn : (a.group == dgNone) = true
  · have hnb : (b.group == dgNone) = true := by
      by_cases hb : (b.group == dgNone) = true
      · exact hb
      · rw [slotKey, if_pos hn, slotKey, if_neg (by simpa using hb)] at hk
        simp at hk
    have hga : a.group = dgNone := by simpa using hn
    have hgb : b.group = dgNone := by simpa using hnb
    rw [hga, hgb]
    refine ⟨rfl, ?_⟩
    have h1 : (dgNone == dgLSym) = false := by decide
    have h2 : (dgNone == dgTStop) = false := by decide
    have hda : disc a = 0 := by simp [disc, hga, h1, h2]
    have hdb : disc b = 0 := by simp [disc, hgb, h1, h2]
    rw [hda, hdb]
  · have hna : slotKey a = some (a.group.toNat, disc a) := by
      rw [slotKey, if_neg (by simpa using hn)]
    rw [hna] at hk
    have hbf : (b.group == dgNone) = false := by
      by_cases hb : (b.group == dgNone) = true
      · rw [slotKey, if_pos hb] at hk
        simp at hk
      · simpa using hb
    rw [slotKey, if_neg (by simpa using hbf)] at hk
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    exact hk

/-- The fold's conflict flag is the cut's `conflictEv`. -/
theorem dupFrom_six {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) : dupFrom [] (keyAt m) 6 = conflictEv b := by
  rw [dupFrom_eq_any, conflictEv_eq_pairSameKey]
  unfold pairSameKey
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [List.mem_range] at hj
    have hj6 : j < 6 := by omega
    cases hg : keyAt m j with
    | none => simp [hg] at h
    | some kk =>
      simp only [hg] at h
      rw [keySeen] at h
      have hany : (List.range j).any (fun i => keyAt m i == some kk) = true := by
        simpa using h
      rw [List.any_eq_true] at hany
      obtain ⟨i, hi, hik⟩ := hany
      rw [List.mem_range] at hi
      refine ⟨j, by simpa [List.mem_range] using hj6, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨keyAt_valid_of_some hMT hj6 hg, ?_⟩
      rw [List.any_eq_true]
      exact ⟨i, by simpa [List.mem_range] using hi,
        (sameKey_of_key (b := b) (m := m) hMT (j := i) (k := j) (by omega) hj6 hg).symm ▸ hik⟩
  · rintro ⟨j, hj, h⟩
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true] at h
    obtain ⟨hvj, hinner⟩ := h
    rw [List.any_eq_true] at hinner
    obtain ⟨i, hi, hik⟩ := hinner
    rw [List.mem_range] at hi
    rw [Bool.and_eq_true] at hik
    obtain ⟨hvi, hski⟩ := hik
    have hkey := keyAt_of_valid hMT (by omega) hvj
    refine ⟨j, by simpa [List.mem_range] using hj, ?_⟩
    simp only [hkey]
    rw [keySeen]
    simp only [List.contains_nil, Bool.false_or]
    rw [List.any_eq_true]
    have hii : (keyAt m i == some ((b.get j).group.toNat, disc (b.get j))) = true := by
      rw [beq_iff_eq, keyAt_of_valid hMT (by omega) hvi]
      obtain ⟨h1, h2⟩ := sameKey_fst hski
      rw [h1, h2]
    exact ⟨i, by simpa [List.mem_range] using hi, hii⟩

/-- The machine's winner list is exactly the cut's `winAt` set, in slot order. -/
theorem resolveMoves_winners {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) :
    (Metronome.Machine.resolveMoves (six m)).1 =
      (List.range 6).filterMap (fun k => if winAt b k then some (m k) else none) := by
  rw [resolveMoves_eq]
  have h := (fold_prefix m 6 (Nat.le_refl 6) [] [] false).1
  rw [six_take_six] at h
  rw [h, List.nil_append]
  unfold winsFrom
  exact filterMap_range_congr _ _ 6 (fun k hk => by rw [winFrom_eq_winAt hMT hk])

/-- The machine's conflict flag is the cut's `conflictEv`. -/
theorem resolveMoves_conflict {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) :
    (Metronome.Machine.resolveMoves (six m)).2 = conflictEv b := by
  rw [resolveMoves_eq]
  have h := (fold_prefix m 6 (Nat.le_refl 6) [] [] false).2.2
  rw [six_take_six] at h
  rw [h]
  simp only [Bool.false_or]
  exact dupFrom_six hMT

/-! ## The per-group written word (`pick`)

The RTL's `pick(hits(mv_en, grp_v, G), c_dst, c_dat)` selects the lowest enabled
slot of group `G` and packs `{1, dst, data}`.  The machine's winner list selects
the first valid move of the key; for a group that is not keyed by line or thread
the two are the same slot, and both models write that slot's `{dst, data}`. -/

/-- A contender of a real group is a valid move of that group. -/
theorem contender_eq_valid_group (s : Slot) (G : BitVec 5) (hG : (G == dgNone) = false) :
    contender s G = (validAt s && (s.group == G)) := by
  unfold contender validAt
  by_cases h : (s.group == G) = true
  · have hgn : (s.group == dgNone) = false := by
      rw [beq_iff_eq] at h
      rw [h]
      exact hG
    simp [h, hgn]
  · simp [h]

/-- The bus-level hit of a slot of a real group is its "valid and in `G`" flag. -/
theorem hitAt_eq_valid_group (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6) (G : BitVec 5)
    (hG : (G == dgNone) = false) (q : Nat) (hq : q < 6) :
    hitAt en grp G q =
      (validAt ((bundleOf en grp dst dat xl xt).get q) &&
        (((bundleOf en grp dst dat xl xt).get q).group == G)) := by
  rw [hitAt_contender en grp dst dat xl xt G q hq]
  exact contender_eq_valid_group _ G hG

/-- Two valid slots of one non-keyed group contend. -/
theorem sameKey_of_group {a b : Slot} {G : BitVec 5}
    (hGa : (a.group == G) = true) (hGb : (b.group == G) = true)
    (hG0 : (G == dgLSym) = false) (hG1 : (G == dgTStop) = false) :
    sameKey a b = true := by
  have hgg : (a.group == b.group) = true := by
    rw [beq_iff_eq] at hGa hGb ⊢
    rw [hGa, hGb]
  have h0 : (a.group == dgLSym) = false := by
    rw [beq_iff_eq] at hGa
    rw [hGa]
    exact hG0
  have h1 : (a.group == dgTStop) = false := by
    rw [beq_iff_eq] at hGa
    rw [hGa]
    exact hG1
  rw [sameKey, hgg, h0, h1]
  simp

/-- The machine's winners of a non-keyed group: exactly the lowest valid slot of
the group, in slot order. -/
theorem winnerGroup_eq_singleton {b : Bundle} {m : Nat → Metronome.Machine.Move}
    (hMT : MoveTable b (six m)) (G : BitVec 5)
    (hG : (G == dgNone) = false) (hG0 : (G == dgLSym) = false)
    (hG1 : (G == dgTStop) = false)
    (k : Nat) (hk : k < 6) (hval : validAt (b.get k) = true)
    (hgrp : ((b.get k).group == G) = true)
    (hfirst : ∀ j, j < k → (validAt (b.get j) && ((b.get j).group == G)) = false) :
    (List.range 6).filterMap
      (fun q => if winAt b q && ((b.get q).group == G) then some (m q) else none) = [m k] := by
  have hwin : winAt b k = true := by
    refine winAt_true_of_unblocked hval ?_
    have h : ¬(blocked b k = true) := by
      intro hb
      obtain ⟨j, hj, hvj, hsk⟩ := (blocked_spec b k).1 hb
      have hgj : ((b.get j).group == (b.get k).group) = true := by
        have := hsk
        unfold sameKey at this
        rw [Bool.and_eq_true, Bool.and_eq_true] at this
        exact this.1.1
      have hg : ((b.get j).group == G) = true := by
        rw [beq_iff_eq] at hgj hgrp ⊢
        rw [hgj, hgrp]
      have hf := hfirst j hj
      simp [hvj, hg] at hf
    simpa using h
  have hother : ∀ q, q < 6 → q ≠ k → (winAt b q && ((b.get q).group == G)) = false := by
    intro q hq hne
    by_cases hqg : ((b.get q).group == G) = true
    · by_cases hlt : q < k
      · have hf := hfirst q hlt
        rw [hqg, Bool.and_true] at hf
        rw [winAt, hf, Bool.false_and, hqg, Bool.and_true]
      · have hgt : k < q := by omega
        have hbq : blocked b q = true := by
          rw [blocked_spec]
          exact ⟨k, hgt, hval, sameKey_of_group hgrp hqg hG0 hG1⟩
        rw [winAt_false_of_blocked hbq, hqg]
        simp
    · have hqf : ((b.get q).group == G) = false := by simpa using hqg
      rw [hqf, Bool.and_false]
  have hfm := filterMap_range_congr
    (fun q => if winAt b q && ((b.get q).group == G) then some (m q) else none)
    (fun q => if q = k then some (m k) else none) 6
    (fun q hq => by
      by_cases hqk : q = k
      · have htrue : (winAt b q && ((b.get q).group == G)) = true := by
          rw [hqk, hwin, hgrp]
          rfl
        rw [htrue, if_pos hqk, hqk]
        rfl
      · have h : (winAt b q && ((b.get q).group == G)) = false := hother q hq hqk
        rw [h]
        simp only [Bool.false_eq_true, if_false]
        rw [if_neg hqk])
  rw [hfm]
  have hrange : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [hrange]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The cut's `pickWord` of a non-keyed group is the lowest contender's word. -/
theorem pickWord_eq_word (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6) (G : BitVec 5)
    (k : Nat) (hk : k < 6)
    (hhit : hitAt en grp G k = true)
    (hfirst : ∀ j, j < k → hitAt en grp G j = false) :
    pickWord (hitsMask en grp G) dst dat =
      ⟨true, ((bundleOf en grp dst dat xl xt).get k).dst,
        ((bundleOf en grp dst dat xl xt).get k).data⟩ := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact (pick_first_0 en grp G dst dat hhit).trans (by rfl)
  · exact (pick_first_1 en grp G dst dat (hfirst 0 (by omega)) hhit).trans (by rfl)
  · exact (pick_first_2 en grp G dst dat (hfirst 0 (by omega)) (hfirst 1 (by omega))
      hhit).trans (by rfl)
  · exact (pick_first_3 en grp G dst dat (hfirst 0 (by omega)) (hfirst 1 (by omega))
      (hfirst 2 (by omega)) hhit).trans (by rfl)
  · exact (pick_first_4 en grp G dst dat (hfirst 0 (by omega)) (hfirst 1 (by omega))
      (hfirst 2 (by omega)) (hfirst 3 (by omega)) hhit).trans (by rfl)
  · exact (pick_first_5 en grp G dst dat (hfirst 0 (by omega)) (hfirst 1 (by omega))
      (hfirst 2 (by omega)) (hfirst 3 (by omega)) (hfirst 4 (by omega)) hhit).trans (by rfl)

/-- The machine's written word of a non-keyed group is the cut's `pickWord`, and
the cut's pick is the machine's only winner of the group. -/
theorem resolveMoves_pick (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (m : Nat → Metronome.Machine.Move) (G : BitVec 5)
    (hMT : MoveTable (bundleOf en grp dst dat xl xt) (six m))
    (hG : (G == dgNone) = false) (hG0 : (G == dgLSym) = false)
    (hG1 : (G == dgTStop) = false)
    (k : Nat) (hk : k < 6)
    (hhit : hitAt en grp G k = true)
    (hfirst : ∀ j, j < k → hitAt en grp G j = false) :
    (List.range 6).filterMap
        (fun q => if winAt (bundleOf en grp dst dat xl xt) q &&
          (((bundleOf en grp dst dat xl xt).get q).group == G) then some (m q) else none)
        = [m k] ∧
      pickWord (hitsMask en grp G) dst dat =
        ⟨true, ((bundleOf en grp dst dat xl xt).get k).dst,
          ((bundleOf en grp dst dat xl xt).get k).data⟩ := by
  have hval : validAt ((bundleOf en grp dst dat xl xt).get k) = true := by
    have h := hhit
    rw [hitAt_eq_valid_group en grp dst dat xl xt G hG k hk, Bool.and_eq_true] at h
    exact h.1
  have hgrp : (((bundleOf en grp dst dat xl xt).get k).group == G) = true := by
    have h := hhit
    rw [hitAt_eq_valid_group en grp dst dat xl xt G hG k hk, Bool.and_eq_true] at h
    exact h.2
  have hfirst' : ∀ j, j < k →
      (validAt ((bundleOf en grp dst dat xl xt).get j) &&
        (((bundleOf en grp dst dat xl xt).get j).group == G)) = false := by
    intro j hj
    have h := hfirst j hj
    rwa [hitAt_eq_valid_group en grp dst dat xl xt G hG j (by omega)] at h
  exact ⟨winnerGroup_eq_singleton hMT G hG hG0 hG1 k hk hval hgrp hfirst',
    pickWord_eq_word en grp dst dat xl xt G k hk hhit hfirst⟩

/-- A padded (`NULL`) move does not change the fold, so listing only the enabled
moves and listing all six with `NULL` padding give the same result. -/
theorem resolveAux_pad {b : Bundle} (hkind : DstKindTable) (m : Metronome.Machine.Move)
    (h : m.dst = 0) (ms : List Metronome.Machine.Move) (acc : St) :
    resolveAux (ms ++ [m]) acc = resolveAux ms acc := by
  rw [resolveAux, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [stepOn_none _ _ (moveGroup_null_of_dst_zero hkind m h)]
  rfl

/-! ## Reading witness: the conflict rule is per key, not per group code

SPEC_V2 §6 says "If two or more enabled moves target one group in a cycle,
`CONFLICT'` is set".  Read group-code-only, two `L.SYM` moves on *different*
lines would conflict, since both have destination group code 0.  Read per key —
which is what §6's parentheticals "the three symbol ports of **one line**" and
"`T.STOP` (per thread)" say, and what both implementations do — they do not.
The witness below (kernel `decide`, no native decision procedure) fixes the
reading used by the bridge: two enabled `L.SYM` moves on lines 0 and 1 both win,
and no conflict is raised.  `Metronome/Machine/AMBIGUITIES.md` has no
move-resolution entry. -/

/-- Two enabled `L.SYM` moves on different lines both win and do not conflict,
although they share destination group code 0. -/
theorem lsym_two_lines_witness :
    let b : Bundle :=
      { m0 := ⟨true, dgLSym, 1, 0, 0, 0⟩, m1 := ⟨true, dgLSym, 2, 0, 1, 0⟩,
        m2 := ⟨false, dgNone, 0, 0, 0, 0⟩, m3 := ⟨false, dgNone, 0, 0, 0, 0⟩,
        m4 := ⟨false, dgNone, 0, 0, 0, 0⟩, m5 := ⟨false, dgNone, 0, 0, 0, 0⟩ }
    winAt b 0 = true ∧ winAt b 1 = true ∧
      ((b.get 0).group == (b.get 1).group) = true ∧
      sameKey (b.get 0) (b.get 1) = false ∧ conflictEv b = false := by
  decide

end Metronome.Bridge.Moves