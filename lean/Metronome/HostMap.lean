/-
# Metronome v4: the host write map, stated independently

This module is the specification side of the host write-decode cut.  It says,
without reference to the RTL, which 16-bit host addresses carry a write target
and which block each address belongs to.  `hostmap_check.py` elaborates the
chip top, extracts the decode cones, and proves the generated Lean equalities
in `HostMapEquivalence.lean.in` against the definitions here.

The map is the one recorded in SPEC_V2 §9 and generated into
`src/md2_map.vh` (`HA_*_BASE`, `HSPAN_*`, `HS_*`, `HO_*`).  The literals below
are deliberately duplicated by hand: the checker proves that the elaborated
cells decode *these* addresses, so a change to the generated header without a
matching change here fails the proof rather than silently redefining the map.
-/

import Std.Tactic.BVDecide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Metronome.HostMap

/-! ## Blocks and regions -/

/-- The eight host-map blocks the chip top decodes.  The line, thread, stream
and output register blocks are reached through the configuration window
(`cfg`), not through a block decode of their own. -/
inductive Block where
  | prog
  | data
  | cfg
  | ctrl
  | lrt
  | trt
  | srt
  | dbg
  deriving DecidableEq, Repr

/-- Base address of each block (`HA_*_BASE`, `CFG_LO`). -/
def base : Block → BitVec 16
  | .prog => 0x0000
  | .data => 0x1000
  | .cfg  => 0x2000
  | .ctrl => 0x2400
  | .lrt  => 0x2410
  | .trt  => 0x2440
  | .srt  => 0x2450
  | .dbg  => 0x2460

/-- Byte span of each block (`HSPAN_*`). -/
def span : Block → BitVec 16
  | .prog => 0x1000
  | .data => 0x0800
  | .cfg  => 0x01E0
  | .ctrl => 0x0010
  | .lrt  => 0x0020
  | .trt  => 0x000C
  | .srt  => 0x0008
  | .dbg  => 0x0020

/-- `a` lies in the half-open window `[base b, base b + span b)`. -/
def inRegion (b : Block) (a : BitVec 16) : Bool :=
  base b ≤ a && a < base b + span b

/-- Every block, in map order. -/
def blocks : List Block :=
  [.prog, .data, .cfg, .ctrl, .lrt, .trt, .srt, .dbg]

/-- The wrap-around subtraction the RTL uses is a window test only because
every block fits below `2^16`. -/
theorem block_fit (b : Block) : (base b).toNat + (span b).toNat ≤ 65536 := by
  cases b <;> decide

/-! ## Counting true entries -/

/-- The number of `true` entries of a Bool list, in an 8-bit accumulator.  The
lists below are shorter than 256, so the count is exact. -/
def bitCount : List Bool → BitVec 8
  | [] => 0
  | b :: bs => (if b then (1 : BitVec 8) else 0) + bitCount bs

@[simp] theorem bitCount_nil : bitCount [] = 0 := rfl

theorem bitCount_cons (b : Bool) (bs : List Bool) :
    bitCount (b :: bs) = (if b then (1 : BitVec 8) else 0) + bitCount bs := rfl

/-- A list of `false` entries counts zero. -/
theorem bitCount_map_false (l : List Bool) :
    bitCount (l.map (fun _ => false)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [bitCount, ih]

/-- Masking every entry by one strobe leaves the count unchanged when the
strobe is set and zero when it is clear. -/
theorem bitCount_map_and (w : Bool) (l : List Bool) :
    bitCount (l.map (fun b => w && b)) = (if w then bitCount l else 0) := by
  induction l with
  | nil => cases w <;> rfl
  | cons x xs ih =>
    cases w with
    | true => simp [bitCount]
    | false =>
      have hz : bitCount (List.map (fun _ => false) xs) = 0 := bitCount_map_false xs
      simp [bitCount, hz]

/-! ## The register write addresses

The 43 host-writable register bytes of `ctrl`, `lrt`, `trt`, `srt` and `dbg`,
in the order the checker extracts their write strobes.  Every entry is a base
plus the `HO_*` offset of `md2_map.vh`:

* `ctrl`: RUN, STICKY, IRQEN, DOORBELL, HOSTIN, HOSTSTAT (`0x2400`-`0x2406`);
* `lrt`: four line instances at `0x2410 + 8k`, each PHASE (2 bytes), CTL, STAT;
* `trt`: six thread instances at `0x2440 + 2k`, each PC and STAT;
* `srt`: two stream instances at `0x2450 + 4k`, CTL;
* `dbg`: DBG, MCTL, ECTL, EMASK (2 bytes) and RLV (2 bytes).
-/
def regAddrs : List (BitVec 16) :=
  [ 0x2400, 0x2401, 0x2402, 0x2403, 0x2404, 0x2406,
    0x2410, 0x2411, 0x2412, 0x2415,
    0x2418, 0x2419, 0x241A, 0x241D,
    0x2420, 0x2421, 0x2422, 0x2425,
    0x2428, 0x2429, 0x242A, 0x242D,
    0x2440, 0x2441, 0x2442, 0x2443, 0x2444, 0x2445,
    0x2446, 0x2447, 0x2448, 0x2449, 0x244A, 0x244B,
    0x2452, 0x2456,
    0x2460, 0x2461, 0x2462, 0x2468, 0x2469, 0x2472, 0x2473 ]

/-- The program memory of core 0: the low half of the `prog` block. -/
def progCore0 (a : BitVec 16) : Bool := 0x0000 ≤ a && a < 0x0800

/-- The program memory of core 1: the high half of the `prog` block. -/
def progCore1 (a : BitVec 16) : Bool := 0x0800 ≤ a && a < 0x1000

/-- A configuration-window write also needs the live-byte mask (the separate
address-decode cut's `cfg_address_is_live`); this module keeps it symbolic. -/
def cfgSel (live : Bool) (a : BitVec 16) : Bool := inRegion .cfg a && live

/-- Every selection except the configuration window: the 43 register bytes, the
two program cores and the data RAM.  The generated enable list is this list,
so the configuration strobe can be added on the end. -/
def selListRegs (a : BitVec 16) : List Bool :=
  regAddrs.map (fun x => a == x) ++
    [progCore0 a, progCore1 a, inRegion .data a]

/-- Every selection the host map can assert at `a`: one per register address,
then the two program cores, the data RAM and the configuration window. -/
def selList (live : Bool) (a : BitVec 16) : List Bool :=
  selListRegs a ++ [cfgSel live a]

/-- A host write enables an entry exactly when the write is asserted and the
entry's selection holds. -/
def enabledSels (live write : Bool) (a : BitVec 16) : List Bool :=
  (selList live a).map (fun b => write && b)

/-- The byte lane of the program window the map's offset selects, `[2:0]`. -/
def progLane (a : BitVec 16) : BitVec 3 := (a - base .prog).truncate 3

/-- The word address of the program window the map's offset selects, `[10:3]`. -/
def progWord (a : BitVec 16) : BitVec 8 := ((a - base .prog).ushiftRight 3).truncate 8

/-- The data-RAM byte address the map's offset selects, `[10:0]`. -/
def dataAddr (a : BitVec 16) : BitVec 11 := (a - base .data).truncate 11

/-- The one-hot byte-lane select for `i`: bit `i` set, every other bit clear. -/
def laneOneHot (i : BitVec 3) : BitVec 8 := BitVec.shiftLeft (1 : BitVec 8) i.toNat

/-! ## The map is functional

At most one target per address: the register addresses are distinct and inside
`ctrl`..`dbg`, while the program, data and configuration windows are disjoint
from those and from each other.  `bv_decide` checks the whole 47-entry table at
all 65536 addresses. -/

theorem selList_count_le_one (live : Bool) (a : BitVec 16) :
    bitCount (selList live a) ≤ 1 := by
  simp only [selList, selListRegs, regAddrs, progCore0, progCore1, inRegion, base,
    span, cfgSel, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    bitCount]
  bv_decide

/-- The eight block windows are pairwise disjoint: every address belongs to at
most one block. -/
theorem blockCount_le_one (a : BitVec 16) :
    bitCount (blocks.map (fun b => inRegion b a)) ≤ 1 := by
  simp only [blocks, inRegion, base, span, List.map_cons, List.map_nil, bitCount]
  bv_decide

/-- Masking the selections by the write strobe cannot increase the count, so at
most one write enable fires per host write. -/
theorem enabledSels_le_one (live write : Bool) (a : BitVec 16) :
    bitCount (enabledSels live write a) ≤ 1 := by
  rw [enabledSels, bitCount_map_and]
  cases write with
  | false => exact Nat.zero_le _
  | true =>
    simpa [enabledSels] using selList_count_le_one live a

/-- An address with no write target enables nothing, whatever the strobe. -/
theorem enabledSels_eq_zero (live write : Bool) (a : BitVec 16)
    (h : bitCount (selList live a) = 0) :
    bitCount (enabledSels live write a) = 0 := by
  rw [enabledSels, bitCount_map_and]
  cases write with
  | false => rfl
  | true => simpa [enabledSels] using h

/-- The 43 register addresses are pairwise distinct. -/
theorem regAddrs_nodup : regAddrs.Nodup := by
  simp [regAddrs]

/-- The register addresses all lie inside `ctrl`..`dbg`, so they are disjoint
from the program, data and configuration windows. -/
theorem regAddrs_in_ctrl_dbg :
    regAddrs.all (fun x => 0x2400 ≤ x && x < 0x2480) = true := by
  decide

/-- Every listed address has no write target: `bitCount (selList live r)` is
zero.  Kernel reduction over the concrete table; the generated read-only
theorems instantiate it per address through `enabledSels_eq_zero`. -/
def readOnlyAddrs : List (BitVec 16) :=
  [ 0x2405, 0x2407, 0x2408, 0x240F,
    0x2413, 0x2414,
    0x2464, 0x2465, 0x246A, 0x246B, 0x246C, 0x246D, 0x2470, 0x2471,
    0x1800, 0x1FFF, 0x21E0, 0x21FF, 0x2480, 0x24FF, 0xFFFF ]

theorem readOnly_no_sel (live : Bool) :
    readOnlyAddrs.all (fun r => bitCount (selList live r) == 0) = true := by
  cases live <;> decide

/-! ## Write data semantics

Three local next-state contracts.  The RTL cones are proved equal to these
definitions in the generated file; the lemmas below are the bit-level
statements the write-up quotes. -/

/-- A sticky status bit: an event sets it, a host write of `1` to its
`CTRL.STICKY` bit clears it, anything else holds it. -/
def stickyNext (ev q stk bit : Bool) : Bool := ev || (q && !(stk && bit))

/-- Writing `1` to the bit clears a quiet sticky flag. -/
theorem sticky_cleared (ev q stk bit : Bool) (hev : ev = false)
    (hs : stk = true) (hb : bit = true) : stickyNext ev q stk bit = false := by
  simp [stickyNext, hev, hs, hb]

/-- Writing `0` to the bit holds the flag (plus any new event). -/
theorem sticky_held (ev q stk bit : Bool) (hb : bit = false) :
    stickyNext ev q stk bit = (ev || q) := by
  simp [stickyNext, hb]

/-- A new event sets the flag even if the same write clears it. -/
theorem sticky_set (ev q stk bit : Bool) (hev : ev = true) :
    stickyNext ev q stk bit = true := by
  simp [stickyNext, hev]

/-- The doorbell: a host write loads the word, and it drops to zero on the next
cycle unless the machine is frozen. -/
def doorbellNext {n : Nat} (wr frz : Bool) (d q : BitVec n) : BitVec n :=
  (if wr then d else 0) ||| (if frz then q else 0)

theorem doorbell_pulse {n : Nat} (frz : Bool) (d : BitVec n) (hf : frz = false) :
    doorbellNext true frz d 0 = d := by
  simp [doorbellNext, hf]

theorem doorbell_idle {n : Nat} (frz : Bool) (q : BitVec n) (hf : frz = false) :
    doorbellNext false frz 0 q = 0 := by
  simp [doorbellNext, hf]

theorem doorbell_held {n : Nat} (frz : Bool) (q : BitVec n) (hf : frz = true) :
    doorbellNext false frz 0 q = q := by
  simp [doorbellNext, hf]

/-- While frozen a new host word is ORed into the pending one, so a frozen
machine cannot silently drop a doorbell. -/
theorem doorbell_frozen_new {n : Nat} (frz : Bool) (d q : BitVec n)
    (hf : frz = true) : doorbellNext true frz d q = (d ||| q) := by
  simp [doorbellNext, hf]

/-- A host `HOSTIN` write sets the input-valid flag; a core read of `HOSTIN`
clears it; otherwise it holds. -/
def invNext (wr rdAny inv : Bool) : Bool := wr || (!rdAny && inv)

theorem inv_set (rdAny inv : Bool) : invNext true rdAny inv = true := by
  simp [invNext]

theorem inv_hold (inv : Bool) : invNext false false inv = inv := by
  simp [invNext]

/-- A host `HOSTIN` write loads the mailbox byte; a read leaves it alone. -/
def mailboxNext (wr : Bool) (d m : BitVec 8) : BitVec 8 := if wr then d else m

theorem mailbox_loaded (d m : BitVec 8) : mailboxNext true d m = d := rfl

end Metronome.HostMap
