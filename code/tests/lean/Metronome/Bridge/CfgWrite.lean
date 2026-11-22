import Metronome.Machine
import Metronome.CoreQueue

/-!
# Bridge: the core configuration-write path (`Metronome.CoreQueue`) refines
`Machine.CfgWrite` / `Machine.Host.ctrlNext`

`Metronome.CoreQueue` specifies the core-side `CW.AL` / `CW.AH` / `CW.D` path of
SPEC_V2 §13.1 (`cw_addr`, the one-deep `cw_pending` queue and the sticky
`cw_overrun`) as an independent cut; `CoreQueueEquivalence.lean.in` proves the
elaborated `project.v` registers implement it.  `Metronome.Machine` states the
same path in `Machine.cwNext` (`cwa`, `cwv`, `cwqa`, `cwqd`) and
`Machine.ctrlNext` (`cwovr`).  This file proves the cut's one-cycle transition
is the machine's.

## Abstraction map

`absCw` maps the cut's five registers onto the queue fields of `Machine.CwSt`:
`addr ↔ cwa`, `pending ↔ cwv`, `pendingAddr ↔ cwqa`, `pendingData ↔ cwqd`.  The
bank-port fields (`bwp`, `hh`, `bpa`, `bpd`) belong to the arbiter cut
(`Metronome.Config`), not to this one; the bridge pins them to the quiet values
(`bwp = false`, `hh = false`) and passes `hostCfg = none` and `window = false`,
i.e. a cycle with no pending held host write, no host configuration write and
outside the §1 restart window.  The cut's `Input.cw` is mapped by `mvOf`: the
picked 15-bit write group becomes the machine's `CwMove` (code 58 → `AL`,
59 → `AH`, 60 → `D`, with the write byte).  The three decode tests are
mutually exclusive (`wl_wd`, `wh_wd`, `wl_wh`), which the bridge proves from the
6-bit destination encoding, not assumes.

The cut's `coreIssue` is the arbiter's grant; the bridge assumes `coreIssue =
true`, i.e. the §13.1 arbiter is empty and accepts the queued write this cycle.
In that case the machine's `drains` is exactly the cut's `drain` (both reduce
to `pending`), and the bridge proves `queue_fields`: `cwa`, `cwv`, `cwqa`,
`cwqd` after the step are exactly the cut's `addr`, `pending`, `pendingAddr`,
`pendingData`.

`overrun_bridge` maps the sticky `cw_overrun` to `ctrlNext`'s `cwovr`, given
the documented `CTRL.STICKY` bit-2 clear (the machine's host write of
`CTRL.STICKY` is the cut's `clearSticky && hostData[2]`).

## The bank-port payloads and the composition

`staged_bridge` states that the write the cut staged is the write the machine
performed (same window offset and byte); `staged_bpa` turns it into the
machine's `bpa`/`bpd` and `held_bridge` does the same for the held write
`HH`/`hha`/`hhd`.  Both need the chip step's configuration-address gate
(`hcfg`, `hwIsCfg`): `addrOf (offOf a) = a` holds for a configuration address,
which `isCfgAddr_window` establishes from the latch bank's interval
`0x2000 .. 0x21DF`.

`drain_bridge` identifies the cut's drain with the machine's internal drain
condition when the queue's `coreIssue` is the arbiter's `coreDrain`;
`queue_fields_arb` is `queue_fields` for that free case, and
`cfg_compose_bridge` composes the queue and the arbiter against one
`Machine.cwNext` step.

## A disagreement: the frozen cycle (§12.3 / §13.1, AMBIGUITIES #18)

`CoreQueue` reads §13.1's drain list together with §12.3 "in a frozen cycle no
move happens": its `drain` is gated by `!frz`, so the queue *holds* while
frozen.  Since D50 (2026-11-21, user decision; SPEC_V2 §12.3/§13.1 amended)
`Machine.cwNext` takes the freeze flag and holds the queue too, so the two agree:
`frozen_agrees` states it on the concrete case that `frozen_witness` used to
separate.  `frozen_witness` is kept with its original statement; it now
exercises the machine's unfrozen default (`frozen := false`).  `queue_fields`
is still stated for `frz = false`.

No `sorry`, no `native_decide`.
-/

namespace Metronome.Bridge.CfgWrite

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Metronome

def absCw (q : CoreQueue.State) : Machine.CwSt :=
  { cwa := q.addr, cwv := q.pending, cwqa := q.pendingAddr, cwqd := q.pendingData,
    bwp := false, hh := false, hha := 0, hhd := 0, bpa := 0, bpd := 0 }

def mvOf (i : CoreQueue.Input) : Option Machine.CwMove :=
  if CoreQueue.writeData i then some ⟨2, (CoreQueue.cwData i.cw).toNat⟩
  else if CoreQueue.writeLow i then some ⟨0, (CoreQueue.cwData i.cw).toNat⟩
  else if CoreQueue.writeHigh i then some ⟨1, (CoreQueue.cwData i.cw).toNat⟩
  else none

theorem pack_eq_append (lo hi : BitVec 8) : CoreQueue.pack lo hi = hi ++ lo := by
  simp only [CoreQueue.pack, CoreQueue.bitAt]
  bv_decide

theorem pack_toNat (lo hi : BitVec 8) :
    (CoreQueue.pack lo hi).toNat = hi.toNat * 256 + lo.toNat := by
  rw [pack_eq_append]
  rw [BitVec.toNat_append]
  have hl : lo.toNat < 2 ^ 8 := by
    have := lo.isLt
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]

theorem highByte_toNat (a : BitVec 16) : (CoreQueue.highByte a).toNat = a.toNat / 256 := by
  simp [CoreQueue.highByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h := a.isLt
  omega

theorem lowByte_toNat (a : BitVec 16) : (CoreQueue.lowByte a).toNat = a.toNat % 256 := by
  simp [CoreQueue.lowByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem take8_eq_trunc (a : BitVec 16) : CoreQueue.take8 a = BitVec.truncate 8 a := by
  simp only [CoreQueue.take8, CoreQueue.bitAt]
  bv_decide

theorem bv_toNat {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv]

theorem bv_mod8 (x : BitVec 8) : Machine.Util.bv 8 (x.toNat % 256) = x := by
  have h : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt x.isLt
  rw [h]
  exact bv_toNat x

theorem pack_round (a : BitVec 16) :
    CoreQueue.pack (CoreQueue.lowByte a) (CoreQueue.highByte a) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat, lowByte_toNat, highByte_toNat]
  have h := a.isLt
  omega

theorem pack_low_eq (a : BitVec 16) (d : BitVec 8) :
    CoreQueue.pack d (CoreQueue.highByte a) =
      Machine.Util.bv 16 ((a.toNat / 256) * 256 + d.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat, highByte_toNat, Machine.Util.bv, BitVec.toNat_ofNat]
  have hlt : a.toNat / 256 * 256 + d.toNat % 256 < 2 ^ 16 := by
    have ha := a.isLt
    have hd := d.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hd : d.toNat % 256 = d.toNat := Nat.mod_eq_of_lt d.isLt
  rw [hd]

theorem pack_high_eq (a : BitVec 16) (d : BitVec 8) :
    CoreQueue.pack (CoreQueue.lowByte a) d =
      Machine.Util.bv 16 ((d.toNat % 256) * 256 + a.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat, lowByte_toNat, Machine.Util.bv, BitVec.toNat_ofNat]
  have hlt : d.toNat % 256 * 256 + a.toNat % 256 < 2 ^ 16 := by
    have ha := a.isLt
    have hd := d.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hd : d.toNat % 256 = d.toNat := Nat.mod_eq_of_lt d.isLt
  rw [hd]

theorem bv_add_one (a : BitVec 16) :
    Machine.Util.bv 16 ((a.toNat + 1) % 65536) = a + 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [Machine.Util.bv, BitVec.toNat_ofNat, BitVec.toNat_add]
  simp

theorem wl_wd (i : CoreQueue.Input) :
    (CoreQueue.writeLow i && CoreQueue.writeData i) = false := by
  simp only [CoreQueue.writeLow, CoreQueue.writeData, CoreQueue.cwCode, CoreQueue.bitAt]
  bv_decide

theorem wh_wd (i : CoreQueue.Input) :
    (CoreQueue.writeHigh i && CoreQueue.writeData i) = false := by
  simp only [CoreQueue.writeHigh, CoreQueue.writeData, CoreQueue.cwCode, CoreQueue.bitAt]
  bv_decide

theorem wl_wh (i : CoreQueue.Input) :
    (CoreQueue.writeLow i && CoreQueue.writeHigh i) = false := by
  simp only [CoreQueue.writeLow, CoreQueue.writeHigh, CoreQueue.cwCode, CoreQueue.bitAt]
  bv_decide

theorem writeLow_false_of_writeData (i : CoreQueue.Input)
    (h : CoreQueue.writeData i = true) : CoreQueue.writeLow i = false := by
  rcases hb : CoreQueue.writeLow i with _ | _
  · rfl
  · exfalso
    have hw : (CoreQueue.writeLow i && CoreQueue.writeData i) = true := by simp [hb, h]
    rw [wl_wd i] at hw
    exact Bool.noConfusion hw

theorem writeHigh_false_of_writeData (i : CoreQueue.Input)
    (h : CoreQueue.writeData i = true) : CoreQueue.writeHigh i = false := by
  rcases hb : CoreQueue.writeHigh i with _ | _
  · rfl
  · exfalso
    have hw : (CoreQueue.writeHigh i && CoreQueue.writeData i) = true := by simp [hb, h]
    rw [wh_wd i] at hw
    exact Bool.noConfusion hw

theorem writeHigh_false_of_writeLow (i : CoreQueue.Input)
    (h : CoreQueue.writeLow i = true) : CoreQueue.writeHigh i = false := by
  rcases hb : CoreQueue.writeHigh i with _ | _
  · rfl
  · exfalso
    have hw : (CoreQueue.writeLow i && CoreQueue.writeHigh i) = true := by simp [hb, h]
    rw [wl_wh i] at hw
    exact Bool.noConfusion hw

theorem queue_fields (q : CoreQueue.State) (i : CoreQueue.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = false) (hcore : i.coreIssue = true) :
    let st := (Machine.cwNext (absCw q) none (mvOf i) false).st
    let q' := CoreQueue.step q i
    st.cwa = q'.addr ∧ st.cwv = q'.pending ∧ st.cwqa = q'.pendingAddr ∧
      st.cwqd = q'.pendingData := by
  dsimp only
  simp only [absCw, CoreQueue.step, Machine.cwNext]
  by_cases hD : CoreQueue.writeData i = true
  · have hL := writeLow_false_of_writeData i hD
    have hH := writeHigh_false_of_writeData i hD
    by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
    by_cases hp : q.pending = true <;>
    simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
      CoreQueue.nextHigh, CoreQueue.pack_take, bv_add_one, bv_toNat, bv_mod8]
  · by_cases hL : CoreQueue.writeLow i = true
    · have hH := writeHigh_false_of_writeLow i hL
      by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
      by_cases hp : q.pending = true <;>
      simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
        CoreQueue.nextHigh, pack_low_eq, bv_toNat, bv_mod8]
    · by_cases hH : CoreQueue.writeHigh i = true
      · by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
        by_cases hp : q.pending = true <;>
        simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
          CoreQueue.nextHigh, pack_high_eq, bv_toNat, bv_mod8]
      · by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
        by_cases hp : q.pending = true <;>
        simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
          CoreQueue.nextHigh, pack_round, bv_add_one, bv_toNat, bv_mod8]

/-! ## The sticky `CWOVR` (`Machine.ctrlNext`) -/

/-- The machine's queue carries no overrun bit: with the arbiter accepting
(`coreIssue = true`) or draining, its `ovr` output is `false` in the same
`hD/hL/hH/pending/isCfg` cases as `queue_fields`. -/
theorem cwNext_ovr_false (q : CoreQueue.State) (i : CoreQueue.Input) :
    (Machine.cwNext (absCw q) none (mvOf i) false).ovr = false := by
  simp only [absCw, Machine.cwNext]
  by_cases hD : CoreQueue.writeData i = true
  · have hH := writeHigh_false_of_writeData i hD
    by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
    by_cases hp : q.pending = true <;>
    simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
      CoreQueue.nextHigh]
  · by_cases hL : CoreQueue.writeLow i = true
    · have hH := writeHigh_false_of_writeLow i hL
      by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
      by_cases hp : q.pending = true <;>
      simp_all [mvOf, CoreQueue.accept, CoreQueue.drain]
    · by_cases hH : CoreQueue.writeHigh i = true <;>
      by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
      by_cases hp : q.pending = true <;>
      simp_all [mvOf, CoreQueue.accept, CoreQueue.drain]

/-- `ctrlNext`'s sticky `cwovr` is the cut's `overrun`, given the queue's
`ovr` output (above) and the documented `CTRL.STICKY` bit-2 clear.  The
machine's `STICKY` byte and the cut's `clearSticky && hostData[2]` are the same
host write; `hsticky` names that interface equality. -/
theorem overrun_bridge (q : CoreQueue.State) (i : CoreQueue.Input)
    (s : Machine.State) (hw : Option Machine.HostWr) (ci : Machine.CtrlIn)
    (hreset : i.resetN = true) (hfrz : i.frz = false) (hcore : i.coreIssue = true)
    (hcwovr : s.ctrl.cwovr = q.overrun)
    (hsticky : Machine.Util.nbit ((Machine.Util.hwByte hw "CTRL" 0 "STICKY").getD 0) 2 =
      CoreQueue.hostClear i)
    (hovr : ci.cwovr = (Machine.cwNext (absCw q) none (mvOf i) false).ovr) :
    (Machine.ctrlNext s hw ci (s.dbg.frz)).cwovr = (CoreQueue.step q i).overrun := by
  have hovrF := cwNext_ovr_false q i
  simp only [Machine.ctrlNext, CoreQueue.step]
  rw [hsticky, hcwovr, hovr, hovrF]
  by_cases hp : q.pending = true <;>
  by_cases hwrite : CoreQueue.writeData i = true <;>
  by_cases hclear : CoreQueue.hostClear i = true <;>
  by_cases ho : q.overrun = true <;>
  simp_all [CoreQueue.accept, CoreQueue.drain, hreset, hfrz, hcore]

/-- The cut's reset state maps onto the quiet machine queue (all zero). -/
theorem absCw_reset :
    absCw (⟨0, false, 0, 0, false⟩ : CoreQueue.State) = (default : Machine.CwSt) := by
  decide

/-! ## The frozen-cycle disagreement (AMBIGUITIES #18) -/

/-- Concrete witness: a frozen cycle with a queued write.  The cut holds the
entry (`pending` stays `true`, because `CoreQueue.drain` requires `!frz`); the
machine drains it (`cwv` becomes `false`, since `cwNext` has no frozen input).
This is the reading difference recorded as `Machine/AMBIGUITIES.md` #18. -/
theorem frozen_witness :
    let q : CoreQueue.State := ⟨0, true, 0, 0x5A, false⟩
    let i : CoreQueue.Input := ⟨true, 0, true, false, true, false, 0⟩
    CoreQueue.drain q i = false ∧
      (CoreQueue.step q i).pending = true ∧
      (Machine.cwNext (absCw q) none (mvOf i) false).st.cwv = false := by
  dsimp only
  by_cases hcfg : Machine.Config.isCfgAddr 0 = true <;>
    simp [CoreQueue.drain, CoreQueue.step, CoreQueue.accept, CoreQueue.writeData,
      CoreQueue.writeLow, CoreQueue.writeHigh, absCw, mvOf, Machine.cwNext, hcfg,
      CoreQueue.bitAt, CoreQueue.cwCode]

/-- D50: with the freeze flag passed, the machine holds a queued write in a
frozen cycle, as the cut (and the RTL) do. -/
theorem frozen_agrees :
    let q : CoreQueue.State := ⟨0, true, 0, 0x5A, false⟩
    let i : CoreQueue.Input := ⟨true, 0, true, false, true, false, 0⟩
    (CoreQueue.step q i).pending = true ∧
      (Machine.cwNext (absCw q) none (mvOf i) false true).st.cwv = true := by
  dsimp only
  by_cases hcfg : Machine.Config.isCfgAddr 0 = true <;>
    simp [CoreQueue.drain, CoreQueue.step, CoreQueue.accept, CoreQueue.writeData,
      CoreQueue.writeLow, CoreQueue.writeHigh, absCw, mvOf, Machine.cwNext, hcfg,
      CoreQueue.bitAt, CoreQueue.cwCode]

/-! ## The configuration arbiter against the machine's bank port

`Metronome.Config` specifies the §13.1 arbiter and single write stage
(`previousWrite`, the held host write `heldValid`/`held`, the staged write); the
machine states the same port in `Machine.cwNext`'s `bwp`/`hh`/`hha`/`hhd` and
`bpa`/`bpd`.  The cut's nine-bit `Write.addr` is the bank *window offset*; a
machine address is the full host address, so the map is `addrOf`/`offOf` below
(`offset = address - 0x2000`).

`coreDrain` restates the machine's `cwNext` internal condition under which the
queued core write (`CWQ`, at a configuration address) is performed: no held host
write, no host configuration write, no `BWP` interlock.  The §13.1 arbiter's
`coreIssue` is exactly this condition. -/

/-- The configuration window base (`LINE_BASE`, `CFG_LO` in `md2_map.vh`). -/
abbrev CFG_LO : Nat := 0x2000

/-- The nine-bit bank offset of a full host address. -/
def offOf (a : Nat) : BitVec 9 := Machine.Util.bv 9 a

/-- The full host address of a nine-bit bank offset. -/
def addrOf (o : BitVec 9) : Nat := CFG_LO + o.toNat

theorem bv8_toNat (x : BitVec 8) : Machine.Util.bv 8 x.toNat = x := by
  simp [Machine.Util.bv]

/-- offOf undoes ddrOf for every offset (offOf (0x2000 + o) = o). -/
theorem offOf_addrOf (o : BitVec 9) : offOf (addrOf o) = o := by
  apply BitVec.eq_of_toNat_eq
  simp only [offOf, addrOf, CFG_LO, Machine.Util.bv, BitVec.toNat_ofNat]
  have h := o.isLt
  omega

/-- The arbiter cut's input in a cycle of the machine: the host configuration
write of this cycle (`hostCfg`), and the queued core write. The cut's reset is
released (`resetN = true`) and the cycle is not frozen (`CoreQueue.Input.frz` is
a separate side condition of the composed theorem). -/
def cfgIn (q : CoreQueue.State) (hostCfg : Option (Nat × Nat)) : Config.Input :=
  { resetN := true
    hostValid := hostCfg.isSome
    host := match hostCfg with
      | some (a, v) => ⟨offOf a, Machine.Util.bv 8 v⟩
      | none => ⟨0, 0⟩
    coreValid := q.pending && Machine.Config.isCfgAddr q.pendingAddr.toNat
    core := ⟨offOf q.pendingAddr.toNat, q.pendingData⟩ }

/-- The machine's configuration-write state as the arbiter cut's state (the queue
fields come from the queue cut, the bank-port fields from the arbiter cut). -/
def cwOf (q : CoreQueue.State) (c : Config.State) : Machine.CwSt :=
  { cwa := q.addr, cwv := q.pending, cwqa := q.pendingAddr, cwqd := q.pendingData,
    bwp := c.previousWrite, hh := c.heldValid,
    hha := addrOf c.held.addr, hhd := c.held.data,
    bpa := addrOf c.staged.addr, bpd := c.staged.data }

/-- The machine's `cwNext` performs the queued core write exactly under this
condition (the `coreDrain` let of `Machine.cwNext`, restated). -/
def coreDrain (cw : Machine.CwSt) (hostCfg : Option (Nat × Nat)) : Bool :=
  !cw.hh && hostCfg.isNone && (cw.cwv && Machine.Config.isCfgAddr cw.cwqa.toNat) && !cw.bwp

/-- The cut's reset state (all four registers cleared) maps to the machine's
power-on configuration state. -/
theorem absArb_zero :
    cwOf (⟨0, false, 0, 0, false⟩ : CoreQueue.State)
      (⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩ : Config.State) =
      { (default : Machine.CwSt) with hha := addrOf 0, bpa := addrOf 0 } := by
  decide

/-- **One arbiter cycle.**  With no host write arriving while a held host write
waits (`h19`, AMBIGUITIES #19: unreachable at SPI byte spacing), the cut's
`Config.step` issues the same bank write as the machine's `cwNext`, at the same
window offset, with the same next bank-port state, and its `coreIssue` is the
machine's core-drain condition. -/
theorem arbiter_bridge (q : CoreQueue.State) (c : Config.State) (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true)) :
    (Config.step c (cfgIn q hostCfg)).bankWrite =
        (Machine.cwNext (cwOf q c) hostCfg none false).performed.isSome ∧
      (∀ a v, (Machine.cwNext (cwOf q c) hostCfg none false).performed = some (a, v) →
        (Config.step c (cfgIn q hostCfg)).bank = ⟨offOf a, Machine.Util.bv 8 v⟩) ∧
      (Config.step c (cfgIn q hostCfg)).next.previousWrite =
        (Machine.cwNext (cwOf q c) hostCfg none false).st.bwp ∧
      (Config.step c (cfgIn q hostCfg)).next.heldValid =
        (Machine.cwNext (cwOf q c) hostCfg none false).st.hh ∧
      (Config.step c (cfgIn q hostCfg)).coreIssue = coreDrain (cwOf q c) hostCfg := by
  rcases c with ⟨pw, hv, held, staged⟩
  rcases held with ⟨haddr, hdata⟩
  rcases staged with ⟨saddr, sdata⟩
  rcases hostCfg with _ | ⟨ha, hv'⟩
  · -- no host write this cycle
    rcases hv with _ | _
    · -- no held write: the core may issue
      by_cases hq : (q.pending && Machine.Config.isCfgAddr q.pendingAddr.toNat) = true
      · have hp : q.pending = true := by
          rcases hqi : q.pending with _ | _
          · rw [hqi] at hq; exact absurd hq (by simp)
          · rfl
        have hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true := by
          rcases hi : Machine.Config.isCfgAddr q.pendingAddr.toNat with _ | _
          · rw [hp, hi] at hq; exact absurd hq (by simp)
          · rfl
        by_cases hb : pw = true <;>
          simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, coreDrain,
            Machine.cwNext, hq, hb, hp, hic, bv8_toNat, Bool.and_assoc]
      · by_cases hb : pw = true <;>
          simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, coreDrain,
            Machine.cwNext, hq, hb, Bool.and_assoc]
    · -- a held host write is performed
      have hmod : addrOf haddr % 65536 = addrOf haddr := by
        simp only [addrOf, CFG_LO]
        apply Nat.mod_eq_of_lt
        have := haddr.isLt
        omega
      simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, coreDrain,
        Machine.cwNext, offOf_addrOf, bv8_toNat, hmod]
  · -- a host write arrives
    rcases hv with _ | _
    · -- no held write
      by_cases hb : pw = true <;>
        simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, coreDrain,
          Machine.cwNext, hb, bv8_toNat, Bool.and_assoc]
    · exact absurd ⟨rfl, by simp⟩ h19

/-! ## The configuration address window

`Config.isCfgAddr` accepts the mapped byte addresses of the latch bank, all in
`0x2000 .. 0x21DF`.  The bound is a finite check: the kernel cannot unfold
`Array.any` (it reduces through `Array.anyM`), so the check is stated on the
block list (`isCfgAddr_list`) and evaluated with `decide` on the block table
(`blockOk_all`).  It is what makes the cut's nine-bit window offset lossless:
`addrOf (offOf a) = a` for a configuration address. -/

/-- A block's configuration bytes lie in the latch-bank window: its base is at
least `0x2000` and every mapped access-W byte ends below `0x21E0`. -/
def blockOk : String × Nat × Nat × Nat × Array (Nat × String × Nat × String) → Bool
  | (name, base, stride, inst, regs) =>
      !(Machine.Util.cfgBlockNames.contains name) ||
        (0x2000 ≤ base && regs.toList.all (fun (off, _, bytes, acc) =>
          !(acc == "W") || (base + stride * (inst - 1) + off + bytes ≤ 0x21E0)))

/-- The block table checked once (kernel `decide`, no `native_decide`). -/
theorem blockOk_all : Machine.Tables.hostBlocks.toList.all blockOk = true := by decide

/-- `Config.isCfgAddr` on the block list (`Array.any` is `List.any` of the
list). -/
theorem isCfgAddr_list (a : Nat) :
    Machine.Config.isCfgAddr a =
      Machine.Tables.hostBlocks.toList.any (fun (name, base, stride, inst, regs) =>
        Machine.Util.cfgBlockNames.contains name &&
          (List.range inst).any fun i =>
            regs.any fun (off, _, bytes, acc) =>
              acc == "W" && decide (base + stride * i + off ≤ a) &&
                decide (a < base + stride * i + off + bytes)) := by
  unfold Machine.Config.isCfgAddr
  rw [← Array.any_toList]

/-- A configuration address lies in the latch-bank window. -/
theorem isCfgAddr_window (a : Nat) (h : Machine.Config.isCfgAddr a = true) :
    0x2000 ≤ a ∧ a < 0x21E0 := by
  rw [isCfgAddr_list, List.any_eq_true] at h
  obtain ⟨b, hb, hp⟩ := h
  have hshape := (List.all_eq_true.mp blockOk_all) b hb
  obtain ⟨name, base, stride, inst, regs⟩ := b
  simp only [blockOk] at hshape
  rw [Bool.and_eq_true] at hp
  obtain ⟨hname, hinner⟩ := hp
  rw [Bool.or_eq_true] at hshape
  rcases hshape with hnone | hsome
  · rw [hname] at hnone; exact absurd hnone (by simp)
  · rw [Bool.and_eq_true] at hsome
    obtain ⟨hbase, hall⟩ := hsome
    rw [List.any_eq_true] at hinner
    obtain ⟨i, hi, hq⟩ := hinner
    have hi' : i < inst := List.mem_range.mp hi
    rw [← Array.any_toList, List.any_eq_true] at hq
    obtain ⟨reg, hreg, hs⟩ := hq
    obtain ⟨off, rname, bytes, acc⟩ := reg
    simp only at hs
    rw [Bool.and_eq_true, Bool.and_eq_true] at hs
    obtain ⟨⟨hacc, hlo⟩, hup⟩ := hs
    have hall' := (List.all_eq_true.mp hall) (off, rname, bytes, acc) hreg
    simp only at hall'
    rw [Bool.or_eq_true] at hall'
    rcases hall' with hbad | hgood
    · rw [hacc] at hbad; exact absurd hbad (by simp)
    · have hi2 : i ≤ inst - 1 := by omega
      have hmul : stride * i ≤ stride * (inst - 1) := Nat.mul_le_mul_left stride hi2
      simp only [decide_eq_true_eq] at hlo hup hbase hgood
      omega

/-- The nine-bit window offset of a configuration address loses nothing. -/
theorem addrOf_offOf_cfg (a : Nat) (h : Machine.Config.isCfgAddr a = true) :
    addrOf (offOf a) = a := by
  have hb := isCfgAddr_window a h
  have hval : (offOf a).toNat = a % 512 := by
    simp [offOf, Machine.Util.bv, BitVec.toNat_ofNat]
  show 0x2000 + (offOf a).toNat = a
  rw [hval]
  have hmod : a % 512 = a - 0x2000 := by omega
  rw [hmod]
  omega

/-- The nine-bit window offset of any address in the latch-bank window loses
nothing. -/
theorem addrOf_offOf_window (a : Nat) (hlo : 0x2000 ≤ a) (hhi : a < 0x2200) :
    addrOf (offOf a) = a := by
  have hval : (offOf a).toNat = a % 512 := by
    simp [offOf, Machine.Util.bv, BitVec.toNat_ofNat]
  show 0x2000 + (offOf a).toNat = a
  rw [hval]
  have hmod : a % 512 = a - 0x2000 := by omega
  rw [hmod]
  omega

/-! ## The bank-port payloads

The cut stages the write it performs and holds a host write waiting for `BWP`;
the machine's bank port carries `bpa`/`bpd` (the write performed in the cycle,
entering the latches) and `hha`/`hhd` (the held write).  `staged_bridge` and
`held_bridge` prove the payloads are the same write: the cut's nine-bit window
offset is the machine address reduced by `offOf`, and with the chip step's
configuration-address gate (`hcfg`) `addrOf` recovers the machine address.
The converse direction (machine `bpa` from the cut's stage) is `staged_bpa`. -/

/-- **The staged payload (offset form).**  The write the cut staged is the write
the machine performed: the same window offset and byte. -/
theorem staged_bridge (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true)) :
    let cut := Config.step c (cfgIn q hostCfg)
    let mach := Machine.cwNext (cwOf q c) hostCfg none false
    ∀ a v, mach.performed = some (a, v) →
      cut.next.staged.addr = offOf a ∧ cut.next.staged.data = Machine.Util.bv 8 v := by
  dsimp only
  intro a v hperf
  have hb := arbiter_bridge q c hostCfg h19
  have hbw : (Config.step c (cfgIn q hostCfg)).bankWrite = true := by
    rw [hb.1, hperf]
    rfl
  have hstage := Config.stage_captures c (cfgIn q hostCfg) rfl hbw
  rw [hstage.2, hb.2.1 a v hperf]
  exact ⟨rfl, rfl⟩

/-- A performed write is a configuration address: the held host write, the host
configuration write (`hcfg`) or the queued core write at a configuration
address.  All lie in the latch-bank window `0x2000 .. 0x2200`. -/
theorem performed_window (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true) :
    ∀ a v, (Machine.cwNext (cwOf q c) hostCfg none false).performed = some (a, v) →
      0x2000 ≤ a ∧ a < 0x2200 := by
  intro a v hperf
  rcases c with ⟨pw, hv, held, staged⟩
  rcases held with ⟨haddr, hdata⟩
  rcases staged with ⟨saddr, sdata⟩
  rcases hostCfg with _ | ⟨ha, hv'⟩
  · rcases hv with _ | _
    · by_cases hq : (q.pending && Machine.Config.isCfgAddr q.pendingAddr.toNat) = true
      · have hp : q.pending = true := by
          rcases hqi : q.pending with _ | _
          · rw [hqi] at hq; exact absurd hq (by simp)
          · rfl
        have hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true := by
          rcases hi : Machine.Config.isCfgAddr q.pendingAddr.toNat with _ | _
          · rw [hp, hi] at hq; exact absurd hq (by simp)
          · rfl
        have hwin := isCfgAddr_window q.pendingAddr.toNat hic
        by_cases hb : pw = true
        · simp [cwOf, Machine.cwNext, hq, hb] at hperf
        · simp [cwOf, Machine.cwNext, hq, hb, hp, hic] at hperf
          obtain ⟨rfl, rfl⟩ := hperf
          exact ⟨hwin.1, by omega⟩
      · by_cases hb : pw = true <;> simp [cwOf, Machine.cwNext, hq, hb] at hperf
    · -- the held host write is performed at its full window address
      simp [cwOf, Machine.cwNext] at hperf
      obtain ⟨ha, _hd⟩ := hperf
      have hlt := haddr.isLt
      have hbounds : 0x2000 ≤ addrOf haddr ∧ addrOf haddr < 0x2200 := by
        have hval : addrOf haddr = 0x2000 + haddr.toNat := rfl
        rw [hval]
        constructor <;> omega
      have hmod : addrOf haddr % 65536 = addrOf haddr := by
        apply Nat.mod_eq_of_lt
        omega
      rw [← ha, hmod]
      exact hbounds
  · have hwin := isCfgAddr_window ha (hcfg ha hv' rfl)
    rcases hv with _ | _
    · by_cases hb : pw = true
      · simp [cwOf, Machine.cwNext, hb] at hperf
      · simp [cwOf, Machine.cwNext, hb] at hperf
        obtain ⟨rfl, rfl⟩ := hperf
        exact ⟨hwin.1, by omega⟩
    · exact absurd ⟨rfl, by simp⟩ h19

/-- The machine's `bpa`/`bpd` are the performed write's address and byte. -/
theorem bpa_of_performed (cw : Machine.CwSt) (hostCfg : Option (Nat × Nat))
    (mv : Option Machine.CwMove) (window frozen : Bool) (a v : Nat)
    (h : (Machine.cwNext cw hostCfg mv window frozen).performed = some (a, v)) :
    (Machine.cwNext cw hostCfg mv window frozen).st.bpa = Machine.Util.bv 16 a ∧
      (Machine.cwNext cw hostCfg mv window frozen).st.bpd = Machine.Util.bv 8 v := by
  simp only [Machine.cwNext] at h ⊢
  rw [h]
  exact ⟨rfl, rfl⟩

/-- **The staged payload (machine form).**  On a cycle in which the cut performs
a write, the machine's `bpa`/`bpd` are the full address and byte of the write in
the cut's stage.  `hcfg` is the chip step's gate `hwIsCfg`. -/
theorem staged_bpa (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true) :
    let cut := Config.step c (cfgIn q hostCfg)
    let mach := Machine.cwNext (cwOf q c) hostCfg none false
    cut.bankWrite = true →
      mach.st.bpa = Machine.Util.bv 16 (addrOf cut.next.staged.addr) ∧
        mach.st.bpd = cut.next.staged.data := by
  dsimp only
  intro hbank
  have hb := arbiter_bridge q c hostCfg h19
  have hsome : (Machine.cwNext (cwOf q c) hostCfg none false).performed.isSome = true := by
    rw [← hb.1]; exact hbank
  obtain ⟨a, v, hperf⟩ : ∃ a v,
      (Machine.cwNext (cwOf q c) hostCfg none false).performed = some (a, v) := by
    cases hp : (Machine.cwNext (cwOf q c) hostCfg none false).performed with
    | none => rw [hp] at hsome; simp at hsome
    | some p => exact ⟨p.1, p.2, rfl⟩
  have hstage := staged_bridge q c hostCfg h19 a v hperf
  have hp := bpa_of_performed (cwOf q c) hostCfg (none) false false a v hperf
  have hwin := performed_window q c hostCfg h19 hcfg a v hperf
  have hrt : addrOf (offOf a) = a := addrOf_offOf_window a hwin.1 (by omega)
  rw [hp.1, hp.2, hstage.1, hstage.2, hrt]
  exact ⟨rfl, rfl⟩

/-- **The held payload.**  When the machine holds a host configuration write
(`HH`), the cut holds the same write: `hha`/`hhd` are the full address and byte
of the cut's nine-bit held offset and byte.  Under `h19` the two holding
conditions coincide, and `hcfg` is the chip step's configuration-address
gate. -/
theorem held_bridge (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true) :
    let cut := Config.step c (cfgIn q hostCfg)
    let mach := Machine.cwNext (cwOf q c) hostCfg none false
    mach.st.hh = true →
      mach.st.hha = Machine.Util.bv 16 (addrOf cut.next.held.addr) ∧
        mach.st.hhd = cut.next.held.data := by
  dsimp only
  rcases c with ⟨pw, hv, held, staged⟩
  rcases held with ⟨haddr, hdata⟩
  rcases staged with ⟨saddr, sdata⟩
  rcases hostCfg with _ | ⟨ha, hv'⟩
  · rcases hv with _ | _
    · intro h
      by_cases hq : q.pending = true <;>
      by_cases hc : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
      by_cases hb : pw = true <;>
      simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
        hq, hc, hb] at h
    · intro h
      by_cases hb : pw = true <;>
        simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
          hb] at h
  · have hwin := addrOf_offOf_cfg ha (hcfg ha hv' rfl)
    rcases hv with _ | _
    · intro h
      by_cases hb : pw = true
      · simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
          hb, hwin]
      · simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
          hb] at h
    · exact absurd ⟨rfl, by simp⟩ h19

/-! ## The queue and the arbiter composed

`queue_fields` was stated under `coreIssue = true`; here the queue's `coreIssue`
is the arbiter's grant, so the machine's drain condition is the arbiter's
`coreDrain` and the agreeing fragment is the whole arbiter state. -/

/-- **The queue's drain.** The cut's `drain` (its `isCfg` decode leaf and the
arbiter's `coreIssue`) is the machine's internal drain condition.  This is what
lets the queue registers be compared with `queue_fields`'s case analysis; the
adapter's decode equality (`cw_is_cfg`) is `hisCfg`. -/
theorem drain_bridge (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat)) (i : CoreQueue.Input)
    (hfrz : i.frz = false)
    (hisCfg : i.isCfg = Machine.Config.isCfgAddr q.pendingAddr.toNat)
    (hcore : i.coreIssue = coreDrain (cwOf q c) hostCfg) :
    CoreQueue.drain q i =
      ((!false) && (cwOf q c).cwv &&
        (if ((cwOf q c).cwv && Machine.Config.isCfgAddr (cwOf q c).cwqa.toNat) then
          coreDrain (cwOf q c) hostCfg else true)) := by
  rw [CoreQueue.drain, hfrz, hisCfg, hcore]
  simp only [cwOf]
  by_cases hp : q.pending = true <;>
    by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
    simp [hp, hic, coreDrain, cwOf]

/-- **The staged payload relation is conditional.**  With nothing performed the
cut still keeps the core payload in its stage (`staged.addr` is the last bank
address), while the machine zeroes `bpa`/`bpd`.  The bank applies a stage only
on `BWP` (`Machine.cfgNext`), so the difference is unobservable; this is why
`staged_bridge`/`staged_bpa` are stated on a performed write. -/
theorem staged_idle_witness :
    let q : CoreQueue.State := ⟨0x2010, false, 0x2010, 0x5A, false⟩
    let c : Config.State := ⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩
    let cut := Config.step c (cfgIn q none)
    let mach := Machine.cwNext (cwOf q c) none none false
    cut.bankWrite = false ∧ cut.next.staged.addr = offOf 0x2010 ∧
      mach.st.bpa = 0 ∧ mach.st.bpd = 0 := by
  dsimp only
  simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
    offOf, Machine.Util.bv]

/-- **The bank-port payloads.**  The staged and the held host writes are the
same writes on both sides: the cut's nine-bit offsets are the machine's
addresses reduced by `offOf`, and (with the chip step's configuration-address
gate `hcfg`) the machine's `bpa`/`bpd` and `hha`/`hhd` are the cut's staged and
held write in full addresses.  This packages `staged_bridge`, `staged_bpa` and
`held_bridge`. -/
theorem payload_bridge (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat))
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hcfg : ∀ a v, hostCfg = some (a, v) → Machine.Config.isCfgAddr a = true) :
    let cut := Config.step c (cfgIn q hostCfg)
    let mach := Machine.cwNext (cwOf q c) hostCfg none false
    (∀ a v, mach.performed = some (a, v) →
      cut.next.staged.addr = offOf a ∧ cut.next.staged.data = Machine.Util.bv 8 v) ∧
    (cut.bankWrite = true →
      mach.st.bpa = Machine.Util.bv 16 (addrOf cut.next.staged.addr) ∧
        mach.st.bpd = cut.next.staged.data) ∧
    (mach.st.hh = true →
      mach.st.hha = Machine.Util.bv 16 (addrOf cut.next.held.addr) ∧
        mach.st.hhd = cut.next.held.data) := by
  dsimp only
  exact ⟨staged_bridge q c hostCfg h19, staged_bpa q c hostCfg h19 hcfg,
    held_bridge q c hostCfg h19 hcfg⟩

/-- **The queue fields under the arbiter's grant.**  With the queue's
`coreIssue` input driven by the arbiter (`hcore`), the machine's queue registers
after the step are the cut's.  `hisCfg` is the adapter's decode equality
`i.isCfg = isCfgAddr (CWQ.ADDR)`; without it the cut's `drain` and the machine's
would differ when the decode leaf and the machine's map disagree. -/
theorem queue_fields_arb (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat)) (i : CoreQueue.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hisCfg : i.isCfg = Machine.Config.isCfgAddr q.pendingAddr.toNat)
    (hcore : i.coreIssue = coreDrain (cwOf q c) hostCfg) :
    let st := (Machine.cwNext (cwOf q c) hostCfg (mvOf i) false).st
    let q' := CoreQueue.step q i
    st.cwa = q'.addr ∧ st.cwv = q'.pending ∧ st.cwqa = q'.pendingAddr ∧
      st.cwqd = q'.pendingData := by
  dsimp only
  simp only [CoreQueue.step]
  rw [drain_bridge q c hostCfg i hfrz hisCfg hcore]
  simp only [CoreQueue.accept, Machine.cwNext, cwOf, coreDrain, hisCfg, hcore]
  by_cases hD : CoreQueue.writeData i = true
  · have hL := writeLow_false_of_writeData i hD
    have hH := writeHigh_false_of_writeData i hD
    rcases hostCfg with _ | ⟨ha, hv'⟩ <;>
    by_cases hcv : c.heldValid = true <;>
    by_cases hbwp : c.previousWrite = true <;>
    by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
    by_cases hp : q.pending = true <;>
    simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
      CoreQueue.nextHigh, CoreQueue.pack_take, pack_round, coreDrain, cwOf, bv_add_one, bv_toNat, bv_mod8]
  · by_cases hL : CoreQueue.writeLow i = true
    · have hH := writeHigh_false_of_writeLow i hL
      rcases hostCfg with _ | ⟨ha, hv'⟩ <;>
      by_cases hcv : c.heldValid = true <;>
      by_cases hbwp : c.previousWrite = true <;>
      by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
      by_cases hp : q.pending = true <;>
      simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
        CoreQueue.nextHigh, pack_low_eq, coreDrain, cwOf, bv_toNat, bv_mod8]
    · by_cases hH : CoreQueue.writeHigh i = true
      · rcases hostCfg with _ | ⟨ha, hv'⟩ <;>
        by_cases hcv : c.heldValid = true <;>
        by_cases hbwp : c.previousWrite = true <;>
        by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
        by_cases hp : q.pending = true <;>
        simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
          CoreQueue.nextHigh, pack_high_eq, coreDrain, cwOf, bv_toNat, bv_mod8]
      · rcases hostCfg with _ | ⟨ha, hv'⟩ <;>
        by_cases hcv : c.heldValid = true <;>
        by_cases hbwp : c.previousWrite = true <;>
        by_cases hic : Machine.Config.isCfgAddr q.pendingAddr.toNat = true <;>
        by_cases hp : q.pending = true <;>
        simp_all [mvOf, CoreQueue.accept, CoreQueue.drain, CoreQueue.nextLow,
          CoreQueue.nextHigh, pack_round, coreDrain, cwOf, bv_add_one, bv_toNat, bv_mod8]

/-- **The composed configuration write.**  One cycle of the queue cut and the
arbiter cut against one `Machine.cwNext` step: the queue registers, the bank
port flags and the arbiter's grant.  The queue's `coreIssue` is the arbiter's
output (`hcore`), so the composed system is the machine's. -/
theorem cfg_compose_bridge (q : CoreQueue.State) (c : Config.State)
    (hostCfg : Option (Nat × Nat)) (i : CoreQueue.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h19 : ¬ (c.heldValid = true ∧ hostCfg.isSome = true))
    (hisCfg : i.isCfg = Machine.Config.isCfgAddr q.pendingAddr.toNat)
    (hcore : i.coreIssue = (Config.step c (cfgIn q hostCfg)).coreIssue) :
    let mach := Machine.cwNext (cwOf q c) hostCfg (mvOf i) false
    let q' := CoreQueue.step q i
    let arb := Config.step c (cfgIn q hostCfg)
    mach.st.cwa = q'.addr ∧ mach.st.cwv = q'.pending ∧
      mach.st.cwqa = q'.pendingAddr ∧ mach.st.cwqd = q'.pendingData ∧
      mach.st.bwp = arb.next.previousWrite ∧ mach.st.hh = arb.next.heldValid ∧
      arb.coreIssue = coreDrain (cwOf q c) hostCfg := by
  obtain ⟨hbw, hbank, hbwp, hhh, hdrain⟩ := arbiter_bridge q c hostCfg h19
  have hq := queue_fields_arb q c hostCfg i hreset hfrz hisCfg (by rw [hcore, hdrain])
  refine ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, ?_, ?_, hdrain⟩
  · exact hbwp.symm
  · exact hhh.symm

/-- **AMBIGUITIES #19.**  A host configuration write that arrives while a held
host write (`HH`) is pending: the cut performs the held write and *drops* the new
one (its `heldValid` clears and `held` keeps the old value); the machine performs
the held write and *holds* the new one (`hh` stays set, `hha` becomes the new
address).  The machine's own note records this reading and calls it unreachable;
the cut's `adjacent_host_can_drop` states the same drop on the RTL side. -/
theorem adjacent_host_witness :
    let c : Config.State := ⟨false, true, ⟨5, 0x11⟩, ⟨5, 0x11⟩⟩
    let hostCfg : Option (Nat × Nat) := some (addrOf 7, 0x22)
    (Config.step c (cfgIn ⟨0, false, 0, 0, false⟩ hostCfg)).next.heldValid = false ∧
      (Config.step c (cfgIn ⟨0, false, 0, 0, false⟩ hostCfg)).next.held.addr = 5 ∧
      (Machine.cwNext (cwOf ⟨0, false, 0, 0, false⟩ c) hostCfg none false).st.hh = true ∧
      (Machine.cwNext (cwOf ⟨0, false, 0, 0, false⟩ c) hostCfg none false).st.hha =
        Machine.Util.bv 16 (addrOf 7) := by
  simp [Config.step, Config.grant, Config.beforeEdge, cfgIn, cwOf, Machine.cwNext,
    addrOf, CFG_LO, offOf_addrOf, bv8_toNat]

end Metronome.Bridge.CfgWrite
