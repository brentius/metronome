/-
# ChipCut: the abstraction relation

`ChipRel` relates the product state to `Metronome.Machine.State`.  Three groups
are *validity-guarded*, because the RTL and the machine disagree only where a
value is not read:

* the configuration-write bank port (`CwRel`): `bpa`/`bpd` are the performed
  write and are compared only when `bwp`; `hha`/`hhd` only when `hh`;
* the pointer `stale` bit (`P0Rel`): the cut's `!landRdy` against the machine's
  `stale`, compared only while `land`;
* the latch-bank byte image (`BankRel`): bytes without a latch read zero,
  latched bytes equal the machine's configuration byte.

Without the guards `ChipRel` is false at every reset edge: the machine resets
`bpa`/`hha` to 0 while the cut's arbiter stage keeps its payload, and the
machine resets `stale = false` while the cut clears `landRdy = false`.  The
guards are exactly the "payload only meaningful when valid" facts
(`project.v` 136-148, `Machine.cfgNext`, `Machine.p0Next`).
-/

import Metronome.ChipCut.Step

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut

open Metronome

/-! ## Field relations -/

/-- The synchroniser words: `{ui, uio}` on the cut side, two bytes on the
machine side. -/
def SyncRel (a : SpiPins.Sync) (b : Machine.SyncSt) : Prop :=
  a.s1 = b.ui1 ++ b.uio1 ∧ a.s2 = b.ui2 ++ b.uio2 ∧ a.sp = b.uip ++ b.uiop

/-- The seven core registers.  `IR` is compared only while `XV` is set: the cut
(`md2_core.v`) captures the program-memory output on every unfrozen cycle, the
machine only on `load`, so the raw `IR` registers differ in `XV = 0` cycles.
That is unobservable — §5 decodes `IR` only when `XV` — and the register agrees
at the next execute cycle (`xv' = load` captures the same word on both sides).
The clause is therefore `a.xv = true → b.ir = a.ir`. -/
def CoreRegsRel (a : Core.State) (b : Machine.CoreSt) : Prop :=
  b.xv = a.xv ∧ (a.xv = true → b.ir = a.ir) ∧ b.rv = a.rv ∧ b.fpc = a.fpc ∧ b.xt = a.xt ∧
    b.xl = a.xl ∧ b.rr = a.rr

/-- The machine units record from the cut unit states. -/
def UnitsRel (s : State) (u : Machine.UnitsSt) : Prop :=
  u.f = s.glue.fl ∧ u.fp = s.glue.flp ∧ u.a = s.acc.a ∧ u.z = s.acc.z ∧
    u.c = s.acc.c ∧ u.n = s.acc.n ∧
    (∀ k : Fin 4, u.r[k] = BitVec.truncate 8 (BitVec.ushiftRight s.acc.r (8 * k.val))) ∧
    (∀ k : Fin 2, u.sh[k] =
      ({ d := (shAt s k.val).dr, cnt := (shAt s k.val).cnt, len := (shAt s k.val).len,
         msb := (shAt s k.val).msb } : Machine.ShSt)) ∧
    (∀ k : Fin 3, u.cnt[k] = (cntAt s k.val).v) ∧
    (∀ k : Fin 2, u.lf[k] = (lfAt s k.val).s)

/-- The machine control registers from the cut glue state and sticky errors. -/
def CtrlRel (s : State) (c : Machine.CtrlSt) : Prop :=
  c.run = s.glue.runG ∧ c.irqen = s.glue.irqEn ∧ c.conflict = s.conflict ∧
    c.memhaz = s.memhaz ∧ c.cwovr = s.cq.overrun ∧ c.inb = s.glue.inB ∧
    c.inv = s.glue.inv ∧ c.invp = s.glue.invp ∧ c.outb = s.glue.outB ∧
    c.outv = s.glue.outv ∧ c.db = s.glue.db ∧ c.irq = s.glue.irq

/-- The machine debug block from the debug cuts. -/
def DbgRel (s : State) (d : Machine.DbgSt) : Prop :=
  d.freeze = s.freeze.freeze ∧ d.frz = s.freeze.frz ∧ d.frzd = s.freeze.frzd ∧
    d.men = s.dbgDigest.men ∧ d.misr = s.dbgDigest.misr ∧ d.cen = s.dbgCtrl.cen ∧
    d.rpl = s.dbgCtrl.replay ∧ d.emask = s.dbgCtrl.emask ∧ d.dc = s.dbgCtrl.dc ∧
    d.rlv = s.dbgCtrl.rlv ∧ d.rlvp = s.dbgCtrl.rlvPrev

/-- The control relation's `IRQ` projection. -/
theorem CtrlRel.irq_eq {s : State} {c : Machine.CtrlSt} (h : CtrlRel s c) :
    c.irq = s.glue.irq := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12⟩ := h
  exact h12

/-- The pointer relation.  `stale` (the machine's reading) is compared with the
cut's `!landRdy` only in the cycles the machine reads it, i.e. while a landing
is pending (`land`). -/
structure P0Rel (a : Machine.P0St) (b : Mem.State) : Prop where
  ptr : a.ptr = b.ptr
  d : a.d = b.dat
  rdy : a.rdy = b.rdy
  req : a.req = Bridge.Mem.reqOf b
  land : a.land = b.land
  stale : a.land = true → a.stale = !b.landRdy

/-- The configuration-write relation.  The queue and bank-port flags are exact;
the bank-port payloads are compared only on a performed write (`bwp`) or a held
host write (`hh`). -/
structure CwRel (a : Machine.CwSt) (q : CoreQueue.State) (c : Config.State) : Prop where
  cwa : a.cwa = q.addr
  cwv : a.cwv = q.pending
  cwqa : a.cwqa = q.pendingAddr
  cwqd : a.cwqd = q.pendingData
  bwp : a.bwp = c.previousWrite
  hh : a.hh = c.heldValid
  bpa : a.bwp = true → a.bpa = Bridge.CfgWrite.addrOf c.staged.addr
  bpd : a.bwp = true → a.bpd = c.staged.data
  hha : a.hh = true → a.hha = Bridge.CfgWrite.addrOf c.held.addr
  hhd : a.hh = true → a.hhd = c.held.data

/-- The bank carries the fixed RTL mask and agrees with the machine image on
every implemented bit. Bits outside the mask read zero. -/
def BankRel (b : Bank.State) (c : Machine.Config) : Prop :=
  b.mask = Discharge.BankWire.cfgMaskFin ∧
  ∀ k : Fin Bank.BYTES, Bank.read b k =
    BitVec.ofNat 8 (Machine.Util.cfgByte c (Machine.Tables.LINE_BASE + k.val)) &&& b.mask k

/-- The field-wise relation between a product state and a machine state. -/
structure ChipRel (s : State) (m : Machine.State) : Prop where
  rstM : s.rst.rstM = m.r1
  rstQ : s.rst.rstQ = m.rq
  rqh : s.rqh = m.rqh
  sync : SyncRel s.sync m.sync
  lines : ∀ l : Fin 4, m.lines[l] = Bridge.Line.absSt (lineAt s l.val)
  threads : ∀ t : Fin 6, m.threads[t] = Bridge.Thread.absState (threadAt s t.val)
  cores : ∀ c : Fin 2, CoreRegsRel (s.cores[c.val]) m.cores[c]
  mout : ∀ c : Fin 2, m.cores[c].mout = s.cont.mout[c.val]
  units : UnitsRel s m.units
  p0 : P0Rel m.p0 s.p0
  streams : ∀ k : Fin 2,
    Bridge.StreamB.AbsRelB (k.val == 0) (streamAt s k.val) m.streams[k]
  host : Bridge.Host.LinkRelR s.hostRead s.hostCmd.cmd m
  /-- The host data-RAM slot drives the arbiter, so it is related exactly. -/
  hostReq : m.host.req = Bridge.Mem.absSlot s.p0
  ctrl : CtrlRel s m.ctrl
  dbg : DbgRel s m.dbg
  cw : CwRel m.cw s.cq s.arb
  bank : BankRel s.bank m.cfg
  out : m.out = s.outPins
  oen : m.oen = s.oenPins
  cfg : m.cfg = s.cont.cfg
  pmem : m.pmem = s.cont.pmem
  dmem : m.dmem = s.cont.dmem
  ramOut : m.ramOut = s.cont.ramOut
  ramOwner : m.ramOwner = s.cont.ramOwner
  ramLane : m.ramLane = s.cont.ramLane

/-! ## Congruence of the host relation in the machine's `host` field -/

/-- `LinkRel` reads only the machine's `host` field. -/
theorem linkRel_host_congr {s : HostCmd.State} {m m' : Machine.State}
    (h : m.host = m'.host) : Bridge.Host.LinkRel s m' → Bridge.Host.LinkRel s m := by
  intro hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hr
  exact ⟨by simpa [h] using a1, by simpa [h] using a2, by simpa [h] using a3,
    by simpa [h] using a4, by simpa [h] using a5, by simpa [h] using a6,
    by simpa [h] using a7, by simpa [h] using a8, by simpa [h] using a9,
    by simpa [h] using a10, by simpa [h] using a11⟩

/-- `LinkRelR` reads only the machine's `host` field. -/
theorem linkRelR_host_congr {s : HostRead.State} {cmd : BitVec 8} {m m' : Machine.State}
    (h : m.host = m'.host) : Bridge.Host.LinkRelR s cmd m' → Bridge.Host.LinkRelR s cmd m := by
  intro hr
  refine ⟨linkRel_host_congr h hr.base, by simpa [h] using hr.tx, ?_⟩
  intro hh
  simpa [h] using hr.rackv hh

/-- `ChipRel` pins the driven pins: `OUT`/`OEN`, `IRQ` and the `TX[7]` MISO
line are the machine's (`project.v` 818-820). -/
theorem pins_of_rel {s : State} {m : Machine.State} (h : ChipRel s m) :
    pinsOf s = Machine.pinsOut m := by
  simp only [pinsOf, Machine.pinsOut, h.out, h.oen, CtrlRel.irq_eq h.ctrl, h.host.tx]

end Metronome.ChipCut
