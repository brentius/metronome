import Metronome.Machine.Output

/-! §9 Host link (SPI target), host map reads and writes, runtime control registers and mailbox (§6.1, 9a.4, 9a.5,
9a.9); §12 and §13 readback registers. -/

namespace Metronome.Machine

open Util Tables

/-- §9 A host map address located in a register block: block name, instance, register name and byte index. -/
structure HostLoc where
  blk : String
  inst : Nat
  reg : String
  byte : Nat
  access : String
deriving Repr, Inhabited

/-- §9 Locate an address in the generated host map (`machine.HOST_MAP`, `HOST_BLOCKS`); `none` for program memory,
data RAM and unmapped addresses. -/
def hostLocate (a : Nat) : Option HostLoc :=
  hostBlocks.findSome? fun (name, base, stride0, inst, regs) =>
    -- a block with one instance has no stride in the host map (stride 0): its extent is its registers
    let stride := if stride0 == 0 then regs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else stride0
    if base ≤ a && a < base + stride * inst then
      let i := (a - base) / stride
      let off := (a - base) % stride
      regs.findSome? fun (ro, rn, bytes, acc) =>
        if ro ≤ off && off < ro + bytes then some ⟨name, i, rn, off - ro, acc⟩ else none
    else none

/-- §9 A host write in cycle W: address, byte and its location. -/
structure HostWr where
  addr : Nat
  v : Nat
  loc : Option HostLoc
deriving Repr, Inhabited

namespace Util
/-- The byte index and value of a host write to register `reg` of instance `inst` of block `blk`. -/
def hwAt (hw : Option HostWr) (blk : String) (inst : Nat) (reg : String) : Option (Nat × Nat) :=
  match hw with
  | some w => match w.loc with
    | some l => if l.blk == blk && l.inst == inst && l.reg == reg then some (l.byte, w.v) else none
    | none => none
  | none => none
/-- The value of a host write to a one-byte register. -/
def hwByte (hw : Option HostWr) (blk : String) (inst : Nat) (reg : String) : Option Nat :=
  (hwAt hw blk inst reg).map (·.2)
end Util

/-- §9 / §12 / §13 Host read: the register's value in cycle R (no side effect), or a data RAM read (byte address).
Configuration registers (access W) read 0 (D14); program memory reads 0; unmapped addresses read 0. Readable
registers: `CTRL` (`RUN`, `STICKY`, `IRQEN`, `DOORBELL` reads 0, `HOSTIN` = `INB`, `HOSTOUT` = `OUTB`, `HOSTSTAT`,
`ID = 0xA0 | VERSION`, `ERRSUM`); line runtime `PHASE`, `CTL`, `SYM`, `INS`, `STAT`; thread `PC`, `STAT`; stream
`POSL`, `POSH`, `CTL` (0); `DBG`, `MCTL`, `ECTL`, `MISR`, `EMASK`, `ACC`, `AFLG`, `FLAGS`, `CST`, `FPC`, `RLV`. -/
def hostRead (s : State) (cv : CfgView) (a : Nat) : Sum Nat Nat :=
  if DATA_BASE ≤ a && a < DATA_BASE + DATA_BYTES then .inr (a - DATA_BASE) else
  match hostLocate a with
  | none => .inl 0
  | some l =>
    let c := s.ctrl
    let i := l.inst
    let k := l.byte
    let v : Nat := match l.blk, l.reg with
      | "CTRL", "RUN" => b2n c.run
      | "CTRL", "STICKY" => b2n c.conflict + 2 * b2n c.memhaz + 4 * b2n c.cwovr
      | "CTRL", "IRQEN" => c.irqen.toNat
      | "CTRL", "HOSTIN" => c.inb.toNat
      | "CTRL", "HOSTOUT" => c.outb.toNat
      | "CTRL", "HOSTSTAT" => b2n c.inv + 2 * b2n c.outv
      | "CTRL", "ID" => 0xA0 ||| VERSION
      | "CTRL", "ERRSUM" =>
        packBits [s.threads.toList.any (·.late), s.threads.toList.any (·.ovr), s.lines.toList.any (·.tapmiss),
          s.streams.toList.any (·.starved), c.conflict, c.memhaz, c.cwovr]
      | "LRT", "PHASE" => getByte (vget s.lines i).ph k
      | "LRT", "CTL" =>
        let ls := vget s.lines i
        packBits [ls.run, ls.arm, ls.ren, ls.sp] + ls.fired.toNat * 16 + b2n ls.held * 128
      | "LRT", "SYM" => let ls := vget s.lines i; ls.staged.toNat + ls.committed.toNat * 16
      | "LRT", "INS" =>
        let ls := vget s.lines i
        ls.sn.toNat + b2n ls.rem * 16 + inSym (vget cv.lines i) ls * 32
      | "LRT", "STAT" => b2n (vget s.lines i).tapmiss
      | "TRT", "PC" => (vget s.threads i).pc.toNat
      | "TRT", "STAT" =>
        let t := vget s.threads i
        packBits [t.ready, t.running, t.armed, t.en, t.late, t.ovr]
      | "SRT", "POSL" => (vget s.streams i).pos.toNat % 256
      | "SRT", "POSH" =>
        let st := vget s.streams i
        st.pos.toNat / 256 + st.bidx.toNat * 16 + b2n st.starved * 128
      | "DBG", "DBG" => b2n s.dbg.freeze
      | "DBG", "MCTL" => b2n s.dbg.men
      | "DBG", "ECTL" => b2n s.dbg.cen + 2 * b2n s.dbg.rpl
      | "DBG", "MISR" => getByte s.dbg.misr k
      | "DBG", "EMASK" => getByte s.dbg.emask k
      | "DBG", "ACC" => s.units.a.toNat
      | "DBG", "AFLG" => packBits [s.units.z, s.units.c, s.units.n]
      | "DBG", "FLAGS" => getByte s.units.f k
      | "DBG", "CST" =>
        let cs := vget s.cores k
        cs.xt.toNat + 8 * b2n cs.xv + 16 * b2n cs.rv
      | "DBG", "FPC" => (vget s.cores k).fpc.toNat
      | "DBG", "RLV" => getByte s.dbg.rlv k
      | _, _ => 0
    .inl v

/-- §9 SPI target, mode 0, MSB first, in cycle t. `SR` is the synchronised rising edge of SCK in a cycle where the
synchronised CS_N is low.

* While CS_N is high the byte state returns to the command byte, the bit count clears and `TX' = 0`.
* On each `SR`: `RX' = {RX[6:0], MOSI}` and the bit count increments; on the 1st..7th `SR` `TX' = {TX[6:0], 0}`;
  the 8th `SR` in cycle c completes the byte `{RX[6:0], MOSI}` and leaves `TX` unchanged.
* Byte 0 command (`0x02` write, `0x03` read, other: ignore the transaction); byte 1 `ADDR[15:8]`; byte 2 `ADDR[7:0]`
  and, for a read, a read request at `ADDR` in c+1 (9a.9); write bytes 3+: a host write of the byte to `ADDR` in
  W = c+1, `ADDR' = ADDR + 1` at the end of W; read bytes 3+: a read request at `ADDR` in c+1.
* A register read issued in R loads `TX` at the end of R+1 with its value in R; a data RAM read issued in R becomes
  the host request, and served in s its byte loads `TX` at the end of s+1. `ADDR' = ADDR + 1` with each load. A load
  in the same cycle as a shifting `SR` is lost (-- AMBIG(17) `ADDR` still increments).
* 9a.4: one host request; a new one overwrites an unserved one.

Returns the next link state and the host write of this cycle (W). -/
def hostNext (s : State) (cv : CfgView) (p : PinView) (served : Bool) : HostSt × Option HostWr :=
  let h := s.host
  let addr := h.addr.toNat
  -- actions of the byte completed in the previous cycle
  let hw : Option HostWr := if h.wPend then some ⟨addr, h.wData.toNat, hostLocate addr⟩ else none
  let rd : Option (Sum Nat Nat) := if h.rPend then some (hostRead s cv addr) else none
  -- shifting
  let csHigh := p.csn
  let sr := p.sckRise && !p.csn
  let nb := h.nbit.toNat
  let complete := sr && nb == 7
  let v := (h.rx.toNat % 128) * 2 + b2n p.mosi
  let rx' := if sr then bv 8 v else h.rx
  let nbit' := if csHigh then 0 else if sr then (nb + 1) % 8 else nb
  -- byte processing
  let bi := h.nbyte.toNat
  let cmd := h.cmd.toNat
  let (cmd', nbyte1, addrSet, wP, rP) : Nat × Nat × Option Nat × Bool × Bool :=
    if !complete then (cmd, bi, none, false, false)
    else match bi with
      | 0 => (if v == 0x02 then 1 else if v == 0x03 then 2 else 0, 1, none, false, false)
      | 1 => (cmd, 2, if cmd != 0 then some (v * 256 + addr % 256) else none, false, false)
      | 2 => (cmd, 3, if cmd != 0 then some ((addr / 256) * 256 + v) else none, false, cmd == 2)
      | _ => (cmd, 3, none, cmd == 1, cmd == 2)
  let nbyte' := if csHigh then 0 else nbyte1
  -- loads into TX
  -- AMBIG(21) coincident events: a register load wins over a RAM landing; a byte 1/2 address set wins over an
  -- increment; a load and a write increment ADDR once; a load wins over the 8th (non-shifting) SR
  let regLoad := h.ldV
  let ramLoad := s.ramOwner == 4
  let load := regLoad || ramLoad
  let loadByte := if regLoad then h.ldD.toNat else nbits s.ramOut.toNat (8 * s.ramLane.toNat) 8
  let tx' := if csHigh then 0 else if sr && nb < 7 then bv 8 ((h.tx.toNat * 2) % 256)
    else if load then bv 8 loadByte else h.tx
  let addr' := match addrSet with
    | some a => a
    | none => if hw.isSome || load then (addr + 1) % 65536 else addr
  -- register read value, host request
  let (ldV', ldD') := match rd with
    | some (.inl x) => (true, x)
    | _ => (false, 0)
  let req1 := if served then HReq.none else h.req
  let req' := match rd with
    | some (.inr a) => HReq.read (bv 11 a)
    | _ => if h.wPend && DATA_BASE ≤ addr && addr < DATA_BASE + DATA_BYTES then
        HReq.write (bv 11 (addr - DATA_BASE)) h.wData else req1
  ({ rx := rx', tx := tx', nbit := bv 3 nbit', nbyte := bv 2 nbyte', cmd := bv 2 cmd', addr := bv 16 addr',
     wPend := wP, wData := bv 8 v, rPend := rP, ldV := ldV', ldD := bv 8 ldD', req := req' }, hw)

/-- §6.2 / §9 The host's data RAM request to the arbiter. -/
def hostReq (h : HostSt) : RamReq :=
  match h.req with
  | .none => .none
  | .read a => .rd (a.toNat / 4) (a.toNat % 4)
  | .write a v => .wrByte a.toNat v.toNat

/-- §9 / §6.1 / 9a.5 / §12.3 Inputs to the control registers from the moves in cycle t. -/
structure CtrlIn where
  hostOut : Option Nat := none
  hostInRead : Bool := false
  conflict : Bool := false
  memhaz : Bool := false
  cwovr : Bool := false

/-- §9 / §6.1 / 9a.5 / §12.3 Control registers next state.

* `CTRL.RUN` bit 0 is `RUN_global`; `IRQEN` bits 0, 1; `STICKY` write 1 to clear `CONFLICT`, `MEMHAZ`, `CWOVR`
  (bits 0, 1, 2), a flag set in the same cycle stays set.
* `DOORBELL`: writing bit t in W makes `DB[t] = 1` in W+1 only; in a frozen cycle `DB' = written bits | DB`.
* Mailbox: `HOST.OUT: OUTB' = v, OUTV' = 1` (wins over a host clear of `OUTV` by `HOSTSTAT` bit 1); `HOSTIN` write:
  `INB' = v, INV' = 1` (wins over a `HOST.IN` read, which clears `INV`); `INVP' = INV` (held while frozen).
* `IRQ'` (§9). -/
def ctrlNext (s : State) (hw : Option HostWr) (i : CtrlIn) (frozen : Bool) : CtrlSt :=
  let c := s.ctrl
  let w := hwByte hw "CTRL" 0
  let sticky := (w "STICKY").getD 0
  let hin := w "HOSTIN"
  let db := (w "DOORBELL").getD 0 % 64
  { run := match w "RUN" with
      | some v => nbit v 0
      | none => c.run
    irqen := match w "IRQEN" with
      | some v => bv 2 v
      | none => c.irqen
    conflict := (c.conflict && !nbit sticky 0) || i.conflict
    memhaz := (c.memhaz && !nbit sticky 1) || i.memhaz
    cwovr := (c.cwovr && !nbit sticky 2) || i.cwovr
    inb := match hin with
      | some v => bv 8 v
      | none => c.inb
    inv := if hin.isSome then true else if i.hostInRead then false else c.inv
    invp := if frozen then c.invp else c.inv
    outb := match i.hostOut with
      | some v => bv 8 v
      | none => c.outb
    outv := if i.hostOut.isSome then true else if nbit ((w "HOSTSTAT").getD 0) 1 then false else c.outv
    db := if frozen then bv 6 (db ||| c.db.toNat) else bv 6 db
    irq := irqNext s }

end Metronome.Machine
