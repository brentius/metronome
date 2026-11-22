import Metronome.Machine.Config

/-!
Machine state: every register of SPEC_V2 part B (§1: "while `rst_q` is low every register in this document is 0"),
the configuration latches (§1), program memory (§5) and data RAM (§6.2). A few registers are implied by the SPEC
but not named in it (memory output registers, request slots, the replay buffer); each says where it comes from.
-/

namespace Metronome.Machine

open Util

/-- §3.1 Line state: `PH` (16); `RUN, ARM, REN`; `HELD`; `FIRST`; `SC, SP`; `FIRED[2:0]`; working samples
`W = {B1, A2, A1, A0}`; snapshot `SN` (4); remembered bit `REM`; `STAGED, COMMITTED` (4 each); sticky `TAPMISS`. -/
structure LineSt where
  ph : BitVec 16 := 0
  run : Bool := false
  arm : Bool := false
  ren : Bool := false
  held : Bool := false
  first : Bool := false
  sc : Bool := false
  sp : Bool := false
  fired : BitVec 3 := 0
  w : BitVec 4 := 0
  sn : BitVec 4 := 0
  rem : Bool := false
  staged : BitVec 4 := 0
  committed : BitVec 4 := 0
  tapmiss : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §4 Thread state: `PC` (8), `EN`, `READY`, `RUNNING`, `ARMED`, sticky `LATE`, `OVR`. -/
structure ThreadSt where
  pc : BitVec 8 := 0
  en : Bool := false
  ready : Bool := false
  running : Bool := false
  armed : Bool := false
  late : Bool := false
  ovr : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §5 Core state: `XV`, `IR` (64), `RV`, `FPC` (8), `XT` (3), `XL` (2), `RR` (3), and `mout`, the program memory
output register of the synchronous read ("an address presented in cycle t is registered at the end of t, and its
word is at the memory output during t+1"). -/
structure CoreSt where
  xv : Bool := false
  ir : BitVec 64 := 0
  rv : Bool := false
  fpc : BitVec 8 := 0
  xt : BitVec 3 := 0
  xl : BitVec 2 := 0
  rr : BitVec 3 := 0
  mout : BitVec 64 := 0
deriving Repr, Inhabited, DecidableEq

/-- §6.1 / SPEC v1 6.1 Shifter: `D` (8), `CNT` (4), `LEN` (4, 0 means 8), `MSB`. -/
structure ShSt where
  d : BitVec 8 := 0
  cnt : BitVec 4 := 0
  len : BitVec 4 := 0
  msb : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §6.1 / SPEC v1 6.1 Pointer request `REQ` (none, fetch, write + address + data). -/
inductive PReq where
  | none
  | fetch
  | write (a : BitVec 11) (v : BitVec 8)
deriving Repr, Inhabited, DecidableEq

/-- §6.1 / SPEC v1 6.1 Pointer P0: `PTR` (11), `D` (8), `RDY`, one pending request `REQ`; `land` = a fetch served in
an earlier cycle has not yet updated `RDY` (§12.3 landing exception); `stale` = that fetch is stale (v1 9a.3). -/
structure P0St where
  ptr : BitVec 11 := 0
  d : BitVec 8 := 0
  rdy : Bool := false
  req : PReq := .none
  land : Bool := false
  stale : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §6.1 Units: flags `F`, `FP`; accumulator `A`, `Z, C, N`; scratch `R0..R3`; shifters; counters `V`; LFSR `S`. -/
structure UnitsSt where
  f : BitVec 16 := 0
  fp : BitVec 16 := 0
  a : BitVec 8 := 0
  z : Bool := false
  c : Bool := false
  n : Bool := false
  r : Vector (BitVec 8) 4 := Vector.replicate 4 0
  sh : Vector ShSt 2 := Vector.replicate 2 {}
  cnt : Vector (BitVec 16) 3 := Vector.replicate 3 0
  lf : Vector (BitVec 32) 2 := Vector.replicate 2 0
deriving Repr, Inhabited

/-- §6.3 Stream state: `POS` (12), `BIDX` (3), `BA` (11), `CUR` (8), `CV`, `WB` (32), `WV`, `RQ`, `LD`, `PEND` (8), `PV`,
sticky `STARVED`; §13.2 second replay buffer word `NB` and its valid bit `NV`. -/
structure StreamSt where
  pos : BitVec 12 := 0
  bidx : BitVec 3 := 0
  ba : BitVec 11 := 0
  cur : BitVec 8 := 0
  cv : Bool := false
  wb : BitVec 32 := 0
  wv : Bool := false
  rq : Bool := false
  ld : Bool := false
  pend : BitVec 8 := 0
  pv : Bool := false
  starved : Bool := false
  nb : BitVec 32 := 0
  nv : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §9 Host data RAM request slot (9a.4: one request). -/
inductive HReq where
  | none
  | read (a : BitVec 11)
  | write (a : BitVec 11) (v : BitVec 8)
deriving Repr, Inhabited, DecidableEq

/-- §9 SPI target state: shift registers `RX`, `TX`; bit count; byte index (0 command, 1, 2, 3 = data);
command (0 ignore, 1 write, 2 read); `ADDR`; the action of a byte completed in the previous cycle (`wPend` host write
in W = c+1, `rPend` read request in c+1); a register read value to load into `TX` (`ldV`, `ldD`); the host data RAM
request slot. -/
structure HostSt where
  rx : BitVec 8 := 0
  tx : BitVec 8 := 0
  nbit : BitVec 3 := 0
  nbyte : BitVec 2 := 0
  cmd : BitVec 2 := 0
  addr : BitVec 16 := 0
  wPend : Bool := false
  wData : BitVec 8 := 0
  rPend : Bool := false
  ldV : Bool := false
  ldD : BitVec 8 := 0
  req : HReq := .none
deriving Repr, Inhabited, DecidableEq

/-- §9 / §6.1 Control and mailbox registers: `RUN_global`, `IRQEN`, sticky `CONFLICT`, `MEMHAZ`, `CWOVR` (§13.1),
mailbox `INB, INV, INVP, OUTB, OUTV`, doorbell pulses `DB`, the `IRQ` output register. -/
structure CtrlSt where
  run : Bool := false
  irqen : BitVec 2 := 0
  conflict : Bool := false
  memhaz : Bool := false
  cwovr : Bool := false
  inb : BitVec 8 := 0
  inv : Bool := false
  invp : Bool := false
  outb : BitVec 8 := 0
  outv : Bool := false
  db : BitVec 6 := 0
  irq : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- §12 / §13.2 Debug block: `FREEZE`, `FRZ`, `FRZD`; `MEN`, `MISR` (`M`); `CEN`, `RPL`, `EMASK`, `DC`; `RLV` and
`rlvp`, the `RLV` of the previous cycle (§13.2 "its previous level is `RLV` of the previous cycle"). -/
structure DbgSt where
  freeze : Bool := false
  frz : Bool := false
  frzd : Bool := false
  men : Bool := false
  misr : BitVec 32 := 0
  cen : Bool := false
  rpl : Bool := false
  emask : BitVec 13 := 0
  dc : BitVec 19 := 0
  rlv : BitVec 13 := 0
  rlvp : BitVec 13 := 0
deriving Repr, Inhabited, DecidableEq

/-- §13.1 Core configuration writes and the bank port: `CWA` (16), `CWV`, `CWQ = (address, byte)`; `BWP`; `HH` (held
host configuration write, address and byte); `bpa, bpd` = the write performed in the previous cycle, entering the
latches (seen from t+2, §1). -/
structure CwSt where
  cwa : BitVec 16 := 0
  cwv : Bool := false
  cwqa : BitVec 16 := 0
  cwqd : BitVec 8 := 0
  bwp : Bool := false
  hh : Bool := false
  hha : BitVec 16 := 0
  hhd : BitVec 8 := 0
  bpa : BitVec 16 := 0
  bpd : BitVec 8 := 0
deriving Repr, Inhabited, DecidableEq

/-- §2 Synchronisers `s1, s2, sp` of the raw inputs `ui_in` and `uio_in`. -/
structure SyncSt where
  ui1 : BitVec 8 := 0
  ui2 : BitVec 8 := 0
  uip : BitVec 8 := 0
  uio1 : BitVec 8 := 0
  uio2 : BitVec 8 := 0
  uiop : BitVec 8 := 0
deriving Repr, Inhabited, DecidableEq

/-- §1 The whole chip: reset flops (`r1`, `rq` = `rst_q`, `rqh` = `rst_q` of the two previous cycles), registers,
configuration latches, program memory (2 x 256 x 64, byte image, word w at bytes 8w..8w+7 little-endian), data RAM
(2,048 bytes) and its output register (`ramOut`, `ramOwner`: 0 none, 1 S0, 2 S1, 3 P0, 4 host; `ramLane` byte lane). -/
structure State where
  r1 : Bool := false
  rq : Bool := false
  rqh : BitVec 2 := 0
  sync : SyncSt := {}
  lines : Vector LineSt 4 := Vector.replicate 4 {}
  threads : Vector ThreadSt 6 := Vector.replicate 6 {}
  cores : Vector CoreSt 2 := Vector.replicate 2 {}
  units : UnitsSt := {}
  p0 : P0St := {}
  streams : Vector StreamSt 2 := Vector.replicate 2 {}
  host : HostSt := {}
  ctrl : CtrlSt := {}
  dbg : DbgSt := {}
  cw : CwSt := {}
  out : BitVec 14 := 0
  oen : BitVec 8 := 0
  cfg : Config := Config.zero
  pmem : Vector ByteArray 2 := Vector.replicate 2 (bzero 2048)
  dmem : ByteArray := bzero 2048
  ramOut : BitVec 32 := 0
  ramOwner : Nat := 0
  ramLane : BitVec 2 := 0

/-- §1 Power-on state: everything 0, including program and data memories. -/
def State.init : State := {}

/-- §1 / §2 Pin inputs of one cycle at the `tt_um` boundary. -/
structure PinIn where
  ui : BitVec 8
  uio : BitVec 8
  rstn : Bool
deriving Repr, Inhabited, DecidableEq

end Metronome.Machine
