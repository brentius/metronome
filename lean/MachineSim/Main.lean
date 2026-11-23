import Metronome.Machine

/-!
`machine-sim`: line protocol driver for `Metronome.Machine.step` (BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md).

stdin, one command per line:
* `ui uio rst_n` (decimal): apply one clock cycle with those pin values and print one JSON object with the state
  after the cycle (the values in cycle t+1) and the pins it drives;
* `reset`: return to the power-on state (no output);
* `quit`: exit.
-/

open Metronome.Machine Metronome.Machine.Util

namespace MachineSim

/-- Simulator state: machine state plus incrementally maintained memory sums. -/
structure Sim where
  st : State
  dsum : Nat
  psum : Array Nat

def mod32 : Nat := 2 ^ 32

def initSim : Sim := { st := State.init, dsum := 0, psum := #[0, 0] }

def memOf (s : State) (m : Nat) : ByteArray := if m == 0 then s.dmem else vget s.pmem (m - 1)

/-- Update `sum = Σ mem[i]·(i+1) mod 2^32` for the bytes written in a cycle. -/
def updSums (sim : Sim) (s' : State) (ws : List MemWrite) : Sim :=
  let ws := ws.foldl (fun acc w => if acc.any (fun x => x.mem == w.mem && x.addr == w.addr) then acc else acc ++ [w]) []
  ws.foldl (fun sim w =>
    let o := bget (memOf sim.st w.mem) w.addr
    let n := bget (memOf s' w.mem) w.addr
    let d := (n * (w.addr + 1) + mod32 * 256 - o * (w.addr + 1)) % mod32
    if w.mem == 0 then { sim with dsum := (sim.dsum + d) % mod32 }
    else { sim with psum := sim.psum.modify (w.mem - 1) fun x => (x + d) % mod32 }) sim

def b (x : Bool) : Nat := if x then 1 else 0

def dump (sim : Sim) : String := Id.run do
  let s := sim.st
  let mut kv : Array (String × Nat) := #[]
  let (uo, uio, oe) := pinsOut s
  kv := kv ++ #[("uo_out", uo), ("uio_out", uio), ("uio_oe", oe)]
  for l in [0:4] do
    let x := vget s.lines l
    let p := s!"L{l}."
    kv := kv ++ #[(p ++ "PH", x.ph.toNat), (p ++ "RUN", b x.run), (p ++ "ARM", b x.arm), (p ++ "REN", b x.ren),
      (p ++ "HELD", b x.held), (p ++ "FIRST", b x.first), (p ++ "SC", b x.sc), (p ++ "SP", b x.sp),
      (p ++ "FIRED", x.fired.toNat), (p ++ "W", x.w.toNat), (p ++ "SN", x.sn.toNat), (p ++ "REM", b x.rem),
      (p ++ "STAGED", x.staged.toNat), (p ++ "COMMITTED", x.committed.toNat), (p ++ "TAPMISS", b x.tapmiss)]
  for t in [0:6] do
    let x := vget s.threads t
    let p := s!"T{t}."
    kv := kv ++ #[(p ++ "PC", x.pc.toNat), (p ++ "EN", b x.en), (p ++ "READY", b x.ready),
      (p ++ "RUNNING", b x.running), (p ++ "ARMED", b x.armed), (p ++ "LATE", b x.late), (p ++ "OVR", b x.ovr)]
  for c in [0:2] do
    let x := vget s.cores c
    let p := s!"C{c}."
    kv := kv ++ #[(p ++ "XV", b x.xv), (p ++ "IR", x.ir.toNat), (p ++ "RV", b x.rv), (p ++ "FPC", x.fpc.toNat),
      (p ++ "XT", x.xt.toNat), (p ++ "XL", x.xl.toNat), (p ++ "RR", x.rr.toNat)]
  let u := s.units
  kv := kv ++ #[("F", u.f.toNat), ("FP", u.fp.toNat), ("A", u.a.toNat), ("Z", b u.z), ("C", b u.c), ("N", b u.n)]
  for k in [0:4] do
    kv := kv.push (s!"R{k}", (vget u.r k).toNat)
  for k in [0:2] do
    let x := vget u.sh k
    kv := kv ++ #[(s!"SH{k}.D", x.d.toNat), (s!"SH{k}.CNT", x.cnt.toNat), (s!"SH{k}.LEN", x.len.toNat),
      (s!"SH{k}.MSB", b x.msb)]
  for k in [0:3] do
    kv := kv.push (s!"CNT{k}.V", (vget u.cnt k).toNat)
  for k in [0:2] do
    kv := kv.push (s!"LF{k}.S", (vget u.lf k).toNat)
  kv := kv ++ #[("P0.PTR", s.p0.ptr.toNat), ("P0.D", s.p0.d.toNat), ("P0.RDY", b s.p0.rdy)]
  for k in [0:2] do
    let x := vget s.streams k
    let p := s!"S{k}."
    kv := kv ++ #[(p ++ "POS", x.pos.toNat), (p ++ "BIDX", x.bidx.toNat), (p ++ "BA", x.ba.toNat),
      (p ++ "CUR", x.cur.toNat), (p ++ "CV", b x.cv), (p ++ "WB", x.wb.toNat), (p ++ "WV", b x.wv),
      (p ++ "RQ", b x.rq), (p ++ "LD", b x.ld), (p ++ "PEND", x.pend.toNat), (p ++ "PV", b x.pv),
      (p ++ "STARVED", b x.starved)]
  let c := s.ctrl
  kv := kv ++ #[("RUN", b c.run), ("IRQEN", c.irqen.toNat), ("CONFLICT", b c.conflict), ("MEMHAZ", b c.memhaz),
    ("CWOVR", b c.cwovr), ("INB", c.inb.toNat), ("INV", b c.inv), ("INVP", b c.invp), ("OUTB", c.outb.toNat),
    ("OUTV", b c.outv)]
  let d := s.dbg
  kv := kv ++ #[("FREEZE", b d.freeze), ("FRZ", b d.frz), ("FRZD", b d.frzd), ("MEN", b d.men),
    ("MISR", d.misr.toNat), ("CEN", b d.cen), ("EMASK", d.emask.toNat), ("DC", d.dc.toNat)]
  let w := s.cw
  kv := kv ++ #[("CWA", w.cwa.toNat), ("CWV", b w.cwv), ("CWQA", w.cwqa.toNat), ("CWQD", w.cwqd.toNat),
    ("BWP", b w.bwp), ("RPL", b d.rpl), ("RLV", d.rlv.toNat)]
  kv := kv ++ #[("DMEM.sum", sim.dsum), ("PMEM0.sum", sim.psum[0]!), ("PMEM1.sum", sim.psum[1]!)]
  let body := ", ".intercalate (kv.toList.map fun (k, v) => "\"" ++ k ++ "\": " ++ toString v)
  return "{" ++ body ++ "}"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (sim : Sim) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let t := line.trimAscii.toString
  if t == "quit" then return
  if t == "reset" then
    loop stdin stdout initSim
  else if t == "" then
    loop stdin stdout sim
  else
    match (t.splitOn " ").filter (· ≠ "") |>.map String.toNat? with
    | [some ui, some uio, some rst] =>
      let pin : PinIn := { ui := BitVec.ofNat 8 ui, uio := BitVec.ofNat 8 uio, rstn := rst != 0 }
      let (s', ws) := stepObs sim.st pin
      let sim' := { updSums sim s' ws with st := s' }
      stdout.putStrLn (dump sim')
      stdout.flush
      loop stdin stdout sim'
    | _ =>
      (← IO.getStderr).putStrLn s!"machine-sim: bad input line: {t}"
      loop stdin stdout sim

end MachineSim

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  MachineSim.loop stdin stdout MachineSim.initSim
