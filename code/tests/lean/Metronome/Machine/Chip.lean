import Metronome.Machine.CfgWrite

/-! §1 Reset and the composition of all units into one cycle: `step : State → PinIn → State`. -/

namespace Metronome.Machine

open Util Tables

/-- §6.2 / §9 A memory byte written in a cycle (observation for the state dump): `mem` 0 data RAM, 1 + c program memory of
core c; `addr` byte address. -/
structure MemWrite where
  mem : Nat
  addr : Nat
deriving Repr, Inhabited

/-- §1 Reset. `rst_n` is asserted asynchronously and released synchronously through two flops: `rst_q` is low in any
cycle with `rst_n` low (-- AMBIG(1)) and otherwise is `rst_n` delayed by two rising edges. While `rst_q` is low every
register is 0; configuration clears while `rst_n` is low; memories are not cleared. -/
def resetStep (s : State) (pin : PinIn) : State :=
  let cfg := if pin.rstn then cfgNext s.cfg s.cw else Config.zero
  { State.init with
    r1 := pin.rstn, rq := s.r1 && pin.rstn, rqh := bv 2 ((s.rqh.toNat % 2) * 2),
    cfg := cfg, pmem := s.pmem, dmem := s.dmem, ramOut := s.ramOut }

/-- §1 – §13 One clock cycle with `rst_q` high: every combinational quantity of cycle t from cycle-t registers,
configuration and the synchronised pins, then the next state (two-phase cycle semantics, §1). Host writes take
priority over moves and hardware updates of the same state except where a section says otherwise (§9). Also
returns the memory bytes written in the cycle. -/
def runStep (s : State) (pin : PinIn) : State × List MemWrite :=
  let frozen := s.dbg.frz
  let cv := cfgView s.cfg
  let p := pinView s.sync s.dbg
  -- lines (§3)
  let lcs : Vector LineComb 4 := Vector.ofFn fun l => lineComb cv.lines[l] s.lines[l] p frozen
  -- cores and moves (§5, §6)
  let cbs : Vector CoreComb 2 := Vector.ofFn fun c => coreComb s cv p c.val frozen
  let allMoves := cbs[0].moves ++ cbs[1].moves
  let (ws, conflict) := resolveMoves allMoves
  let hostInRead := allMoves.any fun m => match srcOp m.src with
    | .hostIn => true
    | _ => false
  let pdHaz := !s.p0.rdy && allMoves.any fun m => match srcOp m.src with
    | .pD => true
    | _ => false
  -- data RAM arbiter (§6.2)
  let modes : Vector Nat 2 := Vector.ofFn fun k => streamMode cv.streams[k] k.val s.dbg
  let sreq (k : Fin 2) := streamReq modes[k] s.streams[k]
  let reqs := [sreq 0, sreq 1, p0Req s.p0, hostReq s.host]
  let served := arbiter (sreq 0) (sreq 1) (p0Req s.p0) (hostReq s.host) frozen
  let req := if served == 0 then RamReq.none else reqs.getD (served - 1) .none
  let (dmem', ramOut', dw) := ramAccess s.dmem s.ramOut.toNat req
  let (owner', lane') := match req with
    | .rd _ l => (served, l)
    | _ => (0, 0)
  -- host link (§9)
  let (host', hw) := hostNext s cv p (served == 4)
  let hwIsCfg := match hw with
    | some w => Config.isCfgAddr w.addr
    | none => false
  -- lines next
  let lines' : Vector LineSt 4 := Vector.ofFn fun l =>
    let sym' := ws.findSome? fun m => match dstOp m.dst with
      | .lsym op => if m.line == l.val then some (⟨op, m.v⟩ : SymWrite) else none
      | _ => none
    let ctl := ws.findSome? fun m => match dstOp m.dst with
      | .lCtl k => if k == l.val then some m.v else none
      | _ => none
    let i : LineIn := {
      sym := sym', ctlMove := ctl, hPhase := hwAt hw "LRT" l.val "PHASE",
      hCtl := hwByte hw "LRT" l.val "CTL",
      hTapmissClr := nbit ((hwByte hw "LRT" l.val "STAT").getD 0) 0 }
    lineNext cv.lines[l] s.lines[l] lcs[l] p i frozen
  -- threads next (§4)
  let threads' : Vector ThreadSt 6 := Vector.ofFn fun t =>
    let tc := cv.threads[t]
    let ts := s.threads[t]
    let trig := !frozen && ts.en && (trigEvent s cv p lcs t.val || bit s.ctrl.db t.val)
    let late := allMoves.any fun m => m.thread == t.val && !m.armed && match dstOp m.dst with
      | .lsym _ => true
      | _ => false
    let stop := ws.any fun m => m.thread == t.val && match dstOp m.dst with
      | .stop => true
      | _ => false
    let disp := (List.range 2).any fun c => (vget cbs c).disp && (vget cbs c).dispThread == t.val
    let pause := (List.range 2).findSome? fun c =>
      if (vget cbs c).pse && (vget s.cores c).xt.toNat == t.val then some (vget cbs c).npc else none
    threadNext ts {
      trig := trig, beat := (vget lcs tc.line).beat, late := late, stop := stop, dispatch := disp, pause := pause,
      hPC := hwByte hw "TRT" t.val "PC", hStat := hwByte hw "TRT" t.val "STAT" }
  -- cores next (§5); program memory host write (§9, 9a.8)
  let pw : Option (Nat × Nat × Nat) := match hw with
    | some w => if w.addr < DATA_BASE then some (w.addr / STRIDE_PROG_CORE, w.addr % STRIDE_PROG_CORE, w.v) else none
    | none => none
  let cores' : Vector CoreSt 2 := Vector.ofFn fun c =>
    let cb := cbs[c]
    -- AMBIG(3) a fetch in a cycle with a host write to the same core reads the contents before the write
    let word := cb.fetch.map fun a => progWord s.pmem[c] a
    coreNext s.cores[c] cv cb word frozen
  let pmem' : Vector ByteArray 2 := match pw with
    | some (c, a, v) => vset s.pmem c (bset (vget s.pmem c) a v)
    | none => s.pmem
  -- units (§6.1)
  let ui : UnitsIn := {
    flag := ws.findSome? fun m => match dstOp m.dst with
      | .fset => some (true, m.v)
      | .fclr => some (false, m.v)
      | _ => none
    acc := ws.findSome? fun m => match dstOp m.dst with
      | .acc op => some (op, m.v)
      | _ => none
    reg := Vector.ofFn fun k => ws.findSome? fun m => match dstOp m.dst with
      | .reg j => if j == k.val then some m.v else none
      | _ => none
    sh := Vector.ofFn fun k => ws.findSome? fun m => match dstOp m.dst with
      | .shLd j => if j == k.val then some (true, m.v) else none
      | .shSh j => if j == k.val then some (false, m.v) else none
      | _ => none
    shCfg := Vector.ofFn fun k => ws.findSome? fun m => match dstOp m.dst with
      | .shCfg j => if j == k.val then some m.v else none
      | _ => none
    cnt := Vector.ofFn fun k => ws.findSome? fun m => match dstOp m.dst with
      | .cntLo j => if j == k.val then some (0, m.v) else none
      | .cntHi j => if j == k.val then some (1, m.v) else none
      | .cntDec j => if j == k.val then some (2, m.v) else none
      | _ => none
    lf := Vector.ofFn fun k => ws.findSome? fun m => match dstOp m.dst with
      | .lfSt j => if j == k.val then some (none, m.v) else none
      | .lfB j b => if j == k.val then some (some b, m.v) else none
      | _ => none }
  let units' := unitsNext s.cfg s.units ui frozen
  -- pointer (§6.1, §6.2)
  let pmv : Option P0Move := ws.findSome? fun m => match dstOp m.dst with
    | .pAl => some ⟨0, m.v⟩
    | .pAh => some ⟨1, m.v⟩
    | .pW => some ⟨2, m.v⟩
    | .pR => some ⟨3, m.v⟩
    | _ => none
  let (p0', p0haz) := p0Next s.p0 pmv (served == 3) (s.ramOwner == 3) s.ramOut.toNat s.ramLane.toNat frozen
  -- streams (§6.3, §12.4, §13.2)
  let (cev, record) := captureEvent s.dbg p frozen
  let (apply, late) := replayApply s.dbg s.streams[0] frozen
  let streams' : Vector StreamSt 2 := Vector.ofFn fun k =>
    let sel (f : DstOp → Option Nat) := ws.findSome? fun m => f (dstOp m.dst) |>.map fun _ => m.v
    let i : StreamIn := {
      adv := (sel fun d => match d with
        | .sAdv j => if j == k.val then some 0 else none
        | _ => none).isSome
      rx := sel fun d => match d with
        | .sRx j => if j == k.val then some 0 else none
        | _ => none
      ctlMove := sel fun d => match d with
        | .sCtl j => if j == k.val then some 0 else none
        | _ => none
      hCtl := hwByte hw "SRT" k.val "CTL", served := served == k.val + 1,
      landNow := s.ramOwner == k.val + 1, ramOut := s.ramOut.toNat,
      cev := k.val == 0 && cev, record, apply := k.val == 0 && apply, late := k.val == 0 && late }
    streamNext cv.streams[k] modes[k] s.streams[k] i frozen
  -- configuration writes (§13.1, §1)
  let cwm : Option CwMove := ws.findSome? fun m => match dstOp m.dst with
    | .cwAl => some ⟨0, m.v⟩
    | .cwAh => some ⟨1, m.v⟩
    | .cwD => some ⟨2, m.v⟩
    | _ => none
  -- AMBIG(2) "the two cycles after rst_q rises" = the first two cycles with rst_q high
  let window := !(bit s.rqh 0 && bit s.rqh 1)
  let hostCfg := if hwIsCfg then hw.map fun w => (w.addr, w.v) else none
  let cwo := cwNext s.cw hostCfg cwm window frozen
  -- control, debug, outputs (§9, §12)
  let hostOut := ws.findSome? fun m => match dstOp m.dst with
    | .hostOut => some m.v
    | _ => none
  let ctrl' := ctrlNext s hw { hostOut, hostInRead, conflict, memhaz := pdHaz || p0haz, cwovr := cwo.ovr } frozen
  let dbg' := dbgNext s hw cwo.rt cev apply frozen
  let (out', oen') := outNext s cv p frozen
  let mw := dw.map (⟨0, ·⟩) ++ (match pw with
    | some (c, a, _) => [⟨1 + c, a⟩]
    | none => [])
  ({ r1 := pin.rstn, rq := s.r1 && pin.rstn, rqh := bv 2 ((s.rqh.toNat % 2) * 2 + 1),
     sync := syncNext s.sync pin, lines := lines', threads := threads', cores := cores', units := units',
     p0 := p0', streams := streams', host := host', ctrl := ctrl', dbg := dbg', cw := cwo.st,
     out := out', oen := oen', cfg := cfgNext s.cfg s.cw, pmem := pmem', dmem := dmem',
     ramOut := bv 32 ramOut', ramOwner := owner', ramLane := bv 2 lane' }, mw)

/-- §1 One clock cycle at the pin boundary, with the memory bytes written (for observation). -/
def stepObs (s : State) (pin : PinIn) : State × List MemWrite :=
  if s.rq && pin.rstn then runStep s pin else (resetStep s pin, [])

/-- §1 The machine: one clock cycle, `State → PinIn → State`. -/
def step (s : State) (pin : PinIn) : State := (stepObs s pin).1

end Metronome.Machine
