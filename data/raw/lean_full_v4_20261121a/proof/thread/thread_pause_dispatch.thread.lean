import Metronome.Thread
import Metronome.HostMap

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 3331242e400c5fe4e83ee1e1153cc17903ffbe349871b8252ab9886384036053
-- Module: the elaborated `md2_thread` instance shared by
-- `tt_um_brentius_metronome.g_thr[0..5].u`.  Every register is sampled; `rst_n` is a synchroniser
-- input of the cut, so the reset branch is part of the extracted transition.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Metronome.Thread

/-- The elaborated thread transition.  `state` is the cycle's register value and
`input` the sampled cycle inputs. -/
def rtlStep (state : State) (input : Input) : State :=
  let thread0 := if input.pause then input.npc else state.pc
  let thread1 := if input.hPcWe then input.hD else thread0
  let thread2 := if input.resetN then thread1 else (0 : BitVec 8)
  let thread3 := (if input.stop then false else state.en)
  let thread4 := (if input.hStatWe then ((BitVec.truncate 1 (BitVec.ushiftRight input.hD 3)) != 0) else thread3)
  let thread5 := (if input.resetN then thread4 else false)
  let thread6 := input.ev || input.db
  let thread7 := state.en && thread6
  let thread8 := state.ready || state.running
  let thread9 := !thread8
  let thread10 := thread7 && thread9
  let thread11 := (if thread10 then true else state.ready)
  let thread12 := (if input.disp then false else thread11)
  let thread13 := (if input.resetN then thread12 else false)
  let thread14 := (if input.pause then false else state.running)
  let thread15 := (if input.disp then true else thread14)
  let thread16 := (if input.resetN then thread15 else false)
  let thread17 := (if input.lineBeat then false else state.armed)
  let thread18 := (if thread10 then true else thread17)
  let thread19 := (if input.resetN then thread18 else false)
  let thread20 := input.hStatWe && ((BitVec.truncate 1 (BitVec.ushiftRight input.hD 4)) != 0)
  let thread21 := !thread20
  let thread22 := state.late && thread21
  let thread23 := input.lateSet || thread22
  let thread24 := (if input.resetN then thread23 else false)
  let thread25 := thread7 && thread8
  let thread26 := input.hStatWe && ((BitVec.truncate 1 (BitVec.ushiftRight input.hD 5)) != 0)
  let thread27 := !thread26
  let thread28 := state.ovr && thread27
  let thread29 := thread25 || thread28
  let thread30 := (if input.resetN then thread29 else false)
  ⟨thread2, thread5, thread13, thread16,
   thread19, thread24, thread30⟩

end Metronome.Thread

namespace Metronome.Thread

/-! ## The documented resolutions, on the extracted transition

SPEC_V2 section 4 gives the two priorities it states (a host `PC` write over a
pause, a host `EN` write over `T.STOP`) and leaves two implicit: dispatch over a
same-cycle accepted trigger for `READY`, and pause over dispatch for `RUNNING`
and `PC`.  Section 5 makes the last two address different threads in a legal
state, so only a free-input cut sees their order.  `step` states the RTL's
order; the equalities below transfer that to the extracted transition, so a
mutant that swaps either priority fails in `rtlStep_eq_step`.
-/

/-! ## The extracted transition is the specification

`thread_check.py` generated `rtlStep` above from the elaborated `md2_thread`
module.  The proof below destructures the state and the sampled inputs so that
every leaf is a plain `BitVec`/`Bool` value, then proves the seven register
equations of `Metronome.Thread.step` (SPEC_V2 sections 4, 5, 9 and 12.3) with one
`bv_decide` per field.  The two documented resolutions (dispatch over an accepted
trigger for `READY`, pause over dispatch for `RUNNING`) are part of `step`, so
the theorem is what makes them the RTL's behaviour.
-/

theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  obtain ⟨pc, en, ready, running, armed, late, ovr⟩ := state
  obtain ⟨resetN, ev, db, disp, pause, npc, stop, lateSet, lineBeat, hPcWe,
    hStatWe, hD⟩ := input
  cases resetN
  · simp [rtlStep, step, resetState]
  · simp only [rtlStep, step]
    ext <;>
      simp only [pcNext, enNext, readyNext, runningNext, armedNext, lateNext,
        ovrNext, accept, trig, busy, overrunEvent, statEn, statClearLate,
        statClearOvr, bitAt]
    all_goals bv_decide

/-! ## Trace lifting -/

/-- The extracted thread trace: `rtlStep` from the same sampled inputs. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

/-- The extracted trace equals the specification trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-- `READY` and `RUNNING` stay exclusive on the extracted trace. -/
theorem rtl_trace_exclusive (inputs : Nat → Input) (n : Nat) :
    Exclusive (rtlStateAt inputs resetState n) := by
  rw [rtlStateAt_eq]
  exact trace_exclusive inputs n

/-- A trigger while busy on the extracted trace sets the sticky `OVR`. -/
theorem rtl_trace_ovr_of_busy_trigger (inputs : Nat → Input) (n : Nat)
    (hr : (inputs n).resetN = true)
    (h : overrunEvent (rtlStateAt inputs resetState n) (inputs n) = true) :
    (rtlStateAt inputs resetState (n + 1)).ovr = true := by
  rw [rtlStateAt_eq] at h ⊢
  exact trace_ovr_of_busy_trigger inputs n hr h

/-- A dispatch on the extracted trace leaves the thread running unless it also
pauses in that cycle. -/
theorem rtl_trace_dispatch_running (inputs : Nat → Input) (n : Nat)
    (hr : (inputs n).resetN = true) (h : (inputs n).disp = true)
    (hp : (inputs n).pause = false) :
    (rtlStateAt inputs resetState (n + 1)).running = true := by
  rw [rtlStateAt_eq]
  exact trace_dispatch_running inputs n hr h hp

/-- A pause beats a same-cycle dispatch for `RUNNING` on the extracted
transition. -/
theorem rtlRunning_pause_dispatch (state : State) (input : Input)
    (hr : input.resetN = true) (hp : input.pause = true) (hd : input.disp = true) :
    (rtlStep state input).running = false := by
  rw [rtlStep_eq_step]
  exact pause_clears_running state input hr hp

/-- A host write of `PC` beats a same-cycle pause on the extracted transition
(SPEC_V2 section 4). -/
theorem rtlPc_host_beats_pause (state : State) (input : Input)
    (hr : input.resetN = true) (hh : input.hPcWe = true) (hp : input.pause = true) :
    (rtlStep state input).pc = input.hD := by
  rw [rtlStep_eq_step]
  exact host_pc_beats_pause state input hr hh

/-- A trigger while busy beats a same-cycle host `STAT` clear of `OVR` on the
extracted transition (SPEC_V2 sections 4 and 9). -/
theorem rtlOvr_set_beats_clear (state : State) (input : Input)
    (hr : input.resetN = true) (h : overrunEvent state input = true)
    (hc : statClearOvr input = true) : (rtlStep state input).ovr = true := by
  rw [rtlStep_eq_step]
  exact ovr_set_beats_clear state input hr h hc

/-- A host `STAT` write of `EN` beats a same-cycle `T.STOP` on the extracted
transition (SPEC_V2 section 4). -/
theorem rtlEn_host_beats_stop (state : State) (input : Input)
    (hr : input.resetN = true) (hs : input.hStatWe = true) (hst : input.stop = true) :
    (rtlStep state input).en = statEn input := by
  rw [rtlStep_eq_step]
  exact host_en_beats_stop state input hr hs

/-- An accepted trigger beats a same-cycle line `BEAT` for `ARMED` on the
extracted transition (SPEC_V2 section 4). -/
theorem rtlArmed_accept_beats_beat (state : State) (input : Input)
    (hr : input.resetN = true) (ha : accept state input = true)
    (hb : input.lineBeat = true) : (rtlStep state input).armed = true := by
  rw [rtlStep_eq_step]
  exact accept_sets_armed state input hr ha

-- `thread_check.py` parses these records and rejects `sorryAx`.
#print axioms rtlRunning_pause_dispatch
#print axioms rtlPc_host_beats_pause
#print axioms rtlOvr_set_beats_clear
#print axioms rtlStep_eq_step
#print axioms rtlStateAt_eq
#print axioms rtl_trace_result
#print axioms rtl_trace_exclusive

end Metronome.Thread

namespace Metronome.Thread.Top

-- The generated `src/md2_defs.vh` and `src/md2_map.vh` constants the statements
-- below are written with.  `thread_check.py` reads them from the headers and
-- rejects a value that is not the documented one.
abbrev TRIG_PINA_RISE : BitVec 5 := 25
abbrev TRIG_PINA_FALL : BitVec 5 := 26
abbrev TRIG_PINA_EDGE : BitVec 5 := 27
abbrev TRIG_ALWAYS : BitVec 5 := 29
abbrev DG_L_SYM : BitVec 5 := 0
abbrev DG_T_STOP : BitVec 5 := 1
abbrev HA_TRT_BASE : BitVec 16 := 9280
abbrev HSPAN_TRT : BitVec 16 := 12

/-! ## The chip-top leaves

Every net below is upstream of a `g_thr[k].u` input and is bound free for the
cycle: `frz` is the SPEC 12.3 freeze register, the event sources are outputs of
the lines and the flag registers, the move bus is the picked move of each core,
and the host side is `h_wr`/`ha`/`h_wd` of the host link.  The theorems below
prove each instance's input cone is the SPEC quantity of these leaves, so the
elaborated chip top is the specification *when* the leaves are what SPEC_V2
says they are.
-/

structure Leaves where
  /-- `FRZ` of SPEC 12.3 (this cycle is frozen). -/
  frz : Bool
  /-- `l_beat`: the four lines' `BEAT` (SPEC 3.2). -/
  beat : BitVec 4
  /-- `l_tap`: the four lines' three tap-fired bits (SPEC 3.4). -/
  tap : BitVec 12
  /-- `F[15:0]`, the flags (SPEC 6.1). -/
  flag : BitVec 16
  /-- `FP`, the flags of the previous cycle. -/
  flagPrev : BitVec 16
  /-- `INV`, the mailbox-valid flag (SPEC 9). -/
  inv : Bool
  /-- `INVP`, `INV` of the previous cycle. -/
  invPrev : Bool
  /-- `l_parise`: per line, a rise of the bound `PINA` pin (SPEC 3.4). -/
  parise : BitVec 4
  /-- `l_pafall`: per line, a fall of the bound `PINA` pin. -/
  pafall : BitVec 4
  /-- `t_ready`: the six threads' `READY`. -/
  ready : BitVec 6
  /-- `t_running`: the six threads' `RUNNING`. -/
  running : BitVec 6
  /-- `t_armed`: the six threads' `ARMED`. -/
  armed : BitVec 6
  /-- `db`: the doorbell pulse register (SPEC 9). -/
  doorbell : BitVec 6
  /-- `dsp`: each core's dispatch strobe (SPEC 5). -/
  dispatchCore : BitVec 2
  /-- `disp_e`: each core's selected thread to dispatch (SPEC 5). -/
  dispatchThread : BitVec 6
  /-- `pse`: each core's pause strobe (SPEC 5). -/
  pauseCore : BitVec 2
  /-- `xt`: each core's executing thread (SPEC 5). -/
  execThread : BitVec 6
  /-- `npc`: each core's next-PC byte, core 0 low, core 1 high (SPEC 5). -/
  nextPc : BitVec 16
  /-- `grp_v`: the picked move's destination group per move (SPEC 6). -/
  groups : BitVec 30
  /-- `mv_valid`: the six moves' enable bits (SPEC 5/6). -/
  valid : BitVec 6
  /-- `w_trt`: the host write strobe into the thread block (SPEC 9). -/
  hostWrite : Bool
  /-- `ha`: the host address (SPEC 9). -/
  hostAddr : BitVec 16
  /-- `h_wd`: the host write data byte (SPEC 9). -/
  hostData : BitVec 8
  deriving DecidableEq, Repr

/-- The thread's `LINE` field `tc[2:1]` (SPEC 4 configuration). -/
def ln (tc : BitVec 8) : BitVec 2 := (tc >>> 1).truncate 2

/-- The thread's `TRIG` field `tc[7:3]` (SPEC 4 configuration). -/
def ts (tc : BitVec 8) : BitVec 5 := (tc >>> 3).truncate 5

/-- The three-bit field at `i` of a six-bit core vector. -/
def blk (x : BitVec 6) (i : Nat) : BitVec 3 := (x >>> i).truncate 3

/-- Move `j`'s destination group, `grp_v[5j +: 5]` (SPEC 6). -/
def grp (L : Leaves) (j : Nat) : BitVec 5 := (L.groups >>> (5 * j)).truncate 5

/-- `FLAGk.RISE = F[k] && !FP[k]` (SPEC 4). -/
def flagRise (L : Leaves) (i : Nat) : Bool :=
  bitAt L.flag i && !bitAt L.flagPrev i

/-- `v[i]` through a two-bit index, the shape of `l_parise[ln]`. -/
def mux4 (v : BitVec 4) (i : BitVec 2) : Bool :=
  (i == 0 && bitAt v 0) || (i == 1 && bitAt v 1) ||
    (i == 2 && bitAt v 2) || (i == 3 && bitAt v 3)

/-- The event table of SPEC_V2 section 4, as codes from `md2_defs.vh` /
`machine.json`: `Lg.BEAT`, `Lg.TAPk`, `FLAGk.RISE` and `HOST.INV`.  `NONE` (0),
the three `PINA` codes (handled by the thread's line) and `ALWAYS` (29) have no
entry here, and codes 30 and 31 are past the table, so they never fire. -/
def evTable (L : Leaves) (c : BitVec 5) : Bool :=
  (c == 1 && bitAt L.beat 0) ||
  (c == 2 && bitAt L.tap 0) ||
  (c == 3 && bitAt L.tap 1) ||
  (c == 4 && bitAt L.tap 2) ||
  (c == 5 && bitAt L.beat 1) ||
  (c == 6 && bitAt L.tap 3) ||
  (c == 7 && bitAt L.tap 4) ||
  (c == 8 && bitAt L.tap 5) ||
  (c == 9 && bitAt L.beat 2) ||
  (c == 10 && bitAt L.tap 6) ||
  (c == 11 && bitAt L.tap 7) ||
  (c == 12 && bitAt L.tap 8) ||
  (c == 13 && bitAt L.beat 3) ||
  (c == 14 && bitAt L.tap 9) ||
  (c == 15 && bitAt L.tap 10) ||
  (c == 16 && bitAt L.tap 11) ||
  (c == 17 && flagRise L 0) ||
  (c == 18 && flagRise L 1) ||
  (c == 19 && flagRise L 2) ||
  (c == 20 && flagRise L 3) ||
  (c == 21 && flagRise L 4) ||
  (c == 22 && flagRise L 5) ||
  (c == 23 && flagRise L 6) ||
  (c == 24 && flagRise L 7) ||
  (c == 28 && (L.inv && !L.invPrev))

/-- `event(TRIG)` of SPEC_V2 section 4: the code table plus the thread's own
line's pin edges plus `ALWAYS = !READY && !RUNNING`.  `NONE` never fires, so it
has no term. -/
def evRaw (L : Leaves) (tc : BitVec 8) (ready running : Bool) : Bool :=
  evTable L (ts tc) ||
    ((ts tc == TRIG_PINA_RISE) && mux4 L.parise (ln tc)) ||
    ((ts tc == TRIG_PINA_FALL) && mux4 L.pafall (ln tc)) ||
    ((ts tc == TRIG_PINA_EDGE) && (mux4 L.parise (ln tc) || mux4 L.pafall (ln tc))) ||
    ((ts tc == TRIG_ALWAYS) && !ready && !running)

/-- An enabled move to `T.STOP`: a move `j` is the thread's own when its core
executes this thread (`c0` for core 0's three moves, `c1` for core 1's), it is
valid, and its destination group is `DG_T_STOP` (SPEC_V2 sections 4 and 6). -/
def stopSpec (L : Leaves) (c0 c1 : Bool) : Bool :=
  (c0 && bitAt L.valid 0 && grp L 0 == DG_T_STOP) ||
  (c0 && bitAt L.valid 1 && grp L 1 == DG_T_STOP) ||
  (c0 && bitAt L.valid 2 && grp L 2 == DG_T_STOP) ||
  (c1 && bitAt L.valid 3 && grp L 3 == DG_T_STOP) ||
  (c1 && bitAt L.valid 4 && grp L 4 == DG_T_STOP) ||
  (c1 && bitAt L.valid 5 && grp L 5 == DG_T_STOP)

/-- An enabled symbol move (`L.SYM`, `L.DBIT` or `L.XOR`, one destination group)
by this thread while `ARMED = 0` sets `LATE` (SPEC_V2 section 4). -/
def lateSpec (L : Leaves) (c0 c1 armed : Bool) : Bool :=
  ((c0 && bitAt L.valid 0 && grp L 0 == DG_L_SYM) ||
   (c0 && bitAt L.valid 1 && grp L 1 == DG_L_SYM) ||
   (c0 && bitAt L.valid 2 && grp L 2 == DG_L_SYM) ||
   (c1 && bitAt L.valid 3 && grp L 3 == DG_L_SYM) ||
   (c1 && bitAt L.valid 4 && grp L 4 == DG_L_SYM) ||
   (c1 && bitAt L.valid 5 && grp L 5 == DG_L_SYM)) && !armed

/-- The `npc` byte the pausing core presents: core 1's high byte when core 1 is
the one pausing this thread, core 0's low byte otherwise (SPEC_V2 section 5). -/
def selectedPc (L : Leaves) (core1 : Bool) : BitVec 8 :=
  if core1 then (L.nextPc >>> 8).truncate 8 else L.nextPc.truncate 8

/-- `HA_TRT_BASE`: the base of the thread runtime block (SPEC_V2 section 9). -/
def hostBase : BitVec 16 := HA_TRT_BASE

/-- `HSPAN_TRT`: the size of the thread runtime block. -/
def hostSpan : BitVec 16 := HSPAN_TRT

/-- `a_trt >> TRT_SH`: the thread instance index of a host address (SPEC 9). -/
def threadIndex (a : BitVec 16) : BitVec 16 := (a - hostBase) >>> 1

/-- `{16'd0, a_trt} & (HS_TRT - 1)`: the byte offset inside the thread block. -/
def threadOffset (a : BitVec 16) : BitVec 32 := (a - hostBase).setWidth 32 &&& 1

/-- The thread `PC` write enable: `w_trt & i_trt == k & o_trt == HO_TRT_PC`. -/
def hostPcWe (k : Nat) (hw : Bool) (a : BitVec 16) : Bool :=
  hw && (a - hostBase < hostSpan) && (threadIndex a == (k : BitVec 16)) &&
    (threadOffset a == 0)

/-- The thread `STAT` write enable: `w_trt & i_trt == k & o_trt == HO_TRT_STAT`. -/
def hostStatWe (k : Nat) (hw : Bool) (a : BitVec 16) : Bool :=
  hw && (a - hostBase < hostSpan) && (threadIndex a == (k : BitVec 16)) &&
    (threadOffset a == 1)
-- Chip top: `tt_um_brentius_metronome.g_thr[k].u` for k = 0..5 (SPEC_V2 4, 5, 9, 12.3).
-- Upstream nets are free per-cycle leaves (`Leaves`); the generated theorems
-- state each extracted cone in terms of them.

/-! ### Instance 0 -/

/-- The extracted `ev` input of `g_thr[0].u`. -/
def rtlEv0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th0Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th0Ev0
  let th0Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th0Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th0Ev2
  let th0Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th0Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th0Ev4
  let th0Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th0Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th0Ev6
  let th0Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th0Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th0Ev8
  let th0Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th0Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th0Ev10
  let th0Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th0Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th0Ev12
  let th0Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th0Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th0Ev14
  let th0Ev16 := !(L.invPrev)
  let th0Ev17 := (L.inv) && th0Ev16
  let th0Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th0Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th0Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th0Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th0Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th0Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th0Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th0Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th0Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th0Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th0Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th0Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th0Ev21 := th0Ev19 && th0Ev20
  let th0Ev22 := th0Ev18 || th0Ev21
  let th0Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th0Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th0Ev25 := th0Ev23 && th0Ev24
  let th0Ev26 := th0Ev22 || th0Ev25
  let th0Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th0Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th0Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th0Ev30 := th0Ev28 || th0Ev29
  let th0Ev31 := th0Ev27 && th0Ev30
  let th0Ev32 := th0Ev26 || th0Ev31
  let th0Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th0Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 0)) != 0)
  let th0Ev35 := th0Ev33 && th0Ev34
  let th0Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 0)) != 0)
  let th0Ev37 := th0Ev35 && th0Ev36
  let th0Ev38 := th0Ev32 || th0Ev37
  let th0Ev39 := !(L.frz)
  let th0Ev40 := th0Ev38 && th0Ev39
  th0Ev40

/-- The extracted `db` input of `g_thr[0].u`. -/
def rtlDb0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Db0 := !(L.frz)
  let th0Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 0)) != 0) && th0Db0
  th0Db1

/-- The extracted `disp` input of `g_thr[0].u`. -/
def rtlDisp0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (0 : BitVec 3))
  let th0Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th0Disp0
  let th0Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (0 : BitVec 3))
  let th0Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th0Disp2
  let th0Disp4 := th0Disp1 || th0Disp3
  th0Disp4

/-- The extracted `pause` input of `g_thr[0].u`. -/
def rtlPause0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (0 : BitVec 3))
  let th0Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th0Pause0
  let th0Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (0 : BitVec 3))
  let th0Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th0Pause2
  let th0Pause4 := th0Pause1 || th0Pause3
  th0Pause4

/-- The extracted `npc` input of `g_thr[0].u`. -/
def rtlNpc0 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th0Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (0 : BitVec 3))
  let th0Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th0Npc0
  let th0Npc2 := if th0Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th0Npc2

/-- The extracted `stop` input of `g_thr[0].u`. -/
def rtlStop0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (0 : BitVec 3))
  let th0Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (0 : BitVec 3))
  let th0Stop2 := (((if th0Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th0Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th0Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th0Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th0Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th0Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th0Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th0Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th0Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th0Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th0Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th0Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th0Stop9 := (th0Stop2 &&& ((if th0Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th0Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th0Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th0Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th0Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th0Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th0Stop10 := (th0Stop9 != (0 : BitVec 6))
  th0Stop10

/-- The extracted `late_set` input of `g_thr[0].u`. -/
def rtlLate0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (0 : BitVec 3))
  let th0Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (0 : BitVec 3))
  let th0Late2 := (((if th0Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th0Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th0Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th0Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th0Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th0Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th0Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th0Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th0Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th0Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th0Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th0Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th0Late9 := (th0Late2 &&& ((if th0Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th0Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th0Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th0Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th0Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th0Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th0Late10 := (th0Late9 != (0 : BitVec 6))
  let th0Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 0)) != 0)
  let th0Late12 := th0Late10 && th0Late11
  th0Late12

/-- The extracted `line_beat` input of `g_thr[0].u`. -/
def rtlBeat0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th0Beat0

/-- The extracted `h_pc_we` input of `g_thr[0].u`. -/
def rtlPcWe0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th0PcWe1 := (th0PcWe0 < (12 : BitVec 16))
  let th0PcWe2 := (L.hostWrite) && th0PcWe1
  let th0PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (0 : BitVec 16))
  let th0PcWe4 := th0PcWe2 && th0PcWe3
  let th0PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th0PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th0PcWe6 := th0PcWe4 && th0PcWe5
  th0PcWe6

/-- The extracted `h_stat_we` input of `g_thr[0].u`. -/
def rtlStatWe0 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th0StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th0StatWe1 := (th0StatWe0 < (12 : BitVec 16))
  let th0StatWe2 := (L.hostWrite) && th0StatWe1
  let th0StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (0 : BitVec 16))
  let th0StatWe4 := th0StatWe2 && th0StatWe3
  let th0StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th0StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th0StatWe6 := th0StatWe4 && th0StatWe5
  th0StatWe6

/-! ### Instance 1 -/

/-- The extracted `ev` input of `g_thr[1].u`. -/
def rtlEv1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th1Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th1Ev0
  let th1Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th1Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th1Ev2
  let th1Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th1Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th1Ev4
  let th1Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th1Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th1Ev6
  let th1Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th1Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th1Ev8
  let th1Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th1Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th1Ev10
  let th1Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th1Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th1Ev12
  let th1Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th1Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th1Ev14
  let th1Ev16 := !(L.invPrev)
  let th1Ev17 := (L.inv) && th1Ev16
  let th1Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th1Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th1Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th1Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th1Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th1Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th1Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th1Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th1Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th1Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th1Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th1Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th1Ev21 := th1Ev19 && th1Ev20
  let th1Ev22 := th1Ev18 || th1Ev21
  let th1Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th1Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th1Ev25 := th1Ev23 && th1Ev24
  let th1Ev26 := th1Ev22 || th1Ev25
  let th1Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th1Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th1Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th1Ev30 := th1Ev28 || th1Ev29
  let th1Ev31 := th1Ev27 && th1Ev30
  let th1Ev32 := th1Ev26 || th1Ev31
  let th1Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th1Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 1)) != 0)
  let th1Ev35 := th1Ev33 && th1Ev34
  let th1Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 1)) != 0)
  let th1Ev37 := th1Ev35 && th1Ev36
  let th1Ev38 := th1Ev32 || th1Ev37
  let th1Ev39 := !(L.frz)
  let th1Ev40 := th1Ev38 && th1Ev39
  th1Ev40

/-- The extracted `db` input of `g_thr[1].u`. -/
def rtlDb1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Db0 := !(L.frz)
  let th1Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 1)) != 0) && th1Db0
  th1Db1

/-- The extracted `disp` input of `g_thr[1].u`. -/
def rtlDisp1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (1 : BitVec 3))
  let th1Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th1Disp0
  let th1Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (1 : BitVec 3))
  let th1Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th1Disp2
  let th1Disp4 := th1Disp1 || th1Disp3
  th1Disp4

/-- The extracted `pause` input of `g_thr[1].u`. -/
def rtlPause1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (1 : BitVec 3))
  let th1Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th1Pause0
  let th1Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (1 : BitVec 3))
  let th1Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th1Pause2
  let th1Pause4 := th1Pause1 || th1Pause3
  th1Pause4

/-- The extracted `npc` input of `g_thr[1].u`. -/
def rtlNpc1 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th1Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (1 : BitVec 3))
  let th1Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th1Npc0
  let th1Npc2 := if th1Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th1Npc2

/-- The extracted `stop` input of `g_thr[1].u`. -/
def rtlStop1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (1 : BitVec 3))
  let th1Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (1 : BitVec 3))
  let th1Stop2 := (((if th1Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th1Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th1Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th1Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th1Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th1Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th1Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th1Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th1Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th1Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th1Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th1Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th1Stop9 := (th1Stop2 &&& ((if th1Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th1Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th1Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th1Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th1Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th1Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th1Stop10 := (th1Stop9 != (0 : BitVec 6))
  th1Stop10

/-- The extracted `late_set` input of `g_thr[1].u`. -/
def rtlLate1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (1 : BitVec 3))
  let th1Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (1 : BitVec 3))
  let th1Late2 := (((if th1Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th1Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th1Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th1Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th1Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th1Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th1Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th1Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th1Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th1Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th1Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th1Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th1Late9 := (th1Late2 &&& ((if th1Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th1Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th1Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th1Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th1Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th1Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th1Late10 := (th1Late9 != (0 : BitVec 6))
  let th1Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 1)) != 0)
  let th1Late12 := th1Late10 && th1Late11
  th1Late12

/-- The extracted `line_beat` input of `g_thr[1].u`. -/
def rtlBeat1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th1Beat0

/-- The extracted `h_pc_we` input of `g_thr[1].u`. -/
def rtlPcWe1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th1PcWe1 := (th1PcWe0 < (12 : BitVec 16))
  let th1PcWe2 := (L.hostWrite) && th1PcWe1
  let th1PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (1 : BitVec 16))
  let th1PcWe4 := th1PcWe2 && th1PcWe3
  let th1PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th1PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th1PcWe6 := th1PcWe4 && th1PcWe5
  th1PcWe6

/-- The extracted `h_stat_we` input of `g_thr[1].u`. -/
def rtlStatWe1 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th1StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th1StatWe1 := (th1StatWe0 < (12 : BitVec 16))
  let th1StatWe2 := (L.hostWrite) && th1StatWe1
  let th1StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (1 : BitVec 16))
  let th1StatWe4 := th1StatWe2 && th1StatWe3
  let th1StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th1StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th1StatWe6 := th1StatWe4 && th1StatWe5
  th1StatWe6

/-! ### Instance 2 -/

/-- The extracted `ev` input of `g_thr[2].u`. -/
def rtlEv2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th2Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th2Ev0
  let th2Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th2Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th2Ev2
  let th2Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th2Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th2Ev4
  let th2Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th2Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th2Ev6
  let th2Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th2Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th2Ev8
  let th2Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th2Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th2Ev10
  let th2Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th2Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th2Ev12
  let th2Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th2Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th2Ev14
  let th2Ev16 := !(L.invPrev)
  let th2Ev17 := (L.inv) && th2Ev16
  let th2Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th2Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th2Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th2Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th2Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th2Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th2Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th2Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th2Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th2Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th2Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th2Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th2Ev21 := th2Ev19 && th2Ev20
  let th2Ev22 := th2Ev18 || th2Ev21
  let th2Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th2Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th2Ev25 := th2Ev23 && th2Ev24
  let th2Ev26 := th2Ev22 || th2Ev25
  let th2Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th2Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th2Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th2Ev30 := th2Ev28 || th2Ev29
  let th2Ev31 := th2Ev27 && th2Ev30
  let th2Ev32 := th2Ev26 || th2Ev31
  let th2Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th2Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 2)) != 0)
  let th2Ev35 := th2Ev33 && th2Ev34
  let th2Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 2)) != 0)
  let th2Ev37 := th2Ev35 && th2Ev36
  let th2Ev38 := th2Ev32 || th2Ev37
  let th2Ev39 := !(L.frz)
  let th2Ev40 := th2Ev38 && th2Ev39
  th2Ev40

/-- The extracted `db` input of `g_thr[2].u`. -/
def rtlDb2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Db0 := !(L.frz)
  let th2Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 2)) != 0) && th2Db0
  th2Db1

/-- The extracted `disp` input of `g_thr[2].u`. -/
def rtlDisp2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (2 : BitVec 3))
  let th2Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th2Disp0
  let th2Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (2 : BitVec 3))
  let th2Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th2Disp2
  let th2Disp4 := th2Disp1 || th2Disp3
  th2Disp4

/-- The extracted `pause` input of `g_thr[2].u`. -/
def rtlPause2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (2 : BitVec 3))
  let th2Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th2Pause0
  let th2Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (2 : BitVec 3))
  let th2Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th2Pause2
  let th2Pause4 := th2Pause1 || th2Pause3
  th2Pause4

/-- The extracted `npc` input of `g_thr[2].u`. -/
def rtlNpc2 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th2Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (2 : BitVec 3))
  let th2Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th2Npc0
  let th2Npc2 := if th2Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th2Npc2

/-- The extracted `stop` input of `g_thr[2].u`. -/
def rtlStop2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (2 : BitVec 3))
  let th2Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (2 : BitVec 3))
  let th2Stop2 := (((if th2Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th2Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th2Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th2Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th2Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th2Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th2Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th2Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th2Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th2Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th2Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th2Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th2Stop9 := (th2Stop2 &&& ((if th2Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th2Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th2Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th2Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th2Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th2Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th2Stop10 := (th2Stop9 != (0 : BitVec 6))
  th2Stop10

/-- The extracted `late_set` input of `g_thr[2].u`. -/
def rtlLate2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (2 : BitVec 3))
  let th2Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (2 : BitVec 3))
  let th2Late2 := (((if th2Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th2Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th2Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th2Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th2Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th2Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th2Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th2Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th2Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th2Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th2Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th2Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th2Late9 := (th2Late2 &&& ((if th2Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th2Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th2Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th2Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th2Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th2Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th2Late10 := (th2Late9 != (0 : BitVec 6))
  let th2Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 2)) != 0)
  let th2Late12 := th2Late10 && th2Late11
  th2Late12

/-- The extracted `line_beat` input of `g_thr[2].u`. -/
def rtlBeat2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th2Beat0

/-- The extracted `h_pc_we` input of `g_thr[2].u`. -/
def rtlPcWe2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th2PcWe1 := (th2PcWe0 < (12 : BitVec 16))
  let th2PcWe2 := (L.hostWrite) && th2PcWe1
  let th2PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (2 : BitVec 16))
  let th2PcWe4 := th2PcWe2 && th2PcWe3
  let th2PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th2PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th2PcWe6 := th2PcWe4 && th2PcWe5
  th2PcWe6

/-- The extracted `h_stat_we` input of `g_thr[2].u`. -/
def rtlStatWe2 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th2StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th2StatWe1 := (th2StatWe0 < (12 : BitVec 16))
  let th2StatWe2 := (L.hostWrite) && th2StatWe1
  let th2StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (2 : BitVec 16))
  let th2StatWe4 := th2StatWe2 && th2StatWe3
  let th2StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th2StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th2StatWe6 := th2StatWe4 && th2StatWe5
  th2StatWe6

/-! ### Instance 3 -/

/-- The extracted `ev` input of `g_thr[3].u`. -/
def rtlEv3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th3Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th3Ev0
  let th3Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th3Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th3Ev2
  let th3Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th3Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th3Ev4
  let th3Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th3Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th3Ev6
  let th3Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th3Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th3Ev8
  let th3Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th3Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th3Ev10
  let th3Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th3Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th3Ev12
  let th3Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th3Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th3Ev14
  let th3Ev16 := !(L.invPrev)
  let th3Ev17 := (L.inv) && th3Ev16
  let th3Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th3Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th3Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th3Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th3Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th3Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th3Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th3Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th3Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th3Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th3Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th3Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th3Ev21 := th3Ev19 && th3Ev20
  let th3Ev22 := th3Ev18 || th3Ev21
  let th3Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th3Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th3Ev25 := th3Ev23 && th3Ev24
  let th3Ev26 := th3Ev22 || th3Ev25
  let th3Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th3Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th3Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th3Ev30 := th3Ev28 || th3Ev29
  let th3Ev31 := th3Ev27 && th3Ev30
  let th3Ev32 := th3Ev26 || th3Ev31
  let th3Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th3Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 3)) != 0)
  let th3Ev35 := th3Ev33 && th3Ev34
  let th3Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 3)) != 0)
  let th3Ev37 := th3Ev35 && th3Ev36
  let th3Ev38 := th3Ev32 || th3Ev37
  let th3Ev39 := !(L.frz)
  let th3Ev40 := th3Ev38 && th3Ev39
  th3Ev40

/-- The extracted `db` input of `g_thr[3].u`. -/
def rtlDb3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Db0 := !(L.frz)
  let th3Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 3)) != 0) && th3Db0
  th3Db1

/-- The extracted `disp` input of `g_thr[3].u`. -/
def rtlDisp3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (3 : BitVec 3))
  let th3Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th3Disp0
  let th3Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (3 : BitVec 3))
  let th3Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th3Disp2
  let th3Disp4 := th3Disp1 || th3Disp3
  th3Disp4

/-- The extracted `pause` input of `g_thr[3].u`. -/
def rtlPause3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (3 : BitVec 3))
  let th3Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th3Pause0
  let th3Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (3 : BitVec 3))
  let th3Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th3Pause2
  let th3Pause4 := th3Pause1 || th3Pause3
  th3Pause4

/-- The extracted `npc` input of `g_thr[3].u`. -/
def rtlNpc3 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th3Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (3 : BitVec 3))
  let th3Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th3Npc0
  let th3Npc2 := if th3Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th3Npc2

/-- The extracted `stop` input of `g_thr[3].u`. -/
def rtlStop3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (3 : BitVec 3))
  let th3Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (3 : BitVec 3))
  let th3Stop2 := (((if th3Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th3Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th3Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th3Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th3Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th3Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th3Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th3Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th3Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th3Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th3Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th3Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th3Stop9 := (th3Stop2 &&& ((if th3Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th3Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th3Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th3Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th3Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th3Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th3Stop10 := (th3Stop9 != (0 : BitVec 6))
  th3Stop10

/-- The extracted `late_set` input of `g_thr[3].u`. -/
def rtlLate3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (3 : BitVec 3))
  let th3Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (3 : BitVec 3))
  let th3Late2 := (((if th3Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th3Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th3Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th3Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th3Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th3Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th3Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th3Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th3Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th3Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th3Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th3Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th3Late9 := (th3Late2 &&& ((if th3Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th3Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th3Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th3Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th3Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th3Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th3Late10 := (th3Late9 != (0 : BitVec 6))
  let th3Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 3)) != 0)
  let th3Late12 := th3Late10 && th3Late11
  th3Late12

/-- The extracted `line_beat` input of `g_thr[3].u`. -/
def rtlBeat3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th3Beat0

/-- The extracted `h_pc_we` input of `g_thr[3].u`. -/
def rtlPcWe3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th3PcWe1 := (th3PcWe0 < (12 : BitVec 16))
  let th3PcWe2 := (L.hostWrite) && th3PcWe1
  let th3PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (3 : BitVec 16))
  let th3PcWe4 := th3PcWe2 && th3PcWe3
  let th3PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th3PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th3PcWe6 := th3PcWe4 && th3PcWe5
  th3PcWe6

/-- The extracted `h_stat_we` input of `g_thr[3].u`. -/
def rtlStatWe3 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th3StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th3StatWe1 := (th3StatWe0 < (12 : BitVec 16))
  let th3StatWe2 := (L.hostWrite) && th3StatWe1
  let th3StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (3 : BitVec 16))
  let th3StatWe4 := th3StatWe2 && th3StatWe3
  let th3StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th3StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th3StatWe6 := th3StatWe4 && th3StatWe5
  th3StatWe6

/-! ### Instance 4 -/

/-- The extracted `ev` input of `g_thr[4].u`. -/
def rtlEv4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th4Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th4Ev0
  let th4Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th4Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th4Ev2
  let th4Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th4Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th4Ev4
  let th4Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th4Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th4Ev6
  let th4Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th4Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th4Ev8
  let th4Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th4Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th4Ev10
  let th4Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th4Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th4Ev12
  let th4Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th4Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th4Ev14
  let th4Ev16 := !(L.invPrev)
  let th4Ev17 := (L.inv) && th4Ev16
  let th4Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th4Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th4Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th4Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th4Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th4Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th4Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th4Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th4Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th4Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th4Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th4Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th4Ev21 := th4Ev19 && th4Ev20
  let th4Ev22 := th4Ev18 || th4Ev21
  let th4Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th4Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th4Ev25 := th4Ev23 && th4Ev24
  let th4Ev26 := th4Ev22 || th4Ev25
  let th4Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th4Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th4Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th4Ev30 := th4Ev28 || th4Ev29
  let th4Ev31 := th4Ev27 && th4Ev30
  let th4Ev32 := th4Ev26 || th4Ev31
  let th4Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th4Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 4)) != 0)
  let th4Ev35 := th4Ev33 && th4Ev34
  let th4Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 4)) != 0)
  let th4Ev37 := th4Ev35 && th4Ev36
  let th4Ev38 := th4Ev32 || th4Ev37
  let th4Ev39 := !(L.frz)
  let th4Ev40 := th4Ev38 && th4Ev39
  th4Ev40

/-- The extracted `db` input of `g_thr[4].u`. -/
def rtlDb4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Db0 := !(L.frz)
  let th4Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 4)) != 0) && th4Db0
  th4Db1

/-- The extracted `disp` input of `g_thr[4].u`. -/
def rtlDisp4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (4 : BitVec 3))
  let th4Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th4Disp0
  let th4Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (4 : BitVec 3))
  let th4Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th4Disp2
  let th4Disp4 := th4Disp1 || th4Disp3
  th4Disp4

/-- The extracted `pause` input of `g_thr[4].u`. -/
def rtlPause4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (4 : BitVec 3))
  let th4Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th4Pause0
  let th4Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (4 : BitVec 3))
  let th4Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th4Pause2
  let th4Pause4 := th4Pause1 || th4Pause3
  th4Pause4

/-- The extracted `npc` input of `g_thr[4].u`. -/
def rtlNpc4 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th4Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (4 : BitVec 3))
  let th4Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th4Npc0
  let th4Npc2 := if th4Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th4Npc2

/-- The extracted `stop` input of `g_thr[4].u`. -/
def rtlStop4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (4 : BitVec 3))
  let th4Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (4 : BitVec 3))
  let th4Stop2 := (((if th4Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th4Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th4Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th4Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th4Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th4Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th4Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th4Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th4Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th4Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th4Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th4Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th4Stop9 := (th4Stop2 &&& ((if th4Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th4Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th4Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th4Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th4Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th4Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th4Stop10 := (th4Stop9 != (0 : BitVec 6))
  th4Stop10

/-- The extracted `late_set` input of `g_thr[4].u`. -/
def rtlLate4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (4 : BitVec 3))
  let th4Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (4 : BitVec 3))
  let th4Late2 := (((if th4Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th4Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th4Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th4Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th4Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th4Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th4Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th4Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th4Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th4Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th4Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th4Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th4Late9 := (th4Late2 &&& ((if th4Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th4Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th4Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th4Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th4Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th4Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th4Late10 := (th4Late9 != (0 : BitVec 6))
  let th4Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 4)) != 0)
  let th4Late12 := th4Late10 && th4Late11
  th4Late12

/-- The extracted `line_beat` input of `g_thr[4].u`. -/
def rtlBeat4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th4Beat0

/-- The extracted `h_pc_we` input of `g_thr[4].u`. -/
def rtlPcWe4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th4PcWe1 := (th4PcWe0 < (12 : BitVec 16))
  let th4PcWe2 := (L.hostWrite) && th4PcWe1
  let th4PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (4 : BitVec 16))
  let th4PcWe4 := th4PcWe2 && th4PcWe3
  let th4PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th4PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th4PcWe6 := th4PcWe4 && th4PcWe5
  th4PcWe6

/-- The extracted `h_stat_we` input of `g_thr[4].u`. -/
def rtlStatWe4 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th4StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th4StatWe1 := (th4StatWe0 < (12 : BitVec 16))
  let th4StatWe2 := (L.hostWrite) && th4StatWe1
  let th4StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (4 : BitVec 16))
  let th4StatWe4 := th4StatWe2 && th4StatWe3
  let th4StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th4StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th4StatWe6 := th4StatWe4 && th4StatWe5
  th4StatWe6

/-! ### Instance 5 -/

/-- The extracted `ev` input of `g_thr[5].u`. -/
def rtlEv5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Ev0 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 0)) != 0)
  let th5Ev1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 0)) != 0) && th5Ev0
  let th5Ev2 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 1)) != 0)
  let th5Ev3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 1)) != 0) && th5Ev2
  let th5Ev4 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 2)) != 0)
  let th5Ev5 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 2)) != 0) && th5Ev4
  let th5Ev6 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 3)) != 0)
  let th5Ev7 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 3)) != 0) && th5Ev6
  let th5Ev8 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 4)) != 0)
  let th5Ev9 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 4)) != 0) && th5Ev8
  let th5Ev10 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 5)) != 0)
  let th5Ev11 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 5)) != 0) && th5Ev10
  let th5Ev12 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 6)) != 0)
  let th5Ev13 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 6)) != 0) && th5Ev12
  let th5Ev14 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.flagPrev) 7)) != 0)
  let th5Ev15 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.flag) 7)) != 0) && th5Ev14
  let th5Ev16 := !(L.invPrev)
  let th5Ev17 := (L.inv) && th5Ev16
  let th5Ev18 := (((BitVec.ushiftRight ((if false then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.beat) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (L.tap) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if th5Ev1 then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if th5Ev3 then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if th5Ev5 then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if th5Ev7 then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if th5Ev9 then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if th5Ev11 then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if th5Ev13 then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if th5Ev15 then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if th5Ev17 then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3))).toNat) &&& (1 : BitVec 32)) != 0)
  let th5Ev19 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (25 : BitVec 5))
  let th5Ev20 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th5Ev21 := th5Ev19 && th5Ev20
  let th5Ev22 := th5Ev18 || th5Ev21
  let th5Ev23 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (26 : BitVec 5))
  let th5Ev24 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th5Ev25 := th5Ev23 && th5Ev24
  let th5Ev26 := th5Ev22 || th5Ev25
  let th5Ev27 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (27 : BitVec 5))
  let th5Ev28 := (((BitVec.ushiftRight (L.parise) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th5Ev29 := (((BitVec.ushiftRight (L.pafall) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  let th5Ev30 := th5Ev28 || th5Ev29
  let th5Ev31 := th5Ev27 && th5Ev30
  let th5Ev32 := th5Ev26 || th5Ev31
  let th5Ev33 := ((BitVec.truncate 5 (BitVec.ushiftRight (tc) 3)) == (29 : BitVec 5))
  let th5Ev34 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.ready) 5)) != 0)
  let th5Ev35 := th5Ev33 && th5Ev34
  let th5Ev36 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.running) 5)) != 0)
  let th5Ev37 := th5Ev35 && th5Ev36
  let th5Ev38 := th5Ev32 || th5Ev37
  let th5Ev39 := !(L.frz)
  let th5Ev40 := th5Ev38 && th5Ev39
  th5Ev40

/-- The extracted `db` input of `g_thr[5].u`. -/
def rtlDb5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Db0 := !(L.frz)
  let th5Db1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.doorbell) 5)) != 0) && th5Db0
  th5Db1

/-- The extracted `disp` input of `g_thr[5].u`. -/
def rtlDisp5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Disp0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 0)) == (5 : BitVec 3))
  let th5Disp1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 0)) != 0) && th5Disp0
  let th5Disp2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.dispatchThread) 3)) == (5 : BitVec 3))
  let th5Disp3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.dispatchCore) 1)) != 0) && th5Disp2
  let th5Disp4 := th5Disp1 || th5Disp3
  th5Disp4

/-- The extracted `pause` input of `g_thr[5].u`. -/
def rtlPause5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Pause0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (5 : BitVec 3))
  let th5Pause1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 0)) != 0) && th5Pause0
  let th5Pause2 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (5 : BitVec 3))
  let th5Pause3 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th5Pause2
  let th5Pause4 := th5Pause1 || th5Pause3
  th5Pause4

/-- The extracted `npc` input of `g_thr[5].u`. -/
def rtlNpc5 (L : Leaves) (tc : BitVec 8) : BitVec 8 :=
  let th5Npc0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (5 : BitVec 3))
  let th5Npc1 := ((BitVec.truncate 1 (BitVec.ushiftRight (L.pauseCore) 1)) != 0) && th5Npc0
  let th5Npc2 := if th5Npc1 then (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 8)) else (BitVec.truncate 8 (BitVec.ushiftRight (L.nextPc) 0))
  th5Npc2

/-- The extracted `stop` input of `g_thr[5].u`. -/
def rtlStop5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Stop0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (5 : BitVec 3))
  let th5Stop1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (5 : BitVec 3))
  let th5Stop2 := (((if th5Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th5Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th5Stop0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th5Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th5Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th5Stop1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th5Stop3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (1 : BitVec 5))
  let th5Stop4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (1 : BitVec 5))
  let th5Stop5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (1 : BitVec 5))
  let th5Stop6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (1 : BitVec 5))
  let th5Stop7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (1 : BitVec 5))
  let th5Stop8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (1 : BitVec 5))
  let th5Stop9 := (th5Stop2 &&& ((if th5Stop3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th5Stop4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th5Stop5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th5Stop6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th5Stop7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th5Stop8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th5Stop10 := (th5Stop9 != (0 : BitVec 6))
  th5Stop10

/-- The extracted `late_set` input of `g_thr[5].u`. -/
def rtlLate5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Late0 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 0)) == (5 : BitVec 3))
  let th5Late1 := ((BitVec.truncate 3 (BitVec.ushiftRight (L.execThread) 3)) == (5 : BitVec 3))
  let th5Late2 := (((if th5Late0 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th5Late0 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th5Late0 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th5Late1 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th5Late1 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th5Late1 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) &&& (L.valid))
  let th5Late3 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 0)) == (0 : BitVec 5))
  let th5Late4 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 5)) == (0 : BitVec 5))
  let th5Late5 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 10)) == (0 : BitVec 5))
  let th5Late6 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 15)) == (0 : BitVec 5))
  let th5Late7 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 20)) == (0 : BitVec 5))
  let th5Late8 := ((BitVec.truncate 5 (BitVec.ushiftRight (L.groups) 25)) == (0 : BitVec 5))
  let th5Late9 := (th5Late2 &&& ((if th5Late3 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if th5Late4 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if th5Late5 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if th5Late6 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if th5Late7 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if th5Late8 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let th5Late10 := (th5Late9 != (0 : BitVec 6))
  let th5Late11 := !((BitVec.truncate 1 (BitVec.ushiftRight (L.armed) 5)) != 0)
  let th5Late12 := th5Late10 && th5Late11
  th5Late12

/-- The extracted `line_beat` input of `g_thr[5].u`. -/
def rtlBeat5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5Beat0 := (((BitVec.ushiftRight (L.beat) ((BitVec.truncate 2 (BitVec.ushiftRight (tc) 1))).toNat) &&& (1 : BitVec 4)) != 0)
  th5Beat0

/-- The extracted `h_pc_we` input of `g_thr[5].u`. -/
def rtlPcWe5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5PcWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th5PcWe1 := (th5PcWe0 < (12 : BitVec 16))
  let th5PcWe2 := (L.hostWrite) && th5PcWe1
  let th5PcWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (5 : BitVec 16))
  let th5PcWe4 := th5PcWe2 && th5PcWe3
  let th5PcWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th5PcWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (0 : BitVec 32))
  let th5PcWe6 := th5PcWe4 && th5PcWe5
  th5PcWe6

/-- The extracted `h_stat_we` input of `g_thr[5].u`. -/
def rtlStatWe5 (L : Leaves) (tc : BitVec 8) : Bool :=
  let th5StatWe0 := ((L.hostAddr) - (9280 : BitVec 16))
  let th5StatWe1 := (th5StatWe0 < (12 : BitVec 16))
  let th5StatWe2 := (L.hostWrite) && th5StatWe1
  let th5StatWe3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16))) == (5 : BitVec 16))
  let th5StatWe4 := th5StatWe2 && th5StatWe3
  let th5StatWe5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight th5StatWe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) == (1 : BitVec 32))
  let th5StatWe6 := th5StatWe4 && th5StatWe5
  th5StatWe6

/-! ### Instance 0: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv0 L tc = (evRaw L tc (bitAt L.ready 0) (bitAt L.running 0) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv0, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb0 L tc = (bitAt L.doorbell 0 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb0, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp0 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (0 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (0 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp0, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause0 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (0 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (0 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause0, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc0 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (0 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc0, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop0 L tc = stopSpec L (blk L.execThread 0 == (0 : BitVec 3))
      (blk L.execThread 3 == (0 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop0, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate0 L tc = lateSpec L (blk L.execThread 0 == (0 : BitVec 3))
      (blk L.execThread 3 == (0 : BitVec 3)) (bitAt L.armed 0) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate0, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat0 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat0, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe0 L tc = hostPcWe 0 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe0, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe0_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe0 L tc = hostStatWe 0 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe0, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide


/-! ### Instance 1: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv1 L tc = (evRaw L tc (bitAt L.ready 1) (bitAt L.running 1) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv1, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb1 L tc = (bitAt L.doorbell 1 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb1, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp1 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (1 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (1 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp1, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause1 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (1 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (1 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause1, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc1 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (1 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc1, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop1 L tc = stopSpec L (blk L.execThread 0 == (1 : BitVec 3))
      (blk L.execThread 3 == (1 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop1, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate1 L tc = lateSpec L (blk L.execThread 0 == (1 : BitVec 3))
      (blk L.execThread 3 == (1 : BitVec 3)) (bitAt L.armed 1) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate1, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat1 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat1, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe1 L tc = hostPcWe 1 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe1, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe1_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe1 L tc = hostStatWe 1 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe1, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide


/-! ### Instance 2: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv2 L tc = (evRaw L tc (bitAt L.ready 2) (bitAt L.running 2) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv2, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb2 L tc = (bitAt L.doorbell 2 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb2, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp2 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (2 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (2 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp2, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause2 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (2 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (2 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause2, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc2 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (2 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc2, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop2 L tc = stopSpec L (blk L.execThread 0 == (2 : BitVec 3))
      (blk L.execThread 3 == (2 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop2, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate2 L tc = lateSpec L (blk L.execThread 0 == (2 : BitVec 3))
      (blk L.execThread 3 == (2 : BitVec 3)) (bitAt L.armed 2) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate2, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat2 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat2, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe2 L tc = hostPcWe 2 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe2, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe2_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe2 L tc = hostStatWe 2 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe2, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide


/-! ### Instance 3: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv3 L tc = (evRaw L tc (bitAt L.ready 3) (bitAt L.running 3) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv3, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb3 L tc = (bitAt L.doorbell 3 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb3, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp3 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (3 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (3 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp3, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause3 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (3 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (3 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause3, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc3 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (3 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc3, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop3 L tc = stopSpec L (blk L.execThread 0 == (3 : BitVec 3))
      (blk L.execThread 3 == (3 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop3, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate3 L tc = lateSpec L (blk L.execThread 0 == (3 : BitVec 3))
      (blk L.execThread 3 == (3 : BitVec 3)) (bitAt L.armed 3) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate3, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat3 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat3, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe3 L tc = hostPcWe 3 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe3, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe3_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe3 L tc = hostStatWe 3 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe3, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide


/-! ### Instance 4: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv4 L tc = (evRaw L tc (bitAt L.ready 4) (bitAt L.running 4) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv4, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb4 L tc = (bitAt L.doorbell 4 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb4, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp4 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (4 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (4 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp4, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause4 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (4 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (4 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause4, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc4 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (4 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc4, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop4 L tc = stopSpec L (blk L.execThread 0 == (4 : BitVec 3))
      (blk L.execThread 3 == (4 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop4, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate4 L tc = lateSpec L (blk L.execThread 0 == (4 : BitVec 3))
      (blk L.execThread 3 == (4 : BitVec 3)) (bitAt L.armed 4) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate4, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat4 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat4, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe4 L tc = hostPcWe 4 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe4, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe4_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe4 L tc = hostStatWe 4 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe4, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide


/-! ### Instance 5: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv5 L tc = (evRaw L tc (bitAt L.ready 5) (bitAt L.running 5) && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlEv5, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  all_goals bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb5 L tc = (bitAt L.doorbell 5 && !L.frz) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDb5, bitAt]
  all_goals bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp5 L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == (5 : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == (5 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlDisp5, bitAt, blk]
  all_goals bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause5 L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == (5 : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == (5 : BitVec 3))) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPause5, bitAt, blk]
  all_goals bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc5 L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == (5 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlNpc5, selectedPc, bitAt, blk]
  all_goals bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop5 L tc = stopSpec L (blk L.execThread 0 == (5 : BitVec 3))
      (blk L.execThread 3 == (5 : BitVec 3)) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStop5, stopSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate5 L tc = lateSpec L (blk L.execThread 0 == (5 : BitVec 3))
      (blk L.execThread 3 == (5 : BitVec 3)) (bitAt L.armed 5) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlLate5, lateSpec, bitAt, blk, grp]
  all_goals bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat5 L tc = mux4 L.beat (ln tc) := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlBeat5, mux4, bitAt, ln]
  all_goals bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe5 L tc = hostPcWe 5 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlPcWe5, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe5_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe5 L tc = hostStatWe 5 L.hostWrite L.hostAddr := by
  obtain ⟨frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, ready, running, armed, doorbell, dispatchCore, dispatchThread, pauseCore, execThread, nextPc, groups, valid, hostWrite, hostAddr, hostData⟩ := L
  simp only [rtlStatWe5, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  all_goals bv_decide

-- The axiom audit of the chip-top equalities.  `thread_check.py` parses these
-- records and rejects `sorryAx`.
#print axioms rtlEvIn0_eq_spec
#print axioms rtlDbIn0_eq_spec
#print axioms rtlStop0_eq_spec
#print axioms rtlLate0_eq_spec
#print axioms rtlBeat0_eq_spec
#print axioms rtlPcWe0_eq_spec
#print axioms rtlStatWe5_eq_spec


/-- `0x2440` is thread 0's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 0, offset 0. -/
theorem hostMap_trt_0_PC :
    Metronome.HostMap.inRegion .trt 0x2440 = true ∧
      ((0x2440 : BitVec 16) - Metronome.HostMap.base .trt) == 0 ∧
      ((((0x2440 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 0) ∧
      ((((0x2440 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x2441` is thread 0's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 0, offset 1. -/
theorem hostMap_trt_0_STAT :
    Metronome.HostMap.inRegion .trt 0x2441 = true ∧
      ((0x2441 : BitVec 16) - Metronome.HostMap.base .trt) == 1 ∧
      ((((0x2441 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 0) ∧
      ((((0x2441 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide


/-- `0x2442` is thread 1's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 1, offset 0. -/
theorem hostMap_trt_1_PC :
    Metronome.HostMap.inRegion .trt 0x2442 = true ∧
      ((0x2442 : BitVec 16) - Metronome.HostMap.base .trt) == 2 ∧
      ((((0x2442 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 1) ∧
      ((((0x2442 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x2443` is thread 1's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 1, offset 1. -/
theorem hostMap_trt_1_STAT :
    Metronome.HostMap.inRegion .trt 0x2443 = true ∧
      ((0x2443 : BitVec 16) - Metronome.HostMap.base .trt) == 3 ∧
      ((((0x2443 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 1) ∧
      ((((0x2443 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide


/-- `0x2444` is thread 2's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 2, offset 0. -/
theorem hostMap_trt_2_PC :
    Metronome.HostMap.inRegion .trt 0x2444 = true ∧
      ((0x2444 : BitVec 16) - Metronome.HostMap.base .trt) == 4 ∧
      ((((0x2444 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 2) ∧
      ((((0x2444 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x2445` is thread 2's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 2, offset 1. -/
theorem hostMap_trt_2_STAT :
    Metronome.HostMap.inRegion .trt 0x2445 = true ∧
      ((0x2445 : BitVec 16) - Metronome.HostMap.base .trt) == 5 ∧
      ((((0x2445 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 2) ∧
      ((((0x2445 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide


/-- `0x2446` is thread 3's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 3, offset 0. -/
theorem hostMap_trt_3_PC :
    Metronome.HostMap.inRegion .trt 0x2446 = true ∧
      ((0x2446 : BitVec 16) - Metronome.HostMap.base .trt) == 6 ∧
      ((((0x2446 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 3) ∧
      ((((0x2446 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x2447` is thread 3's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 3, offset 1. -/
theorem hostMap_trt_3_STAT :
    Metronome.HostMap.inRegion .trt 0x2447 = true ∧
      ((0x2447 : BitVec 16) - Metronome.HostMap.base .trt) == 7 ∧
      ((((0x2447 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 3) ∧
      ((((0x2447 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide


/-- `0x2448` is thread 4's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 4, offset 0. -/
theorem hostMap_trt_4_PC :
    Metronome.HostMap.inRegion .trt 0x2448 = true ∧
      ((0x2448 : BitVec 16) - Metronome.HostMap.base .trt) == 8 ∧
      ((((0x2448 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 4) ∧
      ((((0x2448 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x2449` is thread 4's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 4, offset 1. -/
theorem hostMap_trt_4_STAT :
    Metronome.HostMap.inRegion .trt 0x2449 = true ∧
      ((0x2449 : BitVec 16) - Metronome.HostMap.base .trt) == 9 ∧
      ((((0x2449 : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 4) ∧
      ((((0x2449 : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide


/-- `0x244a` is thread 5's `TRT.PC` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 5, offset 0. -/
theorem hostMap_trt_5_PC :
    Metronome.HostMap.inRegion .trt 0x244a = true ∧
      ((0x244a : BitVec 16) - Metronome.HostMap.base .trt) == 10 ∧
      ((((0x244a : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 5) ∧
      ((((0x244a : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 0) := by
  decide


/-- `0x244b` is thread 5's `TRT.STAT` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance 5, offset 1. -/
theorem hostMap_trt_5_STAT :
    Metronome.HostMap.inRegion .trt 0x244b = true ∧
      ((0x244b : BitVec 16) - Metronome.HostMap.base .trt) == 11 ∧
      ((((0x244b : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == 5) ∧
      ((((0x244b : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == 1) := by
  decide

end Metronome.Thread.Top
