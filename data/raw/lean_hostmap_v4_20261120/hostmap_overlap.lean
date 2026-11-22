import Metronome.HostMap
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 0763ef436ac5136ffda54bfd7bf5cbcd6fe6e4a81e28dc2400ea2691ee401637
--
-- Host write decode cut (SPEC_V2 §9).  The definitions above the fold are the
-- elaborated cones of `src/project.v`: the eight block region flags, their
-- offset buses, and every host write enable of the design.  The theorems
-- below them are checked against `Metronome.HostMap`, the independent host
-- map table, so a decode that drifted from the map fails the proof.
--
-- Everything here is `bv_decide` over a 16-bit address (or 17 bits with the
-- write strobe), plus the composition theorems over the specification.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Metronome.HostMapCheck

open Metronome Metronome.HostMap

/-! ## Region decode and per-block offsets -/

/-- The elaborated `in_prog` flag for the `prog` block. -/
def rtlInProg (a : BitVec 16) : Bool :=
  let rtlRegionProg0 := (a - (0 : BitVec 16))
  let rtlRegionProg1 := (rtlRegionProg0 < (4096 : BitVec 16))
  rtlRegionProg1

/-- `in_prog` is exactly membership in the map's `prog` window. -/
theorem rtlInProg_spec (a : BitVec 16) :
    rtlInProg a = HostMap.inRegion .prog a := by
  unfold rtlInProg HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_prog` offset bus. -/
def rtlOffProg (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetProg0 := (a - (0 : BitVec 16))
  rtlOffsetProg0

/-- The offset is `ha` minus the map's `prog` base. -/
theorem rtlOffProg_spec (a : BitVec 16) :
    rtlOffProg a = a - HostMap.base .prog := by
  unfold rtlOffProg HostMap.base
  bv_decide

/-- The elaborated `in_data` flag for the `data` block. -/
def rtlInData (a : BitVec 16) : Bool :=
  let rtlRegionData0 := (a - (4096 : BitVec 16))
  let rtlRegionData1 := (rtlRegionData0 < (2048 : BitVec 16))
  rtlRegionData1

/-- `in_data` is exactly membership in the map's `data` window. -/
theorem rtlInData_spec (a : BitVec 16) :
    rtlInData a = HostMap.inRegion .data a := by
  unfold rtlInData HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_data` offset bus. -/
def rtlOffData (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetData0 := (a - (4096 : BitVec 16))
  rtlOffsetData0

/-- The offset is `ha` minus the map's `data` base. -/
theorem rtlOffData_spec (a : BitVec 16) :
    rtlOffData a = a - HostMap.base .data := by
  unfold rtlOffData HostMap.base
  bv_decide

/-- The elaborated `in_cfg` flag for the `cfg` block. -/
def rtlInCfg (a : BitVec 16) : Bool :=
  let rtlRegionCfg0 := (a - (8192 : BitVec 16))
  let rtlRegionCfg1 := (rtlRegionCfg0 < (480 : BitVec 16))
  rtlRegionCfg1

/-- `in_cfg` is exactly membership in the map's `cfg` window. -/
theorem rtlInCfg_spec (a : BitVec 16) :
    rtlInCfg a = HostMap.inRegion .cfg a := by
  unfold rtlInCfg HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_cfg` offset bus. -/
def rtlOffCfg (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetCfg0 := (a - (8192 : BitVec 16))
  rtlOffsetCfg0

/-- The offset is `ha` minus the map's `cfg` base. -/
theorem rtlOffCfg_spec (a : BitVec 16) :
    rtlOffCfg a = a - HostMap.base .cfg := by
  unfold rtlOffCfg HostMap.base
  bv_decide

/-- The elaborated `in_ctrl` flag for the `ctrl` block. -/
def rtlInCtrl (a : BitVec 16) : Bool :=
  let rtlRegionCtrl0 := (a - (9216 : BitVec 16))
  let rtlRegionCtrl1 := (rtlRegionCtrl0 < (16 : BitVec 16))
  rtlRegionCtrl1

/-- `in_ctrl` is exactly membership in the map's `ctrl` window. -/
theorem rtlInCtrl_spec (a : BitVec 16) :
    rtlInCtrl a = HostMap.inRegion .ctrl a := by
  unfold rtlInCtrl HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_ctrl` offset bus. -/
def rtlOffCtrl (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetCtrl0 := (a - (9216 : BitVec 16))
  rtlOffsetCtrl0

/-- The offset is `ha` minus the map's `ctrl` base. -/
theorem rtlOffCtrl_spec (a : BitVec 16) :
    rtlOffCtrl a = a - HostMap.base .ctrl := by
  unfold rtlOffCtrl HostMap.base
  bv_decide

/-- The elaborated `in_lrt` flag for the `lrt` block. -/
def rtlInLrt (a : BitVec 16) : Bool :=
  let rtlRegionLrt0 := (a - (9232 : BitVec 16))
  let rtlRegionLrt1 := (rtlRegionLrt0 < (32 : BitVec 16))
  rtlRegionLrt1

/-- `in_lrt` is exactly membership in the map's `lrt` window. -/
theorem rtlInLrt_spec (a : BitVec 16) :
    rtlInLrt a = HostMap.inRegion .lrt a := by
  unfold rtlInLrt HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_lrt` offset bus. -/
def rtlOffLrt (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetLrt0 := (a - (9232 : BitVec 16))
  rtlOffsetLrt0

/-- The offset is `ha` minus the map's `lrt` base. -/
theorem rtlOffLrt_spec (a : BitVec 16) :
    rtlOffLrt a = a - HostMap.base .lrt := by
  unfold rtlOffLrt HostMap.base
  bv_decide

/-- The elaborated `in_trt` flag for the `trt` block. -/
def rtlInTrt (a : BitVec 16) : Bool :=
  let rtlRegionTrt0 := (a - (9280 : BitVec 16))
  let rtlRegionTrt1 := (rtlRegionTrt0 < (12 : BitVec 16))
  rtlRegionTrt1

/-- `in_trt` is exactly membership in the map's `trt` window. -/
theorem rtlInTrt_spec (a : BitVec 16) :
    rtlInTrt a = HostMap.inRegion .trt a := by
  unfold rtlInTrt HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_trt` offset bus. -/
def rtlOffTrt (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetTrt0 := (a - (9280 : BitVec 16))
  rtlOffsetTrt0

/-- The offset is `ha` minus the map's `trt` base. -/
theorem rtlOffTrt_spec (a : BitVec 16) :
    rtlOffTrt a = a - HostMap.base .trt := by
  unfold rtlOffTrt HostMap.base
  bv_decide

/-- The elaborated `in_srt` flag for the `srt` block. -/
def rtlInSrt (a : BitVec 16) : Bool :=
  let rtlRegionSrt0 := (a - (9311 : BitVec 16))
  let rtlRegionSrt1 := (rtlRegionSrt0 < (8 : BitVec 16))
  rtlRegionSrt1

/-- `in_srt` is exactly membership in the map's `srt` window. -/
theorem rtlInSrt_spec (a : BitVec 16) :
    rtlInSrt a = HostMap.inRegion .srt a := by
  unfold rtlInSrt HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_srt` offset bus. -/
def rtlOffSrt (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetSrt0 := (a - (9311 : BitVec 16))
  rtlOffsetSrt0

/-- The offset is `ha` minus the map's `srt` base. -/
theorem rtlOffSrt_spec (a : BitVec 16) :
    rtlOffSrt a = a - HostMap.base .srt := by
  unfold rtlOffSrt HostMap.base
  bv_decide

/-- The elaborated `in_dbg` flag for the `dbg` block. -/
def rtlInDbg (a : BitVec 16) : Bool :=
  let rtlRegionDbg0 := (a - (9312 : BitVec 16))
  let rtlRegionDbg1 := (rtlRegionDbg0 < (32 : BitVec 16))
  rtlRegionDbg1

/-- `in_dbg` is exactly membership in the map's `dbg` window. -/
theorem rtlInDbg_spec (a : BitVec 16) :
    rtlInDbg a = HostMap.inRegion .dbg a := by
  unfold rtlInDbg HostMap.inRegion HostMap.base HostMap.span
  bv_decide

/-- The elaborated `a_dbg` offset bus. -/
def rtlOffDbg (a : BitVec 16) : BitVec 16 :=
  let rtlOffsetDbg0 := (a - (9312 : BitVec 16))
  rtlOffsetDbg0

/-- The offset is `ha` minus the map's `dbg` base. -/
theorem rtlOffDbg_spec (a : BitVec 16) :
    rtlOffDbg a = a - HostMap.base .dbg := by
  unfold rtlOffDbg HostMap.base
  bv_decide

/-- Two block windows never both claim one address: the eight elaborated
region flags are pairwise exclusive, hence a host address has one block. -/
theorem regions_exclusive (a : BitVec 16) :
    HostMap.bitCount [rtlInProg a, rtlInData a, rtlInCfg a, rtlInCtrl a, rtlInLrt a, rtlInTrt a, rtlInSrt a, rtlInDbg a] ≤ 1 := by
  simp only [rtlInProg_spec, rtlInData_spec, rtlInCfg_spec, rtlInCtrl_spec, rtlInLrt_spec, rtlInTrt_spec, rtlInSrt_spec, rtlInDbg_spec]
  exact HostMap.blockCount_le_one a


/-! ## Register write enables -/

/-- Host write enable of `CTRL.RUN`. -/
def enCtrlRun (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlRun0 := (a - (9216 : BitVec 16))
  let enCtrlRun1 := (enCtrlRun0 < (16 : BitVec 16))
  let enCtrlRun2 := w && enCtrlRun1
  let enCtrlRun3 := (((BitVec.setWidth 32 enCtrlRun0)) == (0 : BitVec 32))
  let enCtrlRun4 := enCtrlRun2 && enCtrlRun3
  enCtrlRun4

/-- `CTRL.RUN` is written exactly by a host write at `0x2400`. -/
theorem enCtrlRun_spec (w : Bool) (a : BitVec 16) :
    enCtrlRun w a = (w && (a == 0x2400)) := by
  unfold enCtrlRun
  bv_decide

/-- Host write enable of `CTRL.STICKY`. -/
def enCtrlSticky (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlSticky0 := (a - (9216 : BitVec 16))
  let enCtrlSticky1 := (enCtrlSticky0 < (16 : BitVec 16))
  let enCtrlSticky2 := w && enCtrlSticky1
  let enCtrlSticky3 := (((BitVec.setWidth 32 enCtrlSticky0)) == (1 : BitVec 32))
  let enCtrlSticky4 := enCtrlSticky2 && enCtrlSticky3
  enCtrlSticky4

/-- `CTRL.STICKY` is written exactly by a host write at `0x2401`. -/
theorem enCtrlSticky_spec (w : Bool) (a : BitVec 16) :
    enCtrlSticky w a = (w && (a == 0x2401)) := by
  unfold enCtrlSticky
  bv_decide

/-- Host write enable of `CTRL.IRQEN`. -/
def enCtrlIrqen (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlIrqen0 := (a - (9216 : BitVec 16))
  let enCtrlIrqen1 := (enCtrlIrqen0 < (16 : BitVec 16))
  let enCtrlIrqen2 := w && enCtrlIrqen1
  let enCtrlIrqen3 := (((BitVec.setWidth 32 enCtrlIrqen0)) == (2 : BitVec 32))
  let enCtrlIrqen4 := enCtrlIrqen2 && enCtrlIrqen3
  enCtrlIrqen4

/-- `CTRL.IRQEN` is written exactly by a host write at `0x2402`. -/
theorem enCtrlIrqen_spec (w : Bool) (a : BitVec 16) :
    enCtrlIrqen w a = (w && (a == 0x2402)) := by
  unfold enCtrlIrqen
  bv_decide

/-- Host write enable of `CTRL.DOORBELL`. -/
def enCtrlDoorbell (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlDoorbell0 := (a - (9216 : BitVec 16))
  let enCtrlDoorbell1 := (enCtrlDoorbell0 < (16 : BitVec 16))
  let enCtrlDoorbell2 := w && enCtrlDoorbell1
  let enCtrlDoorbell3 := (((BitVec.setWidth 32 enCtrlDoorbell0)) == (3 : BitVec 32))
  let enCtrlDoorbell4 := enCtrlDoorbell2 && enCtrlDoorbell3
  enCtrlDoorbell4

/-- `CTRL.DOORBELL` is written exactly by a host write at `0x2403`. -/
theorem enCtrlDoorbell_spec (w : Bool) (a : BitVec 16) :
    enCtrlDoorbell w a = (w && (a == 0x2403)) := by
  unfold enCtrlDoorbell
  bv_decide

/-- Host write enable of `CTRL.HOSTIN`. -/
def enCtrlHostIn (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlHostIn0 := (a - (9216 : BitVec 16))
  let enCtrlHostIn1 := (enCtrlHostIn0 < (16 : BitVec 16))
  let enCtrlHostIn2 := w && enCtrlHostIn1
  let enCtrlHostIn3 := (((BitVec.setWidth 32 enCtrlHostIn0)) == (4 : BitVec 32))
  let enCtrlHostIn4 := enCtrlHostIn2 && enCtrlHostIn3
  enCtrlHostIn4

/-- `CTRL.HOSTIN` is written exactly by a host write at `0x2404`. -/
theorem enCtrlHostIn_spec (w : Bool) (a : BitVec 16) :
    enCtrlHostIn w a = (w && (a == 0x2404)) := by
  unfold enCtrlHostIn
  bv_decide

/-- Host write enable of `CTRL.HOSTSTAT`. -/
def enCtrlHostStat (w : Bool) (a : BitVec 16) : Bool :=
  let enCtrlHostStat0 := (a - (9216 : BitVec 16))
  let enCtrlHostStat1 := (enCtrlHostStat0 < (16 : BitVec 16))
  let enCtrlHostStat2 := w && enCtrlHostStat1
  let enCtrlHostStat3 := (((BitVec.setWidth 32 enCtrlHostStat0)) == (6 : BitVec 32))
  let enCtrlHostStat4 := enCtrlHostStat2 && enCtrlHostStat3
  enCtrlHostStat4

/-- `CTRL.HOSTSTAT` is written exactly by a host write at `0x2406`. -/
theorem enCtrlHostStat_spec (w : Bool) (a : BitVec 16) :
    enCtrlHostStat w a = (w && (a == 0x2406)) := by
  unfold enCtrlHostStat
  bv_decide

/-- Host write enable of `LRT[0].PHASE low`. -/
def enLine0Phase0 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine0Phase00 := (a - (9232 : BitVec 16))
  let enLine0Phase01 := (enLine0Phase00 < (32 : BitVec 16))
  let enLine0Phase02 := w && enLine0Phase01
  let enLine0Phase03 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine0Phase00 3)))) == (0 : BitVec 16))
  let enLine0Phase04 := enLine0Phase02 && enLine0Phase03
  let enLine0Phase05 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine0Phase00 0)))) == (0 : BitVec 32))
  let enLine0Phase06 := enLine0Phase04 && enLine0Phase05
  enLine0Phase06

/-- `LRT[0].PHASE low` is written exactly by a host write at `0x2410`. -/
theorem enLine0Phase0_spec (w : Bool) (a : BitVec 16) :
    enLine0Phase0 w a = (w && (a == 0x2410)) := by
  unfold enLine0Phase0
  bv_decide

/-- Host write enable of `LRT[0].PHASE high`. -/
def enLine0Phase1 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine0Phase10 := (a - (9232 : BitVec 16))
  let enLine0Phase11 := (enLine0Phase10 < (32 : BitVec 16))
  let enLine0Phase12 := w && enLine0Phase11
  let enLine0Phase13 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine0Phase10 3)))) == (0 : BitVec 16))
  let enLine0Phase14 := enLine0Phase12 && enLine0Phase13
  let enLine0Phase15 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine0Phase10 0)))) == (1 : BitVec 32))
  let enLine0Phase16 := enLine0Phase14 && enLine0Phase15
  enLine0Phase16

/-- `LRT[0].PHASE high` is written exactly by a host write at `0x2411`. -/
theorem enLine0Phase1_spec (w : Bool) (a : BitVec 16) :
    enLine0Phase1 w a = (w && (a == 0x2411)) := by
  unfold enLine0Phase1
  bv_decide

/-- Host write enable of `LRT[0].CTL`. -/
def enLine0Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enLine0Ctl0 := (a - (9232 : BitVec 16))
  let enLine0Ctl1 := (enLine0Ctl0 < (32 : BitVec 16))
  let enLine0Ctl2 := w && enLine0Ctl1
  let enLine0Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine0Ctl0 3)))) == (0 : BitVec 16))
  let enLine0Ctl4 := enLine0Ctl2 && enLine0Ctl3
  let enLine0Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine0Ctl0 0)))) == (2 : BitVec 32))
  let enLine0Ctl6 := enLine0Ctl4 && enLine0Ctl5
  enLine0Ctl6

/-- `LRT[0].CTL` is written exactly by a host write at `0x2412`. -/
theorem enLine0Ctl_spec (w : Bool) (a : BitVec 16) :
    enLine0Ctl w a = (w && (a == 0x2412)) := by
  unfold enLine0Ctl
  bv_decide

/-- Host write enable of `LRT[0].STAT`. -/
def enLine0Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enLine0Stat0 := (a - (9232 : BitVec 16))
  let enLine0Stat1 := (enLine0Stat0 < (32 : BitVec 16))
  let enLine0Stat2 := w && enLine0Stat1
  let enLine0Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine0Stat0 3)))) == (0 : BitVec 16))
  let enLine0Stat4 := enLine0Stat2 && enLine0Stat3
  let enLine0Stat5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine0Stat0 0)))) == (5 : BitVec 32))
  let enLine0Stat6 := enLine0Stat4 && enLine0Stat5
  enLine0Stat6

/-- `LRT[0].STAT` is written exactly by a host write at `0x2415`. -/
theorem enLine0Stat_spec (w : Bool) (a : BitVec 16) :
    enLine0Stat w a = (w && (a == 0x2415)) := by
  unfold enLine0Stat
  bv_decide

/-- Host write enable of `LRT[1].PHASE low`. -/
def enLine1Phase0 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine1Phase00 := (a - (9232 : BitVec 16))
  let enLine1Phase01 := (enLine1Phase00 < (32 : BitVec 16))
  let enLine1Phase02 := w && enLine1Phase01
  let enLine1Phase03 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine1Phase00 3)))) == (1 : BitVec 16))
  let enLine1Phase04 := enLine1Phase02 && enLine1Phase03
  let enLine1Phase05 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine1Phase00 0)))) == (0 : BitVec 32))
  let enLine1Phase06 := enLine1Phase04 && enLine1Phase05
  enLine1Phase06

/-- `LRT[1].PHASE low` is written exactly by a host write at `0x2418`. -/
theorem enLine1Phase0_spec (w : Bool) (a : BitVec 16) :
    enLine1Phase0 w a = (w && (a == 0x2418)) := by
  unfold enLine1Phase0
  bv_decide

/-- Host write enable of `LRT[1].PHASE high`. -/
def enLine1Phase1 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine1Phase10 := (a - (9232 : BitVec 16))
  let enLine1Phase11 := (enLine1Phase10 < (32 : BitVec 16))
  let enLine1Phase12 := w && enLine1Phase11
  let enLine1Phase13 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine1Phase10 3)))) == (1 : BitVec 16))
  let enLine1Phase14 := enLine1Phase12 && enLine1Phase13
  let enLine1Phase15 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine1Phase10 0)))) == (1 : BitVec 32))
  let enLine1Phase16 := enLine1Phase14 && enLine1Phase15
  enLine1Phase16

/-- `LRT[1].PHASE high` is written exactly by a host write at `0x2419`. -/
theorem enLine1Phase1_spec (w : Bool) (a : BitVec 16) :
    enLine1Phase1 w a = (w && (a == 0x2419)) := by
  unfold enLine1Phase1
  bv_decide

/-- Host write enable of `LRT[1].CTL`. -/
def enLine1Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enLine1Ctl0 := (a - (9232 : BitVec 16))
  let enLine1Ctl1 := (enLine1Ctl0 < (32 : BitVec 16))
  let enLine1Ctl2 := w && enLine1Ctl1
  let enLine1Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine1Ctl0 3)))) == (1 : BitVec 16))
  let enLine1Ctl4 := enLine1Ctl2 && enLine1Ctl3
  let enLine1Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine1Ctl0 0)))) == (2 : BitVec 32))
  let enLine1Ctl6 := enLine1Ctl4 && enLine1Ctl5
  enLine1Ctl6

/-- `LRT[1].CTL` is written exactly by a host write at `0x241A`. -/
theorem enLine1Ctl_spec (w : Bool) (a : BitVec 16) :
    enLine1Ctl w a = (w && (a == 0x241A)) := by
  unfold enLine1Ctl
  bv_decide

/-- Host write enable of `LRT[1].STAT`. -/
def enLine1Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enLine1Stat0 := (a - (9232 : BitVec 16))
  let enLine1Stat1 := (enLine1Stat0 < (32 : BitVec 16))
  let enLine1Stat2 := w && enLine1Stat1
  let enLine1Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine1Stat0 3)))) == (1 : BitVec 16))
  let enLine1Stat4 := enLine1Stat2 && enLine1Stat3
  let enLine1Stat5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine1Stat0 0)))) == (5 : BitVec 32))
  let enLine1Stat6 := enLine1Stat4 && enLine1Stat5
  enLine1Stat6

/-- `LRT[1].STAT` is written exactly by a host write at `0x241D`. -/
theorem enLine1Stat_spec (w : Bool) (a : BitVec 16) :
    enLine1Stat w a = (w && (a == 0x241D)) := by
  unfold enLine1Stat
  bv_decide

/-- Host write enable of `LRT[2].PHASE low`. -/
def enLine2Phase0 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine2Phase00 := (a - (9232 : BitVec 16))
  let enLine2Phase01 := (enLine2Phase00 < (32 : BitVec 16))
  let enLine2Phase02 := w && enLine2Phase01
  let enLine2Phase03 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine2Phase00 3)))) == (2 : BitVec 16))
  let enLine2Phase04 := enLine2Phase02 && enLine2Phase03
  let enLine2Phase05 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine2Phase00 0)))) == (0 : BitVec 32))
  let enLine2Phase06 := enLine2Phase04 && enLine2Phase05
  enLine2Phase06

/-- `LRT[2].PHASE low` is written exactly by a host write at `0x2420`. -/
theorem enLine2Phase0_spec (w : Bool) (a : BitVec 16) :
    enLine2Phase0 w a = (w && (a == 0x2420)) := by
  unfold enLine2Phase0
  bv_decide

/-- Host write enable of `LRT[2].PHASE high`. -/
def enLine2Phase1 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine2Phase10 := (a - (9232 : BitVec 16))
  let enLine2Phase11 := (enLine2Phase10 < (32 : BitVec 16))
  let enLine2Phase12 := w && enLine2Phase11
  let enLine2Phase13 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine2Phase10 3)))) == (2 : BitVec 16))
  let enLine2Phase14 := enLine2Phase12 && enLine2Phase13
  let enLine2Phase15 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine2Phase10 0)))) == (1 : BitVec 32))
  let enLine2Phase16 := enLine2Phase14 && enLine2Phase15
  enLine2Phase16

/-- `LRT[2].PHASE high` is written exactly by a host write at `0x2421`. -/
theorem enLine2Phase1_spec (w : Bool) (a : BitVec 16) :
    enLine2Phase1 w a = (w && (a == 0x2421)) := by
  unfold enLine2Phase1
  bv_decide

/-- Host write enable of `LRT[2].CTL`. -/
def enLine2Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enLine2Ctl0 := (a - (9232 : BitVec 16))
  let enLine2Ctl1 := (enLine2Ctl0 < (32 : BitVec 16))
  let enLine2Ctl2 := w && enLine2Ctl1
  let enLine2Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine2Ctl0 3)))) == (2 : BitVec 16))
  let enLine2Ctl4 := enLine2Ctl2 && enLine2Ctl3
  let enLine2Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine2Ctl0 0)))) == (2 : BitVec 32))
  let enLine2Ctl6 := enLine2Ctl4 && enLine2Ctl5
  enLine2Ctl6

/-- `LRT[2].CTL` is written exactly by a host write at `0x2422`. -/
theorem enLine2Ctl_spec (w : Bool) (a : BitVec 16) :
    enLine2Ctl w a = (w && (a == 0x2422)) := by
  unfold enLine2Ctl
  bv_decide

/-- Host write enable of `LRT[2].STAT`. -/
def enLine2Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enLine2Stat0 := (a - (9232 : BitVec 16))
  let enLine2Stat1 := (enLine2Stat0 < (32 : BitVec 16))
  let enLine2Stat2 := w && enLine2Stat1
  let enLine2Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine2Stat0 3)))) == (2 : BitVec 16))
  let enLine2Stat4 := enLine2Stat2 && enLine2Stat3
  let enLine2Stat5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine2Stat0 0)))) == (5 : BitVec 32))
  let enLine2Stat6 := enLine2Stat4 && enLine2Stat5
  enLine2Stat6

/-- `LRT[2].STAT` is written exactly by a host write at `0x2425`. -/
theorem enLine2Stat_spec (w : Bool) (a : BitVec 16) :
    enLine2Stat w a = (w && (a == 0x2425)) := by
  unfold enLine2Stat
  bv_decide

/-- Host write enable of `LRT[3].PHASE low`. -/
def enLine3Phase0 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine3Phase00 := (a - (9232 : BitVec 16))
  let enLine3Phase01 := (enLine3Phase00 < (32 : BitVec 16))
  let enLine3Phase02 := w && enLine3Phase01
  let enLine3Phase03 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine3Phase00 3)))) == (3 : BitVec 16))
  let enLine3Phase04 := enLine3Phase02 && enLine3Phase03
  let enLine3Phase05 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine3Phase00 0)))) == (0 : BitVec 32))
  let enLine3Phase06 := enLine3Phase04 && enLine3Phase05
  enLine3Phase06

/-- `LRT[3].PHASE low` is written exactly by a host write at `0x2428`. -/
theorem enLine3Phase0_spec (w : Bool) (a : BitVec 16) :
    enLine3Phase0 w a = (w && (a == 0x2428)) := by
  unfold enLine3Phase0
  bv_decide

/-- Host write enable of `LRT[3].PHASE high`. -/
def enLine3Phase1 (w : Bool) (a : BitVec 16) : Bool :=
  let enLine3Phase10 := (a - (9232 : BitVec 16))
  let enLine3Phase11 := (enLine3Phase10 < (32 : BitVec 16))
  let enLine3Phase12 := w && enLine3Phase11
  let enLine3Phase13 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine3Phase10 3)))) == (3 : BitVec 16))
  let enLine3Phase14 := enLine3Phase12 && enLine3Phase13
  let enLine3Phase15 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine3Phase10 0)))) == (1 : BitVec 32))
  let enLine3Phase16 := enLine3Phase14 && enLine3Phase15
  enLine3Phase16

/-- `LRT[3].PHASE high` is written exactly by a host write at `0x2429`. -/
theorem enLine3Phase1_spec (w : Bool) (a : BitVec 16) :
    enLine3Phase1 w a = (w && (a == 0x2429)) := by
  unfold enLine3Phase1
  bv_decide

/-- Host write enable of `LRT[3].CTL`. -/
def enLine3Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enLine3Ctl0 := (a - (9232 : BitVec 16))
  let enLine3Ctl1 := (enLine3Ctl0 < (32 : BitVec 16))
  let enLine3Ctl2 := w && enLine3Ctl1
  let enLine3Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine3Ctl0 3)))) == (3 : BitVec 16))
  let enLine3Ctl4 := enLine3Ctl2 && enLine3Ctl3
  let enLine3Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine3Ctl0 0)))) == (2 : BitVec 32))
  let enLine3Ctl6 := enLine3Ctl4 && enLine3Ctl5
  enLine3Ctl6

/-- `LRT[3].CTL` is written exactly by a host write at `0x242A`. -/
theorem enLine3Ctl_spec (w : Bool) (a : BitVec 16) :
    enLine3Ctl w a = (w && (a == 0x242A)) := by
  unfold enLine3Ctl
  bv_decide

/-- Host write enable of `LRT[3].STAT`. -/
def enLine3Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enLine3Stat0 := (a - (9232 : BitVec 16))
  let enLine3Stat1 := (enLine3Stat0 < (32 : BitVec 16))
  let enLine3Stat2 := w && enLine3Stat1
  let enLine3Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 13 (BitVec.ushiftRight enLine3Stat0 3)))) == (3 : BitVec 16))
  let enLine3Stat4 := enLine3Stat2 && enLine3Stat3
  let enLine3Stat5 := (((BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight enLine3Stat0 0)))) == (5 : BitVec 32))
  let enLine3Stat6 := enLine3Stat4 && enLine3Stat5
  enLine3Stat6

/-- `LRT[3].STAT` is written exactly by a host write at `0x242D`. -/
theorem enLine3Stat_spec (w : Bool) (a : BitVec 16) :
    enLine3Stat w a = (w && (a == 0x242D)) := by
  unfold enLine3Stat
  bv_decide

/-- Host write enable of `TRT[0].PC`. -/
def enThread0Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread0Pc0 := (a - (9280 : BitVec 16))
  let enThread0Pc1 := (enThread0Pc0 < (12 : BitVec 16))
  let enThread0Pc2 := w && enThread0Pc1
  let enThread0Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread0Pc0 1)))) == (0 : BitVec 16))
  let enThread0Pc4 := enThread0Pc2 && enThread0Pc3
  let enThread0Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread0Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread0Pc6 := enThread0Pc4 && enThread0Pc5
  enThread0Pc6

/-- `TRT[0].PC` is written exactly by a host write at `0x2440`. -/
theorem enThread0Pc_spec (w : Bool) (a : BitVec 16) :
    enThread0Pc w a = (w && (a == 0x2440)) := by
  unfold enThread0Pc
  bv_decide

/-- Host write enable of `TRT[0].STAT`. -/
def enThread0Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread0Stat0 := (a - (9280 : BitVec 16))
  let enThread0Stat1 := (enThread0Stat0 < (12 : BitVec 16))
  let enThread0Stat2 := w && enThread0Stat1
  let enThread0Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread0Stat0 1)))) == (0 : BitVec 16))
  let enThread0Stat4 := enThread0Stat2 && enThread0Stat3
  let enThread0Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread0Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread0Stat6 := enThread0Stat4 && enThread0Stat5
  enThread0Stat6

/-- `TRT[0].STAT` is written exactly by a host write at `0x2441`. -/
theorem enThread0Stat_spec (w : Bool) (a : BitVec 16) :
    enThread0Stat w a = (w && (a == 0x2441)) := by
  unfold enThread0Stat
  bv_decide

/-- Host write enable of `TRT[1].PC`. -/
def enThread1Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread1Pc0 := (a - (9280 : BitVec 16))
  let enThread1Pc1 := (enThread1Pc0 < (12 : BitVec 16))
  let enThread1Pc2 := w && enThread1Pc1
  let enThread1Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread1Pc0 1)))) == (1 : BitVec 16))
  let enThread1Pc4 := enThread1Pc2 && enThread1Pc3
  let enThread1Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread1Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread1Pc6 := enThread1Pc4 && enThread1Pc5
  enThread1Pc6

/-- `TRT[1].PC` is written exactly by a host write at `0x2442`. -/
theorem enThread1Pc_spec (w : Bool) (a : BitVec 16) :
    enThread1Pc w a = (w && (a == 0x2442)) := by
  unfold enThread1Pc
  bv_decide

/-- Host write enable of `TRT[1].STAT`. -/
def enThread1Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread1Stat0 := (a - (9280 : BitVec 16))
  let enThread1Stat1 := (enThread1Stat0 < (12 : BitVec 16))
  let enThread1Stat2 := w && enThread1Stat1
  let enThread1Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread1Stat0 1)))) == (1 : BitVec 16))
  let enThread1Stat4 := enThread1Stat2 && enThread1Stat3
  let enThread1Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread1Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread1Stat6 := enThread1Stat4 && enThread1Stat5
  enThread1Stat6

/-- `TRT[1].STAT` is written exactly by a host write at `0x2443`. -/
theorem enThread1Stat_spec (w : Bool) (a : BitVec 16) :
    enThread1Stat w a = (w && (a == 0x2443)) := by
  unfold enThread1Stat
  bv_decide

/-- Host write enable of `TRT[2].PC`. -/
def enThread2Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread2Pc0 := (a - (9280 : BitVec 16))
  let enThread2Pc1 := (enThread2Pc0 < (12 : BitVec 16))
  let enThread2Pc2 := w && enThread2Pc1
  let enThread2Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread2Pc0 1)))) == (2 : BitVec 16))
  let enThread2Pc4 := enThread2Pc2 && enThread2Pc3
  let enThread2Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread2Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread2Pc6 := enThread2Pc4 && enThread2Pc5
  enThread2Pc6

/-- `TRT[2].PC` is written exactly by a host write at `0x2444`. -/
theorem enThread2Pc_spec (w : Bool) (a : BitVec 16) :
    enThread2Pc w a = (w && (a == 0x2444)) := by
  unfold enThread2Pc
  bv_decide

/-- Host write enable of `TRT[2].STAT`. -/
def enThread2Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread2Stat0 := (a - (9280 : BitVec 16))
  let enThread2Stat1 := (enThread2Stat0 < (12 : BitVec 16))
  let enThread2Stat2 := w && enThread2Stat1
  let enThread2Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread2Stat0 1)))) == (2 : BitVec 16))
  let enThread2Stat4 := enThread2Stat2 && enThread2Stat3
  let enThread2Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread2Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread2Stat6 := enThread2Stat4 && enThread2Stat5
  enThread2Stat6

/-- `TRT[2].STAT` is written exactly by a host write at `0x2445`. -/
theorem enThread2Stat_spec (w : Bool) (a : BitVec 16) :
    enThread2Stat w a = (w && (a == 0x2445)) := by
  unfold enThread2Stat
  bv_decide

/-- Host write enable of `TRT[3].PC`. -/
def enThread3Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread3Pc0 := (a - (9280 : BitVec 16))
  let enThread3Pc1 := (enThread3Pc0 < (12 : BitVec 16))
  let enThread3Pc2 := w && enThread3Pc1
  let enThread3Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread3Pc0 1)))) == (3 : BitVec 16))
  let enThread3Pc4 := enThread3Pc2 && enThread3Pc3
  let enThread3Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread3Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread3Pc6 := enThread3Pc4 && enThread3Pc5
  enThread3Pc6

/-- `TRT[3].PC` is written exactly by a host write at `0x2446`. -/
theorem enThread3Pc_spec (w : Bool) (a : BitVec 16) :
    enThread3Pc w a = (w && (a == 0x2446)) := by
  unfold enThread3Pc
  bv_decide

/-- Host write enable of `TRT[3].STAT`. -/
def enThread3Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread3Stat0 := (a - (9280 : BitVec 16))
  let enThread3Stat1 := (enThread3Stat0 < (12 : BitVec 16))
  let enThread3Stat2 := w && enThread3Stat1
  let enThread3Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread3Stat0 1)))) == (3 : BitVec 16))
  let enThread3Stat4 := enThread3Stat2 && enThread3Stat3
  let enThread3Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread3Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread3Stat6 := enThread3Stat4 && enThread3Stat5
  enThread3Stat6

/-- `TRT[3].STAT` is written exactly by a host write at `0x2447`. -/
theorem enThread3Stat_spec (w : Bool) (a : BitVec 16) :
    enThread3Stat w a = (w && (a == 0x2447)) := by
  unfold enThread3Stat
  bv_decide

/-- Host write enable of `TRT[4].PC`. -/
def enThread4Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread4Pc0 := (a - (9280 : BitVec 16))
  let enThread4Pc1 := (enThread4Pc0 < (12 : BitVec 16))
  let enThread4Pc2 := w && enThread4Pc1
  let enThread4Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread4Pc0 1)))) == (4 : BitVec 16))
  let enThread4Pc4 := enThread4Pc2 && enThread4Pc3
  let enThread4Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread4Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread4Pc6 := enThread4Pc4 && enThread4Pc5
  enThread4Pc6

/-- `TRT[4].PC` is written exactly by a host write at `0x2448`. -/
theorem enThread4Pc_spec (w : Bool) (a : BitVec 16) :
    enThread4Pc w a = (w && (a == 0x2448)) := by
  unfold enThread4Pc
  bv_decide

/-- Host write enable of `TRT[4].STAT`. -/
def enThread4Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread4Stat0 := (a - (9280 : BitVec 16))
  let enThread4Stat1 := (enThread4Stat0 < (12 : BitVec 16))
  let enThread4Stat2 := w && enThread4Stat1
  let enThread4Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread4Stat0 1)))) == (4 : BitVec 16))
  let enThread4Stat4 := enThread4Stat2 && enThread4Stat3
  let enThread4Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread4Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread4Stat6 := enThread4Stat4 && enThread4Stat5
  enThread4Stat6

/-- `TRT[4].STAT` is written exactly by a host write at `0x2449`. -/
theorem enThread4Stat_spec (w : Bool) (a : BitVec 16) :
    enThread4Stat w a = (w && (a == 0x2449)) := by
  unfold enThread4Stat
  bv_decide

/-- Host write enable of `TRT[5].PC`. -/
def enThread5Pc (w : Bool) (a : BitVec 16) : Bool :=
  let enThread5Pc0 := (a - (9280 : BitVec 16))
  let enThread5Pc1 := (enThread5Pc0 < (12 : BitVec 16))
  let enThread5Pc2 := w && enThread5Pc1
  let enThread5Pc3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread5Pc0 1)))) == (5 : BitVec 16))
  let enThread5Pc4 := enThread5Pc2 && enThread5Pc3
  let enThread5Pc5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread5Pc0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (0 : BitVec 32))
  let enThread5Pc6 := enThread5Pc4 && enThread5Pc5
  enThread5Pc6

/-- `TRT[5].PC` is written exactly by a host write at `0x244A`. -/
theorem enThread5Pc_spec (w : Bool) (a : BitVec 16) :
    enThread5Pc w a = (w && (a == 0x244A)) := by
  unfold enThread5Pc
  bv_decide

/-- Host write enable of `TRT[5].STAT`. -/
def enThread5Stat (w : Bool) (a : BitVec 16) : Bool :=
  let enThread5Stat0 := (a - (9280 : BitVec 16))
  let enThread5Stat1 := (enThread5Stat0 < (12 : BitVec 16))
  let enThread5Stat2 := w && enThread5Stat1
  let enThread5Stat3 := (((BitVec.setWidth 16 (BitVec.truncate 15 (BitVec.ushiftRight enThread5Stat0 1)))) == (5 : BitVec 16))
  let enThread5Stat4 := enThread5Stat2 && enThread5Stat3
  let enThread5Stat5 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight enThread5Stat0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32))) == (1 : BitVec 32))
  let enThread5Stat6 := enThread5Stat4 && enThread5Stat5
  enThread5Stat6

/-- `TRT[5].STAT` is written exactly by a host write at `0x244B`. -/
theorem enThread5Stat_spec (w : Bool) (a : BitVec 16) :
    enThread5Stat w a = (w && (a == 0x244B)) := by
  unfold enThread5Stat
  bv_decide

/-- Host write enable of `SRT[0].CTL`. -/
def enStream0Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enStream0Ctl0 := (a - (9311 : BitVec 16))
  let enStream0Ctl1 := (enStream0Ctl0 < (8 : BitVec 16))
  let enStream0Ctl2 := w && enStream0Ctl1
  let enStream0Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 14 (BitVec.ushiftRight enStream0Ctl0 2)))) == (0 : BitVec 16))
  let enStream0Ctl4 := enStream0Ctl2 && enStream0Ctl3
  let enStream0Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight enStream0Ctl0 0)))) == (2 : BitVec 32))
  let enStream0Ctl6 := enStream0Ctl4 && enStream0Ctl5
  enStream0Ctl6

/-- `SRT[0].CTL` is written exactly by a host write at `0x2452`. -/
theorem enStream0Ctl_spec (w : Bool) (a : BitVec 16) :
    enStream0Ctl w a = (w && (a == 0x2452)) := by
  unfold enStream0Ctl
  bv_decide

/-- Host write enable of `SRT[1].CTL`. -/
def enStream1Ctl (w : Bool) (a : BitVec 16) : Bool :=
  let enStream1Ctl0 := (a - (9311 : BitVec 16))
  let enStream1Ctl1 := (enStream1Ctl0 < (8 : BitVec 16))
  let enStream1Ctl2 := w && enStream1Ctl1
  let enStream1Ctl3 := (((BitVec.setWidth 16 (BitVec.truncate 14 (BitVec.ushiftRight enStream1Ctl0 2)))) == (1 : BitVec 16))
  let enStream1Ctl4 := enStream1Ctl2 && enStream1Ctl3
  let enStream1Ctl5 := (((BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight enStream1Ctl0 0)))) == (2 : BitVec 32))
  let enStream1Ctl6 := enStream1Ctl4 && enStream1Ctl5
  enStream1Ctl6

/-- `SRT[1].CTL` is written exactly by a host write at `0x2456`. -/
theorem enStream1Ctl_spec (w : Bool) (a : BitVec 16) :
    enStream1Ctl w a = (w && (a == 0x2456)) := by
  unfold enStream1Ctl
  bv_decide

/-- Host write enable of `DBG.DBG`. -/
def enDbgDbg (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgDbg0 := (a - (9312 : BitVec 16))
  let enDbgDbg1 := (enDbgDbg0 < (32 : BitVec 16))
  let enDbgDbg2 := w && enDbgDbg1
  let enDbgDbg3 := (((BitVec.setWidth 32 enDbgDbg0)) == (0 : BitVec 32))
  let enDbgDbg4 := enDbgDbg2 && enDbgDbg3
  enDbgDbg4

/-- `DBG.DBG` is written exactly by a host write at `0x2460`. -/
theorem enDbgDbg_spec (w : Bool) (a : BitVec 16) :
    enDbgDbg w a = (w && (a == 0x2460)) := by
  unfold enDbgDbg
  bv_decide

/-- Host write enable of `DBG.MCTL`. -/
def enDbgMctl (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgMctl0 := (a - (9312 : BitVec 16))
  let enDbgMctl1 := (enDbgMctl0 < (32 : BitVec 16))
  let enDbgMctl2 := w && enDbgMctl1
  let enDbgMctl3 := (((BitVec.setWidth 32 enDbgMctl0)) == (1 : BitVec 32))
  let enDbgMctl4 := enDbgMctl2 && enDbgMctl3
  enDbgMctl4

/-- `DBG.MCTL` is written exactly by a host write at `0x2461`. -/
theorem enDbgMctl_spec (w : Bool) (a : BitVec 16) :
    enDbgMctl w a = (w && (a == 0x2461)) := by
  unfold enDbgMctl
  bv_decide

/-- Host write enable of `DBG.ECTL`. -/
def enDbgEctl (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgEctl0 := (a - (9312 : BitVec 16))
  let enDbgEctl1 := (enDbgEctl0 < (32 : BitVec 16))
  let enDbgEctl2 := w && enDbgEctl1
  let enDbgEctl3 := (((BitVec.setWidth 32 enDbgEctl0)) == (2 : BitVec 32))
  let enDbgEctl4 := enDbgEctl2 && enDbgEctl3
  enDbgEctl4

/-- `DBG.ECTL` is written exactly by a host write at `0x2462`. -/
theorem enDbgEctl_spec (w : Bool) (a : BitVec 16) :
    enDbgEctl w a = (w && (a == 0x2462)) := by
  unfold enDbgEctl
  bv_decide

/-- Host write enable of `DBG.EMASK low`. -/
def enDbgEmask0 (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgEmask00 := (a - (9312 : BitVec 16))
  let enDbgEmask01 := (enDbgEmask00 < (32 : BitVec 16))
  let enDbgEmask02 := w && enDbgEmask01
  let enDbgEmask03 := (((BitVec.setWidth 32 enDbgEmask00)) == (8 : BitVec 32))
  let enDbgEmask04 := enDbgEmask02 && enDbgEmask03
  enDbgEmask04

/-- `DBG.EMASK low` is written exactly by a host write at `0x2468`. -/
theorem enDbgEmask0_spec (w : Bool) (a : BitVec 16) :
    enDbgEmask0 w a = (w && (a == 0x2468)) := by
  unfold enDbgEmask0
  bv_decide

/-- Host write enable of `DBG.EMASK high`. -/
def enDbgEmask1 (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgEmask10 := (a - (9312 : BitVec 16))
  let enDbgEmask11 := (enDbgEmask10 < (32 : BitVec 16))
  let enDbgEmask12 := w && enDbgEmask11
  let enDbgEmask13 := (((BitVec.setWidth 32 enDbgEmask10)) == (9 : BitVec 32))
  let enDbgEmask14 := enDbgEmask12 && enDbgEmask13
  enDbgEmask14

/-- `DBG.EMASK high` is written exactly by a host write at `0x2469`. -/
theorem enDbgEmask1_spec (w : Bool) (a : BitVec 16) :
    enDbgEmask1 w a = (w && (a == 0x2469)) := by
  unfold enDbgEmask1
  bv_decide

/-- Host write enable of `DBG.RLV low`. -/
def enDbgRlv0 (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgRlv00 := (a - (9312 : BitVec 16))
  let enDbgRlv01 := (enDbgRlv00 < (32 : BitVec 16))
  let enDbgRlv02 := w && enDbgRlv01
  let enDbgRlv03 := (((BitVec.setWidth 32 enDbgRlv00)) == (18 : BitVec 32))
  let enDbgRlv04 := enDbgRlv02 && enDbgRlv03
  enDbgRlv04

/-- `DBG.RLV low` is written exactly by a host write at `0x2472`. -/
theorem enDbgRlv0_spec (w : Bool) (a : BitVec 16) :
    enDbgRlv0 w a = (w && (a == 0x2472)) := by
  unfold enDbgRlv0
  bv_decide

/-- Host write enable of `DBG.RLV high`. -/
def enDbgRlv1 (w : Bool) (a : BitVec 16) : Bool :=
  let enDbgRlv10 := (a - (9312 : BitVec 16))
  let enDbgRlv11 := (enDbgRlv10 < (32 : BitVec 16))
  let enDbgRlv12 := w && enDbgRlv11
  let enDbgRlv13 := (((BitVec.setWidth 32 enDbgRlv10)) == (19 : BitVec 32))
  let enDbgRlv14 := enDbgRlv12 && enDbgRlv13
  enDbgRlv14

/-- `DBG.RLV high` is written exactly by a host write at `0x2473`. -/
theorem enDbgRlv1_spec (w : Bool) (a : BitVec 16) :
    enDbgRlv1 w a = (w && (a == 0x2473)) := by
  unfold enDbgRlv1
  bv_decide

/-- The program-memory core-0 host write strobe. -/
def enProg0 (w : Bool) (a : BitVec 16) : Bool :=
  let enPmWe00 := (a - (0 : BitVec 16))
  let enPmWe01 := (enPmWe00 < (4096 : BitVec 16))
  let enPmWe02 := w && enPmWe01
  let enPmWe03 := !((BitVec.truncate 1 (BitVec.ushiftRight enPmWe00 11)) != 0)
  let enPmWe04 := enPmWe02 && enPmWe03
  enPmWe04

/-- Core 0's program memory is written exactly by a host write in its half
of the program window. -/
theorem enProg0_spec (w : Bool) (a : BitVec 16) :
    enProg0 w a = (w && HostMap.progCore0 a) := by
  unfold enProg0
  simp only [HostMap.progCore0]
  bv_decide

/-- The program-memory core-1 host write strobe. -/
def enProg1 (w : Bool) (a : BitVec 16) : Bool :=
  let enPmWe10 := (a - (0 : BitVec 16))
  let enPmWe11 := (enPmWe10 < (4096 : BitVec 16))
  let enPmWe12 := w && enPmWe11
  let enPmWe13 := enPmWe12 && ((BitVec.truncate 1 (BitVec.ushiftRight enPmWe10 11)) != 0)
  enPmWe13

/-- Core 1's program memory is written exactly by a host write in its half
of the program window. -/
theorem enProg1_spec (w : Bool) (a : BitVec 16) :
    enProg1 w a = (w && HostMap.progCore1 a) := by
  unfold enProg1
  simp only [HostMap.progCore1]
  bv_decide

/-- The data-RAM host set strobe, with the read strobe free. -/
def hSet (w r : Bool) (a : BitVec 16) : Bool :=
  let hSet0 := w || r
  let hSet1 := (a - (4096 : BitVec 16))
  let hSet2 := (hSet1 < (2048 : BitVec 16))
  let hSet3 := hSet0 && hSet2
  hSet3

/-- The host set strobe is `(write | read) & in_data`. -/
theorem hSet_spec (w r : Bool) (a : BitVec 16) :
    hSet w r a = ((w || r) && HostMap.inRegion .data a) := by
  unfold hSet
  simp only [HostMap.inRegion, HostMap.base, HostMap.span]
  bv_decide

/-- The data-RAM host **write** strobe is exactly a host write in the data
window, for either value of the (mutually exclusive) read strobe. -/
theorem dataWe_spec (w r : Bool) (a : BitVec 16) :
    (hSet w r a && w) = (w && HostMap.inRegion .data a) := by
  rw [hSet_spec]
  cases w <;> simp

/-- The data-RAM host write enable, as a member of the uniform enable list. -/
def enData (w : Bool) (a : BitVec 16) : Bool := hSet w true a && w

/-- The data RAM is written exactly by a host write in the data window. -/
theorem enData_spec (w : Bool) (a : BitVec 16) :
    enData w a = (w && HostMap.inRegion .data a) :=
  dataWe_spec w true a

/-- The configuration-window write strobe, with the live-byte mask free. -/
def enCfg (w live : Bool) (a : BitVec 16) : Bool :=
  let enCfg0 := (a - (8192 : BitVec 16))
  let enCfg1 := (enCfg0 < (480 : BitVec 16))
  let enCfg2 := w && enCfg1
  let enCfg3 := enCfg2 && live
  enCfg3

/-- A configuration byte is written exactly by a host write at a live window
address; `cfgSel` keeps the mask decode (the separate address-decode cut)
symbolic. -/
theorem enCfg_spec (w live : Bool) (a : BitVec 16) :
    enCfg w live a = (w && HostMap.cfgSel live a) := by
  unfold enCfg
  simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]
  bv_decide

/-- The program-memory byte-lane select. -/
def pmBe (a : BitVec 16) : BitVec 8 :=
  let pmBe0 := (a - (0 : BitVec 16))
  let pmBe1 := (BitVec.shiftLeft (BitVec.setWidth 8 (1 : BitVec 8)) (((if ((BitVec.truncate 1 (BitVec.ushiftRight pmBe0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (BitVec.shiftLeft (BitVec.setWidth 3 (BitVec.truncate 2 (BitVec.ushiftRight pmBe0 1))) 1))).toNat)
  pmBe1

/-- The byte lane is the one-hot `1 << address[2:0]` of the map's program
offset, so a byte write selects exactly its byte of the 64-bit word. -/
theorem pmBe_spec (a : BitVec 16) :
    pmBe a = HostMap.laneOneHot (HostMap.progLane a) := by
  unfold pmBe
  simp only [HostMap.laneOneHot, HostMap.progLane, HostMap.base]
  bv_decide

/-- The program-memory word address. -/
def rtlProgWord (a : BitVec 16) : BitVec 8 :=
  let progWord0 := (a - (0 : BitVec 16))
  ((if ((BitVec.truncate 1 (BitVec.ushiftRight progWord0 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (BitVec.shiftLeft (BitVec.setWidth 8 (BitVec.truncate 7 (BitVec.ushiftRight progWord0 4))) 1))

/-- The program write addresses the map's word offset `[10:3]`. -/
theorem rtlProgWord_spec (a : BitVec 16) :
    rtlProgWord a = HostMap.progWord a := by
  unfold rtlProgWord
  simp only [HostMap.progWord, HostMap.base]
  bv_decide

/-- The data-RAM host byte address. -/
def rtlDataAddr (a : BitVec 16) : BitVec 11 :=
  let dataAddr0 := (a - (4096 : BitVec 16))
  ((if ((BitVec.truncate 1 (BitVec.ushiftRight dataAddr0 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 11) 0) else (0 : BitVec 11)) ||| (BitVec.shiftLeft (BitVec.setWidth 11 (BitVec.truncate 10 (BitVec.ushiftRight dataAddr0 1))) 1))

/-- The data write addresses the map's offset `[10:0]`. -/
theorem rtlDataAddr_spec (a : BitVec 16) :
    rtlDataAddr a = HostMap.dataAddr a := by
  unfold rtlDataAddr
  simp only [HostMap.dataAddr, HostMap.base]
  bv_decide

/-- Every host write enable of the design, in `HostMap.regAddrs` order. -/
def enables : List (Bool → BitVec 16 → Bool) :=
  [    enCtrlRun,
    enCtrlSticky,
    enCtrlIrqen,
    enCtrlDoorbell,
    enCtrlHostIn,
    enCtrlHostStat,
    enLine0Phase0,
    enLine0Phase1,
    enLine0Ctl,
    enLine0Stat,
    enLine1Phase0,
    enLine1Phase1,
    enLine1Ctl,
    enLine1Stat,
    enLine2Phase0,
    enLine2Phase1,
    enLine2Ctl,
    enLine2Stat,
    enLine3Phase0,
    enLine3Phase1,
    enLine3Ctl,
    enLine3Stat,
    enThread0Pc,
    enThread0Stat,
    enThread1Pc,
    enThread1Stat,
    enThread2Pc,
    enThread2Stat,
    enThread3Pc,
    enThread3Stat,
    enThread4Pc,
    enThread4Stat,
    enThread5Pc,
    enThread5Stat,
    enStream0Ctl,
    enStream1Ctl,
    enDbgDbg,
    enDbgMctl,
    enDbgEctl,
    enDbgEmask0,
    enDbgEmask1,
    enDbgRlv0,
    enDbgRlv1,
    enProg0,
    enProg1,
    enData]

/-- The extracted enable list evaluates to the specification's selection list
with the write strobe applied, then the configuration strobe on the end. -/
theorem enables_snoc_spec (w : Bool) (live : Bool) (a : BitVec 16) :
    enables.map (fun f => f w a) ++ [enCfg w live a] = HostMap.enabledSels live w a := by
  simp [enables, HostMap.enabledSels, HostMap.selList, HostMap.selListRegs,
    HostMap.regAddrs, HostMap.base, HostMap.span, HostMap.progCore0,
    HostMap.progCore1, HostMap.inRegion, HostMap.cfgSel, enCtrlRun_spec, enCtrlSticky_spec, enCtrlIrqen_spec, enCtrlDoorbell_spec, enCtrlHostIn_spec, enCtrlHostStat_spec, enLine0Phase0_spec, enLine0Phase1_spec, enLine0Ctl_spec, enLine0Stat_spec, enLine1Phase0_spec, enLine1Phase1_spec, enLine1Ctl_spec, enLine1Stat_spec, enLine2Phase0_spec, enLine2Phase1_spec, enLine2Ctl_spec, enLine2Stat_spec, enLine3Phase0_spec, enLine3Phase1_spec, enLine3Ctl_spec, enLine3Stat_spec, enThread0Pc_spec, enThread0Stat_spec, enThread1Pc_spec, enThread1Stat_spec, enThread2Pc_spec, enThread2Stat_spec, enThread3Pc_spec, enThread3Stat_spec, enThread4Pc_spec, enThread4Stat_spec, enThread5Pc_spec, enThread5Stat_spec, enStream0Ctl_spec, enStream1Ctl_spec, enDbgDbg_spec, enDbgMctl_spec, enDbgEctl_spec, enDbgEmask0_spec, enDbgEmask1_spec, enDbgRlv0_spec, enDbgRlv1_spec, enProg0_spec, enProg1_spec, enData_spec, enCfg_spec]

/-- **At most one write enable fires per host write**, counting the
configuration-window strobe. -/
theorem at_most_one (w live : Bool) (a : BitVec 16) :
    HostMap.bitCount (enables.map (fun f => f w a) ++ [enCfg w live a]) ≤ 1 := by
  rw [enables_snoc_spec]
  exact HostMap.enabledSels_le_one live w a

/-! ## Read-only and unmapped addresses -/

/-- A host write at `0x2405` (`ctrl hostout`) enables nothing. -/
theorem no_write_2405 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2405) ++ [enCfg w live 0x2405]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2405 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2405 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2407` (`ctrl id`) enables nothing. -/
theorem no_write_2407 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2407) ++ [enCfg w live 0x2407]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2407 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2407 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2408` (`ctrl errsum`) enables nothing. -/
theorem no_write_2408 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2408) ++ [enCfg w live 0x2408]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2408 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2408 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x240F` (`ctrl padding`) enables nothing. -/
theorem no_write_240F (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x240F) ++ [enCfg w live 0x240F]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x240F ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x240F (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2413` (`lrt sym`) enables nothing. -/
theorem no_write_2413 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2413) ++ [enCfg w live 0x2413]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2413 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2413 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2414` (`lrt ins`) enables nothing. -/
theorem no_write_2414 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2414) ++ [enCfg w live 0x2414]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2414 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2414 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2464` (`dbg misr`) enables nothing. -/
theorem no_write_2464 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2464) ++ [enCfg w live 0x2464]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2464 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2464 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2465` (`dbg misr+1`) enables nothing. -/
theorem no_write_2465 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2465) ++ [enCfg w live 0x2465]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2465 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2465 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x246A` (`dbg acc`) enables nothing. -/
theorem no_write_246A (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x246A) ++ [enCfg w live 0x246A]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x246A ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x246A (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x246B` (`dbg aflg`) enables nothing. -/
theorem no_write_246B (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x246B) ++ [enCfg w live 0x246B]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x246B ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x246B (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x246C` (`dbg flags`) enables nothing. -/
theorem no_write_246C (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x246C) ++ [enCfg w live 0x246C]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x246C ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x246C (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x246D` (`dbg flags+1`) enables nothing. -/
theorem no_write_246D (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x246D) ++ [enCfg w live 0x246D]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x246D ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x246D (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2470` (`dbg fpc`) enables nothing. -/
theorem no_write_2470 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2470) ++ [enCfg w live 0x2470]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2470 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2470 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2471` (`dbg fpc+1`) enables nothing. -/
theorem no_write_2471 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2471) ++ [enCfg w live 0x2471]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2471 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2471 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x1800` (`data end`) enables nothing. -/
theorem no_write_1800 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x1800) ++ [enCfg w live 0x1800]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x1800 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x1800 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x1FFF` (`gap below cfg`) enables nothing. -/
theorem no_write_1FFF (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x1FFF) ++ [enCfg w live 0x1FFF]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x1FFF ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x1FFF (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x21E0` (`cfg end`) enables nothing. -/
theorem no_write_21E0 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x21E0) ++ [enCfg w live 0x21E0]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x21E0 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x21E0 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x21FF` (`gap`) enables nothing. -/
theorem no_write_21FF (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x21FF) ++ [enCfg w live 0x21FF]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x21FF ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x21FF (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x2480` (`unmapped`) enables nothing. -/
theorem no_write_2480 (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x2480) ++ [enCfg w live 0x2480]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x2480 ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x2480 (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0x24FF` (`unmapped`) enables nothing. -/
theorem no_write_24FF (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x24FF) ++ [enCfg w live 0x24FF]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x24FF ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x24FF (by simp [HostMap.readOnlyAddrs])
  simpa using h

/-- A host write at `0xFFFF` (`top`) enables nothing. -/
theorem no_write_FFFF (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0xFFFF) ++ [enCfg w live 0xFFFF]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0xFFFF ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0xFFFF (by simp [HostMap.readOnlyAddrs])
  simpa using h


/-! ## Write data -/

/-- The `conflict` sticky-bit next state. -/
def rtlStickyConflict (ev q stk bit : Bool) : Bool :=
  let rtlStickyConflict0 := stk && bit
  let rtlStickyConflict1 := !rtlStickyConflict0
  let rtlStickyConflict2 := q && rtlStickyConflict1
  let rtlStickyConflict3 := ev || rtlStickyConflict2
  rtlStickyConflict3

/-- The `memhaz` sticky-bit next state. -/
def rtlStickyMemhaz (ev q stk bit : Bool) : Bool :=
  let rtlStickyMemhaz0 := stk && bit
  let rtlStickyMemhaz1 := !rtlStickyMemhaz0
  let rtlStickyMemhaz2 := q && rtlStickyMemhaz1
  let rtlStickyMemhaz3 := ev || rtlStickyMemhaz2
  rtlStickyMemhaz3

/-- The `cw_overrun` sticky-bit next state. -/
def rtlStickyOverrun (wd acc q stk bit : Bool) : Bool :=
  let rtlStickyOverrun0 := !acc
  let rtlStickyOverrun1 := wd && rtlStickyOverrun0
  let rtlStickyOverrun2 := stk && bit
  let rtlStickyOverrun3 := !rtlStickyOverrun2
  let rtlStickyOverrun4 := q && rtlStickyOverrun3
  let rtlStickyOverrun5 := rtlStickyOverrun1 || rtlStickyOverrun4
  rtlStickyOverrun5

/-- The doorbell word next state. -/
def rtlDoorbell (wr frz : Bool) (q : BitVec 6) (d : BitVec 8) : BitVec 6 :=
  let rtlDoorbell0 := if wr then (BitVec.truncate 6 (BitVec.ushiftRight d 0)) else (0 : BitVec 6)
  let rtlDoorbell1 := if frz then q else (0 : BitVec 6)
  let rtlDoorbell2 := (rtlDoorbell0 ||| rtlDoorbell1)
  rtlDoorbell2

/-- The `HOSTIN` input-valid flag next state. -/
def rtlInv (wr : Bool) (q rd : Bool) : Bool :=
  let rtlInv0 := (if rd then false else q)
  let rtlInv1 := (if wr then true else rtlInv0)
  rtlInv1

/-- The `HOSTIN` mailbox byte next state. -/
def rtlMailbox (wr : Bool) (q d : BitVec 8) : BitVec 8 :=
  let rtlMailbox0 := if wr then d else q
  rtlMailbox0

/-- The extracted next state is the specification's. -/
theorem rtlStickyConflict_spec (ev q stk bit : Bool) :
    rtlStickyConflict ev q stk bit = HostMap.stickyNext ev q stk bit := by
  simp only [rtlStickyConflict, HostMap.stickyNext] <;> cases ev <;> cases q <;> cases stk <;> cases bit <;> rfl

/-- The extracted next state is the specification's. -/
theorem rtlStickyMemhaz_spec (ev q stk bit : Bool) :
    rtlStickyMemhaz ev q stk bit = HostMap.stickyNext ev q stk bit := by
  simp only [rtlStickyMemhaz, HostMap.stickyNext] <;> cases ev <;> cases q <;> cases stk <;> cases bit <;> rfl

/-- The extracted next state is the specification's. -/
theorem rtlStickyOverrun_spec (wd acc q stk bit : Bool) :
    rtlStickyOverrun wd acc q stk bit = HostMap.stickyNext (wd && !acc) q stk bit := by
  simp only [rtlStickyOverrun, HostMap.stickyNext] <;> cases wd <;> cases acc <;> cases q <;> cases stk <;> cases bit <;> rfl

/-- The extracted next state is the specification's. -/
theorem rtlDoorbell_spec (wr frz : Bool) (q : BitVec 6) (d : BitVec 8) :
    rtlDoorbell wr frz q d = HostMap.doorbellNext wr frz (d.truncate 6) q := by
  simp only [rtlDoorbell, HostMap.doorbellNext]
  bv_decide

/-- The extracted next state is the specification's. -/
theorem rtlInv_spec (wr : Bool) (q rd : Bool) :
    rtlInv wr q rd = HostMap.invNext wr rd q := by
  simp only [rtlInv, HostMap.invNext] <;> cases wr <;> cases rd <;> cases q <;> rfl

/-- The extracted next state is the specification's. -/
theorem rtlMailbox_spec (wr : Bool) (q d : BitVec 8) :
    rtlMailbox wr q d = HostMap.mailboxNext wr d q := by
  simp only [rtlMailbox, HostMap.mailboxNext] <;> cases wr <;> rfl


/-! ## Write data corollaries

The cones above are the flop input logic; these are the documented behaviours,
each with the enable and the free event inputs pinned. -/

/-- A host write of `1` to `CTRL.STICKY` bit 0 clears a quiet `CONFLICT`. -/
theorem sticky_conflict_cleared (q : Bool) :
    rtlStickyConflict false q true true = false := by
  rw [rtlStickyConflict_spec]
  exact sticky_cleared _ _ _ _ rfl rfl rfl

/-- A host write of `1` to `CTRL.STICKY` bit 1 clears a quiet `MEMHAZ`. -/
theorem sticky_memhaz_cleared (q : Bool) :
    rtlStickyMemhaz false q true true = false := by
  rw [rtlStickyMemhaz_spec]
  exact sticky_cleared _ _ _ _ rfl rfl rfl

/-- A host write of `1` to `CTRL.STICKY` bit 2 clears a quiet `CWOVR`. -/
theorem sticky_overrun_cleared (acc q : Bool) :
    rtlStickyOverrun false acc q true true = false := by
  rw [rtlStickyOverrun_spec]
  exact sticky_cleared _ _ _ _ rfl rfl rfl

/-- A host write of `0` to the same bit does not clear the flag. -/
theorem sticky_conflict_held (ev q : Bool) :
    rtlStickyConflict ev q true false = (ev || q) := by
  rw [rtlStickyConflict_spec]
  exact sticky_held _ _ _ _ rfl

/-- A new event sets the flag even when the same write clears it. -/
theorem sticky_conflict_set (q stk bit : Bool) :
    rtlStickyConflict true q stk bit = true := by
  rw [rtlStickyConflict_spec]
  exact sticky_set _ _ _ _ rfl

/-- The doorbell registers the host word for one cycle. -/
theorem doorbell_write_pulse (q : BitVec 6) (d : BitVec 8) :
    rtlDoorbell true false q d = d.truncate 6 := by
  rw [rtlDoorbell_spec]
  exact doorbell_pulse _ _ rfl

/-- Without a write the doorbell word drops to zero in the next cycle. -/
theorem doorbell_write_idle (q : BitVec 6) (d : BitVec 8) :
    rtlDoorbell false false q d = 0 := by
  rw [rtlDoorbell_spec]
  exact doorbell_idle _ _ rfl

/-- A frozen machine holds the doorbell word. -/
theorem doorbell_frozen_hold (q : BitVec 6) (d : BitVec 8) :
    rtlDoorbell false true q d = q := by
  rw [rtlDoorbell_spec]
  exact doorbell_held _ _ rfl

/-- A frozen machine cannot drop a new doorbell word: it is ORed into the
pending one. -/
theorem doorbell_frozen_adds (q : BitVec 6) (d : BitVec 8) :
    rtlDoorbell true true q d = (d.truncate 6 ||| q) := by
  rw [rtlDoorbell_spec]
  exact doorbell_frozen_new _ _ _ rfl

/-- `HOSTIN` sets the input-valid flag. -/
theorem hostin_sets_inv (q rd : Bool) :
    rtlInv true q rd = true := by
  rw [rtlInv_spec]
  exact inv_set _ _

/-- `HOSTIN` loads the mailbox byte. -/
theorem hostin_loads_mailbox (q : BitVec 8) (d : BitVec 8) :
    rtlMailbox true q d = d := by
  rw [rtlMailbox_spec]
  exact mailbox_loaded _ _

/-! ## Axiom audit -/

#print axioms regions_exclusive
#print axioms rtlInProg_spec
#print axioms rtlInData_spec
#print axioms rtlInCfg_spec
#print axioms rtlInCtrl_spec
#print axioms rtlInLrt_spec
#print axioms rtlInTrt_spec
#print axioms rtlInSrt_spec
#print axioms rtlInDbg_spec
#print axioms rtlOffProg_spec
#print axioms rtlOffData_spec
#print axioms rtlOffCfg_spec
#print axioms rtlOffCtrl_spec
#print axioms rtlOffLrt_spec
#print axioms rtlOffTrt_spec
#print axioms rtlOffSrt_spec
#print axioms rtlOffDbg_spec
#print axioms enCtrlRun_spec
#print axioms enCtrlSticky_spec
#print axioms enCtrlIrqen_spec
#print axioms enCtrlDoorbell_spec
#print axioms enCtrlHostIn_spec
#print axioms enCtrlHostStat_spec
#print axioms enLine0Phase0_spec
#print axioms enLine0Phase1_spec
#print axioms enLine0Ctl_spec
#print axioms enLine0Stat_spec
#print axioms enLine1Phase0_spec
#print axioms enLine1Phase1_spec
#print axioms enLine1Ctl_spec
#print axioms enLine1Stat_spec
#print axioms enLine2Phase0_spec
#print axioms enLine2Phase1_spec
#print axioms enLine2Ctl_spec
#print axioms enLine2Stat_spec
#print axioms enLine3Phase0_spec
#print axioms enLine3Phase1_spec
#print axioms enLine3Ctl_spec
#print axioms enLine3Stat_spec
#print axioms enThread0Pc_spec
#print axioms enThread0Stat_spec
#print axioms enThread1Pc_spec
#print axioms enThread1Stat_spec
#print axioms enThread2Pc_spec
#print axioms enThread2Stat_spec
#print axioms enThread3Pc_spec
#print axioms enThread3Stat_spec
#print axioms enThread4Pc_spec
#print axioms enThread4Stat_spec
#print axioms enThread5Pc_spec
#print axioms enThread5Stat_spec
#print axioms enStream0Ctl_spec
#print axioms enStream1Ctl_spec
#print axioms enDbgDbg_spec
#print axioms enDbgMctl_spec
#print axioms enDbgEctl_spec
#print axioms enDbgEmask0_spec
#print axioms enDbgEmask1_spec
#print axioms enDbgRlv0_spec
#print axioms enDbgRlv1_spec
#print axioms hSet_spec
#print axioms dataWe_spec
#print axioms enData_spec
#print axioms enProg0_spec
#print axioms enProg1_spec
#print axioms enCfg_spec
#print axioms pmBe_spec
#print axioms rtlProgWord_spec
#print axioms rtlDataAddr_spec
#print axioms enables_snoc_spec
#print axioms at_most_one
#print axioms no_write_2405
#print axioms no_write_2407
#print axioms no_write_2408
#print axioms no_write_240F
#print axioms no_write_2413
#print axioms no_write_2414
#print axioms no_write_2464
#print axioms no_write_2465
#print axioms no_write_246A
#print axioms no_write_246B
#print axioms no_write_246C
#print axioms no_write_246D
#print axioms no_write_2470
#print axioms no_write_2471
#print axioms no_write_1800
#print axioms no_write_1FFF
#print axioms no_write_21E0
#print axioms no_write_21FF
#print axioms no_write_2480
#print axioms no_write_24FF
#print axioms no_write_FFFF
#print axioms rtlStickyConflict_spec
#print axioms rtlStickyMemhaz_spec
#print axioms rtlStickyOverrun_spec
#print axioms rtlDoorbell_spec
#print axioms rtlInv_spec
#print axioms rtlMailbox_spec
#print axioms sticky_conflict_cleared
#print axioms sticky_memhaz_cleared
#print axioms sticky_overrun_cleared
#print axioms doorbell_write_pulse
#print axioms doorbell_write_idle
#print axioms doorbell_frozen_hold
#print axioms doorbell_frozen_adds
#print axioms hostin_sets_inv
#print axioms hostin_loads_mailbox

end Metronome.HostMapCheck
