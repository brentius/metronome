import Metronome.ChipCut.Discharge.HostPinWire

open Metronome.ChipCut.Discharge

-- LineThread.WireAgree fields (W3 scope)
#check @wire_pinAgree
#check @wire_pinLvl
#check @wire_pinPrev
#check @wire_hPhase
#check @wire_hCtl
#check @wire_hTapmissClr
#check @wire_hPC
#check @wire_hStat
#check @wire_beat
-- hcfg of premise_lines
#check @hcfg
-- StreamDbg.DbgWire: host DBG-window byte decode + single-drain exclusivity
#check @dbgWire_hdbg
#check @dbgWire_hESC
#check @dbgWire_hRSC
-- MemHostCfg named facts
#check @hostReq_open_strobe
#check @host_open_quiet
#check @host_open_regVal
-- the new invariant and the named pin-timing premise
#check @HostPinInv
#check @hostPinInv_reset
#check @hostPinInv_step
#check @host_sck_spacing
