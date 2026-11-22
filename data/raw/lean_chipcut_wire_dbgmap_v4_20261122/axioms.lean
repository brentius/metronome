import Metronome.ChipCut.Discharge.DbgMapWire

-- Round 2: leaves under the fixed wiring.
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHEH
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHESH
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHRH
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHRSH
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHEC_false
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHRC_false
-- Round 4: the WV-guarded RLV value (B1's `dbgHwb_of_wv`).
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgRlvValue_of_wv
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgRlvValue_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_value_of_apply
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_value_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbg_wb_of_wv
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbg_bitAt_replayValid
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbg_vget_streams_zero
-- Round 1 leaves that still hold.
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHmctl
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgHectl
-- Round 3: the unconditional value-level fields (restatement proposal).
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgEmaskValue_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.dbgRlvValue_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.emask_value_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_value_of
#check @Metronome.ChipCut.Discharge.DbgMapWire.byteW2_value
-- Round 3: the packaged drain decode (two-lane analogue of machCw_hwByte_ectl).
#check @Metronome.ChipCut.Discharge.DbgMapWire.machCw_emask_lane
#check @Metronome.ChipCut.Discharge.DbgMapWire.machCw_rlv_lane
#check @Metronome.ChipCut.Discharge.DbgMapWire.machCw_runtime
#check @Metronome.ChipCut.Discharge.DbgMapWire.emask_host_01
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_host_01
#check @Metronome.ChipCut.Discharge.DbgMapWire.emask_drain_01
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_drain_01
#check @Metronome.ChipCut.Discharge.DbgMapWire.cwDrain_emask_addr
#check @Metronome.ChipCut.Discharge.DbgMapWire.cwDrain_rlv_addr
#check @Metronome.ChipCut.Discharge.DbgMapWire.emask_drain_imp_C
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_drain_imp_C
-- Round 3: host-decode shape bridges.
#check @Metronome.ChipCut.Discharge.DbgMapWire.emask_hostOpt_eq
#check @Metronome.ChipCut.Discharge.DbgMapWire.rlv_hostOpt_eq
-- Geometry lemmas.
#check @Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_emask0
#check @Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_emask1
#check @Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_rlv0
#check @Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_rlv1
#check @Metronome.ChipCut.Discharge.DbgMapWire.hwAt_two_lane
#check @Metronome.ChipCut.Discharge.DbgMapWire.machCw_hwByte_ectl
#check @Metronome.ChipCut.Discharge.DbgMapWire.wit_coreOpt2_emask_coll
#check @Metronome.ChipCut.Discharge.DbgMapWire.wit_chipRel

#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHEH
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHESH
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHRH
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHRSH
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHEC_false
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHRC_false
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHmctl
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgHectl
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgEmaskValue_of
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgRlvValue_of_wv
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbgRlvValue_of
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.emask_value_of
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_value_of
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_value_of_apply
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbg_wb_of_wv
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.dbg_bitAt_replayValid
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.byteW2_value
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.machCw_emask_lane
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.machCw_rlv_lane
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.machCw_runtime
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.emask_host_01
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_host_01
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.emask_drain_01
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_drain_01
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.cwDrain_emask_addr
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.cwDrain_rlv_addr
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.emask_drain_imp_C
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_drain_imp_C
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.emask_hostOpt_eq
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.rlv_hostOpt_eq
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_emask0
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.hostByteStrobe_rlv1
#print axioms Metronome.ChipCut.Discharge.DbgMapWire.wit_coreOpt2_emask_coll
