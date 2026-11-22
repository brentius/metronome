import Metronome.ChipCut.Discharge.MemHostCfg

open Metronome.ChipCut.Discharge

-- the six `Premises` fields
#print axioms premise_p0
#print axioms premise_hostReq
#print axioms premise_host
#print axioms premise_cw
#print axioms premise_bank
#print axioms premise_contents

-- the two named facts closed in revision c
#print axioms cw_open_hostCfg
#print axioms cw_open_frozen

-- the frozen-cycle chain (D50), one lemma per step
#print axioms hitsMask_zero6
#print axioms gw_frozen
#print axioms cwWord_frozen
#print axioms cqIn_writes_frozen
#print axioms cq_step_frozen
#print axioms coreComb_moves_frozen
#print axioms mhcCwMove_frozen
#print axioms cwNext_frozen_queue
#print axioms frozen_bank_port
#print axioms hostCfgOf_isCfg
#print axioms addrOf_offOf_hostCfg
#print axioms bv16_toNat
#print axioms addrOf_lt

-- pre-existing cw wiring
#print axioms cwNext_st_congr
#print axioms cwNext_abs_bridge
#print axioms mhcHw_bridge
