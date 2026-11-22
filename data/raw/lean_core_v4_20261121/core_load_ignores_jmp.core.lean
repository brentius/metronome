import Metronome.Core
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 223b371f7b375034ba82bf4254f2d41314c3f8f260e543fce2dc450d5d9f2eeb
-- Two elaborated `md2_core` instances: g_core[0].u_core (C = 0) and
-- g_core[1].u_core (C = 1), NT = 6.  Every register input and every
-- combinational output is a Lean function of the elaborated cells; the free
-- leaves are exactly the module ports bound in `rtlStepOut`.

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Metronome.Core

/-! ## The extracted `g_core[0].u_core` transition (C = false) -/

namespace Rtl0

/-- The elaborated `md2_core` next state and combinational outputs as one
function of the register values and the sampled module ports (the free leaves).
255 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core00 := !input.frz
  let core01 := state.rv && core00
  let core02 := (if input.frz then state.xv else core01)
  let core03 := (if input.resetN then core02 else false)
  let core04 := !input.frz
  let core05 := state.xv && core04
  let core06 := !((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core07 := core05 && core06
  let core08 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core09 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core010 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core011 := (core010 + (0 : BitVec 32))
  let core012 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core011)))
  let core013 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core012 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core012 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core014 := core09 && core013
  let core015 := core08 || core014
  let core016 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core017 := !core013
  let core018 := core016 && core017
  let core019 := core015 || core018
  let core020 := core07 && core019
  let core021 := core020 || core01
  let core022 := core05 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core023 := !state.xv
  let core024 := !state.rv
  let core025 := core023 && core024
  let core026 := !input.frz
  let core027 := core025 && core026
  let core028 := core022 || core027
  let core029 := (~~~input.tCore)
  let core030 := (input.tReady &&& core029)
  let core031 := (if input.runG then core030 else (0 : BitVec 6))
  let core032 := ((((BitVec.truncate 1 (BitVec.ushiftRight core031 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core031 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core031 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core031 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core031 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core031 5)) != 0)))
  let core033 := core028 && core032
  let core034 := core021 || core033
  let core035 := (if input.frz then state.rv else core034)
  let core036 := (if input.resetN then core035 else false)
  let core037 := (state.fpc + (1 : BitVec 8))
  let core038 := ((0 : BitVec 3) >= state.rr)
  let core039 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 0)) != 0) && core038
  let core040 := ((1 : BitVec 3) >= state.rr)
  let core041 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 1)) != 0) && core040
  let core042 := ((2 : BitVec 3) >= state.rr)
  let core043 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 2)) != 0) && core042
  let core044 := ((3 : BitVec 3) >= state.rr)
  let core045 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 3)) != 0) && core044
  let core046 := ((4 : BitVec 3) >= state.rr)
  let core047 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 4)) != 0) && core046
  let core048 := ((5 : BitVec 3) >= state.rr)
  let core049 := ((BitVec.truncate 1 (BitVec.ushiftRight core031 5)) != 0) && core048
  let core050 := ((core039) || (core041) || (core043) || (core045) || (core047) || (core049))
  let core051 := (~~~input.tCore)
  let core052 := (input.tReady &&& core051)
  let core053 := (if input.runG then core052 else (0 : BitVec 6))
  let core054 := if core050 then ((if core039 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core041 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core043 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core045 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core047 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core049 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core053
  let core055 := ((BitVec.truncate 1 (BitVec.ushiftRight core054 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core054 1)) != 0)
  let core056 := core055 || ((BitVec.truncate 1 (BitVec.ushiftRight core054 2)) != 0)
  let core057 := core056 || ((BitVec.truncate 1 (BitVec.ushiftRight core054 3)) != 0)
  let core058 := core057 || ((BitVec.truncate 1 (BitVec.ushiftRight core054 4)) != 0)
  let core059 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core054 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core055 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core056 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core057 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core058 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core060 := (core054 &&& core059)
  let core061 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core062 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core063 := (core061 ||| core062)
  let core064 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core065 := (core063 ||| core064)
  let core066 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core067 := (core065 ||| core066)
  let core068 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core069 := (core067 ||| core068)
  let core070 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core071 := (core069 ||| core070)
  let core072 := ((((BitVec.truncate 1 (BitVec.ushiftRight core071 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core071 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core071 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core071 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core071 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core071 5)) != 0)))
  let core073 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core074 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core075 := (core073 ||| core074)
  let core076 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core077 := (core075 ||| core076)
  let core078 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core079 := (core077 ||| core078)
  let core080 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core081 := (core079 ||| core080)
  let core082 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core083 := (core081 ||| core082)
  let core084 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core083))
  let core085 := (core084 + (0 : BitVec 32))
  let core086 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core085)))
  let core087 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core088 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core089 := (core087 ||| core088)
  let core090 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core091 := (core089 ||| core090)
  let core092 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core093 := (core091 ||| core092)
  let core094 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core095 := (core093 ||| core094)
  let core096 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core097 := (core095 ||| core096)
  let core098 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core086) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core097))) != 0)
  let core099 := core072 && core098
  let core0100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core0101 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core0102 := (core0100 ||| core0101)
  let core0103 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core0104 := (core0102 ||| core0103)
  let core0105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core0106 := (core0104 ||| core0105)
  let core0107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core0108 := (core0106 ||| core0107)
  let core0109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core0110 := (core0108 ||| core0109)
  let core0111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0112 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0113 := (core0111 ||| core0112)
  let core0114 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0115 := (core0113 ||| core0114)
  let core0116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0117 := (core0115 ||| core0116)
  let core0118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0119 := (core0117 ||| core0118)
  let core0120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0121 := (core0119 ||| core0120)
  let core0122 := ((((BitVec.truncate 1 (BitVec.ushiftRight core0121 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0121 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0121 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0121 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0121 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0121 5)) != 0)))
  let core0123 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core085)))
  let core0124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0125 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0126 := (core0124 ||| core0125)
  let core0127 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0128 := (core0126 ||| core0127)
  let core0129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0130 := (core0128 ||| core0129)
  let core0131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0132 := (core0130 ||| core0131)
  let core0133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0134 := (core0132 ||| core0133)
  let core0135 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0123) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0134))) != 0)
  let core0136 := core0122 && core0135
  let core0137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core0138 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core0139 := (core0137 ||| core0138)
  let core0140 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core0141 := (core0139 ||| core0140)
  let core0142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core0143 := (core0141 ||| core0142)
  let core0144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core0145 := (core0143 ||| core0144)
  let core0146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core0147 := (core0145 ||| core0146)
  let core0148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core0149 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core0150 := (core0148 ||| core0149)
  let core0151 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core0152 := (core0150 ||| core0151)
  let core0153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core0154 := (core0152 ||| core0153)
  let core0155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core0156 := (core0154 ||| core0155)
  let core0157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core0158 := (core0156 ||| core0157)
  let core0159 := if core0136 then core0147 else core0158
  let core0160 := if core099 then core0110 else core0159
  let core0161 := if core01 then core037 else core0160
  let core0162 := if core020 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core0161
  let core0163 := if core034 then core0162 else state.fpc
  let core0164 := if input.frz then state.fpc else core0163
  let core0165 := if input.resetN then core0164 else (0 : BitVec 8)
  let core0166 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0167 := (core0166 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0168 := (core0167 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0169 := (core0168 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0170 := if core033 then core0169 else state.xt
  let core0171 := if input.frz then state.xt else core0170
  let core0172 := if input.resetN then core0171 else (0 : BitVec 3)
  let core0173 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core0174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core0175 := (core0173 ||| core0174)
  let core0176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core0177 := (core0175 ||| core0176)
  let core0178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core0179 := (core0177 ||| core0178)
  let core0180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core0181 := (core0179 ||| core0180)
  let core0182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core0183 := (core0181 ||| core0182)
  let core0184 := if core033 then core0183 else state.xl
  let core0185 := if input.frz then state.xl else core0184
  let core0186 := if input.resetN then core0185 else (0 : BitVec 2)
  let core0187 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0188 := (core0187 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0189 := (core0188 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0190 := (core0189 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0191 := (core0190 == (5 : BitVec 3))
  let core0192 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0193 := (core0192 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0194 := (core0193 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0195 := (core0194 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0196 := (core0195 + (1 : BitVec 3))
  let core0197 := if core0191 then (0 : BitVec 3) else core0196
  let core0198 := if core033 then core0197 else state.rr
  let core0199 := if input.frz then state.rr else core0198
  let core0200 := if input.resetN then core0199 else (0 : BitVec 3)
  let core0201 := if input.frz then state.ir else input.rdata
  let core0202 := if core019 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core0203 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0204 := (core0203 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0205 := (core0204 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0206 := (core0205 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core060 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0207 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core0208 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core0209 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core011)))
  let core0210 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0209) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core0211 := core0208 && core0210
  let core0212 := core0207 || core0211
  let core0213 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core0214 := !core0210
  let core0215 := core0213 && core0214
  let core0216 := core0212 || core0215
  let core0217 := core05 && core0216
  let core0218 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core0219 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core0220 := core0219 && core0210
  let core0221 := core0218 || core0220
  let core0222 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core0223 := !core0210
  let core0224 := core0222 && core0223
  let core0225 := core0221 || core0224
  let core0226 := core05 && core0225
  let core0227 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core0228 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core0229 := core0228 && core0210
  let core0230 := core0227 || core0229
  let core0231 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core0232 := !core0210
  let core0233 := core0231 && core0232
  let core0234 := core0230 || core0233
  let core0235 := core05 && core0234
  let core0236 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0237 := (core0236 + (0 : BitVec 32))
  let core0238 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0237)))
  let core0239 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0240 := (core0239 + (0 : BitVec 32))
  let core0241 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0240)))
  let core0242 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core0243 := (core0242 + (0 : BitVec 32))
  let core0244 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0238) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0241) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0243)))
  let core0245 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0237)))
  let core0246 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0240)))
  let core0247 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core0248 := (core0247 + (0 : BitVec 32))
  let core0249 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0245) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0246) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0248)))
  let core0250 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0237)))
  let core0251 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0240)))
  let core0252 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core0253 := (core0252 + (0 : BitVec 32))
  let core0254 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0250) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0251) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0253)))
  (⟨core03, core036, core0165, core0172, core0186, core0200, core0201⟩, ⟨core034, core0162, core022, core0202, core033, core0206, state.xt, state.xl, ((if core0217 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core0226 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core0235 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core0244) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0249) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0254) 16)), state.xv, state.rv, state.fpc⟩)

/-- The elaborated next state. -/
def rtlStep (state : State) (input : Input) : State := (rtlStepOut state input).1

/-- The elaborated combinational outputs. -/
def rtlOut (state : State) (input : Input) : Out := (rtlStepOut state input).2

/-- Unfold the extracted transition and the specification to their `BitVec`
primitives. -/
macro "core_simp" : tactic =>
  `(tactic| simp only [rtlStep, rtlStepOut, rtlOut, out, step, next,
      xv_next, rv_next, fpc_next, xt_next, xl_next, rr_next, ir_next,
      load, ra, jmp, pse, xa, free, taken, cc, jc, npc,
      guardVec, lineSlot, lowMask, setBit, bitOf, slice,
      srcVec, withSlot, srcByte, jumpGuardBit,
      cand, mine, winOf, selIdx, selSlot, disp, dispE, dLine, dPc, dW0c, dW1c,
      dW0h, dW1h, watcher0, watcher1, dpc, fetchAddr, fetchEn, rrNext,
      i_pause, i_jmode, i_imm, i_cond, i_jcond, i_g, i_s, i_d,
      mvEnAt, moveGuardOk, boolMask,
      G_TRUE, G_L_IN0, G_L_IN1, G_L_SYNC, G_L_PINA, G_L_PINB,
      MD_N_GUARD, MD_N_SRC, S_ZERO, S_IMM, S_L_IN, S_L_CAP,
      JM_ALWAYS, JM_IF, JM_IFNOT, GD_ALWAYS, GD_IF, GD_IFNOT,
      LAST_T, N_THREADS])

macro "core_proof" : tactic => `(tactic| core_simp <;> bv_decide)

/-! ### Registers (§5: `XV'`, `RV'`, `FPC'`, `IR'`, `XT'`, `XL'`, `RR'`) -/

theorem rtlXv (state : State) (input : Input) :
    (rtlStep state input).xv = (step false state input).xv := by core_proof

theorem rtlRv (state : State) (input : Input) :
    (rtlStep state input).rv = (step false state input).rv := by core_proof

theorem rtlFpc (state : State) (input : Input) :
    (rtlStep state input).fpc = (step false state input).fpc := by core_proof

theorem rtlXt (state : State) (input : Input) :
    (rtlStep state input).xt = (step false state input).xt := by core_proof

theorem rtlXl (state : State) (input : Input) :
    (rtlStep state input).xl = (step false state input).xl := by core_proof

theorem rtlRr (state : State) (input : Input) :
    (rtlStep state input).rr = (step false state input).rr := by core_proof

theorem rtlIr (state : State) (input : Input) :
    (rtlStep state input).ir = (step false state input).ir := by core_proof

/-- The extracted transition is the independent SPEC_V2 §5/§6/§7/§12.3
transition for every state and input. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step false state input := by
  have h1 : rtlStep state input =
      ⟨(rtlStep state input).xv, (rtlStep state input).rv, (rtlStep state input).fpc,
       (rtlStep state input).xt, (rtlStep state input).xl, (rtlStep state input).rr,
       (rtlStep state input).ir⟩ := rfl
  have h2 : step false state input =
      ⟨(step false state input).xv, (step false state input).rv,
       (step false state input).fpc, (step false state input).xt,
       (step false state input).xl, (step false state input).rr,
       (step false state input).ir⟩ := rfl
  rw [h1, h2, rtlXv, rtlRv, rtlFpc, rtlXt, rtlXl, rtlRr, rtlIr]

/-! ### Outputs (§5: fetch, pause, dispatch, watchers, moves; §12.3 readback) -/

theorem rtlFetchEn (state : State) (input : Input) :
    (rtlOut state input).fetchEn = (out false state input).fetchEn := by core_proof

theorem rtlFetchAddr (state : State) (input : Input) :
    (rtlOut state input).fetchAddr = (out false state input).fetchAddr := by core_proof

theorem rtlPause (state : State) (input : Input) :
    (rtlOut state input).pauseO = (out false state input).pauseO := by core_proof

theorem rtlNpc (state : State) (input : Input) :
    (rtlOut state input).npcO = (out false state input).npcO := by core_proof

theorem rtlDisp (state : State) (input : Input) :
    (rtlOut state input).dispO = (out false state input).dispO := by core_proof

theorem rtlDispE (state : State) (input : Input) :
    (rtlOut state input).dispE = (out false state input).dispE := by core_proof

theorem rtlXtO (state : State) (input : Input) :
    (rtlOut state input).xtO = (out false state input).xtO := by core_proof

theorem rtlXlO (state : State) (input : Input) :
    (rtlOut state input).xlO = (out false state input).xlO := by core_proof

theorem rtlMvEn (state : State) (input : Input) :
    (rtlOut state input).mvEn = (out false state input).mvEn := by core_proof

theorem rtlMvSrc (state : State) (input : Input) :
    (rtlOut state input).mvSrc = (out false state input).mvSrc := by core_proof

theorem rtlMvDst (state : State) (input : Input) :
    (rtlOut state input).mvDst = (out false state input).mvDst := by core_proof

theorem rtlMvData (state : State) (input : Input) :
    (rtlOut state input).mvData = (out false state input).mvData := by core_proof

/-- §12.3 readback: `CST.RV`, `CST.XV` and `FPC` are the state registers. -/
theorem rtlDbg (state : State) (input : Input) :
    (rtlOut state input).dbgXv = (out false state input).dbgXv ∧
      (rtlOut state input).dbgRv = (out false state input).dbgRv ∧
      (rtlOut state input).dbgFpc = (out false state input).dbgFpc := by
  simp [rtlOut, rtlStepOut, out]

/-- The extracted outputs are the specification's outputs. -/
theorem rtlOut_eq_out (state : State) (input : Input) :
    rtlOut state input = out false state input := by
  obtain ⟨hdxv, hdrv, hdfpc⟩ := rtlDbg state input
  have h1 : rtlOut state input =
      ⟨(rtlOut state input).fetchEn, (rtlOut state input).fetchAddr,
       (rtlOut state input).pauseO, (rtlOut state input).npcO, (rtlOut state input).dispO,
       (rtlOut state input).dispE, (rtlOut state input).xtO, (rtlOut state input).xlO,
       (rtlOut state input).mvEn, (rtlOut state input).mvSrc, (rtlOut state input).mvDst,
       (rtlOut state input).mvData, (rtlOut state input).dbgXv,
       (rtlOut state input).dbgRv, (rtlOut state input).dbgFpc⟩ := rfl
  have h2 : out false state input =
      ⟨(out false state input).fetchEn, (out false state input).fetchAddr,
       (out false state input).pauseO, (out false state input).npcO,
       (out false state input).dispO, (out false state input).dispE,
       (out false state input).xtO, (out false state input).xlO,
       (out false state input).mvEn, (out false state input).mvSrc,
       (out false state input).mvDst, (out false state input).mvData,
       (out false state input).dbgXv, (out false state input).dbgRv,
       (out false state input).dbgFpc⟩ := rfl
  rw [h1, h2, rtlFetchEn, rtlFetchAddr, rtlPause, rtlNpc, rtlDisp, rtlDispE,
    rtlXtO, rtlXlO, rtlMvEn, rtlMvSrc, rtlMvDst, rtlMvData, hdxv, hdrv, hdfpc]

/-! ### Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

/-- The extracted trace is the specification trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt false inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step false (stateAt false inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-- SPEC §5 "Consequences" (`t + 3`) on the extracted trace. -/
theorem rtl_trace_dispatch_idle (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (rtlStateAt inputs initial n).xv = false)
    (hrv : (rtlStateAt inputs initial n).rv = false)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hcand : cand false (inputs n) ≠ 0)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).rv = true ∧
      (rtlStateAt inputs initial (n + 1)).xv = false ∧
      (rtlStateAt inputs initial (n + 1)).fpc =
        dpc false (rtlStateAt inputs initial n) (inputs n) ∧
      (rtlStateAt inputs initial (n + 2)).xv = true ∧
      (rtlStateAt inputs initial (n + 2)).fpc =
        dpc false (rtlStateAt inputs initial n) (inputs n) + 1 ∧
      (rtlStateAt inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  simp only [rtlStateAt_eq] at hxv hrv ⊢
  exact trace_dispatch_idle false inputs initial n hxv hrv hfrz hreset hcand hfrz1 hreset1

/-- SPEC §5 "Consequences" (taken jump, one idle cycle) on the extracted trace. -/
theorem rtl_trace_jump_idle (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (rtlStateAt inputs initial n).xv = true)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hjmp : jmp (rtlStateAt inputs initial n) (inputs n) = true)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).xv = false ∧
      (rtlStateAt inputs initial (n + 1)).rv = true ∧
      (rtlStateAt inputs initial (n + 1)).fpc =
        i_imm (rtlStateAt inputs initial n) ∧
      (rtlStateAt inputs initial (n + 2)).xv = true ∧
      (rtlStateAt inputs initial (n + 2)).fpc =
        i_imm (rtlStateAt inputs initial n) + 1 ∧
      (rtlStateAt inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  simp only [rtlStateAt_eq] at hxv hjmp ⊢
  exact trace_jump_idle false inputs initial n hxv hfrz hreset hjmp hfrz1 hreset1

/-! ### Axiom audit

`core_check.py` records these records and rejects `sorryAx`.  The per-field
equalities are `bv_decide` goals; the shared lemmas use `decide` over the six
threads. -/

#print axioms rtlStep_eq_step
#print axioms rtlOut_eq_out
#print axioms rtlStateAt_eq
#print axioms rtl_trace_result
#print axioms rtl_trace_dispatch_idle
#print axioms rtl_trace_jump_idle

end Rtl0

/-! ## The extracted `g_core[1].u_core` transition (C = true) -/

namespace Rtl1

/-- The elaborated `md2_core` next state and combinational outputs as one
function of the register values and the sampled module ports (the free leaves).
253 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core10 := !input.frz
  let core11 := state.rv && core10
  let core12 := (if input.frz then state.xv else core11)
  let core13 := (if input.resetN then core12 else false)
  let core14 := !input.frz
  let core15 := state.xv && core14
  let core16 := !((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core17 := core15 && core16
  let core18 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core19 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core110 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core111 := (core110 + (0 : BitVec 32))
  let core112 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core111)))
  let core113 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core112 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core112 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core114 := core19 && core113
  let core115 := core18 || core114
  let core116 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core117 := !core113
  let core118 := core116 && core117
  let core119 := core115 || core118
  let core120 := core17 && core119
  let core121 := core120 || core11
  let core122 := core15 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core123 := !state.xv
  let core124 := !state.rv
  let core125 := core123 && core124
  let core126 := !input.frz
  let core127 := core125 && core126
  let core128 := core122 || core127
  let core129 := (input.tReady &&& input.tCore)
  let core130 := (if input.runG then core129 else (0 : BitVec 6))
  let core131 := ((((BitVec.truncate 1 (BitVec.ushiftRight core130 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core130 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core130 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core130 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core130 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core130 5)) != 0)))
  let core132 := core128 && core131
  let core133 := core121 || core132
  let core134 := (if input.frz then state.rv else core133)
  let core135 := (if input.resetN then core134 else false)
  let core136 := (state.fpc + (1 : BitVec 8))
  let core137 := ((0 : BitVec 3) >= state.rr)
  let core138 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 0)) != 0) && core137
  let core139 := ((1 : BitVec 3) >= state.rr)
  let core140 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 1)) != 0) && core139
  let core141 := ((2 : BitVec 3) >= state.rr)
  let core142 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 2)) != 0) && core141
  let core143 := ((3 : BitVec 3) >= state.rr)
  let core144 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 3)) != 0) && core143
  let core145 := ((4 : BitVec 3) >= state.rr)
  let core146 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 4)) != 0) && core145
  let core147 := ((5 : BitVec 3) >= state.rr)
  let core148 := ((BitVec.truncate 1 (BitVec.ushiftRight core130 5)) != 0) && core147
  let core149 := ((core138) || (core140) || (core142) || (core144) || (core146) || (core148))
  let core150 := (input.tReady &&& input.tCore)
  let core151 := (if input.runG then core150 else (0 : BitVec 6))
  let core152 := if core149 then ((if core138 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core140 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core142 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core144 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core146 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core148 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core151
  let core153 := ((BitVec.truncate 1 (BitVec.ushiftRight core152 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core152 1)) != 0)
  let core154 := core153 || ((BitVec.truncate 1 (BitVec.ushiftRight core152 2)) != 0)
  let core155 := core154 || ((BitVec.truncate 1 (BitVec.ushiftRight core152 3)) != 0)
  let core156 := core155 || ((BitVec.truncate 1 (BitVec.ushiftRight core152 4)) != 0)
  let core157 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core152 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core153 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core154 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core155 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core156 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core158 := (core152 &&& core157)
  let core159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core160 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core161 := (core159 ||| core160)
  let core162 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core163 := (core161 ||| core162)
  let core164 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core165 := (core163 ||| core164)
  let core166 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core167 := (core165 ||| core166)
  let core168 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core169 := (core167 ||| core168)
  let core170 := ((((BitVec.truncate 1 (BitVec.ushiftRight core169 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core169 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core169 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core169 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core169 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core169 5)) != 0)))
  let core171 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core172 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core173 := (core171 ||| core172)
  let core174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core175 := (core173 ||| core174)
  let core176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core177 := (core175 ||| core176)
  let core178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core179 := (core177 ||| core178)
  let core180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core181 := (core179 ||| core180)
  let core182 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core181))
  let core183 := (core182 + (0 : BitVec 32))
  let core184 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core183)))
  let core185 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core187 := (core185 ||| core186)
  let core188 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core189 := (core187 ||| core188)
  let core190 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core191 := (core189 ||| core190)
  let core192 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core193 := (core191 ||| core192)
  let core194 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core195 := (core193 ||| core194)
  let core196 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core184) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core195))) != 0)
  let core197 := core170 && core196
  let core198 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core199 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core1100 := (core198 ||| core199)
  let core1101 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core1102 := (core1100 ||| core1101)
  let core1103 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core1104 := (core1102 ||| core1103)
  let core1105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core1106 := (core1104 ||| core1105)
  let core1107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core1108 := (core1106 ||| core1107)
  let core1109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1110 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1111 := (core1109 ||| core1110)
  let core1112 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1113 := (core1111 ||| core1112)
  let core1114 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1115 := (core1113 ||| core1114)
  let core1116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1117 := (core1115 ||| core1116)
  let core1118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1119 := (core1117 ||| core1118)
  let core1120 := ((((BitVec.truncate 1 (BitVec.ushiftRight core1119 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1119 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1119 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1119 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1119 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1119 5)) != 0)))
  let core1121 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core183)))
  let core1122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1123 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1124 := (core1122 ||| core1123)
  let core1125 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1126 := (core1124 ||| core1125)
  let core1127 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1128 := (core1126 ||| core1127)
  let core1129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1130 := (core1128 ||| core1129)
  let core1131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1132 := (core1130 ||| core1131)
  let core1133 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1121) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1132))) != 0)
  let core1134 := core1120 && core1133
  let core1135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core1136 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core1137 := (core1135 ||| core1136)
  let core1138 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core1139 := (core1137 ||| core1138)
  let core1140 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core1141 := (core1139 ||| core1140)
  let core1142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core1143 := (core1141 ||| core1142)
  let core1144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core1145 := (core1143 ||| core1144)
  let core1146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core1147 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core1148 := (core1146 ||| core1147)
  let core1149 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core1150 := (core1148 ||| core1149)
  let core1151 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core1152 := (core1150 ||| core1151)
  let core1153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core1154 := (core1152 ||| core1153)
  let core1155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core1156 := (core1154 ||| core1155)
  let core1157 := if core1134 then core1145 else core1156
  let core1158 := if core197 then core1108 else core1157
  let core1159 := if core11 then core136 else core1158
  let core1160 := if core120 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core1159
  let core1161 := if core133 then core1160 else state.fpc
  let core1162 := if input.frz then state.fpc else core1161
  let core1163 := if input.resetN then core1162 else (0 : BitVec 8)
  let core1164 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1165 := (core1164 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1166 := (core1165 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1167 := (core1166 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1168 := if core132 then core1167 else state.xt
  let core1169 := if input.frz then state.xt else core1168
  let core1170 := if input.resetN then core1169 else (0 : BitVec 3)
  let core1171 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core1172 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core1173 := (core1171 ||| core1172)
  let core1174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core1175 := (core1173 ||| core1174)
  let core1176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core1177 := (core1175 ||| core1176)
  let core1178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core1179 := (core1177 ||| core1178)
  let core1180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core1181 := (core1179 ||| core1180)
  let core1182 := if core132 then core1181 else state.xl
  let core1183 := if input.frz then state.xl else core1182
  let core1184 := if input.resetN then core1183 else (0 : BitVec 2)
  let core1185 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1186 := (core1185 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1187 := (core1186 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1188 := (core1187 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1189 := (core1188 == (5 : BitVec 3))
  let core1190 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1191 := (core1190 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1192 := (core1191 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1193 := (core1192 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1194 := (core1193 + (1 : BitVec 3))
  let core1195 := if core1189 then (0 : BitVec 3) else core1194
  let core1196 := if core132 then core1195 else state.rr
  let core1197 := if input.frz then state.rr else core1196
  let core1198 := if input.resetN then core1197 else (0 : BitVec 3)
  let core1199 := if input.frz then state.ir else input.rdata
  let core1200 := if core119 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core1201 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1202 := (core1201 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1203 := (core1202 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1204 := (core1203 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core158 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1205 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core1206 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core1207 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core111)))
  let core1208 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1207) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core1209 := core1206 && core1208
  let core1210 := core1205 || core1209
  let core1211 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core1212 := !core1208
  let core1213 := core1211 && core1212
  let core1214 := core1210 || core1213
  let core1215 := core15 && core1214
  let core1216 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core1217 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core1218 := core1217 && core1208
  let core1219 := core1216 || core1218
  let core1220 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core1221 := !core1208
  let core1222 := core1220 && core1221
  let core1223 := core1219 || core1222
  let core1224 := core15 && core1223
  let core1225 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core1226 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core1227 := core1226 && core1208
  let core1228 := core1225 || core1227
  let core1229 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core1230 := !core1208
  let core1231 := core1229 && core1230
  let core1232 := core1228 || core1231
  let core1233 := core15 && core1232
  let core1234 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1235 := (core1234 + (0 : BitVec 32))
  let core1236 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1235)))
  let core1237 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1238 := (core1237 + (0 : BitVec 32))
  let core1239 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1238)))
  let core1240 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core1241 := (core1240 + (0 : BitVec 32))
  let core1242 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1236) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1239) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1241)))
  let core1243 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1235)))
  let core1244 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1238)))
  let core1245 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core1246 := (core1245 + (0 : BitVec 32))
  let core1247 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1243) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1244) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1246)))
  let core1248 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1235)))
  let core1249 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1238)))
  let core1250 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core1251 := (core1250 + (0 : BitVec 32))
  let core1252 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1248) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1249) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1251)))
  (⟨core13, core135, core1163, core1170, core1184, core1198, core1199⟩, ⟨core133, core1160, core122, core1200, core132, core1204, state.xt, state.xl, ((if core1215 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core1224 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core1233 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core1242) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1247) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1252) 16)), state.xv, state.rv, state.fpc⟩)

/-- The elaborated next state. -/
def rtlStep (state : State) (input : Input) : State := (rtlStepOut state input).1

/-- The elaborated combinational outputs. -/
def rtlOut (state : State) (input : Input) : Out := (rtlStepOut state input).2

/-- Unfold the extracted transition and the specification to their `BitVec`
primitives. -/
macro "core_simp" : tactic =>
  `(tactic| simp only [rtlStep, rtlStepOut, rtlOut, out, step, next,
      xv_next, rv_next, fpc_next, xt_next, xl_next, rr_next, ir_next,
      load, ra, jmp, pse, xa, free, taken, cc, jc, npc,
      guardVec, lineSlot, lowMask, setBit, bitOf, slice,
      srcVec, withSlot, srcByte, jumpGuardBit,
      cand, mine, winOf, selIdx, selSlot, disp, dispE, dLine, dPc, dW0c, dW1c,
      dW0h, dW1h, watcher0, watcher1, dpc, fetchAddr, fetchEn, rrNext,
      i_pause, i_jmode, i_imm, i_cond, i_jcond, i_g, i_s, i_d,
      mvEnAt, moveGuardOk, boolMask,
      G_TRUE, G_L_IN0, G_L_IN1, G_L_SYNC, G_L_PINA, G_L_PINB,
      MD_N_GUARD, MD_N_SRC, S_ZERO, S_IMM, S_L_IN, S_L_CAP,
      JM_ALWAYS, JM_IF, JM_IFNOT, GD_ALWAYS, GD_IF, GD_IFNOT,
      LAST_T, N_THREADS])

macro "core_proof" : tactic => `(tactic| core_simp <;> bv_decide)

/-! ### Registers (§5: `XV'`, `RV'`, `FPC'`, `IR'`, `XT'`, `XL'`, `RR'`) -/

theorem rtlXv (state : State) (input : Input) :
    (rtlStep state input).xv = (step true state input).xv := by core_proof

theorem rtlRv (state : State) (input : Input) :
    (rtlStep state input).rv = (step true state input).rv := by core_proof

theorem rtlFpc (state : State) (input : Input) :
    (rtlStep state input).fpc = (step true state input).fpc := by core_proof

theorem rtlXt (state : State) (input : Input) :
    (rtlStep state input).xt = (step true state input).xt := by core_proof

theorem rtlXl (state : State) (input : Input) :
    (rtlStep state input).xl = (step true state input).xl := by core_proof

theorem rtlRr (state : State) (input : Input) :
    (rtlStep state input).rr = (step true state input).rr := by core_proof

theorem rtlIr (state : State) (input : Input) :
    (rtlStep state input).ir = (step true state input).ir := by core_proof

/-- The extracted transition is the independent SPEC_V2 §5/§6/§7/§12.3
transition for every state and input. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step true state input := by
  have h1 : rtlStep state input =
      ⟨(rtlStep state input).xv, (rtlStep state input).rv, (rtlStep state input).fpc,
       (rtlStep state input).xt, (rtlStep state input).xl, (rtlStep state input).rr,
       (rtlStep state input).ir⟩ := rfl
  have h2 : step true state input =
      ⟨(step true state input).xv, (step true state input).rv,
       (step true state input).fpc, (step true state input).xt,
       (step true state input).xl, (step true state input).rr,
       (step true state input).ir⟩ := rfl
  rw [h1, h2, rtlXv, rtlRv, rtlFpc, rtlXt, rtlXl, rtlRr, rtlIr]

/-! ### Outputs (§5: fetch, pause, dispatch, watchers, moves; §12.3 readback) -/

theorem rtlFetchEn (state : State) (input : Input) :
    (rtlOut state input).fetchEn = (out true state input).fetchEn := by core_proof

theorem rtlFetchAddr (state : State) (input : Input) :
    (rtlOut state input).fetchAddr = (out true state input).fetchAddr := by core_proof

theorem rtlPause (state : State) (input : Input) :
    (rtlOut state input).pauseO = (out true state input).pauseO := by core_proof

theorem rtlNpc (state : State) (input : Input) :
    (rtlOut state input).npcO = (out true state input).npcO := by core_proof

theorem rtlDisp (state : State) (input : Input) :
    (rtlOut state input).dispO = (out true state input).dispO := by core_proof

theorem rtlDispE (state : State) (input : Input) :
    (rtlOut state input).dispE = (out true state input).dispE := by core_proof

theorem rtlXtO (state : State) (input : Input) :
    (rtlOut state input).xtO = (out true state input).xtO := by core_proof

theorem rtlXlO (state : State) (input : Input) :
    (rtlOut state input).xlO = (out true state input).xlO := by core_proof

theorem rtlMvEn (state : State) (input : Input) :
    (rtlOut state input).mvEn = (out true state input).mvEn := by core_proof

theorem rtlMvSrc (state : State) (input : Input) :
    (rtlOut state input).mvSrc = (out true state input).mvSrc := by core_proof

theorem rtlMvDst (state : State) (input : Input) :
    (rtlOut state input).mvDst = (out true state input).mvDst := by core_proof

theorem rtlMvData (state : State) (input : Input) :
    (rtlOut state input).mvData = (out true state input).mvData := by core_proof

/-- §12.3 readback: `CST.RV`, `CST.XV` and `FPC` are the state registers. -/
theorem rtlDbg (state : State) (input : Input) :
    (rtlOut state input).dbgXv = (out true state input).dbgXv ∧
      (rtlOut state input).dbgRv = (out true state input).dbgRv ∧
      (rtlOut state input).dbgFpc = (out true state input).dbgFpc := by
  simp [rtlOut, rtlStepOut, out]

/-- The extracted outputs are the specification's outputs. -/
theorem rtlOut_eq_out (state : State) (input : Input) :
    rtlOut state input = out true state input := by
  obtain ⟨hdxv, hdrv, hdfpc⟩ := rtlDbg state input
  have h1 : rtlOut state input =
      ⟨(rtlOut state input).fetchEn, (rtlOut state input).fetchAddr,
       (rtlOut state input).pauseO, (rtlOut state input).npcO, (rtlOut state input).dispO,
       (rtlOut state input).dispE, (rtlOut state input).xtO, (rtlOut state input).xlO,
       (rtlOut state input).mvEn, (rtlOut state input).mvSrc, (rtlOut state input).mvDst,
       (rtlOut state input).mvData, (rtlOut state input).dbgXv,
       (rtlOut state input).dbgRv, (rtlOut state input).dbgFpc⟩ := rfl
  have h2 : out true state input =
      ⟨(out true state input).fetchEn, (out true state input).fetchAddr,
       (out true state input).pauseO, (out true state input).npcO,
       (out true state input).dispO, (out true state input).dispE,
       (out true state input).xtO, (out true state input).xlO,
       (out true state input).mvEn, (out true state input).mvSrc,
       (out true state input).mvDst, (out true state input).mvData,
       (out true state input).dbgXv, (out true state input).dbgRv,
       (out true state input).dbgFpc⟩ := rfl
  rw [h1, h2, rtlFetchEn, rtlFetchAddr, rtlPause, rtlNpc, rtlDisp, rtlDispE,
    rtlXtO, rtlXlO, rtlMvEn, rtlMvSrc, rtlMvDst, rtlMvData, hdxv, hdrv, hdfpc]

/-! ### Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

/-- The extracted trace is the specification trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt true inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step true (stateAt true inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-- SPEC §5 "Consequences" (`t + 3`) on the extracted trace. -/
theorem rtl_trace_dispatch_idle (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (rtlStateAt inputs initial n).xv = false)
    (hrv : (rtlStateAt inputs initial n).rv = false)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hcand : cand true (inputs n) ≠ 0)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).rv = true ∧
      (rtlStateAt inputs initial (n + 1)).xv = false ∧
      (rtlStateAt inputs initial (n + 1)).fpc =
        dpc true (rtlStateAt inputs initial n) (inputs n) ∧
      (rtlStateAt inputs initial (n + 2)).xv = true ∧
      (rtlStateAt inputs initial (n + 2)).fpc =
        dpc true (rtlStateAt inputs initial n) (inputs n) + 1 ∧
      (rtlStateAt inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  simp only [rtlStateAt_eq] at hxv hrv ⊢
  exact trace_dispatch_idle true inputs initial n hxv hrv hfrz hreset hcand hfrz1 hreset1

/-- SPEC §5 "Consequences" (taken jump, one idle cycle) on the extracted trace. -/
theorem rtl_trace_jump_idle (inputs : Nat → Input) (initial : State) (n : Nat)
    (hxv : (rtlStateAt inputs initial n).xv = true)
    (hfrz : (inputs n).frz = false) (hreset : (inputs n).resetN = true)
    (hjmp : jmp (rtlStateAt inputs initial n) (inputs n) = true)
    (hfrz1 : (inputs (n + 1)).frz = false) (hreset1 : (inputs (n + 1)).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).xv = false ∧
      (rtlStateAt inputs initial (n + 1)).rv = true ∧
      (rtlStateAt inputs initial (n + 1)).fpc =
        i_imm (rtlStateAt inputs initial n) ∧
      (rtlStateAt inputs initial (n + 2)).xv = true ∧
      (rtlStateAt inputs initial (n + 2)).fpc =
        i_imm (rtlStateAt inputs initial n) + 1 ∧
      (rtlStateAt inputs initial (n + 2)).ir = (inputs (n + 1)).rdata := by
  simp only [rtlStateAt_eq] at hxv hjmp ⊢
  exact trace_jump_idle true inputs initial n hxv hfrz hreset hjmp hfrz1 hreset1

/-! ### Axiom audit

`core_check.py` records these records and rejects `sorryAx`.  The per-field
equalities are `bv_decide` goals; the shared lemmas use `decide` over the six
threads. -/

#print axioms rtlStep_eq_step
#print axioms rtlOut_eq_out
#print axioms rtlStateAt_eq
#print axioms rtl_trace_result
#print axioms rtl_trace_dispatch_idle
#print axioms rtl_trace_jump_idle

end Rtl1

end Metronome.Core
