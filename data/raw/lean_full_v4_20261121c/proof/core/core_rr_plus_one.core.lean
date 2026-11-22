import Metronome.Core
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 6c7f27a586033cd28d69172178534189f091bd21eb057e9682b5dacc9ba0d52b
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
265 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core00 := !input.frz
  let core01 := state.rv && core00
  let core02 := !input.frz
  let core03 := state.xv && core02
  let core04 := !((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core05 := core03 && core04
  let core06 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core07 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core08 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core09 := (core08 + (0 : BitVec 32))
  let core010 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core09)))
  let core011 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core010 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core010 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core012 := core07 && core011
  let core013 := core06 || core012
  let core014 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core015 := !core011
  let core016 := core014 && core015
  let core017 := core013 || core016
  let core018 := core05 && core017
  let core019 := !core018
  let core020 := core01 && core019
  let core021 := core03 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core022 := !core021
  let core023 := core020 && core022
  let core024 := (if input.frz then state.xv else core023)
  let core025 := (if input.resetN then core024 else false)
  let core026 := core018 || core023
  let core027 := !state.xv
  let core028 := !state.rv
  let core029 := core027 && core028
  let core030 := !input.frz
  let core031 := core029 && core030
  let core032 := core021 || core031
  let core033 := (~~~input.tCore)
  let core034 := (input.tReady &&& core033)
  let core035 := (if input.runG then core034 else (0 : BitVec 6))
  let core036 := ((((BitVec.truncate 1 (BitVec.ushiftRight core035 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core035 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core035 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core035 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core035 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core035 5)) != 0)))
  let core037 := core032 && core036
  let core038 := core026 || core037
  let core039 := (if input.frz then state.rv else core038)
  let core040 := (if input.resetN then core039 else false)
  let core041 := (state.fpc + (1 : BitVec 8))
  let core042 := (state.rr + (1 : BitVec 3))
  let core043 := ((0 : BitVec 3) >= core042)
  let core044 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 0)) != 0) && core043
  let core045 := (state.rr + (1 : BitVec 3))
  let core046 := ((1 : BitVec 3) >= core045)
  let core047 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 1)) != 0) && core046
  let core048 := (state.rr + (1 : BitVec 3))
  let core049 := ((2 : BitVec 3) >= core048)
  let core050 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 2)) != 0) && core049
  let core051 := (state.rr + (1 : BitVec 3))
  let core052 := ((3 : BitVec 3) >= core051)
  let core053 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 3)) != 0) && core052
  let core054 := (state.rr + (1 : BitVec 3))
  let core055 := ((4 : BitVec 3) >= core054)
  let core056 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 4)) != 0) && core055
  let core057 := (state.rr + (1 : BitVec 3))
  let core058 := ((5 : BitVec 3) >= core057)
  let core059 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 5)) != 0) && core058
  let core060 := ((core044) || (core047) || (core050) || (core053) || (core056) || (core059))
  let core061 := (~~~input.tCore)
  let core062 := (input.tReady &&& core061)
  let core063 := (if input.runG then core062 else (0 : BitVec 6))
  let core064 := if core060 then ((if core044 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core047 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core050 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core053 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core056 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core059 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core063
  let core065 := ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0)
  let core066 := core065 || ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0)
  let core067 := core066 || ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0)
  let core068 := core067 || ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0)
  let core069 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core065 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core066 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core067 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core068 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core070 := (core064 &&& core069)
  let core071 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core072 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core073 := (core071 ||| core072)
  let core074 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core075 := (core073 ||| core074)
  let core076 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core077 := (core075 ||| core076)
  let core078 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core079 := (core077 ||| core078)
  let core080 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core081 := (core079 ||| core080)
  let core082 := ((((BitVec.truncate 1 (BitVec.ushiftRight core081 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core081 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core081 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core081 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core081 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core081 5)) != 0)))
  let core083 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core084 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core085 := (core083 ||| core084)
  let core086 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core087 := (core085 ||| core086)
  let core088 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core089 := (core087 ||| core088)
  let core090 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core091 := (core089 ||| core090)
  let core092 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core093 := (core091 ||| core092)
  let core094 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core093))
  let core095 := (core094 + (0 : BitVec 32))
  let core096 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core095)))
  let core097 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core098 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core099 := (core097 ||| core098)
  let core0100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core0101 := (core099 ||| core0100)
  let core0102 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core0103 := (core0101 ||| core0102)
  let core0104 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core0105 := (core0103 ||| core0104)
  let core0106 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core0107 := (core0105 ||| core0106)
  let core0108 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core096) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0107))) != 0)
  let core0109 := core082 && core0108
  let core0110 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core0111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core0112 := (core0110 ||| core0111)
  let core0113 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core0114 := (core0112 ||| core0113)
  let core0115 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core0116 := (core0114 ||| core0115)
  let core0117 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core0118 := (core0116 ||| core0117)
  let core0119 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core0120 := (core0118 ||| core0119)
  let core0121 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0123 := (core0121 ||| core0122)
  let core0124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0125 := (core0123 ||| core0124)
  let core0126 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0127 := (core0125 ||| core0126)
  let core0128 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0129 := (core0127 ||| core0128)
  let core0130 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0131 := (core0129 ||| core0130)
  let core0132 := ((((BitVec.truncate 1 (BitVec.ushiftRight core0131 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0131 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0131 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0131 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0131 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0131 5)) != 0)))
  let core0133 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core095)))
  let core0134 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0136 := (core0134 ||| core0135)
  let core0137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0138 := (core0136 ||| core0137)
  let core0139 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0140 := (core0138 ||| core0139)
  let core0141 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0142 := (core0140 ||| core0141)
  let core0143 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0144 := (core0142 ||| core0143)
  let core0145 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0133) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0144))) != 0)
  let core0146 := core0132 && core0145
  let core0147 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core0148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core0149 := (core0147 ||| core0148)
  let core0150 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core0151 := (core0149 ||| core0150)
  let core0152 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core0153 := (core0151 ||| core0152)
  let core0154 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core0155 := (core0153 ||| core0154)
  let core0156 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core0157 := (core0155 ||| core0156)
  let core0158 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core0159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core0160 := (core0158 ||| core0159)
  let core0161 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core0162 := (core0160 ||| core0161)
  let core0163 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core0164 := (core0162 ||| core0163)
  let core0165 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core0166 := (core0164 ||| core0165)
  let core0167 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core0168 := (core0166 ||| core0167)
  let core0169 := if core0146 then core0157 else core0168
  let core0170 := if core0109 then core0120 else core0169
  let core0171 := if core023 then core041 else core0170
  let core0172 := if core018 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core0171
  let core0173 := if core038 then core0172 else state.fpc
  let core0174 := if input.frz then state.fpc else core0173
  let core0175 := if input.resetN then core0174 else (0 : BitVec 8)
  let core0176 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0177 := (core0176 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0178 := (core0177 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0179 := (core0178 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0180 := if core037 then core0179 else state.xt
  let core0181 := if input.frz then state.xt else core0180
  let core0182 := if input.resetN then core0181 else (0 : BitVec 3)
  let core0183 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core0184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core0185 := (core0183 ||| core0184)
  let core0186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core0187 := (core0185 ||| core0186)
  let core0188 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core0189 := (core0187 ||| core0188)
  let core0190 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core0191 := (core0189 ||| core0190)
  let core0192 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core0193 := (core0191 ||| core0192)
  let core0194 := if core037 then core0193 else state.xl
  let core0195 := if input.frz then state.xl else core0194
  let core0196 := if input.resetN then core0195 else (0 : BitVec 2)
  let core0197 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0198 := (core0197 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0199 := (core0198 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0200 := (core0199 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0201 := (core0200 == (5 : BitVec 3))
  let core0202 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0203 := (core0202 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0204 := (core0203 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0205 := (core0204 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0206 := (core0205 + (1 : BitVec 3))
  let core0207 := if core0201 then (0 : BitVec 3) else core0206
  let core0208 := if core037 then core0207 else state.rr
  let core0209 := if input.frz then state.rr else core0208
  let core0210 := if input.resetN then core0209 else (0 : BitVec 3)
  let core0211 := if input.frz then state.ir else input.rdata
  let core0212 := if core017 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core0213 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0214 := (core0213 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0215 := (core0214 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0216 := (core0215 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core070 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0217 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core0218 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core0219 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core09)))
  let core0220 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0219) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core0221 := core0218 && core0220
  let core0222 := core0217 || core0221
  let core0223 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core0224 := !core0220
  let core0225 := core0223 && core0224
  let core0226 := core0222 || core0225
  let core0227 := core03 && core0226
  let core0228 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core0229 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core0230 := core0229 && core0220
  let core0231 := core0228 || core0230
  let core0232 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core0233 := !core0220
  let core0234 := core0232 && core0233
  let core0235 := core0231 || core0234
  let core0236 := core03 && core0235
  let core0237 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core0238 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core0239 := core0238 && core0220
  let core0240 := core0237 || core0239
  let core0241 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core0242 := !core0220
  let core0243 := core0241 && core0242
  let core0244 := core0240 || core0243
  let core0245 := core03 && core0244
  let core0246 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0247 := (core0246 + (0 : BitVec 32))
  let core0248 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0247)))
  let core0249 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0250 := (core0249 + (0 : BitVec 32))
  let core0251 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0250)))
  let core0252 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core0253 := (core0252 + (0 : BitVec 32))
  let core0254 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0248) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0251) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0253)))
  let core0255 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0247)))
  let core0256 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0250)))
  let core0257 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core0258 := (core0257 + (0 : BitVec 32))
  let core0259 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0255) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0256) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0258)))
  let core0260 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0247)))
  let core0261 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0250)))
  let core0262 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core0263 := (core0262 + (0 : BitVec 32))
  let core0264 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0260) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0261) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0263)))
  (⟨core025, core040, core0175, core0182, core0196, core0210, core0211⟩, ⟨core038, core0172, core021, core0212, core037, core0216, state.xt, state.xl, ((if core0227 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core0236 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core0245 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core0254) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0259) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0264) 16)), state.xv, state.rv, state.fpc⟩)

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
263 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core10 := !input.frz
  let core11 := state.rv && core10
  let core12 := !input.frz
  let core13 := state.xv && core12
  let core14 := !((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core15 := core13 && core14
  let core16 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core17 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core18 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core19 := (core18 + (0 : BitVec 32))
  let core110 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core19)))
  let core111 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core110 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core110 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core112 := core17 && core111
  let core113 := core16 || core112
  let core114 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core115 := !core111
  let core116 := core114 && core115
  let core117 := core113 || core116
  let core118 := core15 && core117
  let core119 := !core118
  let core120 := core11 && core119
  let core121 := core13 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core122 := !core121
  let core123 := core120 && core122
  let core124 := (if input.frz then state.xv else core123)
  let core125 := (if input.resetN then core124 else false)
  let core126 := core118 || core123
  let core127 := !state.xv
  let core128 := !state.rv
  let core129 := core127 && core128
  let core130 := !input.frz
  let core131 := core129 && core130
  let core132 := core121 || core131
  let core133 := (input.tReady &&& input.tCore)
  let core134 := (if input.runG then core133 else (0 : BitVec 6))
  let core135 := ((((BitVec.truncate 1 (BitVec.ushiftRight core134 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core134 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core134 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core134 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core134 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core134 5)) != 0)))
  let core136 := core132 && core135
  let core137 := core126 || core136
  let core138 := (if input.frz then state.rv else core137)
  let core139 := (if input.resetN then core138 else false)
  let core140 := (state.fpc + (1 : BitVec 8))
  let core141 := (state.rr + (1 : BitVec 3))
  let core142 := ((0 : BitVec 3) >= core141)
  let core143 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 0)) != 0) && core142
  let core144 := (state.rr + (1 : BitVec 3))
  let core145 := ((1 : BitVec 3) >= core144)
  let core146 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 1)) != 0) && core145
  let core147 := (state.rr + (1 : BitVec 3))
  let core148 := ((2 : BitVec 3) >= core147)
  let core149 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 2)) != 0) && core148
  let core150 := (state.rr + (1 : BitVec 3))
  let core151 := ((3 : BitVec 3) >= core150)
  let core152 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 3)) != 0) && core151
  let core153 := (state.rr + (1 : BitVec 3))
  let core154 := ((4 : BitVec 3) >= core153)
  let core155 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 4)) != 0) && core154
  let core156 := (state.rr + (1 : BitVec 3))
  let core157 := ((5 : BitVec 3) >= core156)
  let core158 := ((BitVec.truncate 1 (BitVec.ushiftRight core134 5)) != 0) && core157
  let core159 := ((core143) || (core146) || (core149) || (core152) || (core155) || (core158))
  let core160 := (input.tReady &&& input.tCore)
  let core161 := (if input.runG then core160 else (0 : BitVec 6))
  let core162 := if core159 then ((if core143 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core146 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core149 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core152 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core155 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core158 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core161
  let core163 := ((BitVec.truncate 1 (BitVec.ushiftRight core162 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core162 1)) != 0)
  let core164 := core163 || ((BitVec.truncate 1 (BitVec.ushiftRight core162 2)) != 0)
  let core165 := core164 || ((BitVec.truncate 1 (BitVec.ushiftRight core162 3)) != 0)
  let core166 := core165 || ((BitVec.truncate 1 (BitVec.ushiftRight core162 4)) != 0)
  let core167 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core162 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core163 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core164 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core165 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core166 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core168 := (core162 &&& core167)
  let core169 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core170 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core171 := (core169 ||| core170)
  let core172 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core173 := (core171 ||| core172)
  let core174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core175 := (core173 ||| core174)
  let core176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core177 := (core175 ||| core176)
  let core178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core179 := (core177 ||| core178)
  let core180 := ((((BitVec.truncate 1 (BitVec.ushiftRight core179 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core179 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core179 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core179 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core179 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core179 5)) != 0)))
  let core181 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core183 := (core181 ||| core182)
  let core184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core185 := (core183 ||| core184)
  let core186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core187 := (core185 ||| core186)
  let core188 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core189 := (core187 ||| core188)
  let core190 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core191 := (core189 ||| core190)
  let core192 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core191))
  let core193 := (core192 + (0 : BitVec 32))
  let core194 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core193)))
  let core195 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core196 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core197 := (core195 ||| core196)
  let core198 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core199 := (core197 ||| core198)
  let core1100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core1101 := (core199 ||| core1100)
  let core1102 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core1103 := (core1101 ||| core1102)
  let core1104 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core1105 := (core1103 ||| core1104)
  let core1106 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core194) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1105))) != 0)
  let core1107 := core180 && core1106
  let core1108 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core1109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core1110 := (core1108 ||| core1109)
  let core1111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core1112 := (core1110 ||| core1111)
  let core1113 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core1114 := (core1112 ||| core1113)
  let core1115 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core1116 := (core1114 ||| core1115)
  let core1117 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core1118 := (core1116 ||| core1117)
  let core1119 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1121 := (core1119 ||| core1120)
  let core1122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1123 := (core1121 ||| core1122)
  let core1124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1125 := (core1123 ||| core1124)
  let core1126 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1127 := (core1125 ||| core1126)
  let core1128 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1129 := (core1127 ||| core1128)
  let core1130 := ((((BitVec.truncate 1 (BitVec.ushiftRight core1129 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1129 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1129 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1129 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1129 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1129 5)) != 0)))
  let core1131 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core193)))
  let core1132 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1134 := (core1132 ||| core1133)
  let core1135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1136 := (core1134 ||| core1135)
  let core1137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1138 := (core1136 ||| core1137)
  let core1139 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1140 := (core1138 ||| core1139)
  let core1141 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1142 := (core1140 ||| core1141)
  let core1143 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1131) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1142))) != 0)
  let core1144 := core1130 && core1143
  let core1145 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core1146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core1147 := (core1145 ||| core1146)
  let core1148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core1149 := (core1147 ||| core1148)
  let core1150 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core1151 := (core1149 ||| core1150)
  let core1152 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core1153 := (core1151 ||| core1152)
  let core1154 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core1155 := (core1153 ||| core1154)
  let core1156 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core1157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core1158 := (core1156 ||| core1157)
  let core1159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core1160 := (core1158 ||| core1159)
  let core1161 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core1162 := (core1160 ||| core1161)
  let core1163 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core1164 := (core1162 ||| core1163)
  let core1165 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core1166 := (core1164 ||| core1165)
  let core1167 := if core1144 then core1155 else core1166
  let core1168 := if core1107 then core1118 else core1167
  let core1169 := if core123 then core140 else core1168
  let core1170 := if core118 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core1169
  let core1171 := if core137 then core1170 else state.fpc
  let core1172 := if input.frz then state.fpc else core1171
  let core1173 := if input.resetN then core1172 else (0 : BitVec 8)
  let core1174 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1175 := (core1174 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1176 := (core1175 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1177 := (core1176 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1178 := if core136 then core1177 else state.xt
  let core1179 := if input.frz then state.xt else core1178
  let core1180 := if input.resetN then core1179 else (0 : BitVec 3)
  let core1181 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core1182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core1183 := (core1181 ||| core1182)
  let core1184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core1185 := (core1183 ||| core1184)
  let core1186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core1187 := (core1185 ||| core1186)
  let core1188 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core1189 := (core1187 ||| core1188)
  let core1190 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core1191 := (core1189 ||| core1190)
  let core1192 := if core136 then core1191 else state.xl
  let core1193 := if input.frz then state.xl else core1192
  let core1194 := if input.resetN then core1193 else (0 : BitVec 2)
  let core1195 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1196 := (core1195 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1197 := (core1196 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1198 := (core1197 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1199 := (core1198 == (5 : BitVec 3))
  let core1200 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1201 := (core1200 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1202 := (core1201 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1203 := (core1202 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1204 := (core1203 + (1 : BitVec 3))
  let core1205 := if core1199 then (0 : BitVec 3) else core1204
  let core1206 := if core136 then core1205 else state.rr
  let core1207 := if input.frz then state.rr else core1206
  let core1208 := if input.resetN then core1207 else (0 : BitVec 3)
  let core1209 := if input.frz then state.ir else input.rdata
  let core1210 := if core117 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core1211 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1212 := (core1211 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1213 := (core1212 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1214 := (core1213 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core168 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1215 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core1216 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core1217 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core19)))
  let core1218 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1217) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core1219 := core1216 && core1218
  let core1220 := core1215 || core1219
  let core1221 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core1222 := !core1218
  let core1223 := core1221 && core1222
  let core1224 := core1220 || core1223
  let core1225 := core13 && core1224
  let core1226 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core1227 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core1228 := core1227 && core1218
  let core1229 := core1226 || core1228
  let core1230 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core1231 := !core1218
  let core1232 := core1230 && core1231
  let core1233 := core1229 || core1232
  let core1234 := core13 && core1233
  let core1235 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core1236 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core1237 := core1236 && core1218
  let core1238 := core1235 || core1237
  let core1239 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core1240 := !core1218
  let core1241 := core1239 && core1240
  let core1242 := core1238 || core1241
  let core1243 := core13 && core1242
  let core1244 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1245 := (core1244 + (0 : BitVec 32))
  let core1246 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1245)))
  let core1247 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1248 := (core1247 + (0 : BitVec 32))
  let core1249 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1248)))
  let core1250 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core1251 := (core1250 + (0 : BitVec 32))
  let core1252 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1246) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1249) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1251)))
  let core1253 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1245)))
  let core1254 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1248)))
  let core1255 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core1256 := (core1255 + (0 : BitVec 32))
  let core1257 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1253) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1254) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1256)))
  let core1258 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1245)))
  let core1259 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1248)))
  let core1260 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core1261 := (core1260 + (0 : BitVec 32))
  let core1262 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1258) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1259) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1261)))
  (⟨core125, core139, core1173, core1180, core1194, core1208, core1209⟩, ⟨core137, core1170, core121, core1210, core136, core1214, state.xt, state.xl, ((if core1225 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core1234 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core1243 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core1252) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1257) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1262) 16)), state.xv, state.rv, state.fpc⟩)

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
