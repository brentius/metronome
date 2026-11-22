import Metronome.Core
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 27c5eea9ea1309585e96e2423e5657bfad25d5c646bc47f120588c4ffef77e1f
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
259 intermediate signals. -/
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
  let core042 := ((0 : BitVec 3) >= state.rr)
  let core043 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 0)) != 0) && core042
  let core044 := ((1 : BitVec 3) >= state.rr)
  let core045 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 1)) != 0) && core044
  let core046 := ((2 : BitVec 3) >= state.rr)
  let core047 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 2)) != 0) && core046
  let core048 := ((3 : BitVec 3) >= state.rr)
  let core049 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 3)) != 0) && core048
  let core050 := ((4 : BitVec 3) >= state.rr)
  let core051 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 4)) != 0) && core050
  let core052 := ((5 : BitVec 3) >= state.rr)
  let core053 := ((BitVec.truncate 1 (BitVec.ushiftRight core035 5)) != 0) && core052
  let core054 := ((core043) || (core045) || (core047) || (core049) || (core051) || (core053))
  let core055 := (~~~input.tCore)
  let core056 := (input.tReady &&& core055)
  let core057 := (if input.runG then core056 else (0 : BitVec 6))
  let core058 := if core054 then ((if core043 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core045 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core047 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core049 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core051 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core053 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core057
  let core059 := ((BitVec.truncate 1 (BitVec.ushiftRight core058 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core058 1)) != 0)
  let core060 := core059 || ((BitVec.truncate 1 (BitVec.ushiftRight core058 2)) != 0)
  let core061 := core060 || ((BitVec.truncate 1 (BitVec.ushiftRight core058 3)) != 0)
  let core062 := core061 || ((BitVec.truncate 1 (BitVec.ushiftRight core058 4)) != 0)
  let core063 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core058 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core059 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core060 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core061 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core062 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core064 := (core058 &&& core063)
  let core065 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core066 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core067 := (core065 ||| core066)
  let core068 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core069 := (core067 ||| core068)
  let core070 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core071 := (core069 ||| core070)
  let core072 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core073 := (core071 ||| core072)
  let core074 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core075 := (core073 ||| core074)
  let core076 := ((((BitVec.truncate 1 (BitVec.ushiftRight core075 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core075 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core075 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core075 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core075 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core075 5)) != 0)))
  let core077 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core078 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core079 := (core077 ||| core078)
  let core080 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core081 := (core079 ||| core080)
  let core082 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core083 := (core081 ||| core082)
  let core084 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core085 := (core083 ||| core084)
  let core086 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core087 := (core085 ||| core086)
  let core088 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core087))
  let core089 := (core088 + (0 : BitVec 32))
  let core090 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core089)))
  let core091 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core092 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core093 := (core091 ||| core092)
  let core094 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core095 := (core093 ||| core094)
  let core096 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core097 := (core095 ||| core096)
  let core098 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core099 := (core097 ||| core098)
  let core0100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core0101 := (core099 ||| core0100)
  let core0102 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core090) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0101))) != 0)
  let core0103 := core076 && core0102
  let core0104 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core0105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core0106 := (core0104 ||| core0105)
  let core0107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core0108 := (core0106 ||| core0107)
  let core0109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core0110 := (core0108 ||| core0109)
  let core0111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core0112 := (core0110 ||| core0111)
  let core0113 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core0114 := (core0112 ||| core0113)
  let core0115 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0117 := (core0115 ||| core0116)
  let core0118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0119 := (core0117 ||| core0118)
  let core0120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0121 := (core0119 ||| core0120)
  let core0122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0123 := (core0121 ||| core0122)
  let core0124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0125 := (core0123 ||| core0124)
  let core0126 := ((((BitVec.truncate 1 (BitVec.ushiftRight core0125 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0125 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0125 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0125 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0125 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0125 5)) != 0)))
  let core0127 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core089)))
  let core0128 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0130 := (core0128 ||| core0129)
  let core0131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0132 := (core0130 ||| core0131)
  let core0133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0134 := (core0132 ||| core0133)
  let core0135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0136 := (core0134 ||| core0135)
  let core0137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0138 := (core0136 ||| core0137)
  let core0139 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0127) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0138))) != 0)
  let core0140 := core0126 && core0139
  let core0141 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core0142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core0143 := (core0141 ||| core0142)
  let core0144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core0145 := (core0143 ||| core0144)
  let core0146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core0147 := (core0145 ||| core0146)
  let core0148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core0149 := (core0147 ||| core0148)
  let core0150 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core0151 := (core0149 ||| core0150)
  let core0152 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core0153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core0154 := (core0152 ||| core0153)
  let core0155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core0156 := (core0154 ||| core0155)
  let core0157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core0158 := (core0156 ||| core0157)
  let core0159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core0160 := (core0158 ||| core0159)
  let core0161 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core0162 := (core0160 ||| core0161)
  let core0163 := if core0140 then core0151 else core0162
  let core0164 := if core0103 then core0114 else core0163
  let core0165 := if core023 then core041 else core0164
  let core0166 := if core018 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core0165
  let core0167 := if core038 then core0166 else state.fpc
  let core0168 := if input.frz then state.fpc else core0167
  let core0169 := if input.resetN then core0168 else (0 : BitVec 8)
  let core0170 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0171 := (core0170 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0172 := (core0171 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0173 := (core0172 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0174 := if core037 then core0173 else state.xt
  let core0175 := if input.frz then state.xt else core0174
  let core0176 := if input.resetN then core0175 else (0 : BitVec 3)
  let core0177 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core0178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core0179 := (core0177 ||| core0178)
  let core0180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core0181 := (core0179 ||| core0180)
  let core0182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core0183 := (core0181 ||| core0182)
  let core0184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core0185 := (core0183 ||| core0184)
  let core0186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core0187 := (core0185 ||| core0186)
  let core0188 := if core037 then core0187 else state.xl
  let core0189 := if input.frz then state.xl else core0188
  let core0190 := if input.resetN then core0189 else (0 : BitVec 2)
  let core0191 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0192 := (core0191 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0193 := (core0192 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0194 := (core0193 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0195 := (core0194 == (5 : BitVec 3))
  let core0196 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0197 := (core0196 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0198 := (core0197 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0199 := (core0198 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0200 := (core0199 + (1 : BitVec 3))
  let core0201 := if core0195 then (0 : BitVec 3) else core0200
  let core0202 := if core037 then core0201 else state.rr
  let core0203 := if input.frz then state.rr else core0202
  let core0204 := if input.resetN then core0203 else (0 : BitVec 3)
  let core0205 := if input.frz then state.ir else input.rdata
  let core0206 := if core017 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core0207 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0208 := (core0207 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0209 := (core0208 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0210 := (core0209 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core064 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0211 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core0212 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core0213 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core09)))
  let core0214 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0213) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core0215 := core0212 && core0214
  let core0216 := core0211 || core0215
  let core0217 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core0218 := !core0214
  let core0219 := core0217 && core0218
  let core0220 := core0216 || core0219
  let core0221 := core03 && core0220
  let core0222 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core0223 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core0224 := core0223 && core0214
  let core0225 := core0222 || core0224
  let core0226 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core0227 := !core0214
  let core0228 := core0226 && core0227
  let core0229 := core0225 || core0228
  let core0230 := core03 && core0229
  let core0231 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core0232 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core0233 := core0232 && core0214
  let core0234 := core0231 || core0233
  let core0235 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core0236 := !core0214
  let core0237 := core0235 && core0236
  let core0238 := core0234 || core0237
  let core0239 := core03 && core0238
  let core0240 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0241 := (core0240 + (0 : BitVec 32))
  let core0242 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0241)))
  let core0243 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0244 := (core0243 + (0 : BitVec 32))
  let core0245 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0244)))
  let core0246 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core0247 := (core0246 + (0 : BitVec 32))
  let core0248 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0242) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0245) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0247)))
  let core0249 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0241)))
  let core0250 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0244)))
  let core0251 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core0252 := (core0251 + (0 : BitVec 32))
  let core0253 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0249) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0250) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0252)))
  let core0254 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0241)))
  let core0255 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0244)))
  let core0256 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core0257 := (core0256 + (0 : BitVec 32))
  let core0258 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0254) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0255) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0257)))
  (⟨core025, core040, core0169, core0176, core0190, core0204, core0205⟩, ⟨core038, core0166, core021, core0206, core037, core0210, state.xt, state.xl, ((if core0221 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core0230 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core0239 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core0248) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0253) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0258) 16)), state.xv, state.rv, state.fpc⟩)

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
259 intermediate signals. -/
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
  let core133 := (~~~input.tCore)
  let core134 := (input.tReady &&& core133)
  let core135 := (if input.runG then core134 else (0 : BitVec 6))
  let core136 := ((((BitVec.truncate 1 (BitVec.ushiftRight core135 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core135 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core135 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core135 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core135 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core135 5)) != 0)))
  let core137 := core132 && core136
  let core138 := core126 || core137
  let core139 := (if input.frz then state.rv else core138)
  let core140 := (if input.resetN then core139 else false)
  let core141 := (state.fpc + (1 : BitVec 8))
  let core142 := ((0 : BitVec 3) >= state.rr)
  let core143 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 0)) != 0) && core142
  let core144 := ((1 : BitVec 3) >= state.rr)
  let core145 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 1)) != 0) && core144
  let core146 := ((2 : BitVec 3) >= state.rr)
  let core147 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 2)) != 0) && core146
  let core148 := ((3 : BitVec 3) >= state.rr)
  let core149 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 3)) != 0) && core148
  let core150 := ((4 : BitVec 3) >= state.rr)
  let core151 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 4)) != 0) && core150
  let core152 := ((5 : BitVec 3) >= state.rr)
  let core153 := ((BitVec.truncate 1 (BitVec.ushiftRight core135 5)) != 0) && core152
  let core154 := ((core143) || (core145) || (core147) || (core149) || (core151) || (core153))
  let core155 := (~~~input.tCore)
  let core156 := (input.tReady &&& core155)
  let core157 := (if input.runG then core156 else (0 : BitVec 6))
  let core158 := if core154 then ((if core143 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core145 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core147 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core149 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core151 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core153 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core157
  let core159 := ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core158 1)) != 0)
  let core160 := core159 || ((BitVec.truncate 1 (BitVec.ushiftRight core158 2)) != 0)
  let core161 := core160 || ((BitVec.truncate 1 (BitVec.ushiftRight core158 3)) != 0)
  let core162 := core161 || ((BitVec.truncate 1 (BitVec.ushiftRight core158 4)) != 0)
  let core163 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core158 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core159 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core160 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core161 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core162 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core164 := (core158 &&& core163)
  let core165 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core166 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core167 := (core165 ||| core166)
  let core168 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core169 := (core167 ||| core168)
  let core170 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core171 := (core169 ||| core170)
  let core172 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core173 := (core171 ||| core172)
  let core174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core175 := (core173 ||| core174)
  let core176 := ((((BitVec.truncate 1 (BitVec.ushiftRight core175 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core175 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core175 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core175 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core175 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core175 5)) != 0)))
  let core177 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core179 := (core177 ||| core178)
  let core180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core181 := (core179 ||| core180)
  let core182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core183 := (core181 ||| core182)
  let core184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core185 := (core183 ||| core184)
  let core186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core187 := (core185 ||| core186)
  let core188 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core187))
  let core189 := (core188 + (0 : BitVec 32))
  let core190 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core189)))
  let core191 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core192 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core193 := (core191 ||| core192)
  let core194 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core195 := (core193 ||| core194)
  let core196 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core197 := (core195 ||| core196)
  let core198 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core199 := (core197 ||| core198)
  let core1100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core1101 := (core199 ||| core1100)
  let core1102 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core190) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1101))) != 0)
  let core1103 := core176 && core1102
  let core1104 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core1105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core1106 := (core1104 ||| core1105)
  let core1107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core1108 := (core1106 ||| core1107)
  let core1109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core1110 := (core1108 ||| core1109)
  let core1111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core1112 := (core1110 ||| core1111)
  let core1113 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core1114 := (core1112 ||| core1113)
  let core1115 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1117 := (core1115 ||| core1116)
  let core1118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1119 := (core1117 ||| core1118)
  let core1120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1121 := (core1119 ||| core1120)
  let core1122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1123 := (core1121 ||| core1122)
  let core1124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1125 := (core1123 ||| core1124)
  let core1126 := ((((BitVec.truncate 1 (BitVec.ushiftRight core1125 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1125 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1125 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1125 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1125 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1125 5)) != 0)))
  let core1127 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core189)))
  let core1128 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1130 := (core1128 ||| core1129)
  let core1131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1132 := (core1130 ||| core1131)
  let core1133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1134 := (core1132 ||| core1133)
  let core1135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1136 := (core1134 ||| core1135)
  let core1137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1138 := (core1136 ||| core1137)
  let core1139 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1127) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1138))) != 0)
  let core1140 := core1126 && core1139
  let core1141 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core1142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core1143 := (core1141 ||| core1142)
  let core1144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core1145 := (core1143 ||| core1144)
  let core1146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core1147 := (core1145 ||| core1146)
  let core1148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core1149 := (core1147 ||| core1148)
  let core1150 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core1151 := (core1149 ||| core1150)
  let core1152 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core1153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core1154 := (core1152 ||| core1153)
  let core1155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core1156 := (core1154 ||| core1155)
  let core1157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core1158 := (core1156 ||| core1157)
  let core1159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core1160 := (core1158 ||| core1159)
  let core1161 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core1162 := (core1160 ||| core1161)
  let core1163 := if core1140 then core1151 else core1162
  let core1164 := if core1103 then core1114 else core1163
  let core1165 := if core123 then core141 else core1164
  let core1166 := if core118 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core1165
  let core1167 := if core138 then core1166 else state.fpc
  let core1168 := if input.frz then state.fpc else core1167
  let core1169 := if input.resetN then core1168 else (0 : BitVec 8)
  let core1170 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1171 := (core1170 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1172 := (core1171 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1173 := (core1172 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1174 := if core137 then core1173 else state.xt
  let core1175 := if input.frz then state.xt else core1174
  let core1176 := if input.resetN then core1175 else (0 : BitVec 3)
  let core1177 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core1178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core1179 := (core1177 ||| core1178)
  let core1180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core1181 := (core1179 ||| core1180)
  let core1182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core1183 := (core1181 ||| core1182)
  let core1184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core1185 := (core1183 ||| core1184)
  let core1186 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core1187 := (core1185 ||| core1186)
  let core1188 := if core137 then core1187 else state.xl
  let core1189 := if input.frz then state.xl else core1188
  let core1190 := if input.resetN then core1189 else (0 : BitVec 2)
  let core1191 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1192 := (core1191 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1193 := (core1192 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1194 := (core1193 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1195 := (core1194 == (5 : BitVec 3))
  let core1196 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1197 := (core1196 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1198 := (core1197 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1199 := (core1198 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1200 := (core1199 + (1 : BitVec 3))
  let core1201 := if core1195 then (0 : BitVec 3) else core1200
  let core1202 := if core137 then core1201 else state.rr
  let core1203 := if input.frz then state.rr else core1202
  let core1204 := if input.resetN then core1203 else (0 : BitVec 3)
  let core1205 := if input.frz then state.ir else input.rdata
  let core1206 := if core117 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core1207 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1208 := (core1207 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1209 := (core1208 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1210 := (core1209 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1211 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core1212 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core1213 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core19)))
  let core1214 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1213) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core1215 := core1212 && core1214
  let core1216 := core1211 || core1215
  let core1217 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core1218 := !core1214
  let core1219 := core1217 && core1218
  let core1220 := core1216 || core1219
  let core1221 := core13 && core1220
  let core1222 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core1223 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core1224 := core1223 && core1214
  let core1225 := core1222 || core1224
  let core1226 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core1227 := !core1214
  let core1228 := core1226 && core1227
  let core1229 := core1225 || core1228
  let core1230 := core13 && core1229
  let core1231 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core1232 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core1233 := core1232 && core1214
  let core1234 := core1231 || core1233
  let core1235 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core1236 := !core1214
  let core1237 := core1235 && core1236
  let core1238 := core1234 || core1237
  let core1239 := core13 && core1238
  let core1240 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1241 := (core1240 + (0 : BitVec 32))
  let core1242 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1241)))
  let core1243 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1244 := (core1243 + (0 : BitVec 32))
  let core1245 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1244)))
  let core1246 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core1247 := (core1246 + (0 : BitVec 32))
  let core1248 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1242) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1245) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1247)))
  let core1249 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1241)))
  let core1250 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1244)))
  let core1251 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core1252 := (core1251 + (0 : BitVec 32))
  let core1253 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1249) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1250) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1252)))
  let core1254 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1241)))
  let core1255 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1244)))
  let core1256 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core1257 := (core1256 + (0 : BitVec 32))
  let core1258 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1254) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1255) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1257)))
  (⟨core125, core140, core1169, core1176, core1190, core1204, core1205⟩, ⟨core138, core1166, core121, core1206, core137, core1210, state.xt, state.xl, ((if core1221 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core1230 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core1239 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core1248) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1253) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1258) 16)), state.xv, state.rv, state.fpc⟩)

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
