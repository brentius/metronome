import Metronome.Core
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: b58d162e9385cd53ad4dc8eb1984a7b0865365b09bd6d738fc0f9fed73ac5442
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
257 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core00 := !input.frz
  let core01 := state.rv && core00
  let core02 := !input.frz
  let core03 := state.xv && core02
  let core04 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core05 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core06 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core07 := (core06 + (0 : BitVec 32))
  let core08 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core07)))
  let core09 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core08 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core08 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core010 := core05 && core09
  let core011 := core04 || core010
  let core012 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core013 := !core09
  let core014 := core012 && core013
  let core015 := core011 || core014
  let core016 := core03 && core015
  let core017 := !core016
  let core018 := core01 && core017
  let core019 := core03 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core020 := !core019
  let core021 := core018 && core020
  let core022 := (if input.frz then state.xv else core021)
  let core023 := (if input.resetN then core022 else false)
  let core024 := core016 || core021
  let core025 := !state.xv
  let core026 := !state.rv
  let core027 := core025 && core026
  let core028 := !input.frz
  let core029 := core027 && core028
  let core030 := core019 || core029
  let core031 := (~~~input.tCore)
  let core032 := (input.tReady &&& core031)
  let core033 := (if input.runG then core032 else (0 : BitVec 6))
  let core034 := ((((BitVec.truncate 1 (BitVec.ushiftRight core033 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core033 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core033 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core033 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core033 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core033 5)) != 0)))
  let core035 := core030 && core034
  let core036 := core024 || core035
  let core037 := (if input.frz then state.rv else core036)
  let core038 := (if input.resetN then core037 else false)
  let core039 := (state.fpc + (1 : BitVec 8))
  let core040 := ((0 : BitVec 3) >= state.rr)
  let core041 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 0)) != 0) && core040
  let core042 := ((1 : BitVec 3) >= state.rr)
  let core043 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 1)) != 0) && core042
  let core044 := ((2 : BitVec 3) >= state.rr)
  let core045 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 2)) != 0) && core044
  let core046 := ((3 : BitVec 3) >= state.rr)
  let core047 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 3)) != 0) && core046
  let core048 := ((4 : BitVec 3) >= state.rr)
  let core049 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 4)) != 0) && core048
  let core050 := ((5 : BitVec 3) >= state.rr)
  let core051 := ((BitVec.truncate 1 (BitVec.ushiftRight core033 5)) != 0) && core050
  let core052 := ((core041) || (core043) || (core045) || (core047) || (core049) || (core051))
  let core053 := (~~~input.tCore)
  let core054 := (input.tReady &&& core053)
  let core055 := (if input.runG then core054 else (0 : BitVec 6))
  let core056 := if core052 then ((if core041 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core043 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core045 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core047 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core049 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core051 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core055
  let core057 := ((BitVec.truncate 1 (BitVec.ushiftRight core056 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core056 1)) != 0)
  let core058 := core057 || ((BitVec.truncate 1 (BitVec.ushiftRight core056 2)) != 0)
  let core059 := core058 || ((BitVec.truncate 1 (BitVec.ushiftRight core056 3)) != 0)
  let core060 := core059 || ((BitVec.truncate 1 (BitVec.ushiftRight core056 4)) != 0)
  let core061 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core056 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core057 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core058 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core059 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core060 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core062 := (core056 &&& core061)
  let core063 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core064 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core065 := (core063 ||| core064)
  let core066 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core067 := (core065 ||| core066)
  let core068 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core069 := (core067 ||| core068)
  let core070 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core071 := (core069 ||| core070)
  let core072 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core073 := (core071 ||| core072)
  let core074 := ((((BitVec.truncate 1 (BitVec.ushiftRight core073 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core073 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core073 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core073 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core073 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core073 5)) != 0)))
  let core075 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core076 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core077 := (core075 ||| core076)
  let core078 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core079 := (core077 ||| core078)
  let core080 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core081 := (core079 ||| core080)
  let core082 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core083 := (core081 ||| core082)
  let core084 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core085 := (core083 ||| core084)
  let core086 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core085))
  let core087 := (core086 + (0 : BitVec 32))
  let core088 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core087)))
  let core089 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core090 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core091 := (core089 ||| core090)
  let core092 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core093 := (core091 ||| core092)
  let core094 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core095 := (core093 ||| core094)
  let core096 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core097 := (core095 ||| core096)
  let core098 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core099 := (core097 ||| core098)
  let core0100 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core088) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core099))) != 0)
  let core0101 := core074 && core0100
  let core0102 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core0103 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core0104 := (core0102 ||| core0103)
  let core0105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core0106 := (core0104 ||| core0105)
  let core0107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core0108 := (core0106 ||| core0107)
  let core0109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core0110 := (core0108 ||| core0109)
  let core0111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core0112 := (core0110 ||| core0111)
  let core0113 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0114 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0115 := (core0113 ||| core0114)
  let core0116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0117 := (core0115 ||| core0116)
  let core0118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0119 := (core0117 ||| core0118)
  let core0120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0121 := (core0119 ||| core0120)
  let core0122 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0123 := (core0121 ||| core0122)
  let core0124 := ((((BitVec.truncate 1 (BitVec.ushiftRight core0123 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0123 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0123 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0123 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0123 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core0123 5)) != 0)))
  let core0125 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core087)))
  let core0126 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core0127 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core0128 := (core0126 ||| core0127)
  let core0129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core0130 := (core0128 ||| core0129)
  let core0131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core0132 := (core0130 ||| core0131)
  let core0133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core0134 := (core0132 ||| core0133)
  let core0135 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core0136 := (core0134 ||| core0135)
  let core0137 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0125) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core0136))) != 0)
  let core0138 := core0124 && core0137
  let core0139 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core0140 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core0141 := (core0139 ||| core0140)
  let core0142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core0143 := (core0141 ||| core0142)
  let core0144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core0145 := (core0143 ||| core0144)
  let core0146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core0147 := (core0145 ||| core0146)
  let core0148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core0149 := (core0147 ||| core0148)
  let core0150 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core0151 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core0152 := (core0150 ||| core0151)
  let core0153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core0154 := (core0152 ||| core0153)
  let core0155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core0156 := (core0154 ||| core0155)
  let core0157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core0158 := (core0156 ||| core0157)
  let core0159 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core0160 := (core0158 ||| core0159)
  let core0161 := if core0138 then core0149 else core0160
  let core0162 := if core0101 then core0112 else core0161
  let core0163 := if core021 then core039 else core0162
  let core0164 := if core016 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core0163
  let core0165 := if core036 then core0164 else state.fpc
  let core0166 := if input.frz then state.fpc else core0165
  let core0167 := if input.resetN then core0166 else (0 : BitVec 8)
  let core0168 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0169 := (core0168 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0170 := (core0169 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0171 := (core0170 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0172 := if core035 then core0171 else state.xt
  let core0173 := if input.frz then state.xt else core0172
  let core0174 := if input.resetN then core0173 else (0 : BitVec 3)
  let core0175 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core0176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core0177 := (core0175 ||| core0176)
  let core0178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core0179 := (core0177 ||| core0178)
  let core0180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core0181 := (core0179 ||| core0180)
  let core0182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core0183 := (core0181 ||| core0182)
  let core0184 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core0185 := (core0183 ||| core0184)
  let core0186 := if core035 then core0185 else state.xl
  let core0187 := if input.frz then state.xl else core0186
  let core0188 := if input.resetN then core0187 else (0 : BitVec 2)
  let core0189 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0190 := (core0189 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0191 := (core0190 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0192 := (core0191 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0193 := (core0192 == (5 : BitVec 3))
  let core0194 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0195 := (core0194 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0196 := (core0195 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0197 := (core0196 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0198 := (core0197 + (1 : BitVec 3))
  let core0199 := if core0193 then (0 : BitVec 3) else core0198
  let core0200 := if core035 then core0199 else state.rr
  let core0201 := if input.frz then state.rr else core0200
  let core0202 := if input.resetN then core0201 else (0 : BitVec 3)
  let core0203 := if input.frz then state.ir else input.rdata
  let core0204 := if core015 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core0205 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0206 := (core0205 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core0207 := (core0206 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0208 := (core0207 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core062 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core0209 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core0210 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core0211 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core07)))
  let core0212 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core0211) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core0213 := core0210 && core0212
  let core0214 := core0209 || core0213
  let core0215 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core0216 := !core0212
  let core0217 := core0215 && core0216
  let core0218 := core0214 || core0217
  let core0219 := core03 && core0218
  let core0220 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core0221 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core0222 := core0221 && core0212
  let core0223 := core0220 || core0222
  let core0224 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core0225 := !core0212
  let core0226 := core0224 && core0225
  let core0227 := core0223 || core0226
  let core0228 := core03 && core0227
  let core0229 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core0230 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core0231 := core0230 && core0212
  let core0232 := core0229 || core0231
  let core0233 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core0234 := !core0212
  let core0235 := core0233 && core0234
  let core0236 := core0232 || core0235
  let core0237 := core03 && core0236
  let core0238 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0239 := (core0238 + (0 : BitVec 32))
  let core0240 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0239)))
  let core0241 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core0242 := (core0241 + (0 : BitVec 32))
  let core0243 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0242)))
  let core0244 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core0245 := (core0244 + (0 : BitVec 32))
  let core0246 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0240) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0243) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0245)))
  let core0247 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0239)))
  let core0248 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0242)))
  let core0249 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core0250 := (core0249 + (0 : BitVec 32))
  let core0251 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0247) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0248) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0250)))
  let core0252 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core0239)))
  let core0253 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core0242)))
  let core0254 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core0255 := (core0254 + (0 : BitVec 32))
  let core0256 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0252) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core0253) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core0255)))
  (⟨core023, core038, core0167, core0174, core0188, core0202, core0203⟩, ⟨core036, core0164, core019, core0204, core035, core0208, state.xt, state.xl, ((if core0219 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core0228 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core0237 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core0246) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0251) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core0256) 16)), state.xv, state.rv, state.fpc⟩)

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
255 intermediate signals. -/
def rtlStepOut (state : State) (input : Input) : State × Out :=
  let core10 := !input.frz
  let core11 := state.rv && core10
  let core12 := !input.frz
  let core13 := state.xv && core12
  let core14 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (1 : BitVec 2))
  let core15 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (2 : BitVec 2))
  let core16 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core17 := (core16 + (0 : BitVec 32))
  let core18 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core17)))
  let core19 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 8 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 2 (BitVec.ushiftRight input.guards 17))) 9) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight input.guards 21))) 11) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core18 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 3 (BitVec.ushiftRight core18 1))) 18) ||| (BitVec.shiftLeft (BitVec.setWidth 32 (BitVec.truncate 4 (BitVec.ushiftRight input.guards 34))) 21) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.guards 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)) ||| (1 : BitVec 32)) (BitVec.toNat (BitVec.truncate 5 (BitVec.ushiftRight state.ir 59))))) != 0)
  let core110 := core15 && core19
  let core111 := core14 || core110
  let core112 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 1)) == (3 : BitVec 2))
  let core113 := !core19
  let core114 := core112 && core113
  let core115 := core111 || core114
  let core116 := core13 && core115
  let core117 := !core116
  let core118 := core11 && core117
  let core119 := core13 && ((BitVec.truncate 1 (BitVec.ushiftRight state.ir 0)) != 0)
  let core120 := !core119
  let core121 := core118 && core120
  let core122 := (if input.frz then state.xv else core121)
  let core123 := (if input.resetN then core122 else false)
  let core124 := core116 || core121
  let core125 := !state.xv
  let core126 := !state.rv
  let core127 := core125 && core126
  let core128 := !input.frz
  let core129 := core127 && core128
  let core130 := core119 || core129
  let core131 := (input.tReady &&& input.tCore)
  let core132 := (if input.runG then core131 else (0 : BitVec 6))
  let core133 := ((((BitVec.truncate 1 (BitVec.ushiftRight core132 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core132 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core132 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core132 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core132 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core132 5)) != 0)))
  let core134 := core130 && core133
  let core135 := core124 || core134
  let core136 := (if input.frz then state.rv else core135)
  let core137 := (if input.resetN then core136 else false)
  let core138 := (state.fpc + (1 : BitVec 8))
  let core139 := ((0 : BitVec 3) >= state.rr)
  let core140 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 0)) != 0) && core139
  let core141 := ((1 : BitVec 3) >= state.rr)
  let core142 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 1)) != 0) && core141
  let core143 := ((2 : BitVec 3) >= state.rr)
  let core144 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 2)) != 0) && core143
  let core145 := ((3 : BitVec 3) >= state.rr)
  let core146 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 3)) != 0) && core145
  let core147 := ((4 : BitVec 3) >= state.rr)
  let core148 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 4)) != 0) && core147
  let core149 := ((5 : BitVec 3) >= state.rr)
  let core150 := ((BitVec.truncate 1 (BitVec.ushiftRight core132 5)) != 0) && core149
  let core151 := ((core140) || (core142) || (core144) || (core146) || (core148) || (core150))
  let core152 := (input.tReady &&& input.tCore)
  let core153 := (if input.runG then core152 else (0 : BitVec 6))
  let core154 := if core151 then ((if core140 then (BitVec.shiftLeft (1 : BitVec 6) 0) else (0 : BitVec 6)) ||| (if core142 then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core144 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core146 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core148 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core150 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))) else core153
  let core155 := ((BitVec.truncate 1 (BitVec.ushiftRight core154 0)) != 0) || ((BitVec.truncate 1 (BitVec.ushiftRight core154 1)) != 0)
  let core156 := core155 || ((BitVec.truncate 1 (BitVec.ushiftRight core154 2)) != 0)
  let core157 := core156 || ((BitVec.truncate 1 (BitVec.ushiftRight core154 3)) != 0)
  let core158 := core157 || ((BitVec.truncate 1 (BitVec.ushiftRight core154 4)) != 0)
  let core159 := (~~~((if ((BitVec.truncate 1 (BitVec.ushiftRight core154 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 6) 1) else (0 : BitVec 6)) ||| (if core155 then (BitVec.shiftLeft (1 : BitVec 6) 2) else (0 : BitVec 6)) ||| (if core156 then (BitVec.shiftLeft (1 : BitVec 6) 3) else (0 : BitVec 6)) ||| (if core157 then (BitVec.shiftLeft (1 : BitVec 6) 4) else (0 : BitVec 6)) ||| (if core158 then (BitVec.shiftLeft (1 : BitVec 6) 5) else (0 : BitVec 6))))
  let core160 := (core154 &&& core159)
  let core161 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core162 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core163 := (core161 ||| core162)
  let core164 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core165 := (core163 ||| core164)
  let core166 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core167 := (core165 ||| core166)
  let core168 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core169 := (core167 ||| core168)
  let core170 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core171 := (core169 ||| core170)
  let core172 := ((((BitVec.truncate 1 (BitVec.ushiftRight core171 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core171 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core171 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core171 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core171 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core171 5)) != 0)))
  let core173 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core175 := (core173 ||| core174)
  let core176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core177 := (core175 ||| core176)
  let core178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core179 := (core177 ||| core178)
  let core180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core181 := (core179 ||| core180)
  let core182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core183 := (core181 ||| core182)
  let core184 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 core183))
  let core185 := (core184 + (0 : BitVec 32))
  let core186 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core185)))
  let core187 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 0)) else (0 : BitVec 6))
  let core188 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 6)) else (0 : BitVec 6))
  let core189 := (core187 ||| core188)
  let core190 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 12)) else (0 : BitVec 6))
  let core191 := (core189 ||| core190)
  let core192 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 18)) else (0 : BitVec 6))
  let core193 := (core191 ||| core192)
  let core194 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 24)) else (0 : BitVec 6))
  let core195 := (core193 ||| core194)
  let core196 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW0c 30)) else (0 : BitVec 6))
  let core197 := (core195 ||| core196)
  let core198 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core186) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core197))) != 0)
  let core199 := core172 && core198
  let core1100 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 0)) else (0 : BitVec 8))
  let core1101 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 8)) else (0 : BitVec 8))
  let core1102 := (core1100 ||| core1101)
  let core1103 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 16)) else (0 : BitVec 8))
  let core1104 := (core1102 ||| core1103)
  let core1105 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 24)) else (0 : BitVec 8))
  let core1106 := (core1104 ||| core1105)
  let core1107 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 32)) else (0 : BitVec 8))
  let core1108 := (core1106 ||| core1107)
  let core1109 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW0h 40)) else (0 : BitVec 8))
  let core1110 := (core1108 ||| core1109)
  let core1111 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1112 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1113 := (core1111 ||| core1112)
  let core1114 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1115 := (core1113 ||| core1114)
  let core1116 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1117 := (core1115 ||| core1116)
  let core1118 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1119 := (core1117 ||| core1118)
  let core1120 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1121 := (core1119 ||| core1120)
  let core1122 := ((((BitVec.truncate 1 (BitVec.ushiftRight core1121 0)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1121 1)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1121 2)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1121 3)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1121 4)) != 0)) || (((BitVec.truncate 1 (BitVec.ushiftRight core1121 5)) != 0)))
  let core1123 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core185)))
  let core1124 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 0)) else (0 : BitVec 6))
  let core1125 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 6)) else (0 : BitVec 6))
  let core1126 := (core1124 ||| core1125)
  let core1127 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 12)) else (0 : BitVec 6))
  let core1128 := (core1126 ||| core1127)
  let core1129 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 18)) else (0 : BitVec 6))
  let core1130 := (core1128 ||| core1129)
  let core1131 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 24)) else (0 : BitVec 6))
  let core1132 := (core1130 ||| core1131)
  let core1133 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 6 (BitVec.ushiftRight input.tW1c 30)) else (0 : BitVec 6))
  let core1134 := (core1132 ||| core1133)
  let core1135 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1123) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat core1134))) != 0)
  let core1136 := core1122 && core1135
  let core1137 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 0)) else (0 : BitVec 8))
  let core1138 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 8)) else (0 : BitVec 8))
  let core1139 := (core1137 ||| core1138)
  let core1140 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 16)) else (0 : BitVec 8))
  let core1141 := (core1139 ||| core1140)
  let core1142 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 24)) else (0 : BitVec 8))
  let core1143 := (core1141 ||| core1142)
  let core1144 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 32)) else (0 : BitVec 8))
  let core1145 := (core1143 ||| core1144)
  let core1146 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tW1h 40)) else (0 : BitVec 8))
  let core1147 := (core1145 ||| core1146)
  let core1148 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 0)) else (0 : BitVec 8))
  let core1149 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 8)) else (0 : BitVec 8))
  let core1150 := (core1148 ||| core1149)
  let core1151 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 16)) else (0 : BitVec 8))
  let core1152 := (core1150 ||| core1151)
  let core1153 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 24)) else (0 : BitVec 8))
  let core1154 := (core1152 ||| core1153)
  let core1155 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 32)) else (0 : BitVec 8))
  let core1156 := (core1154 ||| core1155)
  let core1157 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.tPc 40)) else (0 : BitVec 8))
  let core1158 := (core1156 ||| core1157)
  let core1159 := if core1136 then core1147 else core1158
  let core1160 := if core199 then core1110 else core1159
  let core1161 := if core121 then core138 else core1160
  let core1162 := if core116 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else core1161
  let core1163 := if core135 then core1162 else state.fpc
  let core1164 := if input.frz then state.fpc else core1163
  let core1165 := if input.resetN then core1164 else (0 : BitVec 8)
  let core1166 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1167 := (core1166 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1168 := (core1167 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1169 := (core1168 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1170 := if core134 then core1169 else state.xt
  let core1171 := if input.frz then state.xt else core1170
  let core1172 := if input.resetN then core1171 else (0 : BitVec 3)
  let core1173 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 0)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 0)) else (0 : BitVec 2))
  let core1174 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 2)) else (0 : BitVec 2))
  let core1175 := (core1173 ||| core1174)
  let core1176 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 4)) else (0 : BitVec 2))
  let core1177 := (core1175 ||| core1176)
  let core1178 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 6)) else (0 : BitVec 2))
  let core1179 := (core1177 ||| core1178)
  let core1180 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 8)) else (0 : BitVec 2))
  let core1181 := (core1179 ||| core1180)
  let core1182 := (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.truncate 2 (BitVec.ushiftRight input.tLine 10)) else (0 : BitVec 2))
  let core1183 := (core1181 ||| core1182)
  let core1184 := if core134 then core1183 else state.xl
  let core1185 := if input.frz then state.xl else core1184
  let core1186 := if input.resetN then core1185 else (0 : BitVec 2)
  let core1187 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1188 := (core1187 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1189 := (core1188 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1190 := (core1189 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1191 := (core1190 == (5 : BitVec 3))
  let core1192 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1193 := (core1192 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1194 := (core1193 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1195 := (core1194 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1196 := (core1195 + (1 : BitVec 3))
  let core1197 := if core1191 then (0 : BitVec 3) else core1196
  let core1198 := if core134 then core1197 else state.rr
  let core1199 := if input.frz then state.rr else core1198
  let core1200 := if input.resetN then core1199 else (0 : BitVec 3)
  let core1201 := if input.frz then state.ir else input.rdata
  let core1202 := if core115 then (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3)) else state.fpc
  let core1203 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3))) ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1204 := (core1203 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3))))
  let core1205 := (core1204 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1206 := (core1205 ||| ((if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight core160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))))
  let core1207 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (0 : BitVec 2))
  let core1208 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (1 : BitVec 2))
  let core1209 := (BitVec.truncate 5 (BitVec.ushiftRight input.gLine (BitVec.toNat core17)))
  let core1210 := ((BitVec.truncate 1 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 26 (BitVec.ushiftRight input.guards 1))) 1) ||| (BitVec.shiftLeft (BitVec.setWidth 64 core1209) 27) ||| (BitVec.shiftLeft (BitVec.setWidth 64 (BitVec.truncate 30 (BitVec.ushiftRight input.guards 32))) 32) ||| (1 : BitVec 64)) (BitVec.toNat (BitVec.truncate 6 (BitVec.ushiftRight state.ir 11))))) != 0)
  let core1211 := core1208 && core1210
  let core1212 := core1207 || core1211
  let core1213 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 17)) == (2 : BitVec 2))
  let core1214 := !core1210
  let core1215 := core1213 && core1214
  let core1216 := core1212 || core1215
  let core1217 := core13 && core1216
  let core1218 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (0 : BitVec 2))
  let core1219 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (1 : BitVec 2))
  let core1220 := core1219 && core1210
  let core1221 := core1218 || core1220
  let core1222 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 31)) == (2 : BitVec 2))
  let core1223 := !core1210
  let core1224 := core1222 && core1223
  let core1225 := core1221 || core1224
  let core1226 := core13 && core1225
  let core1227 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (0 : BitVec 2))
  let core1228 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (1 : BitVec 2))
  let core1229 := core1228 && core1210
  let core1230 := core1227 || core1229
  let core1231 := ((BitVec.truncate 2 (BitVec.ushiftRight state.ir 45)) == (2 : BitVec 2))
  let core1232 := !core1210
  let core1233 := core1231 && core1232
  let core1234 := core1230 || core1233
  let core1235 := core13 && core1234
  let core1236 := ((BitVec.setWidth 32 (2 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1237 := (core1236 + (0 : BitVec 32))
  let core1238 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1237)))
  let core1239 := ((BitVec.setWidth 32 (5 : BitVec 32)) * (BitVec.setWidth 32 state.xl))
  let core1240 := (core1239 + (0 : BitVec 32))
  let core1241 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1240)))
  let core1242 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))))
  let core1243 := (core1242 + (0 : BitVec 32))
  let core1244 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1238) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1241) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1243)))
  let core1245 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1237)))
  let core1246 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1240)))
  let core1247 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))))
  let core1248 := (core1247 + (0 : BitVec 32))
  let core1249 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1245) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1246) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1248)))
  let core1250 := (BitVec.truncate 2 (BitVec.ushiftRight input.lIn (BitVec.toNat core1237)))
  let core1251 := (BitVec.truncate 5 (BitVec.ushiftRight input.lCap (BitVec.toNat core1240)))
  let core1252 := ((BitVec.setWidth 32 (8 : BitVec 32)) * (BitVec.setWidth 32 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))))
  let core1253 := (core1252 + (0 : BitVec 32))
  let core1254 := (BitVec.truncate 8 (BitVec.ushiftRight ((BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 8 (BitVec.ushiftRight state.ir 3))) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1250) 16) ||| (BitVec.shiftLeft (BitVec.setWidth 512 core1251) 24) ||| (BitVec.shiftLeft (BitVec.setWidth 512 (BitVec.truncate 280 (BitVec.ushiftRight input.srcs 32))) 32)) (BitVec.toNat core1253)))
  (⟨core123, core137, core1165, core1172, core1186, core1200, core1201⟩, ⟨core135, core1162, core119, core1202, core134, core1206, state.xt, state.xl, ((if core1217 then (BitVec.shiftLeft (1 : BitVec 3) 0) else (0 : BitVec 3)) ||| (if core1226 then (BitVec.shiftLeft (1 : BitVec 3) 1) else (0 : BitVec 3)) ||| (if core1235 then (BitVec.shiftLeft (1 : BitVec 3) 2) else (0 : BitVec 3))), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 19))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 33))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 47))) 12)), ((BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 25))) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 39))) 6) ||| (BitVec.shiftLeft (BitVec.setWidth 18 (BitVec.truncate 6 (BitVec.ushiftRight state.ir 53))) 12)), ((BitVec.setWidth 24 core1244) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1249) 8) ||| (BitVec.shiftLeft (BitVec.setWidth 24 core1254) 16)), state.xv, state.rv, state.fpc⟩)

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
