import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk33 : List (ℕ×ℕ) := [(1060,1056),(1061,1057),(1062,1058),(1063,1059),(1064,1060),(1065,1061),(1066,1062),(1067,1063),(1068,1064),(1069,1065),(1070,1066),(1071,1067),(1072,1068),(1073,1069),(1074,1070),(1075,1071),(1076,1072),(1077,1073),(1078,1074),(1079,1075),(1080,1076),(1081,1077),(1082,1078),(1083,1079),(1084,1080),(1085,1081),(1086,1082),(1087,1083),(1088,1084),(1089,1085),(1090,1086),(1091,1087)]
theorem crossPrivateChunk33_valid : ∀p∈crossPrivateChunk33,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
