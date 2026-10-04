import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk35 : List (ℕ×ℕ) := [(1124,1120),(1125,1121),(1126,1122),(1127,1123),(1128,1124),(1129,1125),(1130,1126),(1131,1127),(1132,1128),(1133,1129),(1134,1130),(1135,1131),(1136,1132),(1137,1133),(1138,1134),(1139,1135),(1140,1136),(1141,1137),(1142,1138),(1143,1139),(1144,1140),(1145,1141),(1146,1142),(1147,1143),(1148,1144),(1149,1145),(1150,1146),(1151,1147),(1152,1148),(1153,1149),(1154,1150),(1155,1151)]
theorem crossPrivateChunk35_valid : ∀p∈crossPrivateChunk35,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
