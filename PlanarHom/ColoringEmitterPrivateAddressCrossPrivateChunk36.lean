import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk36 : List (ℕ×ℕ) := [(1156,1152),(1157,1153),(1158,1154),(1159,1155),(1160,1156),(1161,1157),(1162,1158),(1163,1159),(1164,1160),(1165,1161),(1166,1162),(1167,1163),(1168,1164),(1169,1165),(1170,1166),(1171,1167),(1172,1168),(1173,1169),(1174,1170),(1175,1171),(1176,1172),(1177,1173),(1178,1174),(1179,1175),(1180,1176),(1181,1177),(1182,1178),(1183,1179),(1184,1180),(1185,1181),(1186,1182),(1187,1183)]
theorem crossPrivateChunk36_valid : ∀p∈crossPrivateChunk36,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
