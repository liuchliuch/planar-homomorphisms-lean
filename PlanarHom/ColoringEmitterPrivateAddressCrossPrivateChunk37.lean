import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk37 : List (ℕ×ℕ) := [(1188,1184),(1189,1185),(1190,1186),(1191,1187),(1192,1188),(1193,1189),(1194,1190),(1195,1191),(1196,1192),(1197,1193),(1198,1194),(1199,1195),(1200,1196),(1201,1197),(1202,1198),(1203,1199),(1204,1200),(1205,1201),(1206,1202),(1207,1203),(1208,1204),(1209,1205),(1210,1206),(1211,1207),(1212,1208),(1213,1209),(1214,1210),(1215,1211),(1216,1212),(1217,1213),(1218,1214),(1219,1215)]
theorem crossPrivateChunk37_valid : ∀p∈crossPrivateChunk37,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
