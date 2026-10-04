import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk38 : List (ℕ×ℕ) := [(1220,1216),(1221,1217),(1222,1218),(1223,1219),(1224,1220),(1225,1221),(1226,1222),(1227,1223),(1228,1224),(1229,1225),(1230,1226),(1231,1227),(1232,1228),(1233,1229),(1234,1230),(1235,1231),(1236,1232),(1237,1233),(1238,1234),(1239,1235),(1240,1236),(1249,1237),(1250,1238),(1251,1239),(1252,1240),(1253,1241),(1254,1242),(1255,1243),(1256,1244),(1257,1245),(1258,1246),(1259,1247)]
theorem crossPrivateChunk38_valid : ∀p∈crossPrivateChunk38,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
