import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk39 : List (ℕ×ℕ) := [(1260,1248),(1261,1249),(1262,1250),(1263,1251),(1264,1252),(1265,1253),(1266,1254),(1267,1255),(1268,1256),(1269,1257)]
theorem crossPrivateChunk39_valid : ∀p∈crossPrivateChunk39,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
