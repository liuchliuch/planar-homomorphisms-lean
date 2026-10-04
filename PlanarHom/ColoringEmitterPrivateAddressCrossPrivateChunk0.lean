import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk0 : List (ℕ×ℕ) := [(4,0),(5,1),(6,2),(7,3),(8,4),(9,5),(10,6),(11,7),(12,8),(13,9),(14,10),(15,11),(16,12),(17,13),(18,14),(19,15),(20,16),(21,17),(22,18),(23,19),(24,20),(25,21),(26,22),(27,23),(28,24),(29,25),(30,26),(31,27),(32,28),(33,29),(34,30),(35,31)]
theorem crossPrivateChunk0_valid : ∀p∈crossPrivateChunk0,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
