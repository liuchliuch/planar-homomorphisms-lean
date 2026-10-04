import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk0 : List (ℕ×ℕ) := [(2,0),(3,1),(4,2),(5,3),(6,4),(7,5),(8,6),(9,7),(10,8),(11,9),(12,10),(13,11),(14,12),(15,13),(16,14),(17,15),(18,16),(19,17),(20,18),(21,19),(22,20),(23,21),(24,22),(25,23),(26,24),(27,25),(28,26),(29,27),(30,28),(31,29),(32,30),(33,31)]
theorem wirePrivateChunk0_valid : ∀p∈wirePrivateChunk0,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
