import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk11 : List (ℕ×ℕ) := [(355,352),(356,353),(357,354),(358,355),(359,356),(360,357),(361,358),(362,359),(363,360),(364,361),(365,362),(366,363),(367,364),(368,365),(369,366),(370,367),(371,368),(372,369),(373,370),(374,371),(375,372),(376,373),(377,374),(378,375),(379,376),(380,377),(381,378),(382,379),(383,380),(384,381),(385,382),(386,383)]
theorem fanPrivateChunk11_valid : ∀p∈fanPrivateChunk11,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
