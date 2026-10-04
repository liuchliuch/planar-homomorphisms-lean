import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk11 : List (ℕ×ℕ) := [(356,352),(357,353),(358,354),(359,355),(360,356),(361,357),(362,358),(363,359),(364,360),(365,361),(366,362),(367,363),(368,364),(369,365),(370,366),(371,367),(372,368),(373,369),(374,370),(375,371),(376,372),(377,373),(378,374),(379,375),(380,376),(381,377),(382,378),(383,379),(384,380),(385,381),(386,382),(387,383)]
theorem crossPrivateChunk11_valid : ∀p∈crossPrivateChunk11,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
