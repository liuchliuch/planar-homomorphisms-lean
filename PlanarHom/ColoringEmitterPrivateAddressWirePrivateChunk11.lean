import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk11 : List (ℕ×ℕ) := [(354,352),(355,353),(356,354),(357,355),(358,356),(359,357),(360,358),(361,359),(362,360),(363,361),(364,362),(365,363),(366,364),(367,365),(368,366),(369,367),(370,368),(371,369),(372,370),(373,371),(374,372),(375,373),(376,374),(377,375),(378,376),(379,377),(380,378),(381,379),(382,380),(383,381),(384,382),(385,383)]
theorem wirePrivateChunk11_valid : ∀p∈wirePrivateChunk11,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
