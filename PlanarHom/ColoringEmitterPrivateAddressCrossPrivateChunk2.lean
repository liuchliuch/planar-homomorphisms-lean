import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk2 : List (ℕ×ℕ) := [(68,64),(69,65),(70,66),(71,67),(72,68),(73,69),(74,70),(75,71),(76,72),(77,73),(78,74),(79,75),(80,76),(81,77),(82,78),(83,79),(84,80),(85,81),(86,82),(87,83),(88,84),(89,85),(90,86),(91,87),(92,88),(93,89),(94,90),(95,91),(96,92),(97,93),(98,94),(99,95)]
theorem crossPrivateChunk2_valid : ∀p∈crossPrivateChunk2,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
