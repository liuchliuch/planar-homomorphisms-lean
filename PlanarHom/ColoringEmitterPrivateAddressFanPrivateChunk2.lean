import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk2 : List (ℕ×ℕ) := [(67,64),(68,65),(69,66),(70,67),(71,68),(72,69),(73,70),(74,71),(75,72),(76,73),(77,74),(78,75),(79,76),(80,77),(81,78),(82,79),(83,80),(84,81),(85,82),(86,83),(87,84),(88,85),(89,86),(90,87),(91,88),(92,89),(93,90),(94,91),(95,92),(96,93),(97,94),(98,95)]
theorem fanPrivateChunk2_valid : ∀p∈fanPrivateChunk2,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
