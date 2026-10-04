import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk2 : List (ℕ×ℕ) := [(66,64),(67,65),(68,66),(69,67),(70,68),(71,69),(72,70),(73,71),(74,72),(75,73),(76,74),(77,75),(78,76),(79,77),(80,78),(81,79),(82,80),(83,81),(84,82),(85,83),(86,84),(87,85),(88,86),(89,87),(90,88),(91,89),(92,90),(93,91),(94,92),(95,93),(96,94),(97,95)]
theorem wirePrivateChunk2_valid : ∀p∈wirePrivateChunk2,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
