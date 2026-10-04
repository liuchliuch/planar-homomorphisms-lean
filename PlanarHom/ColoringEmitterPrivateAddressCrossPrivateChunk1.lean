import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk1 : List (ℕ×ℕ) := [(36,32),(37,33),(38,34),(39,35),(40,36),(41,37),(42,38),(43,39),(44,40),(45,41),(46,42),(47,43),(48,44),(49,45),(50,46),(51,47),(52,48),(53,49),(54,50),(55,51),(56,52),(57,53),(58,54),(59,55),(60,56),(61,57),(62,58),(63,59),(64,60),(65,61),(66,62),(67,63)]
theorem crossPrivateChunk1_valid : ∀p∈crossPrivateChunk1,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
