import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk1 : List (ℕ×ℕ) := [(34,32),(35,33),(36,34),(37,35),(38,36),(39,37),(40,38),(41,39),(42,40),(43,41),(44,42),(45,43),(46,44),(47,45),(48,46),(49,47),(50,48),(51,49),(52,50),(53,51),(54,52),(55,53),(56,54),(57,55),(58,56),(59,57),(60,58),(61,59),(62,60),(63,61),(64,62),(65,63)]
theorem wirePrivateChunk1_valid : ∀p∈wirePrivateChunk1,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
