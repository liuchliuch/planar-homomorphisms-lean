import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def testPrivateChunk1 : List (ℕ×ℕ) := [(35,32),(36,33),(37,34),(38,35),(39,36),(40,37),(41,38),(42,39),(43,40),(44,41),(45,42),(46,43),(47,44),(48,45),(49,46),(50,47),(51,48),(52,49),(53,50),(54,51),(55,52),(56,53),(57,54),(58,55),(59,56),(60,57),(61,58),(62,59),(63,60),(64,61),(65,62),(66,63)]
theorem testPrivateChunk1_valid : ∀p∈testPrivateChunk1,address .test p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
