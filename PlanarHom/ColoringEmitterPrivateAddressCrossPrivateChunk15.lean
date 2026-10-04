import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk15 : List (ℕ×ℕ) := [(484,480),(485,481),(486,482),(487,483),(488,484),(489,485),(490,486),(491,487),(492,488),(493,489),(494,490),(495,491),(496,492),(497,493),(498,494),(499,495),(500,496),(501,497),(502,498),(503,499),(504,500),(505,501),(506,502),(507,503),(508,504),(509,505),(510,506),(511,507),(512,508),(513,509),(514,510),(515,511)]
theorem crossPrivateChunk15_valid : ∀p∈crossPrivateChunk15,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
