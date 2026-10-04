import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk15 : List (ℕ×ℕ) := [(483,480),(484,481),(485,482),(486,483),(487,484),(488,485),(489,486),(490,487),(491,488),(492,489),(493,490),(494,491),(495,492),(496,493),(497,494),(498,495),(499,496),(500,497),(501,498),(502,499),(503,500),(504,501),(505,502),(506,503),(507,504),(508,505),(509,506),(510,507),(511,508),(512,509),(513,510),(514,511)]
theorem fanPrivateChunk15_valid : ∀p∈fanPrivateChunk15,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
