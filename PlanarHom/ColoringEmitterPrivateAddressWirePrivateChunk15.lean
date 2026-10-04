import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk15 : List (ℕ×ℕ) := [(482,480),(483,481),(484,482),(485,483),(486,484),(487,485),(488,486),(489,487),(490,488),(491,489),(492,490),(493,491),(494,492),(495,493),(496,494),(497,495),(498,496),(499,497),(500,498),(501,499),(502,500),(503,501),(504,502),(505,503),(506,504),(507,505),(508,506),(509,507),(510,508),(511,509),(512,510),(513,511)]
theorem wirePrivateChunk15_valid : ∀p∈wirePrivateChunk15,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
