import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk14 : List (ℕ×ℕ) := [(451,448),(452,449),(453,450),(454,451),(455,452),(456,453),(457,454),(458,455),(459,456),(460,457),(461,458),(462,459),(463,460),(464,461),(465,462),(466,463),(467,464),(468,465),(469,466),(470,467),(471,468),(472,469),(473,470),(474,471),(475,472),(476,473),(477,474),(478,475),(479,476),(480,477),(481,478),(482,479)]
theorem fanPrivateChunk14_valid : ∀p∈fanPrivateChunk14,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
