import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk14 : List (ℕ×ℕ) := [(452,448),(453,449),(454,450),(455,451),(456,452),(457,453),(458,454),(459,455),(460,456),(461,457),(462,458),(463,459),(464,460),(465,461),(466,462),(467,463),(468,464),(469,465),(470,466),(471,467),(472,468),(473,469),(474,470),(475,471),(476,472),(477,473),(478,474),(479,475),(480,476),(481,477),(482,478),(483,479)]
theorem crossPrivateChunk14_valid : ∀p∈crossPrivateChunk14,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
