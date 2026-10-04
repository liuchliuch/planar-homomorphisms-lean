import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk14 : List (ℕ×ℕ) := [(450,448),(451,449),(452,450),(453,451),(454,452),(455,453),(456,454),(457,455),(458,456),(459,457),(460,458),(461,459),(462,460),(463,461),(464,462),(465,463),(466,464),(467,465),(468,466),(469,467),(470,468),(471,469),(472,470),(473,471),(474,472),(475,473),(476,474),(477,475),(478,476),(479,477),(480,478),(481,479)]
theorem wirePrivateChunk14_valid : ∀p∈wirePrivateChunk14,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
