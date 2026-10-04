import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk5 : List (ℕ×ℕ) := [(162,160),(163,161),(164,162),(165,163),(166,164),(167,165),(168,166),(169,167),(170,168),(171,169),(172,170),(173,171),(174,172),(175,173),(176,174),(177,175),(178,176),(179,177),(180,178),(181,179),(182,180),(183,181),(184,182),(185,183),(186,184),(187,185),(188,186),(189,187),(190,188),(191,189),(192,190),(193,191)]
theorem wirePrivateChunk5_valid : ∀p∈wirePrivateChunk5,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
