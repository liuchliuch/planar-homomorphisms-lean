import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk5 : List (ℕ×ℕ) := [(163,160),(164,161),(165,162),(166,163),(167,164),(168,165),(169,166),(170,167),(171,168),(172,169),(173,170),(174,171),(175,172),(176,173),(177,174),(178,175),(179,176),(180,177),(181,178),(182,179),(183,180),(184,181),(185,182),(186,183),(187,184),(188,185),(189,186),(190,187),(191,188),(192,189),(193,190),(194,191)]
theorem fanPrivateChunk5_valid : ∀p∈fanPrivateChunk5,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
