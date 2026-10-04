import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk5 : List (ℕ×ℕ) := [(164,160),(165,161),(166,162),(167,163),(168,164),(169,165),(170,166),(171,167),(172,168),(173,169),(174,170),(175,171),(176,172),(177,173),(178,174),(179,175),(180,176),(181,177),(182,178),(183,179),(184,180),(185,181),(186,182),(187,183),(188,184),(189,185),(190,186),(191,187),(192,188),(193,189),(194,190),(195,191)]
theorem crossPrivateChunk5_valid : ∀p∈crossPrivateChunk5,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
