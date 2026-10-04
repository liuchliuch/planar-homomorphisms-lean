import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk29 : List (ℕ×ℕ) := [(932,928),(933,929),(934,930),(935,931),(936,932),(937,933),(938,934),(939,935),(940,936),(941,937),(942,938),(943,939),(944,940),(945,941),(946,942),(947,943),(948,944),(949,945),(950,946),(951,947),(952,948),(953,949),(954,950),(955,951),(956,952),(957,953),(958,954),(959,955),(960,956),(961,957),(962,958),(963,959)]
theorem crossPrivateChunk29_valid : ∀p∈crossPrivateChunk29,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
