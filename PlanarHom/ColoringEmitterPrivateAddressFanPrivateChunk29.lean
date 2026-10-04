import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk29 : List (ℕ×ℕ) := [(931,928),(932,929),(933,930),(934,931),(935,932),(936,933),(937,934),(938,935),(939,936),(940,937),(941,938),(942,939),(943,940),(944,941),(945,942),(946,943),(947,944),(948,945),(949,946),(950,947),(951,948),(952,949),(953,950),(954,951),(955,952),(956,953),(957,954),(958,955),(959,956),(960,957),(961,958),(962,959)]
theorem fanPrivateChunk29_valid : ∀p∈fanPrivateChunk29,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
