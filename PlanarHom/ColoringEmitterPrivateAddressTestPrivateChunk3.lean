import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def testPrivateChunk3 : List (ℕ×ℕ) := [(99,96),(100,97),(101,98),(102,99),(103,100),(104,101),(111,102),(112,103),(113,104)]
theorem testPrivateChunk3_valid : ∀p∈testPrivateChunk3,address .test p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
