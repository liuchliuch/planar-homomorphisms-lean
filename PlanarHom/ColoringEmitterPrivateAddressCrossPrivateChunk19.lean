import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk19 : List (ℕ×ℕ) := [(612,608),(613,609),(614,610),(615,611),(616,612),(617,613),(618,614),(619,615),(620,616),(621,617),(622,618),(623,619),(624,620),(625,621),(626,622),(627,623),(628,624),(629,625),(630,626),(631,627),(632,628),(633,629),(634,630),(635,631),(636,632),(637,633),(638,634),(639,635),(640,636),(641,637),(642,638),(643,639)]
theorem crossPrivateChunk19_valid : ∀p∈crossPrivateChunk19,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
