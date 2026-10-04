import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk19 : List (ℕ×ℕ) := [(611,608),(612,609),(613,610),(614,611),(615,612),(616,613),(617,614),(618,615),(619,616),(620,617),(621,618),(622,619),(623,620),(624,621),(625,622),(626,623),(627,624),(628,625),(629,626),(630,627),(631,628),(632,629),(633,630),(634,631),(635,632),(636,633),(637,634),(638,635),(639,636),(640,637),(641,638),(642,639)]
theorem fanPrivateChunk19_valid : ∀p∈fanPrivateChunk19,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
