import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk22 : List (ℕ×ℕ) := [(708,704),(709,705),(710,706),(711,707),(712,708),(713,709),(714,710),(715,711),(716,712),(717,713),(718,714),(719,715),(720,716),(721,717),(722,718),(723,719),(724,720),(725,721),(726,722),(727,723),(728,724),(729,725),(730,726),(731,727),(732,728),(733,729),(734,730),(735,731),(736,732),(737,733),(738,734),(739,735)]
theorem crossPrivateChunk22_valid : ∀p∈crossPrivateChunk22,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
