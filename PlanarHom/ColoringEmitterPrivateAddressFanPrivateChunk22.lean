import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk22 : List (ℕ×ℕ) := [(707,704),(708,705),(709,706),(710,707),(711,708),(712,709),(713,710),(714,711),(715,712),(716,713),(717,714),(718,715),(719,716),(720,717),(721,718),(722,719),(723,720),(724,721),(725,722),(726,723),(727,724),(728,725),(729,726),(730,727),(731,728),(732,729),(733,730),(734,731),(735,732),(736,733),(737,734),(738,735)]
theorem fanPrivateChunk22_valid : ∀p∈fanPrivateChunk22,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
