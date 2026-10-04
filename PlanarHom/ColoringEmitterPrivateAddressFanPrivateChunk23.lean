import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk23 : List (ℕ×ℕ) := [(739,736),(740,737),(741,738),(742,739),(743,740),(744,741),(745,742),(746,743),(747,744),(748,745),(749,746),(750,747),(751,748),(752,749),(753,750),(754,751),(755,752),(756,753),(757,754),(758,755),(759,756),(760,757),(761,758),(762,759),(763,760),(764,761),(765,762),(766,763),(767,764),(768,765),(769,766),(770,767)]
theorem fanPrivateChunk23_valid : ∀p∈fanPrivateChunk23,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
