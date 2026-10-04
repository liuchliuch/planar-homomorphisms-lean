import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk23 : List (ℕ×ℕ) := [(740,736),(741,737),(742,738),(743,739),(744,740),(745,741),(746,742),(747,743),(748,744),(749,745),(750,746),(751,747),(752,748),(753,749),(754,750),(755,751),(756,752),(757,753),(758,754),(759,755),(760,756),(761,757),(762,758),(763,759),(764,760),(765,761),(766,762),(767,763),(768,764),(769,765),(770,766),(771,767)]
theorem crossPrivateChunk23_valid : ∀p∈crossPrivateChunk23,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
