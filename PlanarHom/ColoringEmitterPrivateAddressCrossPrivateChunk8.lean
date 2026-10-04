import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk8 : List (ℕ×ℕ) := [(260,256),(261,257),(262,258),(263,259),(264,260),(265,261),(266,262),(267,263),(268,264),(269,265),(270,266),(271,267),(272,268),(273,269),(274,270),(275,271),(276,272),(277,273),(278,274),(279,275),(280,276),(281,277),(282,278),(283,279),(284,280),(285,281),(286,282),(287,283),(288,284),(289,285),(290,286),(291,287)]
theorem crossPrivateChunk8_valid : ∀p∈crossPrivateChunk8,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
