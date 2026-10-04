import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk8 : List (ℕ×ℕ) := [(259,256),(260,257),(261,258),(262,259),(263,260),(264,261),(265,262),(266,263),(267,264),(268,265),(269,266),(270,267),(271,268),(272,269),(273,270),(274,271),(275,272),(276,273),(277,274),(278,275),(279,276),(280,277),(281,278),(282,279),(283,280),(284,281),(285,282),(286,283),(287,284),(288,285),(289,286),(290,287)]
theorem fanPrivateChunk8_valid : ∀p∈fanPrivateChunk8,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
