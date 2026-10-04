import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk8 : List (ℕ×ℕ) := [(258,256),(259,257),(260,258),(261,259),(262,260),(263,261),(264,262),(265,263),(266,264),(267,265),(268,266),(269,267),(270,268),(271,269),(272,270),(273,271),(274,272),(275,273),(276,274),(277,275),(278,276),(279,277),(280,278),(281,279),(282,280),(283,281),(284,282),(285,283),(286,284),(287,285),(288,286),(289,287)]
theorem wirePrivateChunk8_valid : ∀p∈wirePrivateChunk8,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
