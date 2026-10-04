import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk4 : List (ℕ×ℕ) := [(132,128),(133,129),(134,130),(135,131),(136,132),(137,133),(138,134),(139,135),(140,136),(141,137),(142,138),(143,139),(144,140),(145,141),(146,142),(147,143),(148,144),(149,145),(150,146),(151,147),(152,148),(153,149),(154,150),(155,151),(156,152),(157,153),(158,154),(159,155),(160,156),(161,157),(162,158),(163,159)]
theorem crossPrivateChunk4_valid : ∀p∈crossPrivateChunk4,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
