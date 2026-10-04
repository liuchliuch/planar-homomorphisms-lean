import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk4 : List (ℕ×ℕ) := [(131,128),(132,129),(133,130),(134,131),(135,132),(136,133),(137,134),(138,135),(139,136),(140,137),(141,138),(142,139),(143,140),(144,141),(145,142),(146,143),(147,144),(148,145),(149,146),(150,147),(151,148),(152,149),(153,150),(154,151),(155,152),(156,153),(157,154),(158,155),(159,156),(160,157),(161,158),(162,159)]
theorem fanPrivateChunk4_valid : ∀p∈fanPrivateChunk4,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
