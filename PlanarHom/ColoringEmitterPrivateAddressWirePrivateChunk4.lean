import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk4 : List (ℕ×ℕ) := [(130,128),(131,129),(132,130),(133,131),(134,132),(135,133),(136,134),(137,135),(138,136),(139,137),(140,138),(141,139),(142,140),(143,141),(144,142),(145,143),(146,144),(147,145),(148,146),(149,147),(150,148),(151,149),(152,150),(153,151),(154,152),(155,153),(156,154),(157,155),(158,156),(159,157),(160,158),(161,159)]
theorem wirePrivateChunk4_valid : ∀p∈wirePrivateChunk4,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
