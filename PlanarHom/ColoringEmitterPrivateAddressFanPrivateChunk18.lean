import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk18 : List (ℕ×ℕ) := [(579,576),(580,577),(581,578),(582,579),(583,580),(584,581),(585,582),(586,583),(587,584),(588,585),(589,586),(590,587),(591,588),(592,589),(593,590),(594,591),(595,592),(596,593),(597,594),(598,595),(599,596),(600,597),(601,598),(602,599),(603,600),(604,601),(605,602),(606,603),(607,604),(608,605),(609,606),(610,607)]
theorem fanPrivateChunk18_valid : ∀p∈fanPrivateChunk18,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
