import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk18 : List (ℕ×ℕ) := [(580,576),(581,577),(582,578),(583,579),(584,580),(585,581),(586,582),(587,583),(588,584),(589,585),(590,586),(591,587),(592,588),(593,589),(594,590),(595,591),(596,592),(597,593),(598,594),(599,595),(600,596),(601,597),(602,598),(603,599),(604,600),(605,601),(606,602),(607,603),(608,604),(609,605),(610,606),(611,607)]
theorem crossPrivateChunk18_valid : ∀p∈crossPrivateChunk18,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
