import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk10 : List (ℕ×ℕ) := [(324,320),(325,321),(326,322),(327,323),(328,324),(329,325),(330,326),(331,327),(332,328),(333,329),(334,330),(335,331),(336,332),(337,333),(338,334),(339,335),(340,336),(341,337),(342,338),(343,339),(344,340),(345,341),(346,342),(347,343),(348,344),(349,345),(350,346),(351,347),(352,348),(353,349),(354,350),(355,351)]
theorem crossPrivateChunk10_valid : ∀p∈crossPrivateChunk10,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
