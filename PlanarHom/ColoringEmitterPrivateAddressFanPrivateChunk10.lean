import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk10 : List (ℕ×ℕ) := [(323,320),(324,321),(325,322),(326,323),(327,324),(328,325),(329,326),(330,327),(331,328),(332,329),(333,330),(334,331),(335,332),(336,333),(337,334),(338,335),(339,336),(340,337),(341,338),(342,339),(343,340),(344,341),(345,342),(346,343),(347,344),(348,345),(349,346),(350,347),(351,348),(352,349),(353,350),(354,351)]
theorem fanPrivateChunk10_valid : ∀p∈fanPrivateChunk10,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
