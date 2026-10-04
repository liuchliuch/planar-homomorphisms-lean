import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk10 : List (ℕ×ℕ) := [(322,320),(323,321),(324,322),(325,323),(326,324),(327,325),(328,326),(329,327),(330,328),(331,329),(332,330),(333,331),(334,332),(335,333),(336,334),(337,335),(338,336),(339,337),(340,338),(341,339),(342,340),(343,341),(344,342),(345,343),(346,344),(347,345),(348,346),(349,347),(350,348),(351,349),(352,350),(353,351)]
theorem wirePrivateChunk10_valid : ∀p∈wirePrivateChunk10,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
