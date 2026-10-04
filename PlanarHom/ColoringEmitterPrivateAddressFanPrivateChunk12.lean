import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk12 : List (ℕ×ℕ) := [(387,384),(388,385),(389,386),(390,387),(391,388),(392,389),(393,390),(394,391),(395,392),(396,393),(397,394),(398,395),(399,396),(400,397),(401,398),(402,399),(403,400),(404,401),(405,402),(406,403),(407,404),(408,405),(409,406),(410,407),(411,408),(412,409),(413,410),(414,411),(415,412),(416,413),(417,414),(418,415)]
theorem fanPrivateChunk12_valid : ∀p∈fanPrivateChunk12,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
