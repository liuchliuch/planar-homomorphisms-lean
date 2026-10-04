import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk12 : List (ℕ×ℕ) := [(388,384),(389,385),(390,386),(391,387),(392,388),(393,389),(394,390),(395,391),(396,392),(397,393),(398,394),(399,395),(400,396),(401,397),(402,398),(403,399),(404,400),(405,401),(406,402),(407,403),(408,404),(409,405),(410,406),(411,407),(412,408),(413,409),(414,410),(415,411),(416,412),(417,413),(418,414),(419,415)]
theorem crossPrivateChunk12_valid : ∀p∈crossPrivateChunk12,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
