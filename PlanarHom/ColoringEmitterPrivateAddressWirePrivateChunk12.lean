import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk12 : List (ℕ×ℕ) := [(386,384),(387,385),(388,386),(389,387),(390,388),(391,389),(392,390),(393,391),(394,392),(395,393),(396,394),(397,395),(398,396),(399,397),(400,398),(401,399),(402,400),(403,401),(404,402),(405,403),(406,404),(407,405),(408,406),(409,407),(410,408),(411,409),(412,410),(413,411),(414,412),(415,413),(416,414),(417,415)]
theorem wirePrivateChunk12_valid : ∀p∈wirePrivateChunk12,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
