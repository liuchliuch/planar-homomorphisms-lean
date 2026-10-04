import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk9 : List (ℕ×ℕ) := [(292,288),(293,289),(294,290),(295,291),(296,292),(297,293),(298,294),(299,295),(300,296),(301,297),(302,298),(303,299),(304,300),(305,301),(306,302),(307,303),(308,304),(309,305),(310,306),(311,307),(312,308),(313,309),(314,310),(315,311),(316,312),(317,313),(318,314),(319,315),(320,316),(321,317),(322,318),(323,319)]
theorem crossPrivateChunk9_valid : ∀p∈crossPrivateChunk9,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
