import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk9 : List (ℕ×ℕ) := [(291,288),(292,289),(293,290),(294,291),(295,292),(296,293),(297,294),(298,295),(299,296),(300,297),(301,298),(302,299),(303,300),(304,301),(305,302),(306,303),(307,304),(308,305),(309,306),(310,307),(311,308),(312,309),(313,310),(314,311),(315,312),(316,313),(317,314),(318,315),(319,316),(320,317),(321,318),(322,319)]
theorem fanPrivateChunk9_valid : ∀p∈fanPrivateChunk9,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
