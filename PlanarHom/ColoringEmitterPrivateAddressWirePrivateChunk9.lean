import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk9 : List (ℕ×ℕ) := [(290,288),(291,289),(292,290),(293,291),(294,292),(295,293),(296,294),(297,295),(298,296),(299,297),(300,298),(301,299),(302,300),(303,301),(304,302),(305,303),(306,304),(307,305),(308,306),(309,307),(310,308),(311,309),(312,310),(313,311),(314,312),(315,313),(316,314),(317,315),(318,316),(319,317),(320,318),(321,319)]
theorem wirePrivateChunk9_valid : ∀p∈wirePrivateChunk9,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
