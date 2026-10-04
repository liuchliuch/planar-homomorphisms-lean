import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk16 : List (ℕ×ℕ) := [(514,512),(515,513),(516,514),(521,515),(522,516),(523,517),(524,518),(525,519),(526,520),(527,521),(528,522),(529,523)]
theorem wirePrivateChunk16_valid : ∀p∈wirePrivateChunk16,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
