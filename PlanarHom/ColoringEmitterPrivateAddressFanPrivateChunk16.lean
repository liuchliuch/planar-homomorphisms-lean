import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk16 : List (ℕ×ℕ) := [(515,512),(516,513),(517,514),(518,515),(519,516),(520,517),(521,518),(522,519),(523,520),(524,521),(525,522),(526,523),(527,524),(528,525),(529,526),(530,527),(531,528),(532,529),(533,530),(534,531),(535,532),(536,533),(537,534),(538,535),(539,536),(540,537),(541,538),(542,539),(543,540),(544,541),(545,542),(546,543)]
theorem fanPrivateChunk16_valid : ∀p∈fanPrivateChunk16,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
