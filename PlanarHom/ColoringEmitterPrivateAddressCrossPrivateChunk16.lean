import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk16 : List (ℕ×ℕ) := [(516,512),(517,513),(518,514),(519,515),(520,516),(521,517),(522,518),(523,519),(524,520),(525,521),(526,522),(527,523),(528,524),(529,525),(530,526),(531,527),(532,528),(533,529),(534,530),(535,531),(536,532),(537,533),(538,534),(539,535),(540,536),(541,537),(542,538),(543,539),(544,540),(545,541),(546,542),(547,543)]
theorem crossPrivateChunk16_valid : ∀p∈crossPrivateChunk16,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
