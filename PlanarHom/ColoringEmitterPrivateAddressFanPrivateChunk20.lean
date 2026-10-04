import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk20 : List (ℕ×ℕ) := [(643,640),(644,641),(645,642),(646,643),(647,644),(648,645),(649,646),(650,647),(651,648),(652,649),(653,650),(654,651),(655,652),(656,653),(657,654),(658,655),(659,656),(660,657),(661,658),(662,659),(663,660),(664,661),(665,662),(666,663),(667,664),(668,665),(669,666),(670,667),(671,668),(672,669),(673,670),(674,671)]
theorem fanPrivateChunk20_valid : ∀p∈fanPrivateChunk20,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
