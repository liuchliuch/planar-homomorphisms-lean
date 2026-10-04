import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk20 : List (ℕ×ℕ) := [(644,640),(645,641),(646,642),(647,643),(648,644),(649,645),(650,646),(651,647),(652,648),(653,649),(654,650),(655,651),(656,652),(657,653),(658,654),(659,655),(660,656),(661,657),(662,658),(663,659),(664,660),(665,661),(666,662),(667,663),(668,664),(669,665),(670,666),(671,667),(672,668),(673,669),(674,670),(675,671)]
theorem crossPrivateChunk20_valid : ∀p∈crossPrivateChunk20,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
