import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk13 : List (ℕ×ℕ) := [(420,416),(421,417),(422,418),(423,419),(424,420),(425,421),(426,422),(427,423),(428,424),(429,425),(430,426),(431,427),(432,428),(433,429),(434,430),(435,431),(436,432),(437,433),(438,434),(439,435),(440,436),(441,437),(442,438),(443,439),(444,440),(445,441),(446,442),(447,443),(448,444),(449,445),(450,446),(451,447)]
theorem crossPrivateChunk13_valid : ∀p∈crossPrivateChunk13,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
