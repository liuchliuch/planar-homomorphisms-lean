import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk13 : List (ℕ×ℕ) := [(419,416),(420,417),(421,418),(422,419),(423,420),(424,421),(425,422),(426,423),(427,424),(428,425),(429,426),(430,427),(431,428),(432,429),(433,430),(434,431),(435,432),(436,433),(437,434),(438,435),(439,436),(440,437),(441,438),(442,439),(443,440),(444,441),(445,442),(446,443),(447,444),(448,445),(449,446),(450,447)]
theorem fanPrivateChunk13_valid : ∀p∈fanPrivateChunk13,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
