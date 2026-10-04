import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk13 : List (ℕ×ℕ) := [(418,416),(419,417),(420,418),(421,419),(422,420),(423,421),(424,422),(425,423),(426,424),(427,425),(428,426),(429,427),(430,428),(431,429),(432,430),(433,431),(434,432),(435,433),(436,434),(437,435),(438,436),(439,437),(440,438),(441,439),(442,440),(443,441),(444,442),(445,443),(446,444),(447,445),(448,446),(449,447)]
theorem wirePrivateChunk13_valid : ∀p∈wirePrivateChunk13,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
