import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk17 : List (ℕ×ℕ) := [(547,544),(548,545),(549,546),(550,547),(551,548),(552,549),(553,550),(554,551),(555,552),(556,553),(557,554),(558,555),(559,556),(560,557),(561,558),(562,559),(563,560),(564,561),(565,562),(566,563),(567,564),(568,565),(569,566),(570,567),(571,568),(572,569),(573,570),(574,571),(575,572),(576,573),(577,574),(578,575)]
theorem fanPrivateChunk17_valid : ∀p∈fanPrivateChunk17,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
