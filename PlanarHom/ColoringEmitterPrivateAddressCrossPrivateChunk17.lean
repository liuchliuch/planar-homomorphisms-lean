import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk17 : List (ℕ×ℕ) := [(548,544),(549,545),(550,546),(551,547),(552,548),(553,549),(554,550),(555,551),(556,552),(557,553),(558,554),(559,555),(560,556),(561,557),(562,558),(563,559),(564,560),(565,561),(566,562),(567,563),(568,564),(569,565),(570,566),(571,567),(572,568),(573,569),(574,570),(575,571),(576,572),(577,573),(578,574),(579,575)]
theorem crossPrivateChunk17_valid : ∀p∈crossPrivateChunk17,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
