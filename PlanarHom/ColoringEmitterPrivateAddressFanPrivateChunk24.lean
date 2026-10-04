import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk24 : List (ℕ×ℕ) := [(771,768),(772,769),(773,770),(774,771),(775,772),(776,773),(777,774),(778,775),(779,776),(780,777),(781,778),(782,779),(783,780),(784,781),(785,782),(786,783),(787,784),(788,785),(789,786),(790,787),(791,788),(792,789),(793,790),(794,791),(795,792),(796,793),(797,794),(798,795),(799,796),(800,797),(801,798),(802,799)]
theorem fanPrivateChunk24_valid : ∀p∈fanPrivateChunk24,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
