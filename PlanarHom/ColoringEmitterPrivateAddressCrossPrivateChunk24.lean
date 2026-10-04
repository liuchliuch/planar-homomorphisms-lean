import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk24 : List (ℕ×ℕ) := [(772,768),(773,769),(774,770),(775,771),(776,772),(777,773),(778,774),(779,775),(780,776),(781,777),(782,778),(783,779),(784,780),(785,781),(786,782),(787,783),(788,784),(789,785),(790,786),(791,787),(792,788),(793,789),(794,790),(795,791),(796,792),(797,793),(798,794),(799,795),(800,796),(801,797),(802,798),(803,799)]
theorem crossPrivateChunk24_valid : ∀p∈crossPrivateChunk24,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
