import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk27 : List (ℕ×ℕ) := [(868,864),(869,865),(870,866),(871,867),(872,868),(873,869),(874,870),(875,871),(876,872),(877,873),(878,874),(879,875),(880,876),(881,877),(882,878),(883,879),(884,880),(885,881),(886,882),(887,883),(888,884),(889,885),(890,886),(891,887),(892,888),(893,889),(894,890),(895,891),(896,892),(897,893),(898,894),(899,895)]
theorem crossPrivateChunk27_valid : ∀p∈crossPrivateChunk27,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
