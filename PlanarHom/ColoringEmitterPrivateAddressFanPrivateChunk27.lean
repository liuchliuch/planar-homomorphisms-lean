import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk27 : List (ℕ×ℕ) := [(867,864),(868,865),(869,866),(870,867),(871,868),(872,869),(873,870),(874,871),(875,872),(876,873),(877,874),(878,875),(879,876),(880,877),(881,878),(882,879),(883,880),(884,881),(885,882),(886,883),(887,884),(888,885),(889,886),(890,887),(891,888),(892,889),(893,890),(894,891),(895,892),(896,893),(897,894),(898,895)]
theorem fanPrivateChunk27_valid : ∀p∈fanPrivateChunk27,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
