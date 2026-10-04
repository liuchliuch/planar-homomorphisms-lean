import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk21 : List (ℕ×ℕ) := [(676,672),(677,673),(678,674),(679,675),(680,676),(681,677),(682,678),(683,679),(684,680),(685,681),(686,682),(687,683),(688,684),(689,685),(690,686),(691,687),(692,688),(693,689),(694,690),(695,691),(696,692),(697,693),(698,694),(699,695),(700,696),(701,697),(702,698),(703,699),(704,700),(705,701),(706,702),(707,703)]
theorem crossPrivateChunk21_valid : ∀p∈crossPrivateChunk21,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
