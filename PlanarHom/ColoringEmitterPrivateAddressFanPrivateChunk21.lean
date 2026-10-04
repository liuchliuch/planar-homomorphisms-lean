import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk21 : List (ℕ×ℕ) := [(675,672),(676,673),(677,674),(678,675),(679,676),(680,677),(681,678),(682,679),(683,680),(684,681),(685,682),(686,683),(687,684),(688,685),(689,686),(690,687),(691,688),(692,689),(693,690),(694,691),(695,692),(696,693),(697,694),(698,695),(699,696),(700,697),(701,698),(702,699),(703,700),(704,701),(705,702),(706,703)]
theorem fanPrivateChunk21_valid : ∀p∈fanPrivateChunk21,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
