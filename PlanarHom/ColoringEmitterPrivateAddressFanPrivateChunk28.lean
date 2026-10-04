import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk28 : List (ℕ×ℕ) := [(899,896),(900,897),(901,898),(902,899),(903,900),(904,901),(905,902),(906,903),(907,904),(908,905),(909,906),(910,907),(911,908),(912,909),(913,910),(914,911),(915,912),(916,913),(917,914),(918,915),(919,916),(920,917),(921,918),(922,919),(923,920),(924,921),(925,922),(926,923),(927,924),(928,925),(929,926),(930,927)]
theorem fanPrivateChunk28_valid : ∀p∈fanPrivateChunk28,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
