import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk28 : List (ℕ×ℕ) := [(900,896),(901,897),(902,898),(903,899),(904,900),(905,901),(906,902),(907,903),(908,904),(909,905),(910,906),(911,907),(912,908),(913,909),(914,910),(915,911),(916,912),(917,913),(918,914),(919,915),(920,916),(921,917),(922,918),(923,919),(924,920),(925,921),(926,922),(927,923),(928,924),(929,925),(930,926),(931,927)]
theorem crossPrivateChunk28_valid : ∀p∈crossPrivateChunk28,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
